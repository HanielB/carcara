//! An elaborator for Alethe proofs

mod core;
pub mod error;
mod growth;
mod hoist;
mod hole;
mod local;
mod polyeq;
mod prune;
pub use prune::prune;
mod reordering;
mod sat_refutation;
mod scopes;
mod uncrowding;

use crate::{
    Error,
    ast::{
        ContextStack, Polyeq, Problem, ProofNode, ProofNodeForest, Rc, StepNode, SubproofNode,
        VisitedNodes,
        Term, build_term, match_term,
        pool::{PrimitivePool, TermPool},
    },
    external::{ExternalTool, SatTools},
};
use carcara_macros::GenerateSetters;
use error::{ElaborationError, ElaborationErrorAtStep};
use indexmap::IndexSet;
use polyeq::PolyeqElaborator;
use std::cell::Cell;
use std::{
    collections::{HashMap, HashSet},
    path::Path,
    time::{Duration, Instant},
};

/// Prints the per-rewrite recipe costs collected when `CARCARA_RECIPE_COST` is set, and the
/// per-rule growth table collected when `CARCARA_RULE_GROWTH` is set.
pub fn report_recipe_costs() {
    core::rewrites::report_recipe_costs();
    growth::report();
}

/// Configuration options for [`Elaborator`].
#[derive(Debug, Default, Clone, GenerateSetters)]
pub struct Config {
    /// If `Some`, enables the elaboration of `lia_generic` steps using an external solver.
    ///
    /// This involves calling the solver to solve the linear integer arithmetic problem, checking
    /// the proof, and inserting it in the place of the `lia_generic` step.
    lia_solver: Option<ExternalTool>,

    /// Enables an optimization that reorders premises when uncrowding resolution steps, in order to
    /// further minimize the number of `contraction` steps added.
    uncrowd_rotation: bool,

    /// If `Some`, enables the elaboration of `all_simplify` and `rare_rewrite` steps using an
    /// external solver, inserting the solver's proof in the place of those steps.
    hole_solver: Option<ExternalTool>,

    /// The external tools used to elaborate `sat_refutation` steps.
    sat_ref_tools: Option<SatTools>,

    /// Keep the steps nothing on the path to the conclusion uses: disables both the
    /// conversion-time restriction of the forest to the conclusion's derivation and the
    /// print-time filter, so unused input steps survive elaboration verbatim.
    pub keep_unused: bool,

    /// The rules that the checker was told to accept as holes, via `--allowed-rules`. The `hoist`
    /// pass needs them to know which derivations it must not share, so that it cannot replace a
    /// real derivation by a holey one.
    pub allowed_rules: HashSet<String>,

    /// The RARE rule set given to the checker (via `--rare-file`). The `core-simp-rare` pass
    /// needs it to emit `rare_rewrite` lemmas when replaying the `*_simplify` rewrite chains.
    pub rare_rules: Option<crate::ast::rare_rules::Rules>,
}

impl Config {
    /// Constructs a new `Config`, with default settings.
    pub fn new() -> Self {
        Self::default()
    }
}

/// An elaboration pass, to be applied to a proof.
#[derive(Debug, Clone, Copy)]
pub enum ElaborationPass {
    /// Removes every step that the derivation of the empty clause does not use.
    Prune,
    Hoist,
    /// The `hoist` pass, additionally replacing every lemma scope whose discharged clause a
    /// premise-free rule proves outright by that single step.
    DeepHoist,
    /// Elaborates away all uses of polyequality in the proof.
    Polyeq,
    /// Fills holes in the proof using an external solver.
    Hole,
    Core,
    /// The reductions of the *expensive* tier — `poly_simp`, `aci_simp`, the clausal equality
    /// rules and `sko_ex` — which the other regimes leave alone. Applied on top of one of them, it
    /// takes the proof the rest of the way to the core vocabulary.
    CoreExpensive,
    /// The `core` pass, additionally replaying the `*_simplify` rules as chains of
    /// `rare_rewrite`/`evaluate` lemmas (the rewrite vocabulary itself is kept).
    CoreSimpRare,
    /// The `core` pass, additionally reducing `*_simplify` and `rare_rewrite` to the core but
    /// keeping `evaluate`. The rung between `core-simp-rare` and `core-taut`: it isolates the
    /// cost of removing constant folding as a primitive.
    CoreNoRare,
    /// The `core` pass, additionally reducing the whole rewrite vocabulary (`*_simplify`,
    /// `evaluate`, `rare_rewrite`) to the core plus the term-`ite` selection axioms.
    CoreTaut,
    /// Performs small local elaborations.
    ///
    /// Currently, this affects the rules:
    /// - `eq_transitive`
    /// - `trans`
    /// - `resolution`
    /// - `cong`
    /// - `eq_congruent`
    /// - `eq_congruent_pred`
    /// - `bounded_farkas`
    /// - `eq_mp`
    Local,
    /// Uncrowds `resolution` steps, removing the implicit removal of duplicates by adding
    /// `contraction` steps.
    Uncrowd,
    /// Removes `reordering` steps from the proof, recomputing the conclusions of order-sensitive
    /// steps when necessary.
    Reordering,
    /// Elaborates `sat_refutation` steps using an external SAT solver.
    SatRefutation,
}

/// A proof elaborator for Alethe.
pub struct Elaborator<'e> {
    pool: &'e mut PrimitivePool,
    problem: &'e Problem,
    config: Config,
}

/// How many times [`Elaborator::elaborate_core_expensive`] may repeat. A nest of `bind` scopes
/// loses one layer per round, and nests deeper than this are vanishingly rare.
const MAX_EXPENSIVE_ROUNDS: usize = 8;

/// The `bind` scopes that sit inside another `bind` scope.
///
/// Those wait for a later round. Anything a reduction builds is written against the substitution
/// in force where it is built, and reducing an enclosing `bind` afterwards would carry it out of
/// that substitution and leave it stating something else — so the enclosing one goes first, and
/// the scopes it contained are then reduced where they have landed.
fn nested_binds(proof: &ProofNodeForest) -> HashSet<String> {
    fn closes_bind(node: &Rc<ProofNode>) -> bool {
        match node.as_ref() {
            ProofNode::Subproof(sub) => sub.last_step.as_step().is_some_and(|s| s.rule == "bind"),
            _ => false,
        }
    }

    let mut out = HashSet::new();
    let mut seen: HashSet<(*const ProofNode, bool)> = HashSet::new();
    let mut stack: Vec<(&Rc<ProofNode>, bool)> = proof.0.iter().map(|r| (r, false)).collect();
    while let Some((node, inside)) = stack.pop() {
        if !seen.insert((Rc::as_ptr(node), inside)) {
            continue;
        }
        match node.as_ref() {
            ProofNode::Assume { .. } => (),
            ProofNode::Step(s) => stack.extend(
                s.premises
                    .iter()
                    .chain(&s.discharge)
                    .chain(s.previous_step.iter())
                    .map(|p| (p, inside)),
            ),
            ProofNode::Subproof(sub) => {
                let is_bind = closes_bind(node);
                if is_bind && inside {
                    // Keyed by the closing step's id, not by the node: a pass is handed a
                    // *rebuilt* node whenever one of its premises moved, and that node is not
                    // the one this traversal saw
                    if let Some(step) = sub.last_step.as_step() {
                        out.insert(step.id.clone());
                    }
                }
                let within = inside || is_bind;
                stack.push((&sub.last_step, within));
                stack.extend(sub.extra_steps.iter().map(|e| (e, within)));
                stack.extend(sub.outbound_premises.iter().map(|p| (p, inside)));
            }
        }
    }
    out
}

/// Debug validation (`CARCARA_VALIDATE_FOREST`): checks that every subproof's
/// `outbound_premises` lists every premise edge that leaves the scope.
fn validate_forest(proof: &ProofNodeForest, pass: ElaborationPass) {
    fn check_scope(sub: &SubproofNode, closing_depth: usize, scope_id: &str, pass: ElaborationPass) {
        let listed: HashSet<*const ProofNode> =
            sub.outbound_premises.iter().map(Rc::as_ptr).collect();
        let mut seen = HashSet::new();
        let mut stack = vec![&sub.last_step];
        while let Some(node) = stack.pop() {
            if !seen.insert(Rc::as_ptr(node)) {
                continue;
            }
            if node.depth() < closing_depth {
                continue; // outside this scope's interior; reached via an outbound edge
            }
            let premises: Vec<&Rc<ProofNode>> = match node.as_ref() {
                ProofNode::Assume { .. } => Vec::new(),
                ProofNode::Step(s) => s
                    .premises
                    .iter()
                    .chain(&s.discharge)
                    .chain(s.previous_step.iter())
                    .collect(),
                ProofNode::Subproof(inner) => {
                    stack.push(&inner.last_step);
                    stack.extend(inner.extra_steps.iter());
                    inner.outbound_premises.iter().collect()
                }
            };
            for p in premises {
                let crosses = p.depth() < closing_depth;
                if crosses && !listed.contains(&Rc::as_ptr(p)) {
                    eprintln!(
                        "FOREST-INVARIANT after {:?}: scope '{}' is missing outbound premise \
                         '{}' (depth {} < scope interior {}), referenced from '{}'",
                        pass,
                        scope_id,
                        p.id(),
                        p.depth(),
                        closing_depth,
                        node.id(),
                    );
                }
                stack.push(p);
            }
        }
    }
    let mut seen = HashSet::new();
    let mut stack: Vec<&Rc<ProofNode>> = proof.0.iter().collect();
    while let Some(node) = stack.pop() {
        if !seen.insert(Rc::as_ptr(node)) {
            continue;
        }
        match node.as_ref() {
            ProofNode::Assume { .. } => (),
            ProofNode::Step(s) => stack.extend(
                s.premises
                    .iter()
                    .chain(&s.discharge)
                    .chain(s.previous_step.iter()),
            ),
            ProofNode::Subproof(sub) => {
                check_scope(sub, sub.last_step.depth(), sub.last_step.id(), pass);
                stack.push(&sub.last_step);
                stack.extend(sub.extra_steps.iter());
                stack.extend(sub.outbound_premises.iter());
            }
        }
    }
}

/// The number of `bind` scopes left in the proof.
fn count_binds(proof: &ProofNodeForest) -> usize {
    let mut count = 0;
    let mut visited = VisitedNodes::new();
    for root in proof.0.iter() {
        root.traverse_with(&mut visited, |node| {
            if let ProofNode::Subproof(sub) = node.as_ref() {
                if sub.last_step.as_step().is_some_and(|s| s.rule == "bind") {
                    count += 1;
                }
            }
        });
    }
    count
}

impl<'e> Elaborator<'e> {
    /// Constructs a new [`Elaborator`] with the given `pool`, `problem`, and `config`.
    pub fn new(pool: &'e mut PrimitivePool, problem: &'e Problem, config: Config) -> Self {
        Self { pool, problem, config }
    }

    /// Elaborates a proof, applying the default pipeline of passes.
    pub fn elaborate_with_default_pipeline(
        &mut self,
        proof: ProofNodeForest,
        proof_filename: &Path,
    ) -> Result<ProofNodeForest, Error> {
        use ElaborationPass::*;
        let pipeline = vec![Hoist, Polyeq, Hole, Local, Uncrowd, Reordering];
        self.elaborate(proof, proof_filename, pipeline)
    }

    /// Elaborates a proof, applying the given `pipeline` of passes, in order.
    pub fn elaborate(
        &mut self,
        proof: ProofNodeForest,
        proof_filename: &Path,
        pipeline: Vec<ElaborationPass>,
    ) -> Result<ProofNodeForest, Error> {
        Ok(self
            .elaborate_with_stats(proof, proof_filename, pipeline)?
            .0)
    }

    /// Elaborates a proof, applying the given `pipeline` of passes in order, and returns the
    /// elaborated proof together with the time spent on each pass.
    pub fn elaborate_with_stats(
        &mut self,
        proof: ProofNodeForest,
        proof_filename: &Path,
        pipeline: Vec<ElaborationPass>,
    ) -> Result<(ProofNodeForest, Vec<Duration>), Error> {
        let mut durations = Vec::new();
        let mut current = proof;
        for pass in pipeline {
            let time = Instant::now();
            let result = match pass {
                ElaborationPass::Prune => Ok(prune::prune(current)),
                ElaborationPass::Hoist => {
                    Ok(hoist::hoist(self.pool, current, &self.config.allowed_rules, false))
                }
                ElaborationPass::DeepHoist => {
                    Ok(hoist::hoist(self.pool, current, &self.config.allowed_rules, true))
                }
                ElaborationPass::Polyeq => self.elaborate_polyeq(current),
                ElaborationPass::Hole => self.elaborate_hole(current),
                ElaborationPass::Core => {
                    self.elaborate_core(current, core::rewrites::RewriteReduction::Keep)
                }
                ElaborationPass::CoreSimpRare => {
                    self.elaborate_core(current, core::rewrites::RewriteReduction::ToRare)
                }
                ElaborationPass::CoreNoRare => {
                    self.elaborate_core(current, core::rewrites::RewriteReduction::ToCoreKeepEval)
                }
                ElaborationPass::CoreTaut => {
                    self.elaborate_core(current, core::rewrites::RewriteReduction::ToCore)
                }
                ElaborationPass::CoreExpensive => self.elaborate_core_expensive(current),
                ElaborationPass::Local => self.elaborate_local(current),
                ElaborationPass::Uncrowd => current.mutate(|_, node, _| match node.as_ref() {
                    ProofNode::Step(s)
                        if (s.rule == "resolution" || s.rule == "th_resolution")
                            && !s.args.is_empty() =>
                    {
                        uncrowding::uncrowd_resolution(self.pool, s, self.config.uncrowd_rotation)
                            .map_err(|e| e.at(s))
                    }
                    _ => Ok(node.clone()),
                }),
                ElaborationPass::Reordering => reordering::remove_reorderings(current),
                ElaborationPass::SatRefutation => {
                    if self.config.sat_ref_tools.is_some() {
                        current.mutate(|_, node, _| match node.as_ref() {
                            ProofNode::Step(s) if (s.rule == "sat_refutation") => {
                                // TODO: proper error handling
                                Ok(sat_refutation::sat_refutation(self, s)
                                    .unwrap_or_else(|| node.clone()))
                            }
                            _ => Ok(node.clone()),
                        })
                    } else {
                        Ok(current)
                    }
                }
            };
            current = result.map_err(|e| e.at(proof_filename, pass))?;
            if std::env::var_os("CARCARA_VALIDATE_FOREST").is_some() {
                validate_forest(&current, pass);
            }
            durations.push(time.elapsed());
        }
        Ok((current, durations))
    }

    fn elaborate_polyeq(
        &mut self,
        proof: ProofNodeForest,
    ) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
        fn get_elaboration_function(rule: &str) -> Option<ElaborationFunc> {
            Some(match rule {
                "refl" => polyeq::reflexivity::refl,
                "forall_inst" => polyeq::quantifiers::forall_inst,
                "subproof" => polyeq::subproof::subproof,
                "ite_intro" => polyeq::tautology::ite_intro,
                "bfun_elim" => polyeq::clausification::bfun_elim,
                _ => return None,
            })
        }

        proof.mutate(|context, node, _| match node.as_ref() {
            ProofNode::Assume { id, depth, term }
                if context.is_empty() && !self.problem.premises.contains(term) =>
            {
                Ok(self.elaborate_assume(id, *depth, term))
            }
            ProofNode::Step(s) => {
                if let Some(func) = get_elaboration_function(&s.rule) {
                    func(self.pool, context, s).map_err(|e| e.at(s))
                } else {
                    Ok(node.clone())
                }
            }
            _ => Ok(node.clone()),
        })
    }

    fn elaborate_hole(
        &mut self,
        proof: ProofNodeForest,
    ) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
        // Skip `mutate` in the common case where neither option was given
        if self.config.hole_solver.is_none() && self.config.lia_solver.is_none() {
            return Ok(proof);
        }

        proof.mutate(|_, node, _| match node.as_ref() {
            ProofNode::Step(s)
                if self.config.hole_solver.is_some()
                    && (s.rule == "all_simplify" || s.rule == "rare_rewrite") =>
            {
                hole::hole(self, s).map_err(|e| e.at(s))
            }
            ProofNode::Step(s) if self.config.lia_solver.is_some() && s.rule == "lia_generic" => {
                hole::lia_generic(self, s).map_err(|e| e.at(s))
            }
            _ => Ok(node.clone()),
        })
    }

    /// The `core` pass: reduces every step in the *reducible* tier of the core classification to
    /// a derivation over the core fragment. Reductions are best-effort: if a step has a shape a
    /// recipe does not cover (or a reduction fails), the step is kept unchanged and a warning is
    /// logged, so the pass never rejects a proof.
    ///
    /// Recipes are memoized by their conclusion: a derivation that is self-contained and mentions
    /// no anchor-bound variable is emitted once, at depth 0, and every later step with the same
    /// conclusion is replaced by it. See [`core::share`].
    fn elaborate_core(
        &mut self,
        proof: ProofNodeForest,
        rewrites: core::rewrites::RewriteReduction,
    ) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
        use core::rewrites::RewriteReduction;

        let mut sharing = core::share::Sharing::new(&proof);
        let rare_rules = self.config.rare_rules.clone();
        let result = proof.mutate(|context, node, _| {
            match node.as_ref() {
                ProofNode::Step(s) => {
                    let attempt = if core::rewrites::is_rewrite_rule(&s.rule) {
                        match s.rule.as_str() {
                            // These are *reducible*, so the plain `core` pass reduces them
                            // too: `and_simplify`/`or_simplify` because their aci-compatible
                            // instances are `aci_simp` renames and the short-circuiting ones
                            // constant-size chains, and the arithmetic bundle because it
                            // renames onto `poly_simp` (or `evaluate`, for the integer cases)
                            "and_simplify"
                            | "or_simplify"
                            | "prod_simplify"
                            | "sum_simplify"
                            | "minus_simplify"
                            | "unary_minus_simplify"
                            | "div_simplify" => Some(core::rewrites::elaborate_simplify(
                                self.pool,
                                context,
                                s,
                                rewrites,
                                rare_rules.as_ref(),
                            )),
                            _ if rewrites == RewriteReduction::Keep => None,
                            "evaluate" if rewrites == RewriteReduction::ToCore => {
                                Some(core::rewrites::elaborate_evaluate(self.pool, context, s))
                            }
                            "rare_rewrite"
                                if matches!(
                                    rewrites,
                                    RewriteReduction::ToCore | RewriteReduction::ToCoreKeepEval
                                ) =>
                            {
                                Some(core::rewrites::elaborate_rare_rewrite(
                                    self.pool, context, s,
                                ))
                            }
                            "evaluate" | "rare_rewrite" => None,
                            _ => Some(core::rewrites::elaborate_simplify(
                                self.pool,
                                context,
                                s,
                                rewrites,
                                rare_rules.as_ref(),
                            )),
                        }
                    } else {
                        core::get_elaboration_function(&s.rule)
                            .map(|func| func(self.pool, context, s))
                    };
                    match attempt {
                        Some(Ok(new_node)) => {
                            // The derivation is measured *after* sharing, so a reduction whose
                            // result an earlier identical one replaces is charged nothing — the
                            // proof really did not grow for it
                            let shared = sharing.share(self.pool, context, s, new_node);
                            growth::record(s, &shared);
                            return Ok(shared);
                        }
                        Some(Err(e)) => {
                            log::warn!(
                                "core elaboration of '{}' ({}) failed, keeping step: {}",
                                s.id,
                                s.rule,
                                e
                            );
                        }
                        None => (),
                    }
                }
                // A pass may be handed a whole subproof; this one has nothing to do with one
                ProofNode::Subproof(_) => (),
                ProofNode::Assume { .. } => (),
            }
            Ok(node.clone())
        });
        log::info!("core elaboration: sharing saved {} steps", sharing.saved());
        result
    }

    /// The `core-expensive` pass: applies the reductions of the *expensive* tier — `poly_simp`,
    /// `aci_simp`, the clausal equality rules and `sko_ex` — which the other regimes deliberately
    /// leave alone. It shares derivations exactly as the main pass does, and is likewise
    /// best-effort: a shape a recipe does not cover keeps its step.
    /// Runs the expensive reductions, repeating while `bind` steps keep disappearing.
    ///
    /// A `bind` is reduced only where its anchor is the outermost one left (see
    /// [`core::bind::bind`]), so a nest of them peels one layer per round: each round's
    /// replacement leaves the scopes it contained standing outside the anchor that enclosed
    /// them, and the next round reduces those.
    fn elaborate_core_expensive(
        &mut self,
        proof: ProofNodeForest,
    ) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
        let mut proof = proof;
        for round in 0..MAX_EXPENSIVE_ROUNDS {
            let reduced = Cell::new(0usize);
            proof = self.elaborate_core_expensive_round(proof, &reduced)?;
            if count_binds(&proof) == 0 {
                break;
            }
            // A round that reduced nothing will not do better for being repeated. Counting what
            // was reduced rather than what is left is what makes this terminate: a replay copies
            // the scopes inside the body once per direction, so the number of `bind` scopes can
            // *rise* in a round that made real progress
            if reduced.get() == 0 {
                break;
            }
            log::info!(
                "expensive elaboration round {}: {} `bind` scopes reduced, {} left",
                round + 1,
                reduced.get(),
                count_binds(&proof)
            );
        }
        Ok(proof)
    }

    fn elaborate_core_expensive_round(
        &mut self,
        proof: ProofNodeForest,
        reduced: &Cell<usize>,
    ) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
        let mut sharing = core::share::Sharing::new(&proof);
        let deferred = nested_binds(&proof);
        let result = proof.mutate(|context, node, _| {
            match node.as_ref() {
                ProofNode::Step(s) => {
                    if let Some(func) = core::get_expensive_elaboration_function(&s.rule) {
                        match func(self.pool, context, s) {
                            Ok(new_node) => {
                                let shared = sharing.share(self.pool, context, s, new_node);
                                growth::record(s, &shared);
                                return Ok(shared);
                            }
                            Err(e) => log::warn!(
                                "expensive elaboration of '{}' ({}) failed, keeping step: {}",
                                s.id,
                                s.rule,
                                e
                            ),
                        }
                    }
                }
                // `bind` closes a subproof, and its reduction replaces the *whole* scope: the
                // derivation that takes its place lives outside the anchor, since the anchor's
                // substitution is exactly what it eliminates
                ProofNode::Subproof(sub) => {
                    let last = sub.last_step.as_step();
                    if last.is_some_and(|s| s.rule == "bind")
                        && !last.is_some_and(|s| deferred.contains(&s.id))
                    {
                        let s = last.unwrap();
                        match core::bind::bind(self.pool, context, node) {
                            Ok(new_node) => {
                                growth::record(s, &new_node);
                                reduced.set(reduced.get() + 1);
                                return Ok(new_node);
                            }
                            Err(e) => log::warn!(
                                "expensive elaboration of '{}' (bind) failed, keeping step: {}",
                                s.id,
                                e
                            ),
                        }
                    }
                }
                ProofNode::Assume { .. } => (),
            }
            Ok(node.clone())
        });
        log::info!(
            "expensive elaboration: sharing saved {} steps",
            sharing.saved()
        );
        result
    }

    fn elaborate_local(
        &mut self,
        proof: ProofNodeForest,
    ) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
        fn get_elaboration_function(rule: &str) -> Option<ElaborationFunc> {
            Some(match rule {
                "eq_transitive" => local::transitivity::eq_transitive,
                "trans" => local::transitivity::trans,
                "resolution" | "th_resolution" => local::resolution::resolution,
                "cong" => local::congruence::cong,
                "eq_congruent" => local::congruence::eq_congruent,
                "eq_congruent_pred" => local::congruence::eq_congruent_pred,
                "bounded_farkas" => local::farkas::bounded_farkas,
                "eq_mp" => local::eq_mp::eq_mp,
                _ => return None,
            })
        }

        proof.mutate(|context, node, _| {
            match node.as_ref() {
                ProofNode::Step(s) => {
                    if let Some(func) = get_elaboration_function(&s.rule) {
                        return func(self.pool, context, s).map_err(|e| e.at(s));
                    }
                }
                ProofNode::Subproof(_) => (),
                ProofNode::Assume { .. } => (),
            }
            Ok(node.clone())
        })
    }

    fn elaborate_assume(&mut self, id: &str, depth: usize, term: &Rc<Term>) -> Rc<ProofNode> {
        let mut found = None;
        for p in &self.problem.premises {
            if Polyeq::new()
                .mod_reordering(true)
                .mod_nary(true)
                .eq(term, p)
            {
                found = Some(p.clone());
                break;
            }
        }
        let premise = found.expect("trying to elaborate assume, but it is invalid!");

        let new_assume = Rc::new(ProofNode::Assume {
            id: id.to_owned(),
            depth,
            term: premise.clone(),
        });

        let mut ids = IdHelper::new(id);
        let equality_step = PolyeqElaborator::new(&mut ids, depth, false).elaborate(
            self.pool,
            premise.clone(),
            term.clone(),
        );

        let equiv1_step = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth,
            clause: vec![
                build_term!(self.pool, (not {premise.clone()})),
                term.clone(),
            ],
            rule: "equiv1".to_owned(),
            premises: vec![equality_step],
            ..Default::default()
        }));

        Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth,
            clause: vec![term.clone()],
            rule: "resolution".to_owned(),
            premises: vec![new_assume, equiv1_step],
            args: vec![premise, self.pool.bool_true()],
            ..Default::default()
        }))
    }
}

fn add_refl_step(
    pool: &mut dyn TermPool,
    a: Rc<Term>,
    b: Rc<Term>,
    id: String,
    depth: usize,
) -> Rc<ProofNode> {
    Rc::new(ProofNode::Step(StepNode {
        id,
        depth,
        clause: vec![build_term!(pool, (= {a} {b}))],
        rule: "refl".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    }))
}

/// If `node` is itself a `symm` step, returns its premise, as long as that premise concludes
/// exactly `clause`.
///
/// Flipping a `symm` step gives back the clause its premise already concludes, so the premise can
/// be used directly instead of stacking a second `symm` on top of the first. Elaboration produces
/// such round trips often: the `polyeq` pass flips a `refl` step to apply the context on the
/// right-hand term, and the passes that consume that equality then need the original orientation
/// back.
fn unwrap_symm_step(node: &Rc<ProofNode>, clause: &[Rc<Term>]) -> Option<Rc<ProofNode>> {
    let step = node.as_step()?;
    if step.rule != "symm" || step.premises.len() != 1 {
        return None;
    }
    let premise = &step.premises[0];
    (premise.clause() == clause).then(|| premise.clone())
}

fn add_symm_step(pool: &mut PrimitivePool, node: &Rc<ProofNode>, id: String) -> Rc<ProofNode> {
    assert_eq!(node.clause().len(), 1);
    let (a, b) = match_term!((= a b) = node.clause()[0]).unwrap();
    let clause = vec![build_term!(pool, (= {b.clone()} {a.clone()}))];

    if let Some(premise) = unwrap_symm_step(node, &clause) {
        return premise;
    }

    Rc::new(ProofNode::Step(StepNode {
        id,
        depth: node.depth(),
        clause,
        rule: "symm".into(),
        premises: vec![node.clone()],
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    }))
}

fn add_trans_step(
    pool: &mut PrimitivePool,
    nodes: impl IntoIterator<Item = Rc<ProofNode>>,
    id: String,
) -> Rc<ProofNode> {
    let premises: Vec<_> = nodes.into_iter().collect();
    let depth = premises.first().unwrap().depth();
    let (a, _) =
        match_term!((= a b) = premises.first().unwrap().clause().first().unwrap()).unwrap();
    let (_, b) = match_term!((= a b) = premises.last().unwrap().clause().first().unwrap()).unwrap();
    Rc::new(ProofNode::Step(StepNode {
        id,
        depth,
        clause: vec![build_term!(pool, (= {a.clone()} {b.clone()}))],
        rule: "trans".to_owned(),
        premises,
        ..StepNode::default()
    }))
}

type ElaborationFunc =
    fn(&mut PrimitivePool, &mut ContextStack, &StepNode) -> Result<Rc<ProofNode>, ElaborationError>;

/// A proof that can be mutated by applying a function to each of its nodes.
///
/// The function is applied to the nodes in a bottom-up order, so that the premises of a step are
/// always processed before the step itself. Shared nodes are only processed once.
pub trait Mutate: Sized {
    /// Applies `mutate_func` to every node of the proof, returning the new proof.
    ///
    /// `mutate_func` receives the current context, the node, and whether the node's premises were
    /// modified, and returns the new node.
    fn mutate<F, E>(self, mutate_func: F) -> Result<Self, E>
    where
        F: FnMut(&mut ContextStack, &Rc<ProofNode>, bool) -> Result<Rc<ProofNode>, E>;
}

impl Mutate for ProofNodeForest {
    fn mutate<F, E>(self, mut mutate_func: F) -> Result<Self, E>
    where
        F: FnMut(&mut ContextStack, &Rc<ProofNode>, bool) -> Result<Rc<ProofNode>, E>,
    {
        let mut cache = HashMap::new();
        self.0
            .into_iter()
            .map(|node| mutate_impl(&node, &mut cache, &mut mutate_func))
            .collect::<Result<Vec<_>, E>>()
            .map(ProofNodeForest)
    }
}

impl Mutate for Rc<ProofNode> {
    fn mutate<F, E>(self, mutate_func: F) -> Result<Self, E>
    where
        F: FnMut(&mut ContextStack, &Rc<ProofNode>, bool) -> Result<Rc<ProofNode>, E>,
    {
        let mut cache = HashMap::new();
        mutate_impl(&self, &mut cache, mutate_func)
    }
}

fn mutate_impl<F, E>(
    root: &Rc<ProofNode>,
    cache: &mut HashMap<Rc<ProofNode>, Rc<ProofNode>>,
    mut mutate_func: F,
) -> Result<Rc<ProofNode>, E>
where
    F: FnMut(&mut ContextStack, &Rc<ProofNode>, bool) -> Result<Rc<ProofNode>, E>,
{
    let mut did_outbound: HashSet<&Rc<ProofNode>> = HashSet::new();
    let mut todo = vec![(root, false)];

    let mut outbound_premises_stack = vec![IndexSet::new()];
    // Nodes whose outbound premises have already been collected into a frame. Every node the
    // traversal offers to the pass lands here; what remains unseen under a returned replacement
    // is exactly the derivation the pass *built*, whose interior can reference nodes outside the
    // current scope (e.g. a replayed `bind` body keeping its premises, or a shared derivation at
    // depth 0) — those references must reach the enclosing scope's outbound list too, or the
    // printer meets them inside the wrong anchor.
    let mut deep_seen: HashSet<Rc<ProofNode>> = HashSet::new();
    let mut context = ContextStack::new();

    while let Some((node, is_done)) = todo.pop() {
        if cache.contains_key(node) {
            continue;
        }

        let mutated = match node.as_ref() {
            ProofNode::Assume { .. } => mutate_func(&mut context, node, false)?,
            ProofNode::Step(s) if !is_done => {
                todo.push((node, true));

                let all_premises = s
                    .premises
                    .iter()
                    .chain(&s.discharge)
                    .chain(&s.previous_step)
                    .rev();
                todo.extend(
                    all_premises.filter_map(|p| (!cache.contains_key(p)).then_some((p, false))),
                );

                continue;
            }
            ProofNode::Step(s) => {
                let premises: Vec<_> = s.premises.iter().map(|p| cache[p].clone()).collect();
                let discharge: Vec<_> = s.discharge.iter().map(|p| cache[p].clone()).collect();
                let previous_step = s.previous_step.as_ref().map(|p| cache[p].clone());
                let changed = s
                    .premises
                    .iter()
                    .chain(s.discharge.iter())
                    .chain(s.previous_step.iter())
                    .any(|p| *p != cache[p]);

                // A step none of whose premises moved is its own rebuild, so it is passed on as
                // it is. Cloning it instead would copy its id, rule, clause and arguments —
                // per step, on every pass — and hand the pass a node with a fresh identity,
                // which is also worse for the memos that later passes key by node
                if changed {
                    let new_node = Rc::new(ProofNode::Step(StepNode {
                        premises,
                        discharge,
                        previous_step,
                        ..s.clone()
                    }));
                    mutate_func(&mut context, &new_node, true)?
                } else {
                    mutate_func(&mut context, node, false)?
                }
            }
            ProofNode::Subproof(s) if !is_done => {
                assert!(
                    node.depth() == outbound_premises_stack.len() - 1,
                    "all outbound premises should have already been dealt with! \
                     (subproof closing '{}' at depth {}, traversal at {})",
                    s.last_step.id(),
                    node.depth(),
                    outbound_premises_stack.len() - 1
                );

                if !did_outbound.contains(node) {
                    did_outbound.insert(node);
                    todo.push((node, false));
                    todo.extend(s.outbound_premises.iter().map(|premise| (premise, false)));
                    continue;
                }

                todo.push((node, true));
                todo.push((&s.last_step, false));
                todo.extend(s.extra_steps.iter().rev().map(|node| (node, false)));
                outbound_premises_stack.push(IndexSet::new());
                context.push(&s.args);
                continue;
            }
            ProofNode::Subproof(s) => {
                context.pop();
                let mut outbound_premises = outbound_premises_stack.pop().unwrap();
                let extra_steps: Vec<Rc<ProofNode>> = s
                    .extra_steps
                    .iter()
                    .map(|node| cache[node].clone())
                    .collect();

                // A step of this subproof may have been replaced by one of an enclosing scope, as
                // the `hoist` pass does when it lifts a closed derivation to depth 0. Such a step
                // belongs outside the subproof, so it is recorded as an outbound premise even if
                // nothing in the subproof uses it: that is what makes later traversals visit it
                // under the right context, and the proof print it before the anchor
                outbound_premises.extend(
                    extra_steps
                        .iter()
                        .filter(|extra| extra.depth() <= node.depth())
                        .cloned(),
                );

                let new_node = Rc::new(ProofNode::Subproof(SubproofNode {
                    last_step: cache[&s.last_step].clone(),
                    args: s.args.clone(),
                    outbound_premises: outbound_premises.into_iter().collect(),
                    extra_steps,
                }));
                // Subproof nodes are offered to the pass like steps are, so that a pass can replace
                // a whole scope — as `hoist` does when a premise-free rule proves what the scope
                // discharges. The context has already been popped, so the node is seen at the depth
                // it lives at, which is also the depth any replacement has to be built for
                mutate_func(&mut context, &new_node, true)?
            }
        };
        {
            // Collect the outbound premises of the whole returned derivation, not just the
            // returned root: walk the nodes the pass built (everything not yet seen), and record
            // every premise edge that leaves the current depth. Linear overall — the walk stops
            // at nodes already collected for an earlier frame extension.
            let depth = mutated.depth();
            let frame = outbound_premises_stack.last_mut().unwrap();
            let mut walk = vec![mutated.clone()];
            while let Some(n) = walk.pop() {
                if !deep_seen.insert(n.clone()) {
                    continue;
                }
                let premises: Vec<Rc<ProofNode>> = match n.as_ref() {
                    ProofNode::Assume { .. } => continue,
                    ProofNode::Step(step) => step
                        .premises
                        .iter()
                        .chain(&step.discharge)
                        .chain(step.previous_step.iter())
                        .cloned()
                        .collect(),
                    // A subproof's own outbound list is already deep (its builder traverses the
                    // interior), so the interior need not be revisited here
                    ProofNode::Subproof(sub) => sub.outbound_premises.clone(),
                };
                for p in premises {
                    if p.depth() < depth {
                        frame.insert(p);
                    } else {
                        walk.push(p);
                    }
                }
            }
        }
        cache.insert(node.clone(), mutated);
    }
    assert!(outbound_premises_stack.len() == 1 && outbound_premises_stack[0].is_empty());
    Ok(cache[root].clone())
}

/// A helper for generating unique step IDs from a root ID, by appending numeric suffixes to it.
pub struct IdHelper {
    root: String,
    stack: Vec<usize>,
}

impl IdHelper {
    /// Constructs a new [`IdHelper`] for the given root ID.
    pub fn new(root: &str) -> Self {
        Self {
            root: root.to_owned(),
            stack: vec![0],
        }
    }

    /// Returns the next generated ID, and advances the internal counter.
    pub fn next_id(&mut self) -> String {
        use std::fmt::Write;

        let mut current = self.root.clone();
        for i in &self.stack {
            write!(&mut current, ".t{}", i + 1).unwrap();
        }
        *self.stack.last_mut().unwrap() += 1;
        current
    }

    /// Starts a new nesting level.
    ///
    /// That is, if the current ID is `t5.t3`, `push` will use that as the root for the next ids,
    /// such that the following ID will be `t5.t3.t1`. This is reverted by [`IdHelper::pop`].
    pub fn push(&mut self) {
        self.stack.push(0);
    }

    /// Ends the current nesting level.
    pub fn pop(&mut self) {
        assert!(self.stack.len() >= 2, "can't pop last frame from the stack");
        self.stack.pop();
    }
}
