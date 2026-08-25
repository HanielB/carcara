mod core;
pub mod error;
mod hoist;
mod hole;
mod local;
mod polyeq;
mod prune;
mod reordering;
mod sat_refutation;
mod scopes;
mod uncrowding;

use crate::{
    ast::*,
    external::{ExternalTool, SatTools},
    Error,
};
use error::ElaborationError;
use indexmap::IndexSet;
use polyeq::PolyeqElaborator;
use std::{
    collections::{HashMap, HashSet},
    time::{Duration, Instant},
};

#[derive(Debug, Clone, Default)]
pub struct Config {
    /// If `Some`, enables the elaboration of `lia_generic` steps using an external solver. When
    /// checking a proof, this means calling the solver to solve the linear integer arithmetic
    /// problem, checking the proof, and discarding it. When elaborating, the proof will instead be
    /// inserted in the place of the `lia_generic` step.
    pub lia_solver: Option<ExternalTool>,

    /// Enables an optimization that reorders premises when uncrowding resolution steps, in order to
    /// further minimize the number of `contraction` steps added.
    pub uncrowd_rotation: bool,

    pub hole_solver: Option<ExternalTool>,

    pub sat_ref_tools: Option<SatTools>,

    /// The rules that the checker was told to accept as holes, via `--allowed-rules`. The `hoist`
    /// pass needs them to know which derivations it must not share, so that it cannot replace a
    /// real derivation by a holey one.
    pub allowed_rules: HashSet<String>,

    /// The RARE rule set given to the checker (via `--rare-file`). The `core-simp-rare` pass
    /// needs it to emit `rare_rewrite` lemmas when replaying the `*_simplify` rewrite chains.
    pub rare_rules: Option<crate::ast::rare_rules::Rules>,
}

#[derive(Debug, Clone, Copy)]
pub enum ElaborationPass {
    /// Removes every step that the derivation of the empty clause does not use.
    Prune,
    Hoist,
    /// The `hoist` pass, additionally replacing every lemma scope whose discharged clause a
    /// premise-free rule proves outright by that single step.
    DeepHoist,
    Polyeq,
    Hole,
    Core,
    CoreKeepEqCl,
    /// The `core` pass, additionally replaying the `*_simplify` rules as chains of
    /// `rare_rewrite`/`evaluate` lemmas (the rewrite vocabulary itself is kept).
    CoreSimpRare,
    /// The `core` pass, additionally reducing the whole rewrite vocabulary (`*_simplify`,
    /// `evaluate`, `rare_rewrite`) to the core plus the term-`ite` selection axioms.
    CoreTaut,
    Local,
    Uncrowd,
    Reordering,
    SatRefutation,
}

pub struct Elaborator<'e> {
    pool: &'e mut PrimitivePool,
    problem: &'e Problem,
    config: Config,
}

impl<'e> Elaborator<'e> {
    pub fn new(pool: &'e mut PrimitivePool, problem: &'e Problem, config: Config) -> Self {
        Self { pool, problem, config }
    }

    pub fn elaborate_with_default_pipeline(
        &mut self,
        proof: ProofNodeForest,
    ) -> Result<ProofNodeForest, Error> {
        use ElaborationPass::*;
        let pipeline = vec![Hoist, Polyeq, Hole, Local, Uncrowd, Reordering];
        self.elaborate(proof, pipeline)
    }

    pub fn elaborate(
        &mut self,
        proof: ProofNodeForest,
        pipeline: Vec<ElaborationPass>,
    ) -> Result<ProofNodeForest, Error> {
        Ok(self.elaborate_with_stats(proof, pipeline)?.0)
    }

    pub fn elaborate_with_stats(
        &mut self,
        proof: ProofNodeForest,
        pipeline: Vec<ElaborationPass>,
    ) -> Result<(ProofNodeForest, Vec<Duration>), Error> {
        let mut durations = Vec::new();
        let mut current = proof;
        for pass in pipeline {
            let time = Instant::now();
            current = match pass {
                ElaborationPass::Prune => prune::prune(current),
                ElaborationPass::Hoist => {
                    hoist::hoist(self.pool, current, &self.config.allowed_rules, false)
                }
                ElaborationPass::DeepHoist => {
                    hoist::hoist(self.pool, current, &self.config.allowed_rules, true)
                }
                ElaborationPass::Polyeq => self.elaborate_polyeq(current)?,
                ElaborationPass::Hole => self.elaborate_hole(current)?,
                ElaborationPass::Core => {
                    self.elaborate_core(current, false, core::rewrites::RewriteReduction::Keep)?
                }
                ElaborationPass::CoreKeepEqCl => {
                    self.elaborate_core(current, true, core::rewrites::RewriteReduction::Keep)?
                }
                ElaborationPass::CoreSimpRare => {
                    self.elaborate_core(current, false, core::rewrites::RewriteReduction::ToRare)?
                }
                ElaborationPass::CoreTaut => {
                    self.elaborate_core(current, false, core::rewrites::RewriteReduction::ToCore)?
                }
                ElaborationPass::Local => self.elaborate_local(current)?,
                ElaborationPass::Uncrowd => current.mutate(|_, node, _| match node.as_ref() {
                    ProofNode::Step(s)
                        if (s.rule == "resolution" || s.rule == "th_resolution")
                            && !s.args.is_empty() =>
                    {
                        uncrowding::uncrowd_resolution(self.pool, s, self.config.uncrowd_rotation)
                            .map_err(|e| e.at(s))
                    }
                    _ => Ok(node.clone()),
                })?,
                ElaborationPass::Reordering => reordering::remove_reorderings(current)?,
                ElaborationPass::SatRefutation => {
                    if self.config.sat_ref_tools.is_some() {
                        // TODO: proper error handling
                        current
                            .mutate::<_, ()>(|_, node, _| match node.as_ref() {
                                ProofNode::Step(s) if (s.rule == "sat_refutation") => {
                                    Ok(sat_refutation::sat_refutation(self, s)
                                        .unwrap_or_else(|| node.clone()))
                                }
                                _ => Ok(node.clone()),
                            })
                            .unwrap()
                    } else {
                        current
                    }
                }
            };
            durations.push(time.elapsed());
        }
        Ok((current, durations))
    }

    fn elaborate_polyeq(&mut self, proof: ProofNodeForest) -> Result<ProofNodeForest, Error> {
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

    fn elaborate_hole(&mut self, proof: ProofNodeForest) -> Result<ProofNodeForest, Error> {
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
    /// With `keep_equality`, the clausal equality rules (`eq_*`, `not_symm`) are left
    /// unchanged — the vocabulary evaluated as the `eq_cl` configuration.
    ///
    /// Recipes are memoized by their conclusion: a derivation that is self-contained and mentions
    /// no anchor-bound variable is emitted once, at depth 0, and every later step with the same
    /// conclusion is replaced by it. See [`core::share`].
    fn elaborate_core(
        &mut self,
        proof: ProofNodeForest,
        keep_equality: bool,
        rewrites: core::rewrites::RewriteReduction,
    ) -> Result<ProofNodeForest, Error> {
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
                            | "unary_minus_simplify" => Some(core::rewrites::elaborate_simplify(
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
                            "rare_rewrite" if rewrites == RewriteReduction::ToCore => Some(
                                core::rewrites::elaborate_rare_rewrite(self.pool, context, s),
                            ),
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
                        core::get_elaboration_function(&s.rule, keep_equality)
                            .map(|func| func(self.pool, context, s))
                    };
                    match attempt {
                        Some(Ok(new_node)) => {
                            return Ok(sharing.share(self.pool, context, s, new_node));
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

    fn elaborate_local(&mut self, proof: ProofNodeForest) -> Result<ProofNodeForest, Error> {
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

pub trait Mutate: Sized {
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
                    "all outbound premises should have already been dealt with!"
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
        outbound_premises_stack
            .last_mut()
            .unwrap()
            .extend(mutated.get_outbound_premises());
        cache.insert(node.clone(), mutated);
    }
    assert!(outbound_premises_stack.len() == 1 && outbound_premises_stack[0].is_empty());
    Ok(cache[root].clone())
}

pub struct IdHelper {
    root: String,
    stack: Vec<usize>,
}

impl IdHelper {
    pub fn new(root: &str) -> Self {
        Self {
            root: root.to_owned(),
            stack: vec![0],
        }
    }

    pub fn next_id(&mut self) -> String {
        use std::fmt::Write;

        let mut current = self.root.clone();
        for i in &self.stack {
            write!(&mut current, ".t{}", i + 1).unwrap();
        }
        *self.stack.last_mut().unwrap() += 1;
        current
    }

    pub fn push(&mut self) {
        self.stack.push(0);
    }

    pub fn pop(&mut self) {
        assert!(self.stack.len() >= 2, "can't pop last frame from the stack");
        self.stack.pop();
    }
}
