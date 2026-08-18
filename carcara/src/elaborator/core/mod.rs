//! The `core` elaboration pass.
//!
//! This pass rewrites every step whose rule is in the *reducible* level of the core classification
//! (see the "Rule classification" chapter of the documentation) into a derivation that only uses
//! rules of the *core* fragment. It is the elaboration counterpart of that classification: after
//! running it, the only rules left in the proof should be core rules (plus whatever is left of the
//! expensive/aggressive tiers, which this pass does not touch).
//!
//! The recipes implemented here are the ones documented in `docs/src/core/classification.md`; each
//! module below covers one concern category.

// The elaboration functions must all match the `ElaborationFunc` signature, so some of them
// return a `Result` they never fail with
#[allow(clippy::unnecessary_wraps)]
pub mod arithmetic;
#[allow(clippy::unnecessary_wraps)]
pub mod binder;
#[allow(clippy::unnecessary_wraps)]
pub mod clausification;
#[allow(clippy::unnecessary_wraps)]
pub mod equality;
#[allow(clippy::unnecessary_wraps)]
pub mod legacy;
#[allow(clippy::unnecessary_wraps)]
pub mod onepoint;
#[allow(clippy::unnecessary_wraps)]
pub mod simplification;
// `sko_ex` is classified *expensive*, so this recipe is not registered below and the module is
// unused; it is kept because the reduction is complete and validated, and re-enabling it is a
// one-line change (see `investigations/2026-08-18-sko-ex-cost.md` for the cost measurements)
#[allow(clippy::unnecessary_wraps, dead_code)]
pub mod skolem;

use crate::{ast::*, elaborator::error::ElaborationError};
use indexmap::IndexSet;

/// A helper to build the derivations that the `core` pass emits.
///
/// It keeps track of the ids and depth of the steps being added, and knows how to build the step
/// shapes that show up over and over in the reduction recipes: resolutions with explicit pivots,
/// discharge subproofs, and the expansions of the "convenience" rules (`and_intro`, `equiv_intro`
/// and `or_intro`).
pub struct Builder<'a> {
    pub pool: &'a mut PrimitivePool,
    ids: CoreIdHelper,
    depth: usize,
}

/// An id generator for the steps the `core` pass emits. It works like [`IdHelper`], but generates
/// ids in a `.c<n>` namespace (`t1.c1`, `t1.c2`, `t1.c2.c1`, …), so that the ids can never clash
/// with the `.t<n>` ids that the other passes (polyeq, uncrowding, …) generate under the same
/// root.
struct CoreIdHelper {
    root: String,
    stack: Vec<usize>,
}

impl CoreIdHelper {
    fn new(root: &str) -> Self {
        Self {
            root: root.to_owned(),
            stack: vec![0],
        }
    }

    fn next_id(&mut self) -> String {
        use std::fmt::Write;

        let mut current = self.root.clone();
        for i in &self.stack {
            write!(&mut current, ".c{}", i + 1).unwrap();
        }
        *self.stack.last_mut().unwrap() += 1;
        current
    }

    fn push(&mut self) {
        self.stack.push(0);
    }

    fn pop(&mut self) {
        assert!(self.stack.len() >= 2, "can't pop last frame from the stack");
        self.stack.pop();
    }
}

impl<'a> Builder<'a> {
    pub fn new(pool: &'a mut PrimitivePool, step: &StepNode) -> Self {
        Self {
            pool,
            ids: CoreIdHelper::new(&step.id),
            depth: step.depth,
        }
    }

    /// Builds the term `(not term)`.
    pub fn not(&mut self, term: &Rc<Term>) -> Rc<Term> {
        build_term!(self.pool, (not {term.clone()}))
    }

    /// Adds a new step, with a fresh id at the current depth.
    pub fn step(
        &mut self,
        clause: Vec<Rc<Term>>,
        rule: &str,
        premises: Vec<Rc<ProofNode>>,
        args: Vec<Rc<Term>>,
    ) -> Rc<ProofNode> {
        let id = self.ids.next_id();
        Rc::new(ProofNode::Step(StepNode {
            id,
            depth: self.depth,
            clause,
            rule: rule.to_owned(),
            premises,
            args,
            ..Default::default()
        }))
    }

    /// Adds an `assume` command at the current depth.
    pub fn assume(&mut self, term: Rc<Term>) -> Rc<ProofNode> {
        let id = self.ids.next_id();
        Rc::new(ProofNode::Assume { id, depth: self.depth, term })
    }

    /// Computes the clause that results from resolving the given premises with the given pivots.
    ///
    /// Each pivot is a pair of a literal and a polarity, following the convention of the `:args` of
    /// an elaborated `resolution` step: the polarity is `true` if the literal occurs (positively,
    /// that is, as given) in the clause accumulated so far, and `false` if it occurs in the next
    /// premise.
    fn resolve_clause(
        &mut self,
        premises: &[Rc<ProofNode>],
        pivots: &[(Rc<Term>, bool)],
    ) -> Result<Vec<Rc<Term>>, ElaborationError> {
        use crate::resolution::ResolutionError;

        assert_eq!(premises.len(), pivots.len() + 1);
        let mut current: IndexSet<Rc<Term>> = premises[0].clause().iter().cloned().collect();
        for (premise, (pivot, polarity)) in premises[1..].iter().zip(pivots) {
            let negated = self.not(pivot);
            let (in_current, in_next) = if *polarity {
                (pivot.clone(), negated)
            } else {
                (negated, pivot.clone())
            };
            if !current.shift_remove(&in_current) {
                return Err(ResolutionError::PivotNotFound(in_current).into());
            }
            let mut found = false;
            for t in premise.clause() {
                if !found && *t == in_next {
                    found = true;
                } else {
                    current.insert(t.clone());
                }
            }
            if !found {
                return Err(ResolutionError::PivotNotFound(in_next).into());
            }
        }
        Ok(current.into_iter().collect())
    }

    /// Builds the `:args` of a `resolution` step from a list of pivots.
    fn pivot_args(&mut self, pivots: &[(Rc<Term>, bool)]) -> Vec<Rc<Term>> {
        let mut args = Vec::with_capacity(2 * pivots.len());
        for (pivot, polarity) in pivots {
            let polarity = if *polarity {
                self.pool.bool_true()
            } else {
                self.pool.bool_false()
            };
            args.push(pivot.clone());
            args.push(polarity);
        }
        args
    }

    /// Adds a `resolution` step with explicit pivots, computing its conclusion.
    pub fn resolve(
        &mut self,
        premises: Vec<Rc<ProofNode>>,
        pivots: Vec<(Rc<Term>, bool)>,
    ) -> Result<Rc<ProofNode>, ElaborationError> {
        let clause = self.resolve_clause(&premises, &pivots)?;
        let args = self.pivot_args(&pivots);
        Ok(self.step(clause, "resolution", premises, args))
    }

    /// Adds the final step of a reduction, that is, the step that takes the place of the original
    /// one. It keeps the original id, depth, clause and `:discharge`/previous step, so that the
    /// steps that referred to it are unaffected.
    #[allow(clippy::unused_self)]
    pub fn finish(
        &self,
        step: &StepNode,
        rule: &str,
        premises: Vec<Rc<ProofNode>>,
        args: Vec<Rc<Term>>,
    ) -> Rc<ProofNode> {
        Rc::new(ProofNode::Step(StepNode {
            rule: rule.to_owned(),
            premises,
            args,
            ..step.clone()
        }))
    }

    /// Takes the last step of a derivation and gives it back the identity of the step being
    /// elaborated: its id, depth, conclusion, and `:discharge`/previous step.
    ///
    /// This is what makes a reduction transparent to the rest of the proof.
    pub fn relabel(&self, step: &StepNode, node: Rc<ProofNode>) -> Rc<ProofNode> {
        let last = node
            .as_step()
            .expect("last step of a reduction must be a step");
        self.finish(step, &last.rule, last.premises.clone(), last.args.clone())
    }

    /// Adds a `symm` step over a unit-equality node, with a fresh id at the current depth.
    pub fn symm(&mut self, node: &Rc<ProofNode>) -> Rc<ProofNode> {
        let (a, b) = match_term!((= a b) = node.clause()[0]).unwrap();
        let clause = vec![build_term!(self.pool, (= {b.clone()} {a.clone()}))];
        self.step(clause, "symm", vec![node.clone()], Vec::new())
    }

    /// Opens a subproof: from now on, new steps are added one level deeper.
    pub fn open(&mut self) {
        self.ids.push();
        self.depth += 1;
    }

    /// Closes a subproof opened by [`Builder::open`] with a `subproof` step discharging the given
    /// assumptions: the closing clause is the negation of each assumption followed by the (unit or
    /// empty) conclusion of the subproof's last step.
    pub fn close_subproof(
        &mut self,
        discharge: Vec<Rc<ProofNode>>,
        last_inner: Rc<ProofNode>,
    ) -> Rc<ProofNode> {
        let phi = match last_inner.clause() {
            [] => self.pool.bool_false(),
            [t] => t.clone(),
            _ => panic!("last step of a discharge subproof must have a unit or empty clause"),
        };
        let mut clause: Vec<_> = discharge
            .iter()
            .map(|h| {
                let (_, _, term) = h.as_assume().unwrap();
                let term = term.clone();
                self.not(&term)
            })
            .collect();
        clause.push(phi);
        self.close_with(Vec::new(), "subproof", clause, discharge, last_inner)
    }

    /// Closes a subproof opened by [`Builder::open`], adding its closing step with a fresh id.
    pub fn close_with(
        &mut self,
        anchor_args: Vec<AnchorArg>,
        rule: &str,
        clause: Vec<Rc<Term>>,
        discharge: Vec<Rc<ProofNode>>,
        last_inner: Rc<ProofNode>,
    ) -> Rc<ProofNode> {
        let inner_depth = self.depth;
        self.ids.pop();
        self.depth -= 1;
        let id = self.ids.next_id();
        let last_step = Rc::new(ProofNode::Step(StepNode {
            id,
            depth: inner_depth,
            clause,
            rule: rule.to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge,
            previous_step: Some(last_inner),
        }));
        Self::subproof_node(last_step, anchor_args)
    }

    /// Closes a subproof whose closing step is the step being elaborated, that is, the step that
    /// keeps the original id and conclusion.
    #[allow(clippy::too_many_arguments)]
    pub fn close_finish(
        &mut self,
        step: &StepNode,
        anchor_args: Vec<AnchorArg>,
        rule: &str,
        premises: Vec<Rc<ProofNode>>,
        args: Vec<Rc<Term>>,
        discharge: Vec<Rc<ProofNode>>,
        previous_step: Rc<ProofNode>,
    ) -> Rc<ProofNode> {
        self.ids.pop();
        self.depth -= 1;
        let last_step = Rc::new(ProofNode::Step(StepNode {
            depth: step.depth + 1,
            rule: rule.to_owned(),
            premises,
            args,
            discharge,
            previous_step: Some(previous_step),
            ..step.clone()
        }));
        Self::subproof_node(last_step, anchor_args)
    }

    fn subproof_node(last_step: Rc<ProofNode>, args: Vec<AnchorArg>) -> Rc<ProofNode> {
        let depth = last_step.depth();
        let mut outbound_premises: IndexSet<Rc<ProofNode>> = IndexSet::new();
        last_step.traverse(|node| {
            if node.depth() >= depth {
                outbound_premises.extend(node.get_outbound_premises());
            }
        });
        Rc::new(ProofNode::Subproof(SubproofNode {
            last_step,
            args,
            outbound_premises: outbound_premises.into_iter().collect(),
            extra_steps: Vec::new(),
        }))
    }

    /// Emits the derivation of `and_intro`: from unit clauses `(cl l₁)`, …, `(cl lₙ)`, derives
    /// `(cl (and l₁ … lₙ))` with one `and_neg` step and one resolution.
    pub fn and_intro(
        &mut self,
        premises: Vec<Rc<ProofNode>>,
    ) -> Result<Rc<ProofNode>, ElaborationError> {
        let conjuncts: Vec<_> = premises
            .iter()
            .map(|p| {
                let [term] = p.clause() else {
                    panic!("premise of `and_intro` must be a unit clause");
                };
                term.clone()
            })
            .collect();
        let and_term = self.pool.add(Term::Op(Operator::And, conjuncts.clone()));
        let mut clause = vec![and_term];
        let mut pivots = Vec::new();
        for c in conjuncts {
            let negated = self.not(&c);
            clause.push(negated);
            // The negated conjunct is in the `and_neg` clause, and the conjunct itself is in the
            // corresponding premise
            pivots.push((c, false));
        }
        let and_neg = self.step(clause, "and_neg", Vec::new(), Vec::new());
        let premises = std::iter::once(and_neg).chain(premises).collect();
        self.resolve(premises, pivots)
    }

    /// Emits the derivation of `or_intro`: from a clause `(cl l₁ … lₙ)`, derives the unit clause
    /// `(cl (or l₁ … lₙ))`, with `n` `or_neg` steps, `n` resolutions and one `contraction`.
    pub fn or_intro(&mut self, premise: Rc<ProofNode>) -> Result<Rc<ProofNode>, ElaborationError> {
        let literals: Vec<_> = premise.clause().to_vec();
        assert!(literals.len() >= 2);
        let or_term = self.pool.add(Term::Op(Operator::Or, literals.clone()));

        let mut current = premise;
        for (i, literal) in literals.iter().enumerate() {
            let negated = self.not(literal);
            let index = self.pool.add(Term::new_int(i));
            let or_neg = self.step(
                vec![or_term.clone(), negated],
                "or_neg",
                Vec::new(),
                vec![index],
            );
            current = self.resolve(vec![current, or_neg], vec![(literal.clone(), true)])?;
        }
        // The last resolution concludes `(cl (or l₁ … lₙ))`, possibly with repetitions, which the
        // `resolve` helper already merged. If it didn't, a contraction closes it
        if current.clause().len() > 1 {
            let clause = vec![or_term];
            current = self.step(clause, "contraction", vec![current], Vec::new());
        }
        Ok(current)
    }

    /// Emits the derivation of `equiv_intro`: from `(cl (not a) b)` and `(cl a (not b))`, derives
    /// `(cl (= a b))`, with the two `equiv_neg` axioms, resolutions and contractions.
    pub fn equiv_intro(
        &mut self,
        a: Rc<Term>,
        b: Rc<Term>,
        right: Rc<ProofNode>,
        left: Rc<ProofNode>,
    ) -> Result<Rc<ProofNode>, ElaborationError> {
        let equiv = build_term!(self.pool, (= {a.clone()} {b.clone()}));
        let (not_a, not_b) = (self.not(&a), self.not(&b));

        let neg2 = self.step(
            vec![equiv.clone(), a.clone(), b.clone()],
            "equiv_neg2",
            Vec::new(),
            Vec::new(),
        );
        let neg1 = self.step(
            vec![equiv.clone(), not_a, not_b],
            "equiv_neg1",
            Vec::new(),
            Vec::new(),
        );
        let s1 = self.resolve(vec![neg2, right], vec![(a.clone(), true)])?;
        let s2 = self.resolve(vec![neg1, left], vec![(a, false)])?;
        // The final resolution always merges the two copies of the equivalence; emit the
        // crowding explicitly (resolution + `contraction`), so that the uncrowding pass does not
        // need to rewrite the step — which matters when the caller gives this step the identity
        // of a subproof-closing step, whose fresh uncrowding ids could collide with the
        // subproof's inner ids
        let args = self.pivot_args(&[(b, true)]);
        let crowded = self.step(
            vec![equiv.clone(), equiv.clone()],
            "resolution",
            vec![s1, s2],
            args,
        );
        Ok(self.step(vec![equiv], "contraction", vec![crowded], Vec::new()))
    }
}

/// Returns the elaboration function for the given rule, if the `core` pass knows how to reduce
/// it. With `keep_equality`, the clausal equality rules (`eq_*`, `not_symm`) are kept.
pub fn get_elaboration_function(rule: &str, keep_equality: bool) -> Option<super::ElaborationFunc> {
    if keep_equality
        && matches!(
            rule,
            "eq_reflexive"
                | "eq_transitive"
                | "eq_congruent"
                | "eq_congruent_pred"
                | "eq_symmetric"
                | "not_symm"
                | "eq_mp"
        )
    {
        return None;
    }
    Some(match rule {
        // Clausal
        "th_resolution" => clausification::th_resolution,
        "tautology" => clausification::tautology,
        "and" | "not_or" | "or" | "not_and" | "xor1" | "xor2" | "not_xor1" | "not_xor2"
        | "implies" | "not_implies1" | "not_implies2" | "equiv1" | "equiv2" | "not_equiv1"
        | "not_equiv2" | "ite1" | "ite2" | "not_ite1" | "not_ite2" => {
            clausification::premise_clausification
        }
        "and_intro" => clausification::and_intro,
        "eq_mp" => super::local::eq_mp::eq_mp,

        // Equality and rewriting
        "eq_reflexive" => equality::eq_reflexive,
        "eq_transitive" => equality::eq_transitive,
        "eq_congruent" => equality::eq_congruent,
        "eq_congruent_pred" => equality::eq_congruent_pred,
        "eq_symmetric" => equality::eq_symmetric,
        "not_symm" => equality::not_symm,

        // Arithmetic
        "la_totality" => arithmetic::la_totality,
        "la_tautology" => arithmetic::la_tautology,
        "la_rw_eq" => arithmetic::la_rw_eq,

        // ACI reasoning (`ac_simp` is the one legacy rule with a working fallback: `lia_generic`
        // is excluded from this pass, `qnt_cnf` is oracle-only, and `ite_intro`/`bfun_elim` need
        // term-level `ite` axioms outside the core — their classification is *removal*)
        "shuffle" => simplification::shuffle,
        "nary_elim" => simplification::nary_elim,
        "ac_simp" => simplification::ac_simp,

        // Binder
        "qnt_simplify" => binder::qnt_simplify,
        "qnt_rm_unused" => binder::qnt_rm_unused,
        "qnt_join" => binder::qnt_join,
        "miniscope_distribute" => binder::miniscope_distribute,
        "miniscope_split" => binder::miniscope_split,
        "miniscope_ite" => binder::miniscope_ite,
        "onepoint" => onepoint::onepoint,
        // `sko_ex` is classified *expensive* and deliberately left unreduced: its recipe (in
        // `skolem.rs`, still available and tested) costs ~35 emitted steps per binding, an ~8x
        // local blowup, which the classification is not willing to pay by default

        "qnt_cnf" => legacy::qnt_cnf,
        "bfun_elim" => legacy::bfun_elim,
        "ite_intro" => legacy::ite_intro,

        _ => return None,
    })
}
