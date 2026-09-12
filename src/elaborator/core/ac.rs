//! The structural AC rules.
//!
//! `aci_simp` names one normal form for a small algebraic hierarchy of operators; `absorb` names
//! the annihilator law separately. The core vocabulary splits them by the structure of the
//! operator instead — `semilattice_simp` (bounded semilattices), `boolean_group_simp` (abelian
//! groups of exponent two), `assoc_simp` (free monoids), and `poly_simp` (commutative rings) —
//! so that each rule's normal form is exactly its operators', and a consumer can check each with
//! the matching verified normalizer. This module is the translation: a step of one of the legacy
//! rules is relabeled to the structural rule of its top operator, after the structural rule's own
//! checker has accepted the conclusion.

use super::*;
use crate::{checker, CheckerError};

type Res = Result<Rc<ProofNode>, ElaborationError>;

/// The structural rule whose normal form the equality `(= t1 t2)` is an instance of. `None` when
/// no structural rule accepts it.
///
/// Each rule's checker is asked in turn, and each already looks for its own operator on *either*
/// side (`structural_side`) before normalizing both. Selecting the rule by the head of one side
/// instead would miss the equalities whose normalized side is not headed by the operator at all:
/// `(= (not p) (or (not p) (not p)))`, idempotence read backwards, is headed by `not` on the left,
/// and cvc5 emits exactly that. The four operator sets are disjoint, so at most one checker can
/// accept and the order is only for determinism.
pub fn structural_rule(
    pool: &mut PrimitivePool,
    t1: &Rc<Term>,
    t2: &Rc<Term>,
) -> Option<&'static str> {
    type Check =
        fn(&mut dyn crate::ast::TermPool, &Rc<Term>, &Rc<Term>) -> Result<(), CheckerError>;
    const RULES: [(&str, Check); 4] = [
        ("semilattice_simp", checker::semilattice_simp_equal),
        ("boolean_group_simp", checker::boolean_group_simp_equal),
        ("assoc_simp", checker::assoc_simp_equal),
        ("poly_simp", checker::poly_simp_equal),
    ];
    RULES
        .into_iter()
        .find_map(|(rule, accepts)| accepts(pool, t1, t2).is_ok().then_some(rule))
}

/// The structural rule for a unit-equality clause, if any.
pub fn structural_label(pool: &mut PrimitivePool, equality: &Rc<Term>) -> Option<&'static str> {
    let (t1, t2) = match_term!((= t1 t2) = equality)?;
    structural_rule(pool, t1, t2)
}

/// Relabels a legacy AC step (`aci_simp`, `absorb`) to the structural rule of its operator. A
/// step no structural rule accepts is kept as it is, with a warning: that is a legacy instance
/// outside the structural vocabulary (e.g. an `aci_simp` over a bitvector operator whose
/// normal form is `poly_simp`'s but which `poly_simp` reads differently), not a defect.
pub fn relabel(pool: &mut PrimitivePool, _: &mut ContextStack, step: &StepNode) -> Res {
    let [conclusion] = step.clause.as_slice() else {
        return Err(CheckerError::WrongLengthOfClause(1.into(), step.clause.len()).into());
    };
    let Some(rule) = structural_label(pool, conclusion) else {
        log::warn!(
            "{} '{}': no structural rule accepts the conclusion, keeping step",
            step.rule,
            step.id
        );
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    let b = Builder::new(pool, step);
    Ok(b.finish(step, rule, Vec::new(), Vec::new()))
}
