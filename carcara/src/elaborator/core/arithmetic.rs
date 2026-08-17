//! Reductions of the linear-arithmetic category: everything reduces to `la_generic` (Farkas
//! certificates) and the `la_disequality` axiom, plus clausal packaging.

use super::Builder;
use crate::{ast::*, elaborator::error::ElaborationError};

fn real(pool: &mut PrimitivePool, n: i32) -> Rc<Term> {
    pool.add(Term::new_real(n))
}

/// `la_totality` concludes `(or (<= t1 t2) (<= t2 t1))`: a two-literal `la_generic` step with
/// coefficients `[1, 1]` derives the clause, and the `or_intro` pattern packs it into the `or`
/// term.
pub fn la_totality(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let (le_1, le_2) = match_term_err!((or l r) = &step.clause[0])?;
    let (le_1, le_2) = (le_1.clone(), le_2.clone());

    let mut b = Builder::new(pool, step);
    let args = vec![real(b.pool, 1), real(b.pool, 1)];
    let la_generic = b.step(vec![le_1, le_2], "la_generic", Vec::new(), args);
    let node = b.or_intro(la_generic)?;
    Ok(b.relabel(step, node))
}

/// `la_tautology` is `la_generic` with coefficient `[1]` (unit form) or `[1, 1]` plus `or_intro`
/// packaging (binary form) — the specification itself states the equivalence.
pub fn la_tautology(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    if let Some((phi_1, phi_2)) = match_term!((or phi_1 phi_2) = &step.clause[0]) {
        let (phi_1, phi_2) = (phi_1.clone(), phi_2.clone());
        let mut b = Builder::new(pool, step);
        let args = vec![real(b.pool, 1), real(b.pool, 1)];
        let la_generic = b.step(vec![phi_1, phi_2], "la_generic", Vec::new(), args);
        let node = b.or_intro(la_generic)?;
        Ok(b.relabel(step, node))
    } else {
        let args = vec![real(pool, 1)];
        Ok(Rc::new(ProofNode::Step(StepNode {
            rule: "la_generic".to_owned(),
            args,
            ..step.clone()
        })))
    }
}

/// `la_rw_eq` concludes `(= (= t u) (and (<= t u) (<= u t)))`. The → direction is two Farkas
/// steps under a discharge subproof; the ← direction comes from the `la_disequality` axiom
/// unpacked by `or_pos` and crossed with `and_pos`; the `equiv_intro` pattern closes.
pub fn la_rw_eq(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let (eq, conj) = match_term_err!((= eq conj) = &step.clause[0])?;
    let (eq, conj) = (eq.clone(), conj.clone());
    let (le_1, le_2) = match_term_err!((and l r) = &conj)?;
    let (le_1, le_2) = (le_1.clone(), le_2.clone());

    let mut b = Builder::new(pool, step);

    // Direction →, under a discharge subproof
    b.open();
    let assumption = b.assume(eq.clone());
    let not_eq = b.not(&eq);
    let args = vec![real(b.pool, -1), real(b.pool, 1)];
    let g1 = b.step(
        vec![not_eq.clone(), le_1.clone()],
        "la_generic",
        Vec::new(),
        args,
    );
    let args = vec![real(b.pool, 1), real(b.pool, 1)];
    let g2 = b.step(vec![not_eq, le_2.clone()], "la_generic", Vec::new(), args);
    let r1 = b.resolve(vec![g1, assumption.clone()], vec![(eq.clone(), false)])?;
    let r2 = b.resolve(vec![g2, assumption.clone()], vec![(eq.clone(), false)])?;
    let and_step = b.and_intro(vec![r1, r2])?;
    let forward = b.close_subproof(vec![assumption], and_step);

    // Direction ←, from the `la_disequality` axiom
    let (not_le_1, not_le_2) = (b.not(&le_1), b.not(&le_2));
    let axiom_term = build_term!(
        b.pool,
        (or {eq.clone()} {not_le_1.clone()} {not_le_2.clone()})
    );
    let axiom = b.step(
        vec![axiom_term.clone()],
        "la_disequality",
        Vec::new(),
        Vec::new(),
    );
    let not_axiom_term = b.not(&axiom_term);
    let or_pos = b.step(
        vec![not_axiom_term, eq.clone(), not_le_1, not_le_2],
        "or_pos",
        Vec::new(),
        Vec::new(),
    );
    let unpacked = b.resolve(vec![or_pos, axiom], vec![(axiom_term, false)])?;

    let not_conj = b.not(&conj);
    let index = b.pool.add(Term::new_int(0));
    let p1 = b.step(
        vec![not_conj.clone(), le_1.clone()],
        "and_pos",
        Vec::new(),
        vec![index],
    );
    let index = b.pool.add(Term::new_int(1));
    let p2 = b.step(
        vec![not_conj, le_2.clone()],
        "and_pos",
        Vec::new(),
        vec![index],
    );
    let r3 = b.resolve(vec![unpacked, p1], vec![(le_1, false)])?;
    let backward = b.resolve(vec![r3, p2], vec![(le_2, false)])?;

    let node = b.equiv_intro(eq, conj, forward, backward)?;
    Ok(b.relabel(step, node))
}
