use super::{IdHelper, PolyeqElaborator};
use crate::{
    ast::{
        ContextStack, Operator, ProofNode, Rc, Sort, StepNode, Term, build_term, match_term,
        pool::{PrimitivePool, TermPool},
    },
    checker::{apply_bfun_elim, error::CheckerError},
    elaborator::error::ElaborationError,
};
use indexmap::IndexMap;

/// The elimination `distinct_elim` is checked against: the pairwise disequalities of `args`, in
/// lexicographic order, each written `(not (= aᵢ aⱼ))` with `i < j`. Mirrors the shape the
/// checker's `distinct_elim` recomputes; the checker accepts either orientation per pair, and
/// this is the orientation it recomputes.
fn canonical_elimination(pool: &mut PrimitivePool, args: &[Rc<Term>]) -> Option<Rc<Term>> {
    match args {
        [] | [_] => None,
        [a, b] => {
            let (a, b) = (a.clone(), b.clone());
            Some(build_term!(pool, (not (= {a} {b}))))
        }
        _ if pool.sort(&args[0]).as_ref() == &Sort::Bool => Some(pool.bool_false()),
        _ => {
            let mut conjuncts = Vec::with_capacity(args.len() * (args.len() - 1) / 2);
            for i in 0..args.len() {
                for j in (i + 1)..args.len() {
                    let (a, b) = (args[i].clone(), args[j].clone());
                    conjuncts.push(build_term!(pool, (not (= {a} {b}))));
                }
            }
            Some(pool.add(Term::Op(Operator::And, conjuncts)))
        }
    }
}

/// `distinct_elim` accepts each disequality in either orientation, so a producer may write the
/// conclusion with some of them flipped -- veriT does, on about a quarter of the pairs of the
/// large `distinct`s in the ESC/Java benchmarks. That is a polyequality, and eliminating it is
/// this pass's job; left in, it makes a consumer reconcile two conjunctions of up to n(n-1)/2
/// conjuncts, which for n = 148 is 10,878.
///
/// The step is rewritten to conclude the canonical elimination, with a bridge from there to the
/// stated one. The step's own conclusion is unchanged, which matters: its consumers include
/// `and` steps that project a conjunct by index, and those read the orientation the producer
/// wrote.
pub fn distinct_elim(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let unchanged = || Ok(Rc::new(ProofNode::Step(step.clone())));
    if step.clause.len() != 1 {
        return unchanged();
    }
    let Some((distinct, got)) = match_term!((= d s) = &step.clause[0]) else {
        return unchanged();
    };
    let Some(args) = match_term!((distinct ...) = distinct) else {
        return unchanged();
    };
    let (distinct, got, args) = (distinct.clone(), got.clone(), args.to_vec());
    let Some(expected) = canonical_elimination(pool, &args) else {
        return unchanged();
    };
    if got == expected {
        return unchanged();
    }

    let mut ids = IdHelper::new(&step.id);
    let canonical_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![build_term!(pool, (= {distinct.clone()} {expected.clone()}))],
        rule: "distinct_elim".to_owned(),
        ..StepNode::default()
    }));
    let bridge = PolyeqElaborator::new(&mut ids, step.depth, false).elaborate(pool, expected, got);
    Ok(Rc::new(ProofNode::Step(StepNode {
        id: step.id.clone(),
        depth: step.depth,
        clause: step.clause.clone(),
        rule: "trans".to_owned(),
        premises: vec![canonical_step, bridge],
        ..StepNode::default()
    })))
}

pub fn bfun_elim(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    assert_eq!(step.premises.len(), 1);
    assert_eq!(step.clause.len(), 1);
    let psi = &step.premises[0].clause()[0];
    let expected = apply_bfun_elim(pool, psi, &mut IndexMap::new()).map_err(CheckerError::from)?;
    let got = &step.clause[0];

    if *got == expected {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    let mut ids = IdHelper::new(&step.id);
    let polyeq_step = PolyeqElaborator::new(&mut ids, step.depth, false).elaborate(
        pool,
        expected.clone(),
        got.clone(),
    );
    let equiv1_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![build_term!(pool, (not {expected.clone()})), got.clone()],
        rule: "equiv1".to_owned(),
        premises: vec![polyeq_step],
        ..StepNode::default()
    }));
    let new_bfun_elim_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: vec![expected.clone()],
        rule: "bfun_elim".to_owned(),
        premises: step.premises.clone(),
        ..StepNode::default()
    }));
    let resolution_step = Rc::new(ProofNode::Step(StepNode {
        id: step.id.clone(),
        depth: step.depth,
        clause: step.clause.clone(),
        rule: "resolution".to_owned(),
        premises: vec![equiv1_step, new_bfun_elim_step],
        args: vec![expected, pool.bool_false()],
        ..StepNode::default()
    }));
    Ok(resolution_step)
}
