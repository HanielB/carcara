//! The `budget` pass: split resolution chains that are too long for a consumer to check in one
//! piece.
//!
//! A `resolution` step over `n` premises is one derivation, and a checker that replays it as a
//! single proof term — lean-smt does, with each intermediate clause an explicit list of literals
//! — pays for the whole chain at once: the term is `n` layers deep and its checking is
//! superlinear in `n`. A chain of 327 premises exhausts Lean's kernel where one of 134 takes
//! under a second. Splitting the chain into pieces of at most `budget` premises keeps every
//! piece within what the kernel disposes of quickly, and the checker discards each piece once
//! checked, so the peak cost is that of one piece rather than the chain.
//!
//! The split is only a regrouping of the same binary resolutions in the same order, with the
//! same pivots: the first piece resolves the first `budget` premises, and each following piece
//! resolves the previous piece's conclusion against the next `budget - 1` premises. Every piece
//! is a `resolution` step with explicit pivot arguments, closed by a `contraction` if it
//! introduced duplicates (a piece's conclusion is a multiset, the original step's is a set).
//! Steps with fewer premises than the budget, and steps without pivot arguments (produced by
//! `local`), are left alone.

use super::{IdHelper, error::ElaborationError, uncrowding::{check_clauses_are_compatible, get_weakening_clause}};
use crate::{
    ast::{ProofNode, Rc, StepNode, Term, pool::{PrimitivePool, TermPool}},
    resolution::{Literal, literal_to_term},
};
use rapidhash::{HashSetExt, RapidHashSet};

/// The pivot of a premise, as `(literal, polarity)` read off the step's arguments.
type Pivot<'a> = (Literal<'a>, bool);

/// One premise of the chain with the pivot that resolves it against the running clause.
struct Premise<'a> {
    node: Rc<ProofNode>,
    clause: Vec<Literal<'a>>,
    pivot: Option<Pivot<'a>>,
}

fn premises_of<'a>(step: &'a StepNode) -> Vec<Premise<'a>> {
    let pivots = std::iter::once(None).chain(step.args.chunks(2).map(|c| {
        let pivot = c[0].remove_all_negations();
        let polarity = c[1].is_bool_true();
        Some((pivot, polarity))
    }));
    step.premises
        .iter()
        .zip(pivots)
        .map(|(node, pivot)| Premise {
            node: node.clone(),
            clause: node.clause().iter().map(Rc::remove_all_negations).collect(),
            pivot,
        })
        .collect()
}

/// Resolve `current` against `next` on `pivot`, as Alethe does: every occurrence of the pivot
/// leaves the running clause, the first occurrence of its negation leaves `next`, and what remains
/// of `next` is appended.
fn resolve<'a>(current: &mut Vec<Literal<'a>>, next: &[Literal<'a>], (pivot, polarity): Pivot<'a>) {
    let negated = (pivot.0 + 1, pivot.1);
    let (in_current, in_next) = if polarity { (pivot, negated) } else { (negated, pivot) };
    current.retain(|l| *l != in_current);
    let mut found = false;
    for &l in next {
        if !found && l == in_next {
            found = true;
        } else {
            current.push(l);
        }
    }
}

/// A `resolution` step over `premises` (the first carrying no pivot), followed by a `contraction`
/// when the conclusion has duplicates. Returns the node and its clause as literals.
fn piece<'a>(
    pool: &mut PrimitivePool,
    ids: &mut IdHelper,
    depth: usize,
    premises: &[Premise<'a>],
) -> (Rc<ProofNode>, Vec<Literal<'a>>) {
    let mut conclusion = premises[0].clause.clone();
    for p in &premises[1..] {
        resolve(&mut conclusion, &p.clause, p.pivot.unwrap());
    }
    let args = premises[1..]
        .iter()
        .flat_map(|p| {
            let (literal, polarity) = p.pivot.unwrap();
            [literal_to_term(pool, literal), pool.bool_constant(polarity)]
        })
        .collect();
    let to_clause = |pool: &mut PrimitivePool, ls: &[Literal<'a>]| -> Vec<Rc<Term>> {
        ls.iter().map(|&l| literal_to_term(pool, l)).collect()
    };
    let resolution = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth,
        clause: to_clause(pool, &conclusion),
        rule: "resolution".to_owned(),
        premises: premises.iter().map(|p| p.node.clone()).collect(),
        args,
        discharge: Vec::new(),
        previous_step: None,
    }));
    let mut seen = RapidHashSet::new();
    let deduped: Vec<_> = conclusion.iter().copied().filter(|l| seen.insert(*l)).collect();
    if deduped.len() == conclusion.len() {
        return (resolution, conclusion);
    }
    let contraction = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth,
        clause: to_clause(pool, &deduped),
        rule: "contraction".to_owned(),
        premises: vec![resolution],
        args: Vec::new(),
        discharge: Vec::new(),
        previous_step: None,
    }));
    (contraction, deduped)
}

/// Split `step`, a `resolution` with pivot arguments over more than `budget` premises, into a
/// chain of resolutions of at most `budget` premises each. The last piece keeps the step's id and
/// clause, so the rest of the proof is untouched.
pub fn split_resolution(
    pool: &mut PrimitivePool,
    step: &StepNode,
    budget: usize,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let budget = budget.max(2);
    let premises = premises_of(step);
    if premises.len() <= budget || step.args.len() != 2 * (premises.len() - 1) {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    let mut ids = IdHelper::new(&step.id);
    let (mut node, mut clause) = piece(pool, &mut ids, step.depth, &premises[..budget]);
    let mut next = budget;
    while next < premises.len() {
        let end = (next + budget - 1).min(premises.len());
        let head = Premise { node: node.clone(), clause: clause.clone(), pivot: None };
        let mut group = vec![head];
        group.extend(premises[next..end].iter().map(|p| Premise {
            node: p.node.clone(),
            clause: p.clause.clone(),
            pivot: p.pivot,
        }));
        (node, clause) = piece(pool, &mut ids, step.depth, &group);
        next = end;
    }
    // the last piece stands for the original step: same id, and its clause, which the pieces
    // reach up to order and multiplicity (the checker's clauses are sets)
    let mut last = node.as_step().unwrap().clone();
    // the pieces reach the stated clause as a set; the stated clause is whatever multiset the
    // solver wrote. Close the gap as `uncrowd` does: a `weakening` restores any multiplicity the
    // split lost (the last piece has already contracted its own duplicates), and a `reordering`
    // the order.
    check_clauses_are_compatible(&last.clause, &step.clause)
        .map_err(|_| ElaborationError::BudgetConclusionMismatch(step.id.clone()))?;
    if last.clause.len() != step.clause.len() {
        let clause = get_weakening_clause(&last.clause, &step.clause)
            .map_err(|_| ElaborationError::BudgetConclusionMismatch(step.id.clone()))?;
        last = StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause,
            rule: "weakening".to_owned(),
            premises: vec![Rc::new(ProofNode::Step(last))],
            ..Default::default()
        };
    }
    if last.clause != step.clause {
        last = StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: step.clause.clone(),
            rule: "reordering".to_owned(),
            premises: vec![Rc::new(ProofNode::Step(last))],
            ..Default::default()
        };
    }
    last.id = step.id.clone();
    Ok(Rc::new(ProofNode::Step(last)))
}
