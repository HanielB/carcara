//! Reductions of the *expensive* computational primitives, `poly_simp` and `aci_simp`.
//!
//! Both are kept out of the default regimes: their reductions add no checking power, and the
//! rules they replace are perfectly good targets. What the reductions buy is a smaller trusted
//! base — 149 lines of ring normalization and 144 of ACI normalization leave the core with them —
//! and the regime that applies them is what measures that price.
//!
//! - **`poly_simp`** states a ring identity `(= t u)`. Whenever the identity is *linear* — which
//!   every instance in the evaluation corpus is, since the multipliers solvers emit are numerals
//!   — the core proves it from two Farkas bounds and the antisymmetry axiom: `t ≤ u`, `u ≤ t`,
//!   `la_disequality`, and the resolutions that close them. Genuinely nonlinear identities
//!   (`(* x y) = (* y x)`, a binomial expansion) have no core route and keep the step.
//! - **`aci_simp`** states that two terms agree modulo associativity, commutativity, identity
//!   elements and idempotence. For the semilattice connectives (`and`, `or`) — the only headers
//!   the corpus exercises — that is a propositional equivalence, and the core proves it the way
//!   it proves any equivalence: each direction under a discharge subproof, taking the premise
//!   apart with the CNF axioms and putting the conclusion together with them, closed by the
//!   `equiv_intro` pattern.

use super::Builder;
use crate::{ast::*, checker::error::CheckerError, elaborator::error::ElaborationError};
use indexmap::IndexSet;

type Res = Result<Rc<ProofNode>, ElaborationError>;

fn explanation(msg: impl Into<String>) -> ElaborationError {
    CheckerError::Explanation(msg.into()).into()
}

/// Derives `(cl (= t u))` for a linear identity, from two Farkas bounds and antisymmetry.
///
/// This is the core's only way to conclude a *positive* arithmetic equality: no `la_generic`
/// clause can carry one, which is exactly why `la_disequality` is an axiom.
pub(super) fn linear_equality(b: &mut Builder, t: &Rc<Term>, u: &Rc<Term>) -> Res {
    let (le, ge) = (
        build_term!(b.pool, (<= {t.clone()} {u.clone()})),
        build_term!(b.pool, (<= {u.clone()} {t.clone()})),
    );
    let lower = super::arithmetic::unit_farkas(b, vec![le.clone()])?;
    let upper = super::arithmetic::unit_farkas(b, vec![ge.clone()])?;

    let goal = build_term!(b.pool, (= {t.clone()} {u.clone()}));
    let (not_le, not_ge) = (b.not(&le), b.not(&ge));
    let disj = build_term!(b.pool, (or {goal.clone()} {not_le.clone()} {not_ge.clone()}));
    let axiom = b.step(vec![disj.clone()], "la_disequality", Vec::new(), Vec::new());
    let not_disj = b.not(&disj);
    let or_pos = b.step(
        vec![not_disj, goal, not_le, not_ge],
        "or_pos",
        Vec::new(),
        Vec::new(),
    );
    let unpacked = b.resolve(vec![or_pos, axiom], vec![(disj, false)])?;
    b.resolve(vec![unpacked, lower, upper], vec![(le, false), (ge, false)])
}

/// `poly_simp` concludes a ring identity; the linear ones are core-derivable.
pub fn poly_simp(pool: &mut PrimitivePool, _: &mut ContextStack, step: &StepNode) -> Res {
    let [conclusion] = step.clause.as_slice() else {
        return Err(CheckerError::WrongLengthOfClause(1.into(), step.clause.len()).into());
    };
    let (t, u) = match_term_err!((= t u) = conclusion)?;
    let (t, u) = (t.clone(), u.clone());
    if matches!(pool.sort(&t).as_sort(), Some(Sort::BitVec(_))) {
        return Err(explanation(
            "the bitvector case of `poly_simp` has no core reduction",
        ));
    }

    let mut b = Builder::new(pool, step);
    // The two sides are often the same term: `poly_simp` is emitted wherever a normalization
    // *could* have applied, and the identity is then reflexivity, which needs no arithmetic
    if t == u {
        let node = b.step(vec![conclusion.clone()], "refl", Vec::new(), Vec::new());
        return Ok(b.relabel(step, node));
    }
    let node = linear_equality(&mut b, &t, &u)?;
    Ok(b.relabel(step, node))
}

/// The leaves of a term headed by `op`, flattened through nested applications of `op` — the
/// associativity half of what `aci_simp` normalizes.
fn flatten(op: Operator, term: &Rc<Term>, acc: &mut Vec<Rc<Term>>) {
    match term.as_ref() {
        Term::Op(inner, args) if *inner == op => {
            for arg in args {
                flatten(op, arg, acc);
            }
        }
        _ => acc.push(term.clone()),
    }
}

fn is_identity(op: Operator, term: &Rc<Term>) -> bool {
    match op {
        Operator::And => term.is_bool_true(),
        Operator::Or => term.is_bool_false(),
        _ => false,
    }
}

/// Emits `(cl (not tree) leaf)`, descending the `and`-tree with one `and_pos` step per layer.
fn and_descend(b: &mut Builder, tree: &Rc<Term>, leaf: &Rc<Term>) -> Res {
    let Term::Op(Operator::And, args) = tree.as_ref() else {
        return Err(explanation("not an `and` term"));
    };
    let args = args.clone();
    let index = args
        .iter()
        .position(|a| a == leaf || has_leaf(Operator::And, a, leaf))
        .ok_or_else(|| explanation("conjunct not found"))?;
    let not_tree = b.not(tree);
    let index_arg = b.pool.add(Term::new_int(index));
    let step = b.step(
        vec![not_tree, args[index].clone()],
        "and_pos",
        Vec::new(),
        vec![index_arg],
    );
    if args[index] == *leaf {
        return Ok(step);
    }
    let inner = and_descend(b, &args[index], leaf)?;
    b.resolve(vec![step, inner], vec![(args[index].clone(), true)])
}

/// Emits `(cl tree (not leaf))`, descending the `or`-tree with one `or_neg` step per layer.
fn or_descend(b: &mut Builder, tree: &Rc<Term>, leaf: &Rc<Term>) -> Res {
    let Term::Op(Operator::Or, args) = tree.as_ref() else {
        return Err(explanation("not an `or` term"));
    };
    let args = args.clone();
    let index = args
        .iter()
        .position(|a| a == leaf || has_leaf(Operator::Or, a, leaf))
        .ok_or_else(|| explanation("disjunct not found"))?;
    let index_arg = b.pool.add(Term::new_int(index));
    let not_arg = b.not(&args[index]);
    let step = b.step(
        vec![tree.clone(), not_arg],
        "or_neg",
        Vec::new(),
        vec![index_arg],
    );
    if args[index] == *leaf {
        return Ok(step);
    }
    let inner = or_descend(b, &args[index], leaf)?;
    b.resolve(vec![step, inner], vec![(args[index].clone(), false)])
}

fn has_leaf(op: Operator, term: &Rc<Term>, leaf: &Rc<Term>) -> bool {
    let mut leaves = Vec::new();
    flatten(op, term, &mut leaves);
    leaves.iter().any(|l| l == leaf)
}

/// Derives `(cl tree)` for an `and`-tree, given a way to derive each of its leaves.
fn and_build(
    b: &mut Builder,
    tree: &Rc<Term>,
    leaf: &mut dyn FnMut(&mut Builder, &Rc<Term>) -> Res,
) -> Res {
    let Term::Op(Operator::And, args) = tree.as_ref() else {
        return leaf(b, tree);
    };
    let args = args.clone();
    let mut premises = Vec::new();
    let mut clause = vec![tree.clone()];
    let mut pivots = Vec::new();
    let mut resolved: Vec<Rc<Term>> = Vec::new();
    for arg in &args {
        let negated = b.not(arg);
        clause.push(negated);
        // A conjunction may repeat a conjunct — `(and true true φ ψ)` is what an `aci_simp` step
        // looks like when it drops identity elements. The `and_neg` clause holds one literal for
        // it however often it occurs, and resolution at elaborated granularity is set-wise, so
        // the conjunct is discharged once
        if resolved.contains(arg) {
            continue;
        }
        resolved.push(arg.clone());
        premises.push(and_build(b, arg, leaf)?);
        pivots.push((arg.clone(), false));
    }
    let and_neg = b.step(clause, "and_neg", Vec::new(), Vec::new());
    let all = std::iter::once(and_neg).chain(premises).collect();
    b.resolve(all, pivots)
}

/// One direction of an ACI equivalence: under a discharge subproof assuming `from`, derives `to`.
/// The closing clause is `(cl (not from) to)`.
fn aci_direction(b: &mut Builder, op: Operator, from: &Rc<Term>, to: &Rc<Term>) -> Res {
    b.open();
    let assumption = b.assume(from.clone());
    let from = from.clone();
    let derived = match op {
        Operator::And => {
            let mut leaf = |b: &mut Builder, target: &Rc<Term>| -> Res {
                if *target == from {
                    return Ok(assumption.clone());
                }
                if is_identity(Operator::And, target) {
                    let t = b.pool.bool_true();
                    return Ok(b.step(vec![t], "true", Vec::new(), Vec::new()));
                }
                let descent = and_descend(b, &from, target)?;
                b.resolve(
                    vec![descent, assumption.clone()],
                    vec![(from.clone(), false)],
                )
            };
            and_build(b, to, &mut leaf)?
        }
        Operator::Or => {
            // Take `from` apart into the clause of its leaves, then put `to` together from it
            let mut node = assumption.clone();
            let mut current = vec![from.clone()];
            while let Some(pos) = current
                .iter()
                .position(|t| matches!(t.as_ref(), Term::Op(Operator::Or, _)))
            {
                let tree = current[pos].clone();
                let Term::Op(_, args) = tree.as_ref() else {
                    unreachable!()
                };
                let args = args.clone();
                let not_tree = b.not(&tree);
                let clause = std::iter::once(not_tree)
                    .chain(args.iter().cloned())
                    .collect();
                let or_pos = b.step(clause, "or_pos", Vec::new(), Vec::new());
                node = b.resolve(vec![node, or_pos], vec![(tree.clone(), true)])?;
                current.splice(pos..pos + 1, args);
                // A disjunct may repeat — `(or φ φ)` is what an `aci_simp` step looks like when
                // it drops idempotence — and the clause being taken apart holds one literal for
                // it however often it occurs, so the leaves are tracked the same way
                let mut seen = Vec::new();
                current.retain(|t| {
                    let fresh = !seen.contains(t);
                    if fresh {
                        seen.push(t.clone());
                    }
                    fresh
                });
            }
            // An identity leaf is discharged by the `false` axiom — unless the target still has
            // it as a leaf, as in `(or false false) ≈ false` read the other way round, where it
            // has to be packed instead of thrown away
            let mut to_leaves = Vec::new();
            flatten(Operator::Or, to, &mut to_leaves);
            for lit in current.clone() {
                if is_identity(Operator::Or, &lit) && !to_leaves.contains(&lit) {
                    let f = b.pool.bool_false();
                    let not_false = b.not(&f);
                    let axiom = b.step(vec![not_false], "false", Vec::new(), Vec::new());
                    node = b.resolve(vec![node, axiom], vec![(lit, true)])?;
                }
            }
            for lit in current {
                let discharged = is_identity(Operator::Or, &lit) && !to_leaves.contains(&lit);
                if discharged || !node.clause().contains(&lit) {
                    continue;
                }
                let packing = if *to == lit {
                    // `to` is that leaf itself: nothing to pack
                    continue;
                } else {
                    or_descend(b, to, &lit)?
                };
                node = b.resolve(vec![node, packing], vec![(lit, true)])?;
            }
            node
        }
        _ => return Err(explanation("ACI reduction only covers `and` and `or`")),
    };
    Ok(b.close_subproof(vec![assumption], derived))
}

/// `aci_simp` concludes `(= t u)` for two terms equal modulo ACI; for `and`/`or` the equivalence
/// is propositional, and the core proves both directions clausally.
pub fn aci_simp(pool: &mut PrimitivePool, _: &mut ContextStack, step: &StepNode) -> Res {
    let [conclusion] = step.clause.as_slice() else {
        return Err(CheckerError::WrongLengthOfClause(1.into(), step.clause.len()).into());
    };
    let (t, u) = match_term_err!((= t u) = conclusion)?;
    let (t, u) = (t.clone(), u.clone());

    let op = match (t.as_ref(), u.as_ref()) {
        (Term::Op(a @ (Operator::And | Operator::Or), _), _) => *a,
        (_, Term::Op(a @ (Operator::And | Operator::Or), _)) => *a,
        _ => {
            return Err(explanation(
                "the ACI reduction needs a semilattice connective on at least one side",
            ))
        }
    };

    // The leaves must agree once the identity element is dropped; what is left of the
    // normalization — associativity, commutativity, idempotence — is what the clausal derivation
    // below reproduces
    let leaves = |term: &Rc<Term>| -> IndexSet<Rc<Term>> {
        let mut acc = Vec::new();
        flatten(op, term, &mut acc);
        acc.into_iter().filter(|l| !is_identity(op, l)).collect()
    };
    if leaves(&t) != leaves(&u) {
        return Err(explanation(
            "the two sides do not have the same leaves modulo the identity element",
        ));
    }

    let mut b = Builder::new(pool, step);
    let forward = aci_direction(&mut b, op, &t, &u)?;
    let backward = aci_direction(&mut b, op, &u, &t)?;
    let node = b.equiv_intro(t, u, forward, backward)?;
    Ok(b.relabel(step, node))
}
