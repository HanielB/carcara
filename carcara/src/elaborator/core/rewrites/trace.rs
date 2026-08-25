//! Trace producers: the rewrite sequence a `*_simplify` step's check corresponds to.
//!
//! For the rules checked by `generic_simplify_rule` the trace is read off the checker's own
//! labeled step functions, iterated exactly as the checker iterates them (root rewrites until the
//! goal or a fixed point is reached, in either orientation). For `and_simplify`/`or_simplify`,
//! whose checker is not a rewrite fixpoint, the three phases of `generic_and_or_simplify` are
//! mirrored as an explicit rewrite sequence.

use super::Link;
use crate::{
    ast::*,
    checker::error::CheckerError,
    checker::{
        bool_simplify_step, comp_simplify_step, eq_simplify_step, equiv_simplify_step,
        implies_simplify_step, ite_simplify_step, not_simplify_step, SimplifyStepFn,
    },
    elaborator::error::ElaborationError,
};
use indexmap::IndexSet;

fn explanation(msg: impl Into<String>) -> ElaborationError {
    CheckerError::Explanation(msg.into()).into()
}

/// Computes the rewrite chain from `lhs` to `rhs` for the given `*_simplify` rule. The returned
/// flag is true when the chain actually goes from `rhs` to `lhs` (the conclusion's equality is
/// flipped relative to the rewrite direction), in which case the caller must close with `symm`.
pub fn simplify_trace(
    pool: &mut PrimitivePool,
    rule: &str,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
) -> Result<(Vec<Link>, bool), ElaborationError> {
    match rule {
        "and_simplify" => Ok((and_or_trace(pool, Operator::And, lhs, rhs)?, false)),
        "or_simplify" => Ok((and_or_trace(pool, Operator::Or, lhs, rhs)?, false)),
        _ => {
            let step_fn: SimplifyStepFn = match rule {
                "ite_simplify" => ite_simplify_step,
                "eq_simplify" => eq_simplify_step,
                "not_simplify" => not_simplify_step,
                "implies_simplify" => implies_simplify_step,
                "equiv_simplify" => equiv_simplify_step,
                "bool_simplify" => bool_simplify_step,
                "comp_simplify" => comp_simplify_step,
                _ => return Err(explanation(format!("no trace producer for '{rule}'"))),
            };
            if let Some(links) = root_rewrite_trace(pool, step_fn, lhs, rhs) {
                return Ok((links, false));
            }
            if let Some(links) = root_rewrite_trace(pool, step_fn, rhs, lhs) {
                return Ok((links, true));
            }
            Err(explanation(format!(
                "the '{rule}' rewrites do not take one side of the conclusion to the other"
            )))
        }
    }
}

/// Iterates a labeled step function from `from`, mirroring the loop of `generic_simplify_rule`:
/// stop (successfully) as soon as the goal is produced, or (unsuccessfully) at a fixed point or
/// cycle.
fn root_rewrite_trace(
    pool: &mut PrimitivePool,
    step_fn: SimplifyStepFn,
    from: &Rc<Term>,
    goal: &Rc<Term>,
) -> Option<Vec<Link>> {
    let mut links = Vec::new();
    let mut current = from.clone();
    let mut seen = IndexSet::new();
    loop {
        if !seen.insert(current.clone()) {
            return None;
        }
        match step_fn(&current, pool) {
            Some((next, label)) => {
                links.push(Link {
                    before: current.clone(),
                    after: next.clone(),
                    label,
                    inner: None,
                });
                if next == *goal {
                    return Some(links);
                }
                current = next;
            }
            None => return None,
        }
    }
}

/// The n-ary application of `op` a phase state corresponds to: the operator applied to the
/// arguments, collapsing a singleton to its element and the empty application to the operator's
/// neutral element — which is how the RARE list semantics reads the corresponding rule instances.
fn form(pool: &mut PrimitivePool, op: Operator, args: &[Rc<Term>], skip_term: bool) -> Rc<Term> {
    match args.len() {
        0 => pool.bool_constant(skip_term),
        1 => args[0].clone(),
        _ => pool.add(Term::Op(op, args.to_vec())),
    }
}

/// Mirrors the phases of `generic_and_or_simplify` as a rewrite sequence.
fn and_or_trace(
    pool: &mut PrimitivePool,
    op: Operator,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
) -> Result<Vec<Link>, ElaborationError> {
    let skip_term = op == Operator::And;
    let short_circuit = !skip_term;
    let (flatten, skip_elim, dup_elim, const_elim, conf, conf_flipped) = match op {
        Operator::And => (
            "and-flatten",
            "and-true-elim",
            "and-dup-elim",
            "and-false",
            "bool-and-conf",
            "bool-and-conf2",
        ),
        Operator::Or => (
            "or-flatten",
            "or-false-elim",
            "or-dup-elim",
            "or-true",
            "bool-or-taut",
            "bool-or-taut2",
        ),
        _ => unreachable!(),
    };

    let mut links = Vec::new();
    let mut phis = match lhs.as_ref() {
        Term::Op(o, args) if *o == op => args.clone(),
        _ => {
            return Err(explanation(
                "left-hand side is not an application of the operator",
            ))
        }
    };
    // The checker compares *argument lists*, reading a non-application right-hand side as a
    // one-element list — and a singleton application `(or x)` as the list `[x]`. Mirror that, and
    // when the target is reached give the final link the right-hand side exactly as written
    // (which may be a singleton application `form` would collapse).
    let rhs_args: Vec<Rc<Term>> = match rhs.as_ref() {
        Term::Op(o, args) if *o == op => args.clone(),
        _ => vec![rhs.clone()],
    };

    macro_rules! done {
        () => {
            if phis == rhs_args && !links.is_empty() {
                links.last_mut().unwrap().after = rhs.clone();
                return Ok(links);
            }
        };
    }

    // A singleton application equated with its own argument list (`(or x) ≈ x`, or an identical
    // argument list under a differently-shaped application) is the unit collapse. Such terms are
    // out of spec — Alethe has no singleton application of an n-ary connective — but veriT emits
    // them, so the trace handles them: the flatten recipe proves the equality in one
    // `or_pos`/`or_neg` (or `and_pos`/`and_neg`) pair.
    if phis == rhs_args && lhs != rhs {
        links.push(Link {
            before: lhs.clone(),
            after: rhs.clone(),
            label: flatten,
            inner: None,
        });
        return Ok(links);
    }

    // Singleton unwrap: `(and (and p q r))` is read as `(and p q r)`
    if phis.len() == 1 {
        if let Term::Op(o, inner) = phis[0].as_ref() {
            if *o == op {
                let after = phis[0].clone();
                links.push(Link {
                    before: lhs.clone(),
                    after,
                    label: flatten,
                    inner: None,
                });
                phis = inner.clone();
                done!();
            }
        }
    }

    // Phase 1: remove the skip term ("true" for `and`, "false" for `or`)
    while let Some(pos) = phis.iter().position(|t| t.is_bool_constant(skip_term)) {
        if phis.len() == 1 {
            break;
        }
        let before = form(pool, op, &phis, skip_term);
        phis.remove(pos);
        let after = form(pool, op, &phis, skip_term);
        links.push(Link {
            before,
            after,
            label: skip_elim,
            inner: None,
        });
        done!();
    }

    // Phase 2: remove duplicates
    let mut seen: IndexSet<Rc<Term>> = IndexSet::new();
    let mut pos = 0;
    while pos < phis.len() {
        if seen.insert(phis[pos].clone()) {
            pos += 1;
            continue;
        }
        let before = form(pool, op, &phis, skip_term);
        phis.remove(pos);
        let after = form(pool, op, &phis, skip_term);
        links.push(Link {
            before,
            after,
            label: dup_elim,
            inner: None,
        });
        done!();
    }

    // Phase 3: short-circuiting, either by the short-circuit constant or by a complementary pair
    // (modulo the parity of stacked negations, which is first normalized away argument-wise)
    if !rhs.is_bool_constant(short_circuit) {
        return Err(explanation(
            "the rewrites do not take the left-hand side to the right-hand side",
        ));
    }
    if phis.iter().any(|t| t.is_bool_constant(short_circuit)) {
        let before = form(pool, op, &phis, skip_term);
        links.push(Link {
            before,
            after: rhs.clone(),
            label: const_elim,
            inner: None,
        });
        return Ok(links);
    }

    let pairs: Vec<(bool, Rc<Term>)> = phis
        .iter()
        .map(|t| {
            let (polarity, inner) = t.remove_all_negations_with_polarity();
            (polarity, inner.clone())
        })
        .collect();
    let mut found = None;
    'outer: for i in 0..phis.len() {
        for k in (i + 1)..phis.len() {
            if pairs[i].1 == pairs[k].1 && pairs[i].0 != pairs[k].0 {
                found = Some((i, k));
                break 'outer;
            }
        }
    }
    let Some((i, k)) = found else {
        return Err(explanation(
            "the rewrites do not take the left-hand side to the right-hand side",
        ));
    };
    let first_is_positive = pairs[i].0;

    // Normalize the two arguments to their parity-canonical forms (`ψ` or `¬ψ`)
    for &idx in &[i, k] {
        let (polarity, inner) = phis[idx].remove_all_negations_with_polarity();
        let inner = inner.clone();
        let canonical = if polarity {
            inner.clone()
        } else {
            build_term!(pool, (not { inner.clone() }))
        };
        while phis[idx] != canonical {
            let arg_before = phis[idx].clone();
            let arg_after = arg_before
                .remove_negation()
                .and_then(Rc::remove_negation)
                .expect("parity-normalization always strips two negations")
                .clone();
            let before = form(pool, op, &phis, skip_term);
            phis[idx] = arg_after.clone();
            let after = form(pool, op, &phis, skip_term);
            links.push(Link {
                before,
                after,
                label: "bool-double-not-elim",
                inner: Some((arg_before, arg_after)),
            });
        }
    }

    let before = form(pool, op, &phis, skip_term);
    let label = if first_is_positive {
        conf
    } else {
        conf_flipped
    };
    links.push(Link {
        before,
        after: rhs.clone(),
        label,
        inner: None,
    });
    Ok(links)
}
