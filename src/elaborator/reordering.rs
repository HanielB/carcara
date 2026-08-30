use rapidhash::{HashSetExt, RapidHashSet};

use super::*;
use crate::{checker::error::CheckerError, resolution::ResolutionError};

pub fn remove_reorderings(
    proof: ProofNodeForest,
) -> Result<ProofNodeForest, ElaborationErrorAtStep> {
    proof.mutate(|_, node, premises_changed| {
        let Some(step) = node.as_step() else {
            return Ok(node.clone());
        };

        // For reordering steps, we remove the step and return its only premise
        if step.rule == "reordering" {
            return Ok(step.premises[0].clone());
        }

        // If the rule is order-sensitive, and any premise was modified, we recompute the conclusion
        if let Some(recompute) = get_recomputation_func(&step.rule)
            && premises_changed
        {
            let new = Rc::new(ProofNode::Step(StepNode {
                clause: recompute(step).map_err(|e| e.at(step))?,
                ..step.clone()
            }));
            return Ok(new);
        }

        // Otherwise the node is unchanged
        Ok(node.clone())
    })
}

type RecomputationFunc = fn(&StepNode) -> Result<Vec<Rc<Term>>, ElaborationError>;

fn get_recomputation_func(rule: &str) -> Option<RecomputationFunc> {
    Some(match rule {
        // Weakening and contraction recomputation is infallible, so we have to wrap in `Ok`
        "weakening" => |step| Ok(recompute_weakening(step)),
        "contraction" => |step| Ok(recompute_contraction(step)),
        "resolution" | "th_resolution" => |step| recompute_resolution(step, false),
        "strict_resolution" => |step| recompute_resolution(step, true),
        _ => return None,
    })
}

fn recompute_weakening(step: &StepNode) -> Vec<Rc<Term>> {
    let mut new = step.clause.clone();
    let premise = step.premises[0].clause();
    new[..premise.len()].clone_from_slice(premise);
    new
}

fn recompute_contraction(step: &StepNode) -> Vec<Rc<Term>> {
    // Doing this is slightly faster than using `.iter().dedup().collect()`
    let mut seen = RapidHashSet::new();
    let mut new = step.premises[0].clause().to_vec();
    new.retain(|elem| seen.insert(elem.clone()));
    new
}

fn recompute_resolution(step: &StepNode, strict: bool) -> Result<Vec<Rc<Term>>, ElaborationError> {
    if step.premises.len() < 2 {
        return Err(CheckerError::WrongNumberOfPremises((2..).into(), step.premises.len()).into());
    }
    let num_args = 2 * (step.premises.len() - 1);
    if step.args.len() != num_args {
        return Err(CheckerError::WrongNumberOfArgs(num_args.into(), step.args.len()).into());
    }

    let premise_clauses: Vec<_> = step.premises.iter().map(|p| p.clause()).collect();
    let pivots: Vec<_> = step
        .args
        .chunks(2)
        .map(|chunk| {
            let pivot = &chunk[0];
            let polarity = chunk[1].is_bool_true();
            (pivot, polarity)
        })
        .collect();
    if strict {
        Ok(apply_naive_resolution(&premise_clauses, &pivots)?)
    } else {
        Ok(apply_set_resolution(&premise_clauses, &pivots)?)
    }
}

/// Applies the resolution steps under the *set* semantics of the checker's
/// `resolution_with_args`: literals are deduplicated, and removing a pivot removes its (single)
/// set entry — which is how the elaboration passes compute crowded resolutions. The naive
/// multiset version below is kept for `strict_resolution`, whose checker removes exactly one
/// copy per step.
fn apply_set_resolution(
    premises: &[&[Rc<Term>]],
    pivots: &[(&Rc<Term>, bool)],
) -> Result<Vec<Rc<Term>>, ResolutionError> {
    fn push(current: &mut Vec<Rc<Term>>, t: &Rc<Term>) {
        if !current.contains(t) {
            current.push(t.clone());
        }
    }

    let mut current = Vec::new();
    for t in premises[0] {
        push(&mut current, t);
    }

    for (&premise, &(pivot, polarity)) in premises[1..].iter().zip(pivots) {
        let is_pivot = |x: &Rc<Term>, is_current: bool| {
            if is_current == polarity {
                x == pivot
            } else {
                x.remove_negation() == Some(pivot)
            }
        };

        let pos = current
            .iter()
            .position(|x| is_pivot(x, true))
            .ok_or_else(|| ResolutionError::PivotNotFound(pivot.clone()))?;
        current.remove(pos);

        let mut found = false;
        for t in premise {
            if !found && is_pivot(t, false) {
                found = true;
            } else {
                push(&mut current, t);
            }
        }
        if !found {
            return Err(ResolutionError::PivotNotFound(pivot.clone()));
        }
    }

    Ok(current)
}

fn apply_naive_resolution(
    premises: &[&[Rc<Term>]],
    pivots: &[(&Rc<Term>, bool)],
) -> Result<Vec<Rc<Term>>, ResolutionError> {
    let mut current = premises[0].to_vec();

    for (&premise, &(pivot, polarity)) in premises[1..].iter().zip(pivots) {
        let is_pivot = |x: &Rc<Term>, is_current: bool| {
            if is_current == polarity {
                x == pivot
            } else {
                x.remove_negation() == Some(pivot)
            }
        };

        let pos = current
            .iter()
            .position(|x| is_pivot(x, true))
            .ok_or_else(|| ResolutionError::PivotNotFound(pivot.clone()))?;
        current.remove(pos);

        let mut found = false;
        for t in premise {
            if !found && is_pivot(t, false) {
                found = true;
            } else {
                current.push(t.clone());
            }
        }
        if !found {
            return Err(ResolutionError::PivotNotFound(pivot.clone()));
        }
    }

    Ok(current)
}
