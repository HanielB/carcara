//! Reductions of the clausal category.
//!
//! The 19 premise clausification rules all follow the same two-step shape: the CNF axiom that pairs
//! with the rule, resolved with the rule's premise on the premise formula. The pairings are the
//! ones in the classification's table (note that the `equiv` family crosses indices).

use super::Builder;
use crate::{ast::*, elaborator::error::ElaborationError};

/// `th_resolution` is the same rule as `resolution`; we only normalize the name.
pub fn th_resolution(
    _: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    Ok(Rc::new(ProofNode::Step(StepNode {
        rule: "resolution".to_owned(),
        ..step.clone()
    })))
}

/// The conclusion of a `tautology` step is literally `true`, so a `true` step derives it, dropping
/// the premise.
pub fn tautology(
    _: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    Ok(Rc::new(ProofNode::Step(StepNode {
        rule: "true".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
        ..step.clone()
    })))
}

/// `and_intro` packs unit clauses into an `and` term, via `and_neg` and one resolution.
pub fn and_intro(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let mut b = Builder::new(pool, step);
    let node = b.and_intro(step.premises.clone())?;
    Ok(b.relabel(step, node))
}

/// The description of the CNF axiom that a premise clausification rule pairs with.
struct Axiom {
    rule: &'static str,
    clause: Vec<Rc<Term>>,
    args: Vec<Rc<Term>>,
    /// Whether the premise formula occurs positively in the axiom's clause. `and`, for instance,
    /// pairs with `and_pos`, whose first literal is the *negated* formula, so this is `false`.
    positive_in_axiom: bool,
}

/// Reduces one of the 19 premise clausification rules to its paired CNF axiom plus a resolution
/// with the rule's premise.
pub fn premise_clausification(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let premise = step.premises[0].clone();
    let [premise_term] = premise.clause() else {
        panic!("premise of a clausification rule must be a unit clause");
    };
    let premise_term = premise_term.clone();

    let mut b = Builder::new(pool, step);
    let axiom = build_axiom(&mut b, step, &premise_term)?;
    // The pivot is the premise formula: the formula itself if the premise is `(cl F)`, and `F` if
    // the premise is `(cl (not F))`
    let (pivot, polarity) = if axiom.positive_in_axiom {
        let formula = premise_term
            .remove_negation()
            .expect("premise formula must be negated")
            .clone();
        (formula, true)
    } else {
        (premise_term.clone(), false)
    };

    let axiom_step = b.step(axiom.clause, axiom.rule, Vec::new(), axiom.args);
    let node = b.resolve(vec![axiom_step, premise], vec![(pivot, polarity)])?;
    Ok(b.relabel(step, node))
}

fn build_axiom(
    b: &mut Builder,
    step: &StepNode,
    premise_term: &Rc<Term>,
) -> Result<Axiom, ElaborationError> {
    // For the rules whose premise is a negated formula, this is the formula itself
    let inner = premise_term.remove_negation().cloned();

    let axiom = match step.rule.as_str() {
        "and" => {
            let contents = match_term_err!((and ...) = premise_term)?.to_vec();
            let index = step.args[0].as_usize_err()?;
            let not_premise = b.not(premise_term);
            Axiom {
                rule: "and_pos",
                clause: vec![not_premise, contents[index].clone()],
                args: vec![step.args[0].clone()],
                positive_in_axiom: false,
            }
        }
        "not_or" => {
            let formula = inner.unwrap();
            let contents = match_term_err!((or ...) = &formula)?.to_vec();
            let index = step.args[0].as_usize_err()?;
            let not_disjunct = b.not(&contents[index]);
            Axiom {
                rule: "or_neg",
                clause: vec![formula, not_disjunct],
                args: vec![step.args[0].clone()],
                positive_in_axiom: true,
            }
        }
        "or" => {
            let contents = match_term_err!((or ...) = premise_term)?.to_vec();
            let not_premise = b.not(premise_term);
            let clause = std::iter::once(not_premise).chain(contents).collect();
            Axiom {
                rule: "or_pos",
                clause,
                args: Vec::new(),
                positive_in_axiom: false,
            }
        }
        "not_and" => {
            let formula = inner.unwrap();
            let contents = match_term_err!((and ...) = &formula)?.to_vec();
            let mut clause = vec![formula];
            for c in contents {
                let negated = b.not(&c);
                clause.push(negated);
            }
            Axiom {
                rule: "and_neg",
                clause,
                args: Vec::new(),
                positive_in_axiom: true,
            }
        }
        "xor1" | "xor2" => {
            let (phi_1, phi_2) = match_term_err!((xor phi_1 phi_2) = premise_term)?;
            let (phi_1, phi_2) = (phi_1.clone(), phi_2.clone());
            let not_premise = b.not(premise_term);
            let (rule, clause) = if step.rule == "xor1" {
                ("xor_pos1", vec![not_premise, phi_1, phi_2])
            } else {
                let (not_1, not_2) = (b.not(&phi_1), b.not(&phi_2));
                ("xor_pos2", vec![not_premise, not_1, not_2])
            };
            Axiom {
                rule,
                clause,
                args: Vec::new(),
                positive_in_axiom: false,
            }
        }
        "not_xor1" | "not_xor2" => {
            let formula = inner.unwrap();
            let (phi_1, phi_2) = match_term_err!((xor phi_1 phi_2) = &formula)?;
            let (phi_1, phi_2) = (phi_1.clone(), phi_2.clone());
            let (rule, clause) = if step.rule == "not_xor1" {
                let not_2 = b.not(&phi_2);
                ("xor_neg1", vec![formula, phi_1, not_2])
            } else {
                let not_1 = b.not(&phi_1);
                ("xor_neg2", vec![formula, not_1, phi_2])
            };
            Axiom {
                rule,
                clause,
                args: Vec::new(),
                positive_in_axiom: true,
            }
        }
        "implies" => {
            let (phi_1, phi_2) = match_term_err!((=> phi_1 phi_2) = premise_term)?;
            let (phi_1, phi_2) = (phi_1.clone(), phi_2.clone());
            let not_premise = b.not(premise_term);
            let not_1 = b.not(&phi_1);
            Axiom {
                rule: "implies_pos",
                clause: vec![not_premise, not_1, phi_2],
                args: Vec::new(),
                positive_in_axiom: false,
            }
        }
        "not_implies1" | "not_implies2" => {
            let formula = inner.unwrap();
            let (phi_1, phi_2) = match_term_err!((=> phi_1 phi_2) = &formula)?;
            let (phi_1, phi_2) = (phi_1.clone(), phi_2.clone());
            let (rule, clause) = if step.rule == "not_implies1" {
                ("implies_neg1", vec![formula, phi_1])
            } else {
                let not_2 = b.not(&phi_2);
                ("implies_neg2", vec![formula, not_2])
            };
            Axiom {
                rule,
                clause,
                args: Vec::new(),
                positive_in_axiom: true,
            }
        }
        "equiv1" | "equiv2" => {
            let (phi_1, phi_2) = match_term_err!((= phi_1 phi_2) = premise_term)?;
            let (phi_1, phi_2) = (phi_1.clone(), phi_2.clone());
            let not_premise = b.not(premise_term);
            let (rule, clause) = if step.rule == "equiv1" {
                let not_1 = b.not(&phi_1);
                ("equiv_pos2", vec![not_premise, not_1, phi_2])
            } else {
                let not_2 = b.not(&phi_2);
                ("equiv_pos1", vec![not_premise, phi_1, not_2])
            };
            Axiom {
                rule,
                clause,
                args: Vec::new(),
                positive_in_axiom: false,
            }
        }
        "not_equiv1" | "not_equiv2" => {
            let formula = inner.unwrap();
            let (phi_1, phi_2) = match_term_err!((= phi_1 phi_2) = &formula)?;
            let (phi_1, phi_2) = (phi_1.clone(), phi_2.clone());
            let (rule, clause) = if step.rule == "not_equiv1" {
                ("equiv_neg2", vec![formula, phi_1, phi_2])
            } else {
                let (not_1, not_2) = (b.not(&phi_1), b.not(&phi_2));
                ("equiv_neg1", vec![formula, not_1, not_2])
            };
            Axiom {
                rule,
                clause,
                args: Vec::new(),
                positive_in_axiom: true,
            }
        }
        "ite1" | "ite2" => {
            let (phi_1, phi_2, phi_3) = match_term_err!((ite phi_1 phi_2 phi_3) = premise_term)?;
            let (phi_1, phi_2, phi_3) = (phi_1.clone(), phi_2.clone(), phi_3.clone());
            let not_premise = b.not(premise_term);
            let (rule, clause) = if step.rule == "ite1" {
                ("ite_pos1", vec![not_premise, phi_1, phi_3])
            } else {
                let not_1 = b.not(&phi_1);
                ("ite_pos2", vec![not_premise, not_1, phi_2])
            };
            Axiom {
                rule,
                clause,
                args: Vec::new(),
                positive_in_axiom: false,
            }
        }
        "not_ite1" | "not_ite2" => {
            let formula = inner.unwrap();
            let (phi_1, phi_2, phi_3) = match_term_err!((ite phi_1 phi_2 phi_3) = &formula)?;
            let (phi_1, phi_2, phi_3) = (phi_1.clone(), phi_2.clone(), phi_3.clone());
            let (rule, clause) = if step.rule == "not_ite1" {
                let not_3 = b.not(&phi_3);
                ("ite_neg1", vec![formula, phi_1, not_3])
            } else {
                let (not_1, not_2) = (b.not(&phi_1), b.not(&phi_2));
                ("ite_neg2", vec![formula, not_1, not_2])
            };
            Axiom {
                rule,
                clause,
                args: Vec::new(),
                positive_in_axiom: true,
            }
        }
        other => unreachable!("not a premise clausification rule: {}", other),
    };
    Ok(axiom)
}
