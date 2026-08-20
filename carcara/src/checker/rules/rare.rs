use indexmap::IndexMap;

use crate::{
    ast::{Constant, Substitution, Term},
    checker::{error::CheckerError, rules::get_premise_term},
    rare::{get_rules, meta_shapes, rewrite_meta_terms},
};

use super::{RuleArgs, RuleResult};

pub fn check_rare(
    RuleArgs {
        premises,
        conclusion,
        pool,
        args,
        rare_rules,
        ..
    }: RuleArgs,
) -> RuleResult {
    let Some(rule_literal) = args.first() else {
        return Err(CheckerError::RareNotSpecifiedRule);
    };

    if let Term::Const(Constant::String(v)) = &**rule_literal {
        let Some(rare_term) = rare_rules.rules.get(v) else {
            return Err(CheckerError::RareRuleNotFound(v.clone()));
        };
        if rare_term.arguments.len() + 1 != args.len() {
            return Err(CheckerError::RareNumberOfPremisesWrong(
                rare_term.arguments.len(),
            ));
        }

        if conclusion.is_empty() || conclusion.len() > 1 {
            return Err(CheckerError::RareConclusionNumberInvalid());
        }

        let mut arguments = args.iter().rev();
        let mut map = IndexMap::new();

        for arg in rare_term.arguments.iter().rev() {
            let variable = rare_term.parameters.get(arg).unwrap().variable.clone();
            let value = arguments.next().unwrap().clone();
            map.insert(variable, value);
        }

        if rare_term.premises.len() != premises.len() {
            return Err(CheckerError::RareNumberOfPremisesWrong(
                rare_term.premises.len(),
            ));
        }

        // Checking the step is dominated by the meta-rewriting sweep that normalizes the n-ary and
        // `rare-list` meta-constructs away, and that sweep is the identity on a term where no
        // meta-rule can match. That is the common case by a wide margin: in cvc5's rule set only
        // 16 of the 119 rules even take a `:list` parameter, and the frequent rules take none.
        //
        // We can settle it from the rule and the step's arguments alone, without looking at the
        // instantiation. `Substitution::apply` replaces variables by argument values and rebuilds
        // every other node with the same operator and the same number of arguments, so every
        // operator application in the instantiated term either occurs verbatim inside an argument
        // value, or has the operator and the arity of an application in the rule's own conclusion
        // or premises. Whether a meta-rule can match at a node depends on nothing else (see
        // `MetaShapes`), so if neither the rule's terms nor any argument value admits a match,
        // neither does the instantiation, and every sweep below is a no-op.
        //
        // Getting this wrong in the unsafe direction would reject a valid step, so the two halves
        // are deliberately over-approximate: `has_meta_construct` is decided by shape rather than
        // by full matching, and every argument value is scanned in full, including those of rules
        // that declare no `:list` parameter.
        let needs_meta_rewriting =
            rare_term.has_meta_construct || meta_shapes().any_contains_redex(map.values());

        let mut rare_premises = rare_term.premises.iter();
        let mut subst = Substitution::new(pool, map)?;

        for premise in premises {
            let premise = get_premise_term(premise)?;
            let rare_premise = rare_premises.next().unwrap();
            let rare_premise = subst.apply(pool, rare_premise);
            let rare_premise = if needs_meta_rewriting {
                rewrite_meta_terms(pool, rare_premise, get_rules())
            } else {
                rare_premise
            };

            if *premise != rare_premise {
                return Err(CheckerError::RarePremiseAreNotEqual(
                    premise.clone(),
                    rare_premise.clone(),
                ));
            }
        }

        let got = subst.apply(pool, &rare_term.conclusion);

        // The premises are also required to be in meta-normal form themselves. When no sweep is
        // needed this check cannot fail: the loop above has already established that each premise
        // is the instantiated rule premise, which we just argued admits no match.
        if needs_meta_rewriting {
            for premise in premises {
                let premise = get_premise_term(premise)?;
                let premise_rare = rewrite_meta_terms(pool, premise.clone(), get_rules());
                if *premise != premise_rare {
                    return Err(CheckerError::RarePremiseAreNotEqual(
                        premise.clone(),
                        premise_rare,
                    ));
                }
            }
        }

        let rule_conclusion = if needs_meta_rewriting {
            rewrite_meta_terms(pool, got, get_rules())
        } else {
            got
        };
        if rule_conclusion != conclusion[0] {
            return Err(CheckerError::RareConclusionAreNotEqual(
                rule_conclusion,
                conclusion[0].clone(),
            ));
        }

        return Ok(());
    }

    Err(CheckerError::RareRuleExpectedLiteral(rule_literal.clone()))
}
