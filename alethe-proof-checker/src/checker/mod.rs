pub mod error;
mod rules;

use crate::{
    ast::*,
    benchmarking::{Metrics, StepId},
    AletheResult, Error,
};
use ahash::{AHashMap, AHashSet};
use error::CheckerError;
use rules::{Rule, RuleArgs, RuleResult};
use std::time::{Duration, Instant};

struct Context {
    substitutions: AHashMap<Rc<Term>, Rc<Term>>,
    substitutions_until_fixed_point: AHashMap<Rc<Term>, Rc<Term>>,
    cumulative_substitutions: AHashMap<Rc<Term>, Rc<Term>>,
    bindings: AHashSet<SortedVar>,
}

#[derive(Debug)]
pub struct CheckerStatistics<'s> {
    pub file_name: &'s str,
    pub checking_time: &'s mut Duration,
    pub step_time: &'s mut Metrics<StepId>,
    pub step_time_by_file: &'s mut AHashMap<String, Metrics<StepId>>,
    pub step_time_by_rule: &'s mut AHashMap<String, Metrics<StepId>>,
}

#[derive(Debug, Default)]
pub struct Config<'c> {
    pub skip_unknown_rules: bool,
    pub is_running_test: bool,
    pub statistics: Option<CheckerStatistics<'c>>,
}

pub struct ProofChecker<'c> {
    pool: TermPool,
    config: Config<'c>,
    context: Vec<Context>,
}

impl<'c> ProofChecker<'c> {
    pub fn new(pool: TermPool, config: Config<'c>) -> Self {
        ProofChecker { pool, config, context: Vec::new() }
    }

    pub fn check(&mut self, proof: &Proof) -> AletheResult<()> {
        // Similarly to the parser, to avoid stack overflows in proofs with many nested subproofs,
        // we check the subproofs iteratively, instead of recursively

        // A stack of the subproof commands, and the index of the command being currently checked
        let mut commands_stack = vec![(0, proof.commands.as_slice())];

        while let Some(&(i, commands)) = commands_stack.last() {
            if i == commands.len() {
                // If we got to the end without popping the commands vector off the stack, we must
                // not be in a subproof
                assert!(commands_stack.len() == 1);
                break;
            }
            match &commands[i] {
                ProofCommand::Step(step) => {
                    let is_end_of_subproof = commands_stack.len() > 1 && i == commands.len() - 1;
                    self.check_step(step, &commands_stack, is_end_of_subproof)
                        .map_err(|e| Error::Checker {
                            inner: e,
                            rule: step.rule.clone(),
                            step: step.index.clone(),
                        })?;

                    // If this is the last command of a subproof, we have to pop the subproof
                    // commands off of the stack. The parser already ensures that the last command
                    // in a subproof is always a "step" command
                    if is_end_of_subproof {
                        commands_stack.pop();
                        self.context.pop();
                    }
                    Ok(())
                }
                ProofCommand::Subproof {
                    commands: inner_commands,
                    assignment_args,
                    variable_args,
                } => {
                    let time = Instant::now();
                    let new_context = self.build_context(assignment_args, variable_args);
                    self.context.push(new_context);
                    commands_stack.push((0, inner_commands));

                    let step_index = inner_commands
                        .last()
                        .and_then(|s| match s {
                            ProofCommand::Step(s) => Some(s.index.clone()),
                            _ => None,
                        })
                        .unwrap_or_default();
                    self.add_statistics_measurement(&step_index, "anchor*", time);
                    continue;
                }
                ProofCommand::Assume { index, term } => {
                    let time = Instant::now();

                    // Some subproofs contain "assume" commands inside them. These don't refer
                    // to the original problem premises, so we ignore the "assume" command if
                    // it is inside a subproof. Since the unit tests for the rules don't define the
                    // original problem, but sometimes use "assume" commands, we also skip the
                    // command if we are in a testing context.
                    let result = if self.config.is_running_test || commands_stack.len() > 1 {
                        Ok(())
                    } else {
                        let is_valid = proof.premises.contains(term)
                            || proof
                                .premises
                                .iter()
                                .any(|u| DeepEq::eq_modulo_reordering(term, u));
                        if is_valid {
                            Ok(())
                        } else {
                            Err(Error::Checker {
                                // TODO: Add specific error for this
                                inner: CheckerError::Unspecified,
                                rule: "assume".into(),
                                step: index.clone(),
                            })
                        }
                    };
                    self.add_statistics_measurement(index, "assume*", time);
                    result
                }
            }?;
            commands_stack.last_mut().unwrap().0 += 1;
        }

        Ok(())
    }

    fn check_step<'a>(
        &mut self,
        ProofStep {
            index,
            clause,
            rule: rule_name,
            premises,
            args,
            discharge: _, // The discharge attribute is not used when checking
        }: &'a ProofStep,
        commands_stack: &'a [(usize, &'a [ProofCommand])],
        is_end_of_subproof: bool,
    ) -> RuleResult {
        let time = Instant::now();
        let rule = match Self::get_rule(rule_name) {
            Some(r) => r,
            None if self.config.skip_unknown_rules => return Ok(()),
            None => return Err(CheckerError::UnknownRule),
        };
        let premises = premises
            .iter()
            .map(|&(depth, i)| &commands_stack[depth].1[i])
            .collect();

        // If this step ends a subproof, it might need to implicitly reference the other commands
        // in the subproof. Therefore, we pass them via the `subproof_commands` field
        let subproof_commands = if is_end_of_subproof {
            Some(commands_stack.last().unwrap().1)
        } else {
            None
        };

        let rule_args = RuleArgs {
            conclusion: clause,
            premises,
            args,
            pool: &mut self.pool,
            context: &self.context,
            subproof_commands,
        };
        rule(rule_args)?;
        self.add_statistics_measurement(index, rule_name, time);
        Ok(())
    }

    fn build_context(
        &mut self,
        assignment_args: &[(String, Rc<Term>)],
        variable_args: &[SortedVar],
    ) -> Context {
        // Since some rules (like "refl") need to apply substitutions until a fixed point, we
        // precompute these substitutions into a separate hash map. This assumes that the assignment
        // arguments are in the correct order.
        let mut substitutions = AHashMap::new();
        let mut substitutions_until_fixed_point = AHashMap::new();

        // We build the `substitutions_until_fixed_point` hash map from the bottom up, by using the
        // substitutions already introduced to transform the result of a new substitution before
        // inserting it into the hash map. So for instance, if the substitutions are "(:= y z)" and
        // "(:= x (f y))", we insert the first substitution, and then, when introducing the second,
        // we use the current state of the hash map to transform "(f y)" into "(f z)". The
        // resulting hash map will then contain "(:= y z)" and "(:= x (f z))"
        for (var, value) in assignment_args.iter() {
            let var_term = terminal!(var var; self.pool.add_term(Term::Sort(value.sort().clone())));
            let var_term = self.pool.add_term(var_term);
            substitutions.insert(var_term.clone(), value.clone());

            let new_value = self
                .pool
                .apply_substitutions(value, &substitutions_until_fixed_point);
            substitutions_until_fixed_point.insert(var_term, new_value);
        }

        // Some rules (notably "refl") need to apply the substitutions introduced by all the
        // previous contexts instead of just the current one. Instead of doing this iteratively
        // everytime the rule is used, we precompute the cumulative substitutions of this context
        // and all the previous ones and store that in a hash map. This improves the performance of
        // these rules considerably
        let mut cumulative_substitutions = substitutions_until_fixed_point.clone();
        if let Some(previous_context) = self.context.last() {
            for (k, v) in previous_context.cumulative_substitutions.iter() {
                let value = match substitutions_until_fixed_point.get(v) {
                    Some(new_value) => new_value,
                    None => v,
                };
                cumulative_substitutions.insert(k.clone(), value.clone());
            }
        }

        let bindings = variable_args.iter().cloned().collect();
        Context {
            substitutions,
            substitutions_until_fixed_point,
            cumulative_substitutions,
            bindings,
        }
    }

    fn add_statistics_measurement(&mut self, step_index: &str, rule: &str, start_time: Instant) {
        if let Some(stats) = &mut self.config.statistics {
            let measurement = start_time.elapsed();
            let file_name = stats.file_name.to_string();
            let step_index = step_index.to_string();
            let rule = rule.to_string();
            let id = StepId {
                file: file_name.clone().into_boxed_str(),
                step_index: step_index.into_boxed_str(),
                rule: rule.clone().into_boxed_str(),
            };
            stats.step_time.add(&id, measurement);
            stats
                .step_time_by_file
                .entry(file_name)
                .or_default()
                .add(&id, measurement);
            stats
                .step_time_by_rule
                .entry(rule)
                .or_default()
                .add(&id, measurement);
            *stats.checking_time += measurement;
        }
    }

    pub fn get_rule(rule_name: &str) -> Option<Rule> {
        use rules::*;

        // Converts a rule in the old format (returning `Option<()>`) to the new format (returning
        // `RuleResult`) by adding a `CheckerError::Unspecified` error
        macro_rules! to_new_format {
            ($old:expr) => {
                |args| $old(args).ok_or(CheckerError::Unspecified)
            };
        }

        Some(match rule_name {
            "true" => tautology::r#true,
            "false" => tautology::r#false,
            "not_not" => tautology::not_not,
            "and_pos" => tautology::and_pos,
            "and_neg" => tautology::and_neg,
            "or_pos" => tautology::or_pos,
            "or_neg" => tautology::or_neg,
            "xor_pos1" => tautology::xor_pos1,
            "xor_pos2" => tautology::xor_pos2,
            "xor_neg1" => tautology::xor_neg1,
            "xor_neg2" => tautology::xor_neg2,
            "implies_pos" => tautology::implies_pos,
            "implies_neg1" => tautology::implies_neg1,
            "implies_neg2" => tautology::implies_neg2,
            "equiv_pos1" => tautology::equiv_pos1,
            "equiv_pos2" => tautology::equiv_pos2,
            "equiv_neg1" => tautology::equiv_neg1,
            "equiv_neg2" => tautology::equiv_neg2,
            "ite_pos1" => tautology::ite_pos1,
            "ite_pos2" => tautology::ite_pos2,
            "ite_neg1" => tautology::ite_neg1,
            "ite_neg2" => tautology::ite_neg2,
            "eq_reflexive" => reflexivity::eq_reflexive,
            "eq_transitive" => transitivity::eq_transitive,
            "eq_congruent" => congruence::eq_congruent,
            "eq_congruent_pred" => congruence::eq_congruent_pred,
            "distinct_elim" => clausification::distinct_elim,
            "la_rw_eq" => linear_arithmetic::la_rw_eq,
            "la_generic" => linear_arithmetic::la_generic,
            "lia_generic" => linear_arithmetic::lia_generic,
            "la_disequality" => linear_arithmetic::la_disequality,
            "la_tautology" => linear_arithmetic::la_tautology,
            "forall_inst" => quantifier::forall_inst,
            "qnt_join" => quantifier::qnt_join,
            "qnt_rm_unused" => quantifier::qnt_rm_unused,
            "th_resolution" | "resolution" => resolution::resolution,
            "refl" => reflexivity::refl,
            "trans" => transitivity::trans,
            "cong" => congruence::cong,
            "and" => clausification::and,
            "tautology" => resolution::tautology,
            "not_or" => clausification::not_or,
            "or" => clausification::or,
            "not_and" => clausification::not_and,
            "implies" => clausification::implies,
            "not_implies1" => clausification::not_implies1,
            "not_implies2" => clausification::not_implies2,
            "equiv1" => tautology::equiv1,
            "equiv2" => tautology::equiv2,
            "not_equiv1" => tautology::not_equiv1,
            "not_equiv2" => tautology::not_equiv2,
            "ite1" => tautology::ite1,
            "ite2" => tautology::ite2,
            "not_ite1" => tautology::not_ite1,
            "not_ite2" => tautology::not_ite2,
            "ite_intro" => tautology::ite_intro,
            "contraction" => resolution::contraction,
            "connective_def" => tautology::connective_def,
            "ite_simplify" => simplification::ite_simplify,
            "eq_simplify" => simplification::eq_simplify,
            "and_simplify" => simplification::and_simplify,
            "or_simplify" => simplification::or_simplify,
            "not_simplify" => simplification::not_simplify,
            "implies_simplify" => simplification::implies_simplify,
            "equiv_simplify" => simplification::equiv_simplify,
            "bool_simplify" => simplification::bool_simplify,
            "qnt_simplify" => simplification::qnt_simplify,
            "div_simplify" => simplification::div_simplify,
            "prod_simplify" => simplification::prod_simplify,
            "minus_simplify" => simplification::minus_simplify,
            "sum_simplify" => simplification::sum_simplify,
            "comp_simplify" => simplification::comp_simplify,
            "nary_elim" => to_new_format!(clausification::nary_elim),
            "ac_simp" => simplification::ac_simp,
            "bfun_elim" => clausification::bfun_elim,
            "bind" => subproof::bind,
            "qnt_cnf" => quantifier::qnt_cnf,
            "subproof" => subproof::subproof,
            "let" => subproof::r#let,
            "onepoint" => subproof::onepoint,
            "sko_ex" => subproof::sko_ex,
            "sko_forall" => subproof::sko_forall,
            "reordering" => extras::reordering,
            "symm" => extras::symm,
            "not_symm" => extras::not_symm,

            // Special rule that always checks as valid. It is mostly used in tests
            "trust" => |_| Ok(()),

            _ => return None,
        })
    }
}
