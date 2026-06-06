//! The per-rule translation of CPC steps into Alethe steps, mirroring the `update()` method of
//! cvc5's `AletheProofPostprocessCallback`.

use super::{CpcTranslator, Info, ResPremise, Result, TranslationError};
use crate::ast::*;

impl CpcTranslator<'_> {
    pub(super) fn translate_step(&mut self, step: &ProofStep) -> Result<Info> {
        let id = step.id.clone();
        let rule = step.rule.as_str();
        let res = self.convert(&step.clause[0]);

        if rule == "process_scope" {
            return self.translate_process_scope(step, res);
        }

        // RARE and theory rewrite rules are printed with their own names, which are hyphenated
        // (while CPC core rules use underscores)
        if rule.contains('-') {
            return self.translate_rewrite(step, res);
        }

        let premises = self.resolve_premises(step)?;
        let positions: Vec<_> = premises.iter().map(|p| p.position).collect();

        let info = match rule {
            //==================================================================================//
            // Rules following the singleton pattern, with a direct correspondence
            //==================================================================================//
            // `skolem_intro` equates a term to its purification skolem, whose conversion is the
            // term itself, so the converted conclusion is a reflexivity
            "refl" | "skolem_intro" | "encode_eq_intro" => {
                self.singleton(id, res, "refl", Vec::new(), Vec::new())
            }
            "evaluate" => self.singleton(id, res, "evaluate", Vec::new(), Vec::new()),
            "trans" => self.singleton(id, res, "trans", positions, Vec::new()),
            "symm" => {
                let alethe_rule = if res.remove_negation().is_some() {
                    "not_symm"
                } else {
                    "symm"
                };
                self.singleton(id, res, alethe_rule, positions, Vec::new())
            }
            "cong" | "nary_cong" | "pairwise_cong" => {
                if let Some((lhs, rhs)) = match_term!((= l r) = res) {
                    // The conversion may turn the conclusion into a reflexivity (e.g. when the
                    // two sides differ only in `@purify` terms, or in cvc5-internal distinctions
                    // that Carcara does not make), in which case a `refl` step suffices
                    if lhs == rhs {
                        return Ok(self.singleton(id, res, "refl", Vec::new(), Vec::new()));
                    }
                    // A congruence over binders becomes a `bind` subproof in Alethe, whose only
                    // step re-states the equality of the bodies from the original premise
                    if matches!(lhs.as_ref(), Term::Binder(..)) {
                        return self.push_bind_subproof(
                            id,
                            res,
                            "trans",
                            vec![premises[0].position],
                        );
                    }
                    // The conversion (in particular the beta-reduction of applications of
                    // defined functions) may change the structure of the terms in a way that no
                    // longer corresponds to a congruence, in which case we give up
                    if !Self::cong_premises_fit(lhs, rhs, &premises) {
                        log::warn!(
                            "conclusion of `cong` step is not a congruence after conversion, \
                            using `hole`"
                        );
                        return Ok(self.hole(step, res));
                    }
                }
                // Ignore the prefix of premises that are reflexivity steps. Note that we check
                // the unconverted conclusions, since the conversion may turn non-reflexive
                // equalities into reflexive ones (e.g. by eliminating `@purify` terms), and
                // those premises are still used
                let first_non_refl = premises
                    .iter()
                    .position(|p| {
                        match p.original.as_ref().and_then(|t| match_term!((= l r) = t)) {
                            Some((l, r)) => l != r,
                            None => true,
                        }
                    })
                    .unwrap_or(premises.len());
                self.singleton(id, res, "cong", positions[first_non_refl..].to_vec(), Vec::new())
            }
            "ho_cong" => {
                let compatible = match match_term!((= l r) = res) {
                    Some((l, r)) => {
                        matches!(l.as_ref(), Term::App(..)) && matches!(r.as_ref(), Term::App(..))
                    }
                    None => false,
                };
                if !compatible {
                    log::warn!(
                        "conclusion of `ho_cong` step is not a congruence after conversion, \
                        using `hole`"
                    );
                    return Ok(self.hole(step, res));
                }
                self.singleton(id, res, "ho_cong", positions, Vec::new())
            }
            "arith_poly_norm" => self.singleton(id, res, "poly_simp", Vec::new(), Vec::new()),
            "arith_poly_norm_rel" => self.singleton(id, res, "poly_simp_rel", positions, Vec::new()),
            "aci_norm" => self.singleton(id, res, "aci_simp", Vec::new(), Vec::new()),
            "and_elim" => {
                let args = self.convert_args(&step.args);
                self.singleton(id, res, "and", positions, args)
            }
            "and_intro" => self.singleton(id, res, "and_intro", positions, Vec::new()),
            "not_or_elim" => {
                let args = self.convert_args(&step.args);
                self.singleton(id, res, "not_or", positions, args)
            }
            "not_implies_elim1" => self.singleton(id, res, "not_implies1", positions, Vec::new()),
            "not_implies_elim2" => self.singleton(id, res, "not_implies2", positions, Vec::new()),
            "arith_mult_pos" => self.singleton(id, res, "la_mult_pos", positions, Vec::new()),
            "arith_mult_neg" => self.singleton(id, res, "la_mult_neg", positions, Vec::new()),
            "arith_mult_sign" => self.singleton(id, res, "la_mult_sign", Vec::new(), Vec::new()),
            "arith_mult_abs_comparison" => {
                self.singleton(id, res, "la_mult_abs_comparison", positions, Vec::new())
            }
            "arrays_read_over_write_1" => {
                self.singleton(id, res, "arrays_idx", Vec::new(), Vec::new())
            }
            "arrays_read_over_write" => {
                self.singleton(id, res, "arrays_row", positions, Vec::new())
            }
            "arrays_read_over_write_contra" => {
                self.singleton(id, res, "arrays_row_contra", positions, Vec::new())
            }
            "arrays_ext" => self.singleton(id, res, "arrays_ext", positions, Vec::new()),

            //==================================================================================//
            // Rules following the clause pattern, with a direct correspondence
            //==================================================================================//
            "implies_elim" => self.clause(id, res, "implies", positions, Vec::new()),
            "equiv_elim1" => self.clause(id, res, "equiv1", positions, Vec::new()),
            "equiv_elim2" => self.clause(id, res, "equiv2", positions, Vec::new()),
            "not_equiv_elim1" => self.clause(id, res, "not_equiv1", positions, Vec::new()),
            "not_equiv_elim2" => self.clause(id, res, "not_equiv2", positions, Vec::new()),
            "xor_elim1" => self.clause(id, res, "xor1", positions, Vec::new()),
            "xor_elim2" => self.clause(id, res, "xor2", positions, Vec::new()),
            "not_xor_elim1" => self.clause(id, res, "not_xor1", positions, Vec::new()),
            "not_xor_elim2" => self.clause(id, res, "not_xor2", positions, Vec::new()),
            // Note that `ite_elim1` maps to `ite2` and vice-versa, and similarly for the others
            "ite_elim1" => self.clause(id, res, "ite2", positions, Vec::new()),
            "ite_elim2" => self.clause(id, res, "ite1", positions, Vec::new()),
            "not_ite_elim1" => self.clause(id, res, "not_ite2", positions, Vec::new()),
            "not_ite_elim2" => self.clause(id, res, "not_ite1", positions, Vec::new()),
            "not_and" => self.clause(id, res, "not_and", positions, Vec::new()),

            //==================================================================================//
            // CNF rules, all following the clause pattern
            //==================================================================================//
            "cnf_and_pos" => {
                let args = self.last_arg_if_integer(&step.args);
                self.clause(id, res, "and_pos", positions, args)
            }
            "cnf_and_neg" => self.clause(id, res, "and_neg", positions, Vec::new()),
            "cnf_or_pos" => self.clause(id, res, "or_pos", positions, Vec::new()),
            "cnf_or_neg" => {
                let args = self.last_arg_if_integer(&step.args);
                self.clause(id, res, "or_neg", positions, args)
            }
            "cnf_implies_pos" => self.clause(id, res, "implies_pos", positions, Vec::new()),
            "cnf_implies_neg1" => self.clause(id, res, "implies_neg1", positions, Vec::new()),
            "cnf_implies_neg2" => self.clause(id, res, "implies_neg2", positions, Vec::new()),
            // Note the swaps: `cnf_equiv_pos1` maps to `equiv_pos2`, etc.
            "cnf_equiv_pos1" => self.clause(id, res, "equiv_pos2", positions, Vec::new()),
            "cnf_equiv_pos2" => self.clause(id, res, "equiv_pos1", positions, Vec::new()),
            "cnf_equiv_neg1" => self.clause(id, res, "equiv_neg2", positions, Vec::new()),
            "cnf_equiv_neg2" => self.clause(id, res, "equiv_neg1", positions, Vec::new()),
            "cnf_xor_pos1" => self.clause(id, res, "xor_pos1", positions, Vec::new()),
            "cnf_xor_pos2" => self.clause(id, res, "xor_pos2", positions, Vec::new()),
            "cnf_xor_neg1" => self.clause(id, res, "xor_neg2", positions, Vec::new()),
            "cnf_xor_neg2" => self.clause(id, res, "xor_neg1", positions, Vec::new()),
            "cnf_ite_pos1" => self.clause(id, res, "ite_pos2", positions, Vec::new()),
            "cnf_ite_pos2" => self.clause(id, res, "ite_pos1", positions, Vec::new()),
            "cnf_ite_neg1" => self.clause(id, res, "ite_neg2", positions, Vec::new()),
            "cnf_ite_neg2" => self.clause(id, res, "ite_neg1", positions, Vec::new()),
            "cnf_ite_pos3" => self.translate_cnf_ite3(&id, res, true)?,
            "cnf_ite_neg3" => self.translate_cnf_ite3(&id, res, false)?,

            //==================================================================================//
            // Resolution and other clause-manipulation rules
            //==================================================================================//
            "resolution" | "chain_resolution" | "chain_m_resolution" => {
                self.translate_resolution(step, res, premises)?
            }
            "factoring" => {
                // If the premise is `(or t1 ... tn)` and the conclusion is one of the `ti`s
                // repeated, the conclusion is a singleton
                let premise = &premises[0];
                let is_clause = premise
                    .term
                    .as_ref()
                    .and_then(Self::or_elements_owned)
                    .is_some_and(|elements| elements.iter().any(|e| *e != res));
                let position = self.fix_clause_premise(&id, &premises[0].clone().into());
                if is_clause {
                    self.clause(id, res, "contraction", vec![position], Vec::new())
                } else {
                    self.singleton(id, res, "contraction", vec![position], Vec::new())
                }
            }
            "reordering" => {
                let position = self.fix_clause_premise(&id, &premises[0].clone().into());
                self.clause(id, res, "reordering", vec![position], Vec::new())
            }
            "contra" => {
                let position = self.push_step(id, Vec::new(), "resolution", positions, Vec::new());
                Info {
                    position,
                    clause: Vec::new(),
                    term: Some(res),
                    original: None,
                }
            }

            //==================================================================================//
            // Rules requiring multi-step expansions
            //==================================================================================//
            "eq_resolve" => self.translate_eq_resolve(step, res, premises)?,
            "modus_ponens" => {
                // (P2: (=> F1 F2)) yields (cl (not F1) F2) via `implies`, which is resolved
                // with (P1: F1)
                let f1 = self.premise_term(&premises[0], &id)?;
                let not_f1 = self.negate(&f1);
                let aux = self.aux_id(&id);
                let vp1 = self.push_step(
                    aux,
                    vec![not_f1, res.clone()],
                    "implies",
                    vec![premises[1].position],
                    Vec::new(),
                );
                self.singleton(
                    id,
                    res,
                    "resolution",
                    vec![vp1, premises[0].position],
                    Vec::new(),
                )
            }
            "not_not_elim" => {
                // P: (not (not F)) is resolved with (cl (not (not (not F))) F)
                let p = self.premise_term(&premises[0], &id)?;
                let not_p = self.negate(&p);
                let aux = self.aux_id(&id);
                let vp1 = self.push_step(
                    aux,
                    vec![not_p, res.clone()],
                    "not_not",
                    Vec::new(),
                    Vec::new(),
                );
                self.singleton(
                    id,
                    res,
                    "resolution",
                    vec![vp1, premises[0].position],
                    Vec::new(),
                )
            }
            "split" => {
                // (cl (not (not (not F))) F) and (cl (not (not (not (not F)))) (not F)), resolved
                let f = self.convert(&step.args[0]);
                let not1 = self.negate(&f);
                let not2 = self.negate(&not1);
                let not3 = self.negate(&not2);
                let not4 = self.negate(&not3);
                let aux = self.aux_id(&id);
                let vp1 = self.push_step(
                    aux,
                    vec![not3, f.clone()],
                    "not_not",
                    Vec::new(),
                    Vec::new(),
                );
                let aux = self.aux_id(&id);
                let vp2 = self.push_step(
                    aux,
                    vec![not4, not1],
                    "not_not",
                    Vec::new(),
                    Vec::new(),
                );
                self.clause(id, res, "resolution", vec![vp1, vp2], Vec::new())
            }
            "true_intro" => {
                // res = (= F true), P: F
                let f = self.premise_term(&premises[0], &id)?;
                let eq = self.build_op(Operator::Equals, vec![res.clone(), f.clone()]);
                let aux = self.aux_id(&id);
                let vp1 = self.push_step(
                    aux,
                    vec![eq],
                    "equiv_simplify",
                    Vec::new(),
                    Vec::new(),
                );
                let not_f = self.negate(&f);
                let aux = self.aux_id(&id);
                let vp2 = self.push_step(
                    aux,
                    vec![res.clone(), not_f],
                    "equiv2",
                    vec![vp1],
                    Vec::new(),
                );
                self.singleton(
                    id,
                    res,
                    "resolution",
                    vec![vp2, premises[0].position],
                    Vec::new(),
                )
            }
            "true_elim" => {
                // res = F, P: (= F true)
                let p = self.premise_term(&premises[0], &id)?;
                let eq = self.build_op(Operator::Equals, vec![p.clone(), res.clone()]);
                let aux = self.aux_id(&id);
                let vp1 = self.push_step(
                    aux,
                    vec![eq],
                    "equiv_simplify",
                    Vec::new(),
                    Vec::new(),
                );
                let not_p = self.negate(&p);
                let aux = self.aux_id(&id);
                let vp2 = self.push_step(
                    aux,
                    vec![not_p, res.clone()],
                    "equiv1",
                    vec![vp1],
                    Vec::new(),
                );
                self.singleton(
                    id,
                    res,
                    "resolution",
                    vec![vp2, premises[0].position],
                    Vec::new(),
                )
            }
            "false_intro" => {
                // res = (= F false), P: (not F)
                let p = self.premise_term(&premises[0], &id)?;
                let f = p
                    .remove_negation()
                    .ok_or_else(|| TranslationError::InvalidStep {
                        id: id.clone(),
                        rule: rule.to_owned(),
                        reason: "premise must be a negation".to_owned(),
                    })?
                    .clone();
                let eq = self.build_op(Operator::Equals, vec![res.clone(), p.clone()]);
                let aux = self.aux_id(&id);
                let vp1 = self.push_step(
                    aux,
                    vec![eq],
                    "equiv_simplify",
                    Vec::new(),
                    Vec::new(),
                );
                let not_p = self.negate(&p);
                let aux = self.aux_id(&id);
                let vp2 = self.push_step(
                    aux,
                    vec![res.clone(), not_p.clone()],
                    "equiv2",
                    vec![vp1],
                    Vec::new(),
                );
                let not_not_not_f = self.negate(&not_p);
                let aux = self.aux_id(&id);
                let vp3 = self.push_step(
                    aux,
                    vec![not_not_not_f, f.clone()],
                    "not_not",
                    Vec::new(),
                    Vec::new(),
                );
                let aux = self.aux_id(&id);
                let vp4 = self.push_step(
                    aux,
                    vec![res.clone(), f],
                    "resolution",
                    vec![vp2, vp3],
                    Vec::new(),
                );
                self.singleton(
                    id,
                    res,
                    "resolution",
                    vec![vp4, premises[0].position],
                    Vec::new(),
                )
            }
            "false_elim" => {
                // res = (not F), P: (= F false)
                let p = self.premise_term(&premises[0], &id)?;
                let eq = self.build_op(Operator::Equals, vec![p.clone(), res.clone()]);
                let aux = self.aux_id(&id);
                let vp1 = self.push_step(
                    aux,
                    vec![eq],
                    "equiv_simplify",
                    Vec::new(),
                    Vec::new(),
                );
                let not_p = self.negate(&p);
                let aux = self.aux_id(&id);
                let vp2 = self.push_step(
                    aux,
                    vec![not_p, res.clone()],
                    "equiv1",
                    vec![vp1],
                    Vec::new(),
                );
                self.singleton(
                    id,
                    res,
                    "resolution",
                    vec![vp2, premises[0].position],
                    Vec::new(),
                )
            }

            //==================================================================================//
            // Quantifier rules
            //==================================================================================//
            "instantiate" => {
                // P: (forall ...), res = the instantiated formula
                let forall_term = self.premise_term(&premises[0], &id)?;
                let not_forall = self.negate(&forall_term);
                let or_term =
                    self.build_op(Operator::Or, vec![not_forall.clone(), res.clone()]);
                let inst_args = Self::list_elements(&step.args[0])
                    .iter()
                    .map(|t| self.convert(t))
                    .collect();
                let aux = self.aux_id(&id);
                let vp1 = self.push_step(
                    aux,
                    vec![or_term],
                    "forall_inst",
                    Vec::new(),
                    inst_args,
                );
                let aux = self.aux_id(&id);
                let vp2 = self.push_step(
                    aux,
                    vec![not_forall, res.clone()],
                    "or",
                    vec![vp1],
                    Vec::new(),
                );
                self.singleton(
                    id,
                    res,
                    "resolution",
                    vec![vp2, premises[0].position],
                    Vec::new(),
                )
            }
            "quant_var_reordering" => self.translate_quant_var_reordering(&id, res)?,
            "skolemize" => self.translate_skolemize(step, res, &premises)?,
            "ite_eq" => {
                // res = (ite C (= (ite C t1 t2) t1) (= (ite C t1 t2) t2)), justified via the
                // RARE rewrite `ite-eq` equating it to `true`
                let Term::Op(Operator::Ite, ite_args) = res.as_ref() else {
                    return Err(TranslationError::InvalidStep {
                        id,
                        rule: rule.to_owned(),
                        reason: "conclusion must be an ite term".to_owned(),
                    });
                };
                let (condition, then_eq) = (ite_args[0].clone(), ite_args[1].clone());
                let Some((ite_term, _)) = match_term!((= i t) = then_eq) else {
                    return Err(TranslationError::InvalidStep {
                        id,
                        rule: rule.to_owned(),
                        reason: "branches must be equalities over the ite term".to_owned(),
                    });
                };
                let Term::Op(Operator::Ite, inner_args) = ite_term.as_ref() else {
                    return Err(TranslationError::InvalidStep {
                        id,
                        rule: rule.to_owned(),
                        reason: "branches must be equalities over the ite term".to_owned(),
                    });
                };
                let (t1, t2) = (inner_args[1].clone(), inner_args[2].clone());

                let true_node = self.pool.bool_true();
                let rule_name = self.new_string("ite-eq");
                let vp1_term =
                    self.build_op(Operator::Equals, vec![res.clone(), true_node.clone()]);
                let aux = self.aux_id(&id);
                let vp1 = self.push_step(
                    aux,
                    vec![vp1_term],
                    "rare_rewrite",
                    Vec::new(),
                    vec![rule_name, condition, t1, t2],
                );
                let not_true = self.negate(&true_node);
                let aux = self.aux_id(&id);
                let vp2 = self.push_step(
                    aux,
                    vec![res.clone(), not_true],
                    "equiv2",
                    vec![vp1],
                    Vec::new(),
                );
                let aux = self.aux_id(&id);
                let true_step =
                    self.push_step(aux, vec![true_node], "true", Vec::new(), Vec::new());
                self.singleton(id, res, "resolution", vec![vp2, true_step], Vec::new())
            }
            "arith_trichotomy" => self.translate_arith_trichotomy(step, res, &premises)?,
            "absorb" => self.translate_absorb(step, res)?,
            "arith_reduction" => self.translate_arith_reduction(step, res)?,
            "alpha_equiv" => {
                // res = (= (forall X F) (forall Y F*sigma)). If the variables are unchanged,
                // this is a reflexivity. Otherwise, it becomes a `bind` subproof whose only step
                // is a reflexivity between the bodies, checked under the renaming context.
                let invalid = |reason: &str| TranslationError::InvalidStep {
                    id: id.clone(),
                    rule: "alpha_equiv".to_owned(),
                    reason: reason.to_owned(),
                };
                let Some((lhs, rhs)) = match_term!((= l r) = res) else {
                    return Err(invalid("conclusion must be an equality"));
                };
                let (Term::Binder(_, x_bindings, _), Term::Binder(_, y_bindings, _)) =
                    (lhs.as_ref(), rhs.as_ref())
                else {
                    return Err(invalid("conclusion must equate two binder terms"));
                };
                if x_bindings == y_bindings {
                    self.singleton(id, res, "refl", Vec::new(), Vec::new())
                } else {
                    // If a variable name in the right-hand side clashes with one in the
                    // left-hand side, we first rename the left-hand side variables to fresh
                    // ones, with two `bind` subproofs connected by a transitivity step
                    let clash = y_bindings.iter().any(|(y_name, _)| {
                        x_bindings.iter().any(|(x_name, _)| x_name == y_name)
                    });
                    if clash {
                        let (Term::Binder(binder, x_bindings, body), _) =
                            (lhs.as_ref(), rhs.as_ref())
                        else {
                            unreachable!()
                        };

                        // Build the left-hand side with fresh variables
                        let fresh_bindings: Vec<SortedVar> = x_bindings
                            .iter()
                            .map(|(_, sort)| (self.fresh_var_name(), sort.clone()))
                            .collect();
                        let mut map = indexmap::IndexMap::new();
                        for (x_var, fresh_var) in
                            x_bindings.iter().zip(fresh_bindings.iter())
                        {
                            let x_term = self.pool.add(x_var.clone().into());
                            let fresh_term = self.pool.add(fresh_var.clone().into());
                            map.insert(x_term, fresh_term);
                        }
                        let renamed_body = Substitution::new(self.pool, map)
                            .map_err(|_| TranslationError::InvalidStep {
                                id: id.clone(),
                                rule: "alpha_equiv".to_owned(),
                                reason: "could not rename variables".to_owned(),
                            })?
                            .apply(self.pool, body);
                        let lhs_renamed = self.pool.add(Term::Binder(
                            *binder,
                            BindingList(fresh_bindings),
                            renamed_body,
                        ));

                        let eq1 = self
                            .build_op(Operator::Equals, vec![lhs.clone(), lhs_renamed.clone()]);
                        let aux = self.aux_id(&id);
                        let first = self.push_bind_subproof(aux, eq1, "refl", Vec::new())?;

                        let eq2 = self.build_op(Operator::Equals, vec![lhs_renamed, rhs.clone()]);
                        let aux = self.aux_id(&id);
                        let second = self.push_bind_subproof(aux, eq2, "refl", Vec::new())?;

                        self.singleton(
                            id,
                            res,
                            "trans",
                            vec![first.position, second.position],
                            Vec::new(),
                        )
                    } else {
                        return self.push_bind_subproof(id, res, "refl", Vec::new());
                    }
                }
            }

            //==================================================================================//
            // Arithmetic rules
            //==================================================================================//
            "arith_sum_ub" => {
                // An `la_generic` step concluding (cl (not P1) ... (not Pn) (>< t1 t2)), resolved
                // with the premises
                let one = self.pool.add(Term::new_real(1));
                let minus_one = self.pool.add(Term::new_real(-1));
                let mut lits = Vec::new();
                let mut la_args = Vec::new();
                for premise in &premises {
                    let term = self.premise_term(premise, &id)?;
                    lits.push(self.negate(&term));
                    // equalities are multiplied by -1 rather than 1
                    let coefficient = if match_term!((= a b) = term).is_some() {
                        minus_one.clone()
                    } else {
                        one.clone()
                    };
                    la_args.push(coefficient);
                }
                lits.push(res.clone());
                la_args.push(one);
                let aux = self.aux_id(&id);
                let la_generic = self.push_step(aux, lits, "la_generic", Vec::new(), la_args);
                let mut res_premises = vec![la_generic];
                res_premises.extend(positions);
                self.singleton(id, res, "resolution", res_premises, Vec::new())
            }
            "int_tight_ub" | "int_tight_lb" => {
                // (cl (not P) res) by `la_generic`, resolved with the premise
                let p = self.premise_term(&premises[0], &id)?;
                let not_p = self.negate(&p);
                let one = self.pool.add(Term::new_real(1));
                let aux = self.aux_id(&id);
                let vp1 = self.push_step(
                    aux,
                    vec![not_p, res.clone()],
                    "la_generic",
                    Vec::new(),
                    vec![one.clone(), one],
                );
                self.singleton(
                    id,
                    res,
                    "resolution",
                    vec![vp1, premises[0].position],
                    Vec::new(),
                )
            }

            //==================================================================================//
            // Trusted steps and unsupported rules
            //==================================================================================//
            "trust" | "trust_theory_rewrite" => self.hole(step, res),
            _ => {
                log::warn!("CPC rule '{}' is not yet translated, using `hole`", rule);
                self.hole(step, res)
            }
        };
        Ok(info)
    }

    //==============================================================================================//
    // Helpers
    //==============================================================================================//

    /// Resolves the premises of a CPC step into their translation data.
    fn resolve_premises(&mut self, step: &ProofStep) -> Result<Vec<ResPremise>> {
        step.premises
            .iter()
            .map(|&premise| {
                let info = self.premise_info(premise, &step.id)?;
                Ok(ResPremise {
                    position: info.position,
                    clause: info.clause,
                    term: info.term,
                    original: info.original,
                })
            })
            .collect()
    }

    /// The (converted) CPC conclusion of a premise.
    #[allow(clippy::unused_self)]
    fn premise_term(&self, premise: &ResPremise, id: &str) -> Result<Rc<Term>> {
        premise
            .term
            .clone()
            .ok_or_else(|| TranslationError::UntranslatedPremise(id.to_owned()))
    }

    /// Adds a step following the singleton pattern, concluding `(cl res)`.
    fn singleton(
        &mut self,
        id: String,
        res: Rc<Term>,
        rule: &str,
        premises: Vec<(usize, usize)>,
        args: Vec<Rc<Term>>,
    ) -> Info {
        let position = self.push_step(id, vec![res.clone()], rule, premises, args);
        Info {
            position,
            clause: vec![res.clone()],
            term: Some(res),
            original: None,
        }
    }

    /// Adds a step following the clause pattern: if `res` is `(or t1 ... tn)`, the conclusion is
    /// `(cl t1 ... tn)`; otherwise it is `(cl res)`.
    fn clause(
        &mut self,
        id: String,
        res: Rc<Term>,
        rule: &str,
        premises: Vec<(usize, usize)>,
        args: Vec<Rc<Term>>,
    ) -> Info {
        let clause = Self::clause_from_or(&res);
        let position = self.push_step(id, clause.clone(), rule, premises, args);
        Info {
            position,
            clause,
            term: Some(res),
            original: None,
        }
    }

    /// Adds a `hole` step for a rule that cannot be translated, including the original rule name
    /// as a string argument.
    fn hole(&mut self, step: &ProofStep, res: Rc<Term>) -> Info {
        let name = self.new_string(&step.rule);
        let position = self.push_step(
            step.id.clone(),
            vec![res.clone()],
            "hole",
            Vec::new(),
            vec![name],
        );
        Info {
            position,
            clause: vec![res.clone()],
            term: Some(res),
            original: None,
        }
    }

    fn convert_args(&mut self, args: &[Rc<Term>]) -> Vec<Rc<Term>> {
        args.iter().map(|arg| self.convert(arg)).collect()
    }

    /// Returns the last argument, if it is an integer constant. Used for rules whose Alethe
    /// counterpart takes the term index as an argument.
    #[allow(clippy::unused_self)]
    fn last_arg_if_integer(&mut self, args: &[Rc<Term>]) -> Vec<Rc<Term>> {
        args.last()
            .filter(|arg| arg.as_integer().is_some())
            .map(|arg| vec![arg.clone()])
            .unwrap_or_default()
    }

    /// Checks that the equality between `lhs` and `rhs` can be justified as a congruence with
    /// the given premises: the two terms must be applications of the same function or operator,
    /// and each differing pair of arguments must be justified, in order, by a premise (in either
    /// direction).
    fn cong_premises_fit(lhs: &Rc<Term>, rhs: &Rc<Term>, premises: &[ResPremise]) -> bool {
        let (l_args, r_args) = match (lhs.as_ref(), rhs.as_ref()) {
            (Term::App(f, l_args), Term::App(g, r_args)) if f == g => (l_args, r_args),
            (Term::Op(f, l_args), Term::Op(g, r_args)) if f == g => (l_args, r_args),
            _ => return false,
        };
        if l_args.len() != r_args.len() {
            return false;
        }
        let mut premises = premises.iter();
        for (a, b) in l_args.iter().zip(r_args.iter()) {
            if a == b {
                continue;
            }
            // Find the next premise that justifies this pair. Premises whose conclusions became
            // reflexivities after conversion may be skipped.
            loop {
                let Some(premise) = premises.next() else {
                    return false;
                };
                let Some(term) = &premise.term else {
                    return false;
                };
                let Some((x, y)) = match_term!((= x y) = term) else {
                    return false;
                };
                if (x == a && y == b) || (x == b && y == a) {
                    break;
                }
                if x != y {
                    return false;
                }
            }
        }
        true
    }

    fn or_elements_owned(term: &Rc<Term>) -> Option<Vec<Rc<Term>>> {
        Self::or_elements(term).map(<[Rc<Term>]>::to_vec)
    }

    /// Translates the `resolution`, `chain_resolution` and `chain_m_resolution` rules into an
    /// Alethe `resolution` step, possibly adding `or` steps for premises that were concluded as
    /// singletons but are used as clauses (and vice-versa).
    fn translate_resolution(
        &mut self,
        step: &ProofStep,
        res: Rc<Term>,
        premises: Vec<ResPremise>,
    ) -> Result<Info> {
        let id = &step.id;

        // Build the interleaved list of polarities and pivots `[pol1, piv1, pol2, piv2, ...]`
        let cargs: Vec<Rc<Term>> = match step.rule.as_str() {
            "resolution" => self.convert_args(&step.args),
            "chain_resolution" => {
                let pols = Self::list_elements(&step.args[0]).to_vec();
                let lits = Self::list_elements(&step.args[1]).to_vec();
                pols.iter()
                    .zip(lits.iter())
                    .flat_map(|(pol, lit)| [self.convert(pol), self.convert(lit)])
                    .collect()
            }
            "chain_m_resolution" => {
                let pols = Self::list_elements(&step.args[1]).to_vec();
                let lits = Self::list_elements(&step.args[2]).to_vec();
                pols.iter()
                    .zip(lits.iter())
                    .flat_map(|(pol, lit)| [self.convert(pol), self.convert(lit)])
                    .collect()
            }
            _ => unreachable!(),
        };
        if cargs.len() != 2 * (premises.len() - 1) {
            return Err(TranslationError::InvalidStep {
                id: id.clone(),
                rule: step.rule.clone(),
                reason: format!(
                    "expected {} polarity/pivot pairs, got {}",
                    premises.len() - 1,
                    cargs.len() / 2
                ),
            });
        }

        let children: Vec<_> = premises.iter().map(|p| p.term.clone()).collect();
        let is_singleton = self.is_singleton_clause(&res, &children, &cargs);
        let clause = if !is_singleton {
            Self::or_elements_owned(&res).unwrap()
        } else if res == self.pool.bool_false() {
            Vec::new()
        } else {
            vec![res.clone()]
        };

        let fixed = self.fix_resolution_premises(id, &premises, &cargs);
        let position = self.push_step(id.clone(), clause.clone(), "resolution", fixed, Vec::new());
        Ok(Info {
            position,
            clause,
            term: Some(res),
            original: None,
        })
    }

    /// Translates the `eq_resolve` rule: an `equiv_pos2` step resolved against the premises.
    fn translate_eq_resolve(
        &mut self,
        step: &ProofStep,
        res: Rc<Term>,
        premises: Vec<ResPremise>,
    ) -> Result<Info> {
        let id = &step.id;
        let f1 = self.premise_term(&premises[0], id)?;
        let eq = self.premise_term(&premises[1], id)?;
        let not_eq = self.negate(&eq);
        let not_f1 = self.negate(&f1);
        let aux = self.aux_id(id);
        let vp1 = self.push_step(
            aux,
            vec![not_eq, not_f1, res.clone()],
            "equiv_pos2",
            Vec::new(),
            Vec::new(),
        );

        // The resolution is treated like a `RESOLUTION_OR` step in cvc5, since the proof of the
        // premise `F1`, if it is an `or` term, may conclude either `(cl F1)` or the clause of its
        // elements
        let res_premises = vec![
            ResPremise {
                position: vp1,
                clause: Vec::new(),
                term: None,
                original: None,
            },
            premises[1].clone(),
            premises[0].clone(),
        ];
        let false_node = self.pool.bool_false();
        let cargs = vec![false_node.clone(), eq, false_node, f1];
        let fixed = self.fix_resolution_premises(id, &res_premises, &cargs);
        Ok(self.singleton(id.clone(), res, "resolution", fixed, Vec::new()))
    }

    /// Translates the `cnf_ite_pos3` and `cnf_ite_neg3` rules, which require resolving the
    /// versions 1 and 2 of the corresponding Alethe rules.
    fn translate_cnf_ite3(&mut self, id: &str, res: Rc<Term>, positive: bool) -> Result<Info> {
        let elements = Self::or_elements_owned(&res).ok_or_else(|| {
            TranslationError::InvalidStep {
                id: id.to_owned(),
                rule: if positive { "cnf_ite_pos3" } else { "cnf_ite_neg3" }.to_owned(),
                reason: "conclusion must be an `or` term".to_owned(),
            }
        })?;
        let [res0, res1, res2] = elements.as_slice() else {
            return Err(TranslationError::InvalidStep {
                id: id.to_owned(),
                rule: if positive { "cnf_ite_pos3" } else { "cnf_ite_neg3" }.to_owned(),
                reason: "conclusion must have three literals".to_owned(),
            });
        };
        let (res0, res1, res2) = (res0.clone(), res1.clone(), res2.clone());

        // The condition of the ite term, which appears negated in `res0` for the "pos" version
        let ite_term = if positive {
            res0.remove_negation()
                .ok_or_else(|| TranslationError::InvalidStep {
                    id: id.to_owned(),
                    rule: "cnf_ite_pos3".to_owned(),
                    reason: "first literal must be a negated ite term".to_owned(),
                })?
                .clone()
        } else {
            res0.clone()
        };
        let Term::Op(Operator::Ite, ite_args) = ite_term.as_ref() else {
            return Err(TranslationError::InvalidStep {
                id: id.to_owned(),
                rule: if positive { "cnf_ite_pos3" } else { "cnf_ite_neg3" }.to_owned(),
                reason: "expected an ite term".to_owned(),
            });
        };
        let condition = ite_args[0].clone();
        let not_condition = self.negate(&condition);

        let (rule1, rule2) = if positive {
            ("ite_pos1", "ite_pos2")
        } else {
            ("ite_neg1", "ite_neg2")
        };
        let aux = self.aux_id(id);
        let vp1 = self.push_step(
            aux,
            vec![res0.clone(), condition, res2.clone()],
            rule1,
            Vec::new(),
            Vec::new(),
        );
        let aux = self.aux_id(id);
        let vp2 = self.push_step(
            aux,
            vec![res0.clone(), not_condition, res1.clone()],
            rule2,
            Vec::new(),
            Vec::new(),
        );
        let aux = self.aux_id(id);
        let vp3 = self.push_step(
            aux,
            vec![res0.clone(), res2.clone(), res0.clone(), res1.clone()],
            "resolution",
            vec![vp1, vp2],
            Vec::new(),
        );
        let aux = self.aux_id(id);
        let vp4 = self.push_step(
            aux,
            vec![res0.clone(), res0, res1, res2],
            "reordering",
            vec![vp3],
            Vec::new(),
        );
        Ok(self.clause(id.to_owned(), res, "contraction", vec![vp4], Vec::new()))
    }

    /// Translates the `arith_trichotomy` rule, which concludes one of `(= x c)`, `(> x c)` or
    /// `(< x c)` from premises excluding the other two cases. The translation is based on the
    /// `la_disequality` rule, with `comp_simplify` steps connecting strict and non-strict
    /// inequalities.
    fn translate_arith_trichotomy(
        &mut self,
        step: &ProofStep,
        res: Rc<Term>,
        premises: &[ResPremise],
    ) -> Result<Info> {
        let id = step.id.clone();
        let invalid = |reason: &str| TranslationError::InvalidStep {
            id: id.clone(),
            rule: "arith_trichotomy".to_owned(),
            reason: reason.to_owned(),
        };
        if premises.len() != 2 {
            return Err(invalid("expected two premises"));
        }
        let p0 = self.premise_term(&premises[0], &id)?;
        let p1 = self.premise_term(&premises[1], &id)?;

        let Term::Op(op, res_args) = res.as_ref() else {
            return Err(invalid("conclusion must be a comparison"));
        };
        let (op, x, c) = (*op, res_args[0].clone(), res_args[1].clone());

        let is_op = |term: &Rc<Term>, op: Operator| matches!(term.as_ref(), Term::Op(o, _) if *o == op);

        // Builds PI_0: `(cl (= x c) (not (<= x c)) (not (<= c x)))`, via `la_disequality`
        let pi_0 = |translator: &mut Self,
                        eq: Rc<Term>,
                        leq: Rc<Term>,
                        leq_inverted: Rc<Term>|
         -> (usize, usize) {
            let not_leq = translator.negate(&leq);
            let not_leq_inverted = translator.negate(&leq_inverted);
            let or_term = translator.build_op(
                Operator::Or,
                vec![eq.clone(), not_leq.clone(), not_leq_inverted.clone()],
            );
            let aux = translator.aux_id(&id);
            let la_or =
                translator.push_step(aux, vec![or_term], "la_disequality", Vec::new(), Vec::new());
            let aux = translator.aux_id(&id);
            translator.push_step(
                aux,
                vec![eq, not_leq, not_leq_inverted],
                "or",
                vec![la_or],
                Vec::new(),
            )
        };

        match op {
            Operator::Equals => {
                let (leq_premise, geq_premise, leq, geq) = if is_op(&p0, Operator::LessEq) {
                    (&premises[0], &premises[1], p0, p1)
                } else {
                    (&premises[1], &premises[0], p1, p0)
                };
                let Term::Op(Operator::GreaterEq, geq_args) = geq.as_ref() else {
                    return Err(invalid("expected a `>=` premise"));
                };
                let leq_inverted = self.build_op(
                    Operator::LessEq,
                    vec![geq_args[1].clone(), geq_args[0].clone()],
                );

                let la_diseq = pi_0(self, res.clone(), leq.clone(), leq_inverted.clone());

                // PI_1: from the `>=` premise, conclude the inverted `<=`
                let comp_simp =
                    self.build_op(Operator::Equals, vec![geq.clone(), leq_inverted.clone()]);
                let aux = self.aux_id(&id);
                let cs = self.push_step(
                    aux,
                    vec![comp_simp.clone()],
                    "comp_simplify",
                    Vec::new(),
                    Vec::new(),
                );
                let not_comp_simp = self.negate(&comp_simp);
                let not_geq = self.negate(&geq);
                let aux = self.aux_id(&id);
                let ep2 = self.push_step(
                    aux,
                    vec![not_comp_simp, not_geq, leq_inverted.clone()],
                    "equiv_pos2",
                    Vec::new(),
                    Vec::new(),
                );
                let aux = self.aux_id(&id);
                let pi_1 = self.push_step(
                    aux,
                    vec![leq_inverted],
                    "resolution",
                    vec![cs, ep2, geq_premise.position],
                    Vec::new(),
                );

                let final_premises = vec![leq_premise.position, la_diseq, pi_1];
                Ok(self.singleton(id, res, "resolution", final_premises, Vec::new()))
            }
            Operator::GreaterThan => {
                let (geq_premise, not_eq_premise, geq, not_eq) = if is_op(&p1, Operator::GreaterEq)
                    || p1
                        .remove_negation()
                        .is_some_and(|t| is_op(t, Operator::LessThan))
                {
                    (&premises[1], &premises[0], p1, p0)
                } else {
                    (&premises[0], &premises[1], p0, p1)
                };
                let Some(eq) = not_eq.remove_negation().cloned() else {
                    return Err(invalid("expected a negated equality premise"));
                };
                let leq = self.build_op(Operator::LessEq, vec![x.clone(), c.clone()]);
                let leq_inverted = self.build_op(Operator::LessEq, vec![c.clone(), x.clone()]);

                // If the premise is `(not (< x c))` instead of `(>= x c)`, derive `(>= x c)`
                // from it first
                let (geq, geq_position) = if is_op(&geq, Operator::GreaterEq) {
                    (geq, geq_premise.position)
                } else {
                    let Some(pb) = geq.remove_negation().cloned() else {
                        return Err(invalid("expected a `>=` or `(not (< x c))` premise"));
                    };
                    let pc = leq_inverted.clone();
                    let not_pc = self.negate(&pc);
                    let pa = self.build_op(Operator::Equals, vec![pb.clone(), not_pc.clone()]);

                    // PI_a: conclude `(not (not pc))`
                    let aux = self.aux_id(&id);
                    let cs_a = self.push_step(
                        aux,
                        vec![pa.clone()],
                        "comp_simplify",
                        Vec::new(),
                        Vec::new(),
                    );
                    let not_pa = self.negate(&pa);
                    let not_not_pc = self.negate(&not_pc);
                    let aux = self.aux_id(&id);
                    let ep1_a = self.push_step(
                        aux,
                        vec![not_pa, pb, not_not_pc.clone()],
                        "equiv_pos1",
                        Vec::new(),
                        Vec::new(),
                    );
                    let aux = self.aux_id(&id);
                    let pi_a = self.push_step(
                        aux,
                        vec![not_not_pc.clone()],
                        "resolution",
                        vec![cs_a, ep1_a, geq_premise.position],
                        Vec::new(),
                    );

                    // PI_b: conclude `pc`
                    let not_not_not_pc = self.negate(&not_not_pc);
                    let aux = self.aux_id(&id);
                    let not_not = self.push_step(
                        aux,
                        vec![not_not_not_pc, pc.clone()],
                        "not_not",
                        Vec::new(),
                        Vec::new(),
                    );
                    let aux = self.aux_id(&id);
                    let pi_b = self.push_step(
                        aux,
                        vec![pc.clone()],
                        "resolution",
                        vec![not_not, pi_a],
                        Vec::new(),
                    );

                    // PI_c: conclude `(>= x c)`
                    let geq = self.build_op(Operator::GreaterEq, vec![x.clone(), c.clone()]);
                    let pd = self.build_op(Operator::Equals, vec![geq.clone(), pc.clone()]);
                    let aux = self.aux_id(&id);
                    let cs_c = self.push_step(
                        aux,
                        vec![pd.clone()],
                        "comp_simplify",
                        Vec::new(),
                        Vec::new(),
                    );
                    let not_pd = self.negate(&pd);
                    let not_pc = self.negate(&pc);
                    let aux = self.aux_id(&id);
                    let ep1_c = self.push_step(
                        aux,
                        vec![not_pd, geq.clone(), not_pc],
                        "equiv_pos1",
                        Vec::new(),
                        Vec::new(),
                    );
                    let aux = self.aux_id(&id);
                    let pi_c = self.push_step(
                        aux,
                        vec![geq.clone()],
                        "resolution",
                        vec![cs_c, ep1_c, pi_b],
                        Vec::new(),
                    );
                    (geq, pi_c)
                };

                let la_diseq = pi_0(self, eq, leq.clone(), leq_inverted.clone());

                // PI_1: from the `>=` premise, conclude the inverted `<=`
                let comp_simp =
                    self.build_op(Operator::Equals, vec![geq.clone(), leq_inverted.clone()]);
                let aux = self.aux_id(&id);
                let cs = self.push_step(
                    aux,
                    vec![comp_simp.clone()],
                    "comp_simplify",
                    Vec::new(),
                    Vec::new(),
                );
                let not_comp_simp = self.negate(&comp_simp);
                let not_geq = self.negate(&geq);
                let aux = self.aux_id(&id);
                let ep2 = self.push_step(
                    aux,
                    vec![not_comp_simp, not_geq, leq_inverted.clone()],
                    "equiv_pos2",
                    Vec::new(),
                    Vec::new(),
                );
                let aux = self.aux_id(&id);
                let pi_1 = self.push_step(
                    aux,
                    vec![leq_inverted],
                    "resolution",
                    vec![cs, ep2, geq_position],
                    Vec::new(),
                );

                // PI_2: `(cl (> x c) (not (not (<= x c))))`
                let not_leq = self.negate(&leq);
                let comp_simp_2 =
                    self.build_op(Operator::Equals, vec![res.clone(), not_leq.clone()]);
                let aux = self.aux_id(&id);
                let cs_2 = self.push_step(
                    aux,
                    vec![comp_simp_2.clone()],
                    "comp_simplify",
                    Vec::new(),
                    Vec::new(),
                );
                let not_comp_simp_2 = self.negate(&comp_simp_2);
                let not_not_leq = self.negate(&not_leq);
                let aux = self.aux_id(&id);
                let ep1 = self.push_step(
                    aux,
                    vec![not_comp_simp_2, res.clone(), not_not_leq.clone()],
                    "equiv_pos1",
                    Vec::new(),
                    Vec::new(),
                );
                let aux = self.aux_id(&id);
                let pi_2 = self.push_step(
                    aux,
                    vec![res.clone(), not_not_leq],
                    "resolution",
                    vec![cs_2, ep1],
                    Vec::new(),
                );

                let final_premises = vec![not_eq_premise.position, la_diseq, pi_1, pi_2];
                Ok(self.singleton(id, res, "resolution", final_premises, Vec::new()))
            }
            Operator::LessThan => {
                let (leq_premise, not_eq_premise, leq, not_eq) = if is_op(&p0, Operator::LessEq) {
                    (&premises[0], &premises[1], p0, p1)
                } else {
                    (&premises[1], &premises[0], p1, p0)
                };
                if !is_op(&leq, Operator::LessEq) {
                    return Err(invalid("expected a `<=` premise"));
                }
                let Some(eq) = not_eq.remove_negation().cloned() else {
                    return Err(invalid("expected a negated equality premise"));
                };
                let leq_inverted = self.build_op(Operator::LessEq, vec![c.clone(), x.clone()]);

                let la_diseq = pi_0(self, eq, leq.clone(), leq_inverted.clone());

                // PI_3: `(cl (< x c) (not (not (<= c x))))`
                let not_leq_inverted = self.negate(&leq_inverted);
                let comp_simp =
                    self.build_op(Operator::Equals, vec![res.clone(), not_leq_inverted.clone()]);
                let aux = self.aux_id(&id);
                let cs = self.push_step(
                    aux,
                    vec![comp_simp.clone()],
                    "comp_simplify",
                    Vec::new(),
                    Vec::new(),
                );
                let not_comp_simp = self.negate(&comp_simp);
                let not_not_leq_inverted = self.negate(&not_leq_inverted);
                let aux = self.aux_id(&id);
                let ep1 = self.push_step(
                    aux,
                    vec![not_comp_simp, res.clone(), not_not_leq_inverted],
                    "equiv_pos1",
                    Vec::new(),
                    Vec::new(),
                );

                let final_premises = vec![
                    la_diseq,
                    not_eq_premise.position,
                    leq_premise.position,
                    ep1,
                    cs,
                ];
                Ok(self.singleton(id, res, "resolution", final_premises, Vec::new()))
            }
            _ => Err(invalid("conclusion must be `=`, `>` or `<`")),
        }
    }

    /// Translates the `absorb` rule, which concludes `(= t z)` where `z` is the absorbing
    /// element (`true` for `or`, `false` for `and`) occurring in `t`. The term is first
    /// flattened with `ac_simp`, and then simplified to the constant with `or_simplify` or
    /// `and_simplify`.
    fn translate_absorb(&mut self, step: &ProofStep, res: Rc<Term>) -> Result<Info> {
        use crate::checker::rules::simplification::apply_ac_simp;

        let id = step.id.clone();
        let Some((t, z)) = match_term!((= t z) = res) else {
            return Err(TranslationError::InvalidStep {
                id,
                rule: "absorb".to_owned(),
                reason: "conclusion must be an equality".to_owned(),
            });
        };
        let (t, z) = (t.clone(), z.clone());
        let tf = apply_ac_simp(self.pool, &mut indexmap::IndexMap::new(), &t);

        // If the flattening does not result in a term that directly simplifies to the absorbing
        // constant, give up and use a hole
        let ok = match (t.as_ref(), tf.as_ref()) {
            (Term::Op(op @ (Operator::Or | Operator::And), _), Term::Op(tf_op, tf_args)) => {
                op == tf_op && tf_args.contains(&z)
            }
            _ => false,
        };
        if !ok {
            log::warn!("`absorb` step could not be translated, using `hole`");
            return Ok(self.hole(step, res));
        }
        let simplify_rule = match t.as_ref() {
            Term::Op(Operator::Or, _) => "or_simplify",
            _ => "and_simplify",
        };

        let vp1_term = self.build_op(Operator::Equals, vec![t, tf.clone()]);
        let aux = self.aux_id(&id);
        let vp1 = self.push_step(aux, vec![vp1_term], "ac_simp", Vec::new(), Vec::new());

        let vp2_term = self.build_op(Operator::Equals, vec![tf, z]);
        let aux = self.aux_id(&id);
        let vp2 = self.push_step(aux, vec![vp2_term], simplify_rule, Vec::new(), Vec::new());

        Ok(self.singleton(id, res, "trans", vec![vp1, vp2], Vec::new()))
    }

    /// Translates the `arith_reduction` rule, which concludes a conjunction of an equality
    /// between an arithmetic operator application and another term, and an instantiation of the
    /// axiom defining the operator.
    #[allow(clippy::unnecessary_wraps)]
    fn translate_arith_reduction(&mut self, step: &ProofStep, res: Rc<Term>) -> Result<Info> {
        let id = step.id.clone();
        let op_term = self.convert(&step.args[0]);

        // The conclusion is usually a conjunction of the operator equality and the axiom
        // instantiation, but depending on the operator it may be only the equality
        let (op_eq, op_intro) = match res.as_ref() {
            Term::Op(Operator::And, parts) if parts.len() == 2 => {
                (parts[0].clone(), Some(parts[1].clone()))
            }
            Term::Op(Operator::Equals, _) => (res.clone(), None),
            _ => {
                log::warn!("unsupported `arith_reduction` conclusion, using `hole`");
                return Ok(self.hole(step, res));
            }
        };

        // The equality and intro steps depend on the operator being reduced
        let (eq_steps, intro_rule): (Vec<(&str, Vec<Rc<Term>>)>, &str) = match op_term.as_ref() {
            Term::Op(Operator::RealDiv | Operator::IntDiv, _) => {
                // div is equated to itself
                (vec![("refl", Vec::new())], "div_intro")
            }
            Term::Op(Operator::Mod, args) => {
                // mod is equated to its definition via the `mod-elim` RARE rewrite
                if match_term!((= m (- a (* b (div c d)))) = op_eq).is_none() {
                    log::warn!("unsupported `arith_reduction` equality, using `hole`");
                    return Ok(self.hole(step, res));
                }
                let rule_name = self.new_string("mod-elim");
                (
                    vec![("rare_rewrite", vec![rule_name, args[0].clone(), args[1].clone()])],
                    "div_intro",
                )
            }
            Term::Op(Operator::ToInt, _) => (vec![("refl", Vec::new())], "to_int_intro"),
            Term::Op(Operator::IsInt, args) => {
                let rule_name = self.new_string("is_int-elim");
                (
                    vec![("rare_rewrite", vec![rule_name, args[0].clone()])],
                    "to_int_intro",
                )
            }
            Term::Op(Operator::Log2, _) => (vec![("refl", Vec::new())], "log2_intro"),
            Term::Op(Operator::Abs, args) => {
                // abs is equated to its definition via a RARE rewrite, with no axiom
                // instantiation
                let arg = args[0].clone();
                let is_int = self.pool.sort(&arg).as_sort() == Some(&Sort::Int);
                let rule_name =
                    self.new_string(if is_int { "abs-elim-int" } else { "abs-elim-real" });
                return Ok(self.singleton(
                    id,
                    res,
                    "rare_rewrite",
                    Vec::new(),
                    vec![rule_name, arg],
                ));
            }
            _ => {
                log::warn!(
                    "unsupported operator in `arith_reduction` step, using `hole`: {}",
                    op_term
                );
                return Ok(self.hole(step, res));
            }
        };

        let (eq_rule, eq_args) = eq_steps.into_iter().next().unwrap();

        // Make sure the steps we will produce are valid: a `refl` step requires the equality to
        // be between identical terms, and Carcara's `div_intro` rule only supports the axiom for
        // constant divisors
        if eq_rule == "refl"
            && match_term!((= l r) = op_eq).is_none_or(|(l, r)| l != r)
        {
            log::warn!("unsupported `arith_reduction` equality, using `hole`");
            return Ok(self.hole(step, res));
        }
        if let Some(op_intro) = &op_intro {
            let constant_divisor_form = match_term!(
                (and (<= (* b1 (div a1 b2)) a2) (< a3 (* b3 (+ (div a4 b4) c)))) = op_intro
            )
            .is_some();
            let guarded_form = match_term!(
                (and
                    (=> (> b1 z1) (and (<= (* b2 (div a1 b3)) a2) (< a3 (* b4 (+ (div a4 b5) c1)))))
                    (=> (< b6 z2) (and (<= (* b7 (div a5 b8)) a6) (< a7 (* b9 (+ (div a8 b10) c2))))))
                    = op_intro
            )
            .is_some();
            if intro_rule == "div_intro" && !constant_divisor_form && !guarded_form {
                log::warn!("unsupported `arith_reduction` axiom, using `hole`");
                return Ok(self.hole(step, res));
            }
        }

        let Some(op_intro) = op_intro else {
            // If the conclusion is only the operator equality, the single step suffices
            return Ok(self.singleton(id, res, eq_rule, Vec::new(), eq_args));
        };
        let aux = self.aux_id(&id);
        let eq_position = self.push_step(aux, vec![op_eq], eq_rule, Vec::new(), eq_args);
        let aux = self.aux_id(&id);
        let intro_position = self.push_step(aux, vec![op_intro], intro_rule, Vec::new(), Vec::new());

        Ok(self.singleton(
            id,
            res,
            "and_intro",
            vec![eq_position, intro_position],
            Vec::new(),
        ))
    }

    /// Translates the `skolemize` rule, which from a premise `(not (forall X F))` concludes
    /// `(not F*sigma)`, where `sigma` replaces each bound variable by its skolem (which the term
    /// conversion turns into a choice term). The translation builds a `sko_forall` subproof
    /// concluding `(= (forall X F) F*sigma)`, wraps it in a `cong` step for the negations, and
    /// resolves with the premise via `equiv_pos2`.
    fn translate_skolemize(
        &mut self,
        step: &ProofStep,
        res: Rc<Term>,
        premises: &[ResPremise],
    ) -> Result<Info> {
        let id = step.id.clone();
        let invalid = |reason: &str| TranslationError::InvalidStep {
            id: id.clone(),
            rule: "skolemize".to_owned(),
            reason: reason.to_owned(),
        };
        let premise = premises.first().ok_or_else(|| invalid("expected a premise"))?;
        let premise_term = self.premise_term(premise, &id)?;
        let Some(quant) = premise_term.remove_negation().cloned() else {
            return Err(invalid("premise must be a negated quantifier"));
        };
        let Term::Binder(Binder::Forall, bindings, body) = quant.as_ref() else {
            return Err(invalid("premise must be a negated `forall`"));
        };
        let (bindings, body) = (bindings.clone(), body.clone());
        let Some(skolemized) = res.remove_negation().cloned() else {
            return Err(invalid("conclusion must be a negation"));
        };

        // The anchor assigns each bound variable to its choice term
        let mut anchor_args = Vec::new();
        for (i, var) in bindings.0.iter().enumerate() {
            let Some(choice) = self.quantifiers_skolemize_choice(&quant, i) else {
                return Err(invalid("could not build the choice term for a variable"));
            };
            anchor_args.push(AnchorArg::Assign(var.clone(), choice));
        }

        // The `sko_forall` subproof concluding `(= (forall X F) F*sigma)`
        self.out.push(Vec::new());
        let refl_term = self.build_op(Operator::Equals, vec![body, skolemized.clone()]);
        let aux = self.aux_id(&id);
        self.push_step(aux, vec![refl_term], "refl", Vec::new(), Vec::new());
        let sko_term = self.build_op(Operator::Equals, vec![quant.clone(), skolemized]);
        let aux = self.aux_id(&id);
        self.push_step(aux, vec![sko_term], "sko_forall", Vec::new(), Vec::new());

        let commands = self.out.pop().unwrap();
        let context_id = self.next_context_id;
        self.next_context_id += 1;
        let sko_position = self.push_command(ProofCommand::Subproof(Subproof {
            commands,
            args: anchor_args,
            context_id,
        }));

        // `(= (not (forall X F)) (not F*sigma))` by congruence
        let cong_term =
            self.build_op(Operator::Equals, vec![premise_term.clone(), res.clone()]);
        let aux = self.aux_id(&id);
        let cong = self.push_step(
            aux,
            vec![cong_term.clone()],
            "cong",
            vec![sko_position],
            Vec::new(),
        );

        // Eliminate the equality to obtain the conclusion from the premise
        let not_cong_term = self.negate(&cong_term);
        let not_premise_term = self.negate(&premise_term);
        let aux = self.aux_id(&id);
        let vp1 = self.push_step(
            aux,
            vec![not_cong_term, not_premise_term, res.clone()],
            "equiv_pos2",
            Vec::new(),
            Vec::new(),
        );
        Ok(self.singleton(
            id,
            res,
            "resolution",
            vec![vp1, cong, premise.position],
            Vec::new(),
        ))
    }

    /// Translates the `quant_var_reordering` rule via two `qnt_rm_unused` steps over the
    /// quantifier with the concatenated variable lists.
    fn translate_quant_var_reordering(&mut self, id: &str, res: Rc<Term>) -> Result<Info> {
        let Some((forall_x, forall_y)) = match_term!((= l r) = res) else {
            return Err(TranslationError::InvalidStep {
                id: id.to_owned(),
                rule: "quant_var_reordering".to_owned(),
                reason: "conclusion must be an equality".to_owned(),
            });
        };
        let (Term::Binder(Binder::Forall, x, body), Term::Binder(Binder::Forall, y, _)) =
            (forall_x.as_ref(), forall_y.as_ref())
        else {
            return Err(TranslationError::InvalidStep {
                id: id.to_owned(),
                rule: "quant_var_reordering".to_owned(),
                reason: "conclusion must equate two quantifiers".to_owned(),
            });
        };
        let mut z = x.0.clone();
        for var in &y.0 {
            if !z.contains(var) {
                z.push(var.clone());
            }
        }
        let forall_z = self
            .pool
            .add(Term::Binder(Binder::Forall, BindingList(z), body.clone()));

        let vp1_term = self.build_op(
            Operator::Equals,
            vec![forall_z.clone(), forall_x.clone()],
        );
        let aux = self.aux_id(id);
        let vp1 = self.push_step(aux, vec![vp1_term], "qnt_rm_unused", Vec::new(), Vec::new());

        let vp2_term = self.build_op(
            Operator::Equals,
            vec![forall_x.clone(), forall_z.clone()],
        );
        let aux = self.aux_id(id);
        let vp2 = self.push_step(aux, vec![vp2_term], "symm", vec![vp1], Vec::new());

        let vp3_term = self.build_op(Operator::Equals, vec![forall_z, forall_y.clone()]);
        let aux = self.aux_id(id);
        let vp3 = self.push_step(aux, vec![vp3_term], "qnt_rm_unused", Vec::new(), Vec::new());

        Ok(self.singleton(id.to_owned(), res, "trans", vec![vp2, vp3], Vec::new()))
    }

    /// Translates RARE rewrites and theory rewrites, which are printed with their (hyphenated)
    /// names in CPC proofs. Most become `rare_rewrite` steps, while a few theory rewrites have
    /// special translations.
    fn translate_rewrite(&mut self, step: &ProofStep, res: Rc<Term>) -> Result<Info> {
        let id = step.id.clone();
        let info = match step.rule.as_str() {
            "exists-elim" => self.singleton(id, res, "connective_def", Vec::new(), Vec::new()),
            "quant-unused-vars" => self.singleton(id, res, "qnt_rm_unused", Vec::new(), Vec::new()),
            "beta-reduce" => {
                // The parser beta-reduces applications of lambda terms eagerly, so the
                // conclusion may have become a reflexivity
                let alethe_rule = match match_term!((= l r) = res) {
                    Some((l, r)) if l == r => "refl",
                    _ => "beta_equiv",
                };
                self.singleton(id, res, alethe_rule, Vec::new(), Vec::new())
            }
            "distinct-elim" | "distinct-card-conflict" => {
                self.singleton(id, res, "distinct_elim", Vec::new(), Vec::new())
            }
            "distinct-true" => self.singleton(id, res, "evaluate", Vec::new(), Vec::new()),
            "distinct-false" => return self.translate_distinct_false(step, res),
            "quant-var-elim-eq" => return self.translate_quant_var_elim_eq(step, res),
            "quant-merge-prenex" | "macro-quant-merge-prenex" => {
                return self.translate_quant_merge_prenex(step, res)
            }
            "quant-miniscope-and" => {
                self.singleton(id, res, "miniscope_distribute", Vec::new(), Vec::new())
            }
            "quant-miniscope-or" => {
                self.singleton(id, res, "miniscope_split", Vec::new(), Vec::new())
            }
            "quant-miniscope-ite" => {
                self.singleton(id, res, "miniscope_ite", Vec::new(), Vec::new())
            }
            _ => {
                // A `rare_rewrite` step whose first argument is the rule name, followed by the
                // rule arguments. Note that some RARE rules have premises.
                let premises = self.resolve_premises(step)?;
                let positions = premises.iter().map(|p| p.position).collect();
                let mut args = vec![self.new_string(&step.rule)];
                for (i, arg) in step.args.iter().enumerate() {
                    let converted = self.convert(arg);
                    args.push(self.listify_rewrite_arg(&step.rule, i, converted));
                }
                self.singleton(id, res, "rare_rewrite", positions, args)
            }
        };
        Ok(info)
    }
}

impl CpcTranslator<'_> {
    /// Converts the `i`-th argument of a RARE rewrite step into the form expected by Carcara's
    /// `rare_rewrite` checker. Arguments for `:list` parameters are printed in CPC proofs as
    /// applications of the corresponding n-ary operator (including its neutral element as a
    /// terminator, which by itself denotes the empty list), and must be wrapped in `rare-list`
    /// terms so that they are correctly spliced when instantiating the rule.
    fn listify_rewrite_arg(&mut self, rule: &str, i: usize, arg: Rc<Term>) -> Rc<Term> {
        let Some(definition) = self.rules.rules.get(rule) else {
            return arg;
        };
        let is_list = definition
            .arguments
            .get(i)
            .and_then(|name| definition.parameters.get(name))
            .is_some_and(|p| p.attribute == rare_rules::AttributeParameters::List);
        if !is_list {
            return arg;
        }
        match arg.as_ref() {
            // Already a list
            Term::Op(Operator::RareList, _) => arg,
            // The neutral element of the n-ary operator denotes the empty list
            Term::Op(Operator::True | Operator::False, _) => {
                self.build_op(Operator::RareList, Vec::new())
            }
            // An n-ary operator application: wrap its arguments
            Term::Op(
                Operator::And | Operator::Or | Operator::Add | Operator::Mult,
                elements,
            ) => self.build_op(Operator::RareList, elements.clone()),
            // A single element
            _ => self.build_op(Operator::RareList, vec![arg]),
        }
    }

    /// Translates the `distinct-false` theory rewrite, which concludes
    /// `(= (distinct t1 ... tn) false)` when some element is repeated. The arguments to the RARE
    /// rule are the repeated term and the lists of elements before, between, and after its two
    /// occurrences.
    fn translate_distinct_false(&mut self, step: &ProofStep, res: Rc<Term>) -> Result<Info> {
        let id = step.id.clone();
        let invalid = |reason: &str| TranslationError::InvalidStep {
            id: id.clone(),
            rule: "distinct-false".to_owned(),
            reason: reason.to_owned(),
        };
        let Some((lhs, _)) = match_term!((= l r) = res) else {
            return Err(invalid("conclusion must be an equality"));
        };
        let Term::Op(Operator::Distinct, elements) = lhs.as_ref() else {
            return Err(invalid("left-hand side must be a `distinct` term"));
        };

        // Find the first repeated term and split the elements around its two occurrences
        let mut prefix: Vec<Rc<Term>> = Vec::new();
        let mut repeated = None;
        let mut second_occurrence = 0;
        'outer: for (i, element) in elements.iter().enumerate() {
            for previous in &elements[..i] {
                if previous == element {
                    repeated = Some(element.clone());
                    second_occurrence = i;
                    break 'outer;
                }
            }
            prefix.push(element.clone());
        }
        let Some(repeated) = repeated else {
            return Err(invalid("no repeated element found"));
        };
        let first_occurrence = prefix.iter().position(|e| *e == repeated).unwrap();
        let before = elements[..first_occurrence].to_vec();
        let between = elements[first_occurrence + 1..second_occurrence].to_vec();
        let after = elements[second_occurrence + 1..].to_vec();

        let mut args = vec![self.new_string("distinct-false"), repeated];
        for list in [before, between, after] {
            args.push(self.build_op(Operator::RareList, list));
        }
        Ok(self.singleton(id, res, "rare_rewrite", Vec::new(), args))
    }

    /// Translates the `quant-merge-prenex` theory rewrite, which merges nested quantifiers of
    /// the same kind into a single one (also removing duplicate variables). The Alethe `qnt_join`
    /// rule merges two quantifiers at a time, so a step is added for each nesting level, followed
    /// by a transitivity step and, if there were duplicate variables, a `qnt_rm_unused` step.
    fn translate_quant_merge_prenex(&mut self, step: &ProofStep, res: Rc<Term>) -> Result<Info> {
        let id = step.id.clone();
        let invalid = |reason: &str| TranslationError::InvalidStep {
            id: id.clone(),
            rule: step.rule.clone(),
            reason: reason.to_owned(),
        };
        let Some((lhs, _)) = match_term!((= l r) = res) else {
            return Err(invalid("conclusion must be an equality"));
        };
        let Term::Binder(binder, lhs_bindings, _) = lhs.as_ref() else {
            return Err(invalid("left-hand side must be a quantifier"));
        };
        let binder = *binder;

        let mut vars: Vec<SortedVar> = Vec::new();
        for var in &lhs_bindings.0 {
            if !vars.contains(var) {
                vars.push(var.clone());
            }
        }

        let mut current = lhs.clone();
        let mut trans_eqs: Vec<((usize, usize), Rc<Term>)> = Vec::new();
        loop {
            let Term::Binder(_, _, body) = current.as_ref() else {
                unreachable!()
            };
            let Term::Binder(inner_binder, inner_bindings, inner_body) = body.as_ref() else {
                break;
            };
            if *inner_binder != binder {
                break;
            }
            for var in &inner_bindings.0 {
                if !vars.contains(var) {
                    vars.push(var.clone());
                }
            }
            let joined = self.pool.add(Term::Binder(
                binder,
                BindingList(vars.clone()),
                inner_body.clone(),
            ));
            let eq = self.build_op(Operator::Equals, vec![current.clone(), joined.clone()]);
            let aux = self.aux_id(&id);
            let position = self.push_step(aux, vec![eq.clone()], "qnt_join", Vec::new(), Vec::new());
            trans_eqs.push((position, eq));
            current = joined;
        }

        // No joining happened, so this is just an application of `qnt_rm_unused`
        if trans_eqs.is_empty() {
            return Ok(self.singleton(id, res, "qnt_rm_unused", Vec::new(), Vec::new()));
        }

        let (mut current_position, mut current_eq) = trans_eqs.last().unwrap().clone();
        if trans_eqs.len() > 1 {
            current_eq = self.build_op(Operator::Equals, vec![lhs.clone(), current.clone()]);
            let aux = self.aux_id(&id);
            current_position = self.push_step(
                aux,
                vec![current_eq.clone()],
                "trans",
                trans_eqs.iter().map(|(position, _)| *position).collect(),
                Vec::new(),
            );
        }

        // If there were duplicate variables, the merged quantifier differs from the expected
        // right-hand side, and we connect them with a `qnt_rm_unused` step
        if current_eq != res {
            let Some((_, rhs)) = match_term!((= l r) = res) else {
                unreachable!()
            };
            let rm_unused_term = self.build_op(Operator::Equals, vec![rhs.clone(), current.clone()]);
            let aux = self.aux_id(&id);
            let rm_unused = self.push_step(
                aux,
                vec![rm_unused_term],
                "qnt_rm_unused",
                Vec::new(),
                Vec::new(),
            );
            let symm_term = self.build_op(Operator::Equals, vec![current, rhs.clone()]);
            let aux = self.aux_id(&id);
            let symm = self.push_step(aux, vec![symm_term], "symm", vec![rm_unused], Vec::new());
            return Ok(self.singleton(
                id,
                res,
                "trans",
                vec![current_position, symm],
                Vec::new(),
            ));
        }
        Ok(Info {
            position: current_position,
            clause: vec![res.clone()],
            term: Some(res),
            original: None,
        })
    }

    /// Translates the `quant-var-elim-eq` theory rewrite, which concludes
    /// `(= (forall ((x T)) (or (not (= x t)) F1 ... Fn)) (or F1 ... Fn){x -> t})` (where the
    /// `or`s may be absent if `n` is 0 or 1). The translation builds an `onepoint` subproof
    /// whose body equates the quantifier body with the result via the `or-not-refl` (or
    /// `bool-not-eq-false`) RARE rewrite.
    fn translate_quant_var_elim_eq(&mut self, step: &ProofStep, res: Rc<Term>) -> Result<Info> {
        let id = step.id.clone();
        let invalid = |reason: &str| TranslationError::InvalidStep {
            id: id.clone(),
            rule: "quant-var-elim-eq".to_owned(),
            reason: reason.to_owned(),
        };
        let Some((lhs, rhs)) = match_term!((= l r) = res) else {
            return Err(invalid("conclusion must be an equality"));
        };
        let Term::Binder(Binder::Forall, bindings, body) = lhs.as_ref() else {
            return Err(invalid("left-hand side must be a `forall` term"));
        };
        let [(x_name, x_sort)] = bindings.0.as_slice() else {
            return Err(invalid("quantifier must bind exactly one variable"));
        };

        // The equality `(= x t)`, negated in the body (or in its first disjunct)
        let sub_eq = match body.as_ref() {
            Term::Op(Operator::Or, disjuncts) => disjuncts[0].remove_negation(),
            _ => body.remove_negation(),
        };
        let Some(sub_eq) = sub_eq else {
            return Err(invalid("body must contain a negated equality"));
        };
        let Some((_, t)) = match_term!((= x t) = sub_eq) else {
            return Err(invalid("body must contain a negated equality"));
        };
        let t = t.clone();

        // Build the intermediate term `(or (not (= t t)) (F1 ... Fn){x -> t})` (or just
        // `(not (= t t))` when there are no further disjuncts), and the RARE rewrite that
        // simplifies it to the right-hand side
        let t_eq_t = self.build_op(Operator::Equals, vec![t.clone(), t.clone()]);
        let not_t_eq_t = self.negate(&t_eq_t);
        let (refl_rhs, rw_args) = if let Term::Op(Operator::Or, disjuncts) = body.as_ref() {
            let mut new_disjuncts = vec![not_t_eq_t];
            let rest: Vec<_> = if disjuncts.len() > 2 {
                match rhs.as_ref() {
                    Term::Op(Operator::Or, rhs_disjuncts) => rhs_disjuncts.clone(),
                    _ => return Err(invalid("right-hand side must be an `or` term")),
                }
            } else {
                vec![rhs.clone()]
            };
            new_disjuncts.extend(rest.clone());
            let rule_name = self.new_string("or-not-refl");
            let list = self.build_op(Operator::RareList, rest);
            (
                self.build_op(Operator::Or, new_disjuncts),
                vec![rule_name, t.clone(), list],
            )
        } else {
            let rule_name = self.new_string("bool-not-eq-false");
            (not_t_eq_t, vec![rule_name, t.clone()])
        };

        // Build the `onepoint` subproof. Note that the anchor's variable arguments must be the
        // bindings remaining in the right-hand side, which here are none.
        let anchor_args = vec![AnchorArg::Assign((x_name.clone(), x_sort.clone()), t)];
        self.out.push(Vec::new());

        let refl_term = self.build_op(Operator::Equals, vec![body.clone(), refl_rhs.clone()]);
        let aux = self.aux_id(&id);
        let refl = self.push_step(aux, vec![refl_term], "refl", Vec::new(), Vec::new());

        let rw_term = self.build_op(Operator::Equals, vec![refl_rhs, rhs.clone()]);
        let aux = self.aux_id(&id);
        let rw = self.push_step(aux, vec![rw_term], "rare_rewrite", Vec::new(), rw_args);

        let trans_term = self.build_op(Operator::Equals, vec![body.clone(), rhs.clone()]);
        let aux = self.aux_id(&id);
        self.push_step(aux, vec![trans_term], "trans", vec![refl, rw], Vec::new());

        self.push_step(id, vec![res.clone()], "onepoint", Vec::new(), Vec::new());

        let commands = self.out.pop().unwrap();
        let context_id = self.next_context_id;
        self.next_context_id += 1;
        let position = self.push_command(ProofCommand::Subproof(Subproof {
            commands,
            args: anchor_args,
            context_id,
        }));
        Ok(Info {
            position,
            clause: vec![res.clone()],
            term: Some(res),
            original: None,
        })
    }
}

impl From<ResPremise> for Info {
    fn from(premise: ResPremise) -> Self {
        Info {
            position: premise.position,
            clause: premise.clause,
            term: premise.term,
            original: premise.original,
        }
    }
}
