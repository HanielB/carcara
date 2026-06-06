//! Translation of CPC proofs into Alethe proofs.
//!
//! This module translates a parsed CPC proof (see `parser::cpc`) into an Alethe proof that can be
//! checked by the Alethe checker. The translation mirrors the one implemented in cvc5 itself for
//! its Alethe proof output (see cvc5's `src/proof/alethe/alethe_post_processor.cpp`), since the
//! proof rules appearing in CPC proofs are (a subset of) cvc5's internal proof rules.
//!
//! The two main concerns of the translation are:
//!
//! - Conclusions: CPC steps conclude single formulas, while Alethe steps conclude clauses. A
//!   formula `F` may be translated to the singleton clause `(cl F)`, and a formula
//!   `(or F1 ... Fn)` may be translated either to `(cl F1 ... Fn)` or to the singleton
//!   `(cl (or F1 ... Fn))`, depending on the rule that concludes it and on how it is used. When a
//!   step is concluded as a singleton `(cl (or ...))` but used as a clause (or vice-versa), extra
//!   steps are added to convert between the two.
//!
//! - Rule mapping: each CPC rule is mapped to one or more Alethe steps. Some have a direct
//!   correspondence (e.g. `trans`), while others must be expanded into several steps (e.g.
//!   `eq_resolve` becomes an `equiv_pos2` step followed by a `resolution` step).
//!
//! Subproofs in the CPC proof (from `assume-push`/`step-pop` chains) are translated into Alethe
//! subproofs: a chain of nested single-assumption CPC subproofs (which the cvc5 printer produces
//! for a single internal `SCOPE` step) becomes one Alethe subproof with all the assumptions,
//! ending in a `subproof` step. The `process_scope` step that follows the chain is translated
//! into the steps deriving the implication (or negation) concluded by the original `SCOPE`.

mod rules;

use crate::{
    ast::{rare_rules::Rules, *},
    CarcaraResult,
};
use std::collections::HashMap;
use thiserror::Error;

/// The errors that can occur while translating a CPC proof.
#[derive(Debug, Error)]
pub enum TranslationError {
    #[error("step '{0}' references a command that could not be translated")]
    UntranslatedPremise(String),

    #[error("invalid application of rule '{rule}' in step '{id}': {reason}")]
    InvalidStep {
        id: String,
        rule: String,
        reason: String,
    },

    #[error("subproof '{0}' is not in the expected form for a CPC scope")]
    MalformedScope(String),
}

type Result<T> = std::result::Result<T, TranslationError>;

/// Translates a CPC proof into an Alethe proof. The resulting proof can be checked with the
/// regular Alethe checker. The RARE rules are used to translate the arguments of rewrite steps.
pub fn cpc_to_alethe(
    proof: &Proof,
    pool: &mut PrimitivePool,
    rules: &Rules,
) -> CarcaraResult<Proof> {
    let mut translator = CpcTranslator::new(pool, rules);
    let commands = translator.translate_proof(&proof.commands)?;
    Ok(Proof {
        constant_definitions: proof.constant_definitions.clone(),
        commands,
    })
}

/// The translation data for a single translated CPC command: the position of the final Alethe
/// step corresponding to it, the Alethe clause it concludes, and the original CPC conclusion,
/// both converted and unconverted. Subproofs have no CPC conclusion term.
#[derive(Debug, Clone)]
struct Info {
    position: (usize, usize),
    clause: Vec<Rc<Term>>,
    term: Option<Rc<Term>>,
    original: Option<Rc<Term>>,
}

/// The translation data for an open CPC subproof frame.
struct CpcFrame {
    /// The translation data for each command in the original CPC frame, in order. `None` is used
    /// for commands that have no corresponding Alethe step (e.g. the intermediate `step-pop`s of
    /// a collapsed scope chain).
    infos: Vec<Option<Info>>,
}

/// A premise of an internal resolution step.
#[derive(Debug, Clone)]
struct ResPremise {
    position: (usize, usize),
    clause: Vec<Rc<Term>>,
    /// The original (converted) CPC conclusion of the premise, if it corresponds to a CPC
    /// command. Auxiliary steps added during translation don't have one.
    term: Option<Rc<Term>>,
    /// The original unconverted CPC conclusion of the premise.
    original: Option<Rc<Term>>,
}

struct CpcTranslator<'a> {
    pool: &'a mut PrimitivePool,

    /// The RARE rules, used to determine which arguments of rewrite steps are lists.
    rules: &'a Rules,

    /// The stack of Alethe command lists being built. `out[d]` is the subproof currently open at
    /// depth `d`, with `out[0]` being the root proof.
    out: Vec<Vec<ProofCommand>>,

    /// The stack of open CPC frames, holding the translation data of their commands. Note that
    /// this stack may be larger than `out`, since the frames of a collapsed scope chain all
    /// correspond to the same Alethe subproof.
    cpc_frames: Vec<CpcFrame>,

    /// For collapsed scope subproofs, maps the position of the resulting `subproof` step to the
    /// (converted) assumptions and conclusion of the scope, used by `process_scope`.
    scope_data: HashMap<(usize, usize), (Vec<Rc<Term>>, Rc<Term>)>,

    /// Memoization cache for `convert`.
    cache: HashMap<Rc<Term>, Rc<Term>>,

    next_context_id: usize,
    next_aux_id: usize,
}

impl<'a> CpcTranslator<'a> {
    fn new(pool: &'a mut PrimitivePool, rules: &'a Rules) -> Self {
        Self {
            pool,
            rules,
            out: Vec::new(),
            cpc_frames: Vec::new(),
            scope_data: HashMap::new(),
            cache: HashMap::new(),
            next_context_id: 0,
            next_aux_id: 0,
        }
    }

    fn translate_proof(&mut self, commands: &[ProofCommand]) -> Result<Vec<ProofCommand>> {
        self.out.push(Vec::new());
        self.cpc_frames.push(CpcFrame { infos: Vec::new() });
        self.translate_commands(commands)?;
        self.ensure_final_step();
        self.cpc_frames.pop();
        Ok(self.out.pop().unwrap())
    }

    fn translate_commands(&mut self, commands: &[ProofCommand]) -> Result<()> {
        for command in commands {
            match command {
                ProofCommand::Assume { id, term } => {
                    let original = term.clone();
                    let term = self.convert(term);
                    let position = self.push_command(ProofCommand::Assume {
                        id: id.clone(),
                        term: term.clone(),
                    });
                    self.push_info(Some(Info {
                        position,
                        clause: vec![term.clone()],
                        term: Some(term),
                        original: Some(original),
                    }));
                }
                ProofCommand::Step(step) => {
                    let mut info = self.translate_step(step)?;
                    info.original = Some(step.clause[0].clone());
                    self.push_info(Some(info));
                }
                ProofCommand::Subproof(subproof) => {
                    let info = self.translate_scope_subproof(subproof)?;
                    self.push_info(Some(info));
                }
            }
        }
        Ok(())
    }

    //==========================================================================================//
    // Bookkeeping helpers
    //==========================================================================================//

    /// Pushes an Alethe command into the current output frame, returning its position.
    fn push_command(&mut self, command: ProofCommand) -> (usize, usize) {
        let depth = self.out.len() - 1;
        let frame = self.out.last_mut().unwrap();
        frame.push(command);
        (depth, frame.len() - 1)
    }

    /// Pushes an Alethe step into the current output frame, returning its position.
    fn push_step(
        &mut self,
        id: String,
        clause: Vec<Rc<Term>>,
        rule: &str,
        premises: Vec<(usize, usize)>,
        args: Vec<Rc<Term>>,
    ) -> (usize, usize) {
        self.push_command(ProofCommand::Step(ProofStep {
            id,
            clause,
            rule: rule.to_owned(),
            premises,
            args,
            discharge: Vec::new(),
        }))
    }

    /// Records the translation data for the next command of the current CPC frame.
    fn push_info(&mut self, info: Option<Info>) {
        self.cpc_frames.last_mut().unwrap().infos.push(info);
    }

    /// Retrieves the translation data for the CPC command referenced by a premise.
    fn premise_info(&self, (depth, index): (usize, usize), id: &str) -> Result<Info> {
        self.cpc_frames
            .get(depth)
            .and_then(|frame| frame.infos.get(index))
            .and_then(Clone::clone)
            .ok_or_else(|| TranslationError::UntranslatedPremise(id.to_owned()))
    }

    /// Generates a fresh id for an auxiliary step, based on the id of the step being translated.
    fn aux_id(&mut self, base: &str) -> String {
        self.next_aux_id += 1;
        format!("{}.t{}", base, self.next_aux_id)
    }

    //==========================================================================================//
    // Term conversion and construction
    //==========================================================================================//

    /// Converts a term from its CPC representation into its Alethe representation. Currently this
    /// eliminates applications of the `@purify` skolem, which stand for the term they purify.
    fn convert(&mut self, term: &Rc<Term>) -> Rc<Term> {
        if let Some(cached) = self.cache.get(term) {
            return cached.clone();
        }
        let result = match term.as_ref() {
            Term::App(func, args) => {
                if let Term::Var(name, _) = func.as_ref() {
                    if name == "@purify" {
                        let result = self.convert(&args[0]);
                        self.cache.insert(term.clone(), result.clone());
                        return result;
                    }
                    // The array diff skolem is converted to the corresponding choice term:
                    // `(choice ((x I)) (or (= a b) (not (= (select a x) (select b x)))))`
                    if name == "@array_deq_diff" {
                        let a = self.convert(&args[0]);
                        let b = self.convert(&args[1]);
                        let result = self.build_array_deq_diff_choice(&a, &b);
                        self.cache.insert(term.clone(), result.clone());
                        return result;
                    }
                }
                let func = self.convert(func);
                let args = args.iter().map(|arg| self.convert(arg)).collect();
                self.pool.add(Term::App(func, args))
            }
            Term::Op(op, args) => {
                let args = args.iter().map(|arg| self.convert(arg)).collect();
                self.pool.add(Term::Op(*op, args))
            }
            Term::Binder(binder, bindings, body) => {
                let body = self.convert(body);
                self.pool.add(Term::Binder(*binder, bindings.clone(), body))
            }
            Term::Let(bindings, body) => {
                let body = self.convert(body);
                self.pool.add(Term::Let(bindings.clone(), body))
            }
            Term::ParamOp { op, op_args, args } => {
                let args = args.iter().map(|arg| self.convert(arg)).collect();
                self.pool.add(Term::ParamOp {
                    op: *op,
                    op_args: op_args.clone(),
                    args,
                })
            }
            _ => term.clone(),
        };
        self.cache.insert(term.clone(), result.clone());
        result
    }

    /// Builds the choice term corresponding to the array diff skolem `(@array_deq_diff a b)`:
    /// `(choice ((x I)) (or (= a b) (not (= (select a x) (select b x)))))`, where `I` is the
    /// index sort of the arrays.
    fn build_array_deq_diff_choice(&mut self, a: &Rc<Term>, b: &Rc<Term>) -> Rc<Term> {
        let array_sort = self.pool.sort(a);
        let index_sort = match array_sort.as_sort() {
            Some(Sort::Array(index_sort, _)) => index_sort.clone(),
            _ => return a.clone(), // should not happen; leave the term untouched
        };
        let x = self.pool.add(Term::new_var("x", index_sort.clone()));
        let eq = self.build_op(Operator::Equals, vec![a.clone(), b.clone()]);
        let select_a = self.build_op(Operator::Select, vec![a.clone(), x.clone()]);
        let select_b = self.build_op(Operator::Select, vec![b.clone(), x]);
        let selects_eq = self.build_op(Operator::Equals, vec![select_a, select_b]);
        let not_selects_eq = self.negate(&selects_eq);
        let body = self.build_op(Operator::Or, vec![eq, not_selects_eq]);
        self.pool.add(Term::Binder(
            Binder::Choice,
            BindingList(vec![("x".to_owned(), index_sort)]),
            body,
        ))
    }

    fn negate(&mut self, term: &Rc<Term>) -> Rc<Term> {
        self.pool
            .add(Term::Op(Operator::Not, vec![term.clone()]))
    }

    fn build_op(&mut self, op: Operator, args: Vec<Rc<Term>>) -> Rc<Term> {
        self.pool.add(Term::Op(op, args))
    }

    fn new_int(&mut self, i: usize) -> Rc<Term> {
        self.pool.add(Term::new_int(i))
    }

    fn new_string(&mut self, s: &str) -> Rc<Term> {
        self.pool.add(Term::new_string(s))
    }

    /// Returns the elements of an `or` term, if the term is an `or`.
    fn or_elements(term: &Rc<Term>) -> Option<&[Rc<Term>]> {
        match term.as_ref() {
            Term::Op(Operator::Or, args) => Some(args),
            _ => None,
        }
    }

    /// Returns the elements of a `(@list ...)` (i.e., `rare-list`) term, or a slice with the term
    /// itself if it is not a list.
    fn list_elements(term: &Rc<Term>) -> &[Rc<Term>] {
        match term.as_ref() {
            Term::Op(Operator::RareList, args) => args,
            _ => std::slice::from_ref(term),
        }
    }

    /// The clause corresponding to translating the conclusion `res` with the "clause pattern":
    /// the elements of `res` if it is an `or` term, and the singleton `[res]` otherwise.
    fn clause_from_or(res: &Rc<Term>) -> Vec<Rc<Term>> {
        match Self::or_elements(res) {
            Some(elements) => elements.to_vec(),
            None => vec![res.clone()],
        }
    }

    //==========================================================================================//
    // Resolution machinery
    //==========================================================================================//

    /// Ports cvc5's `isSingletonClause`: returns `true` if the conclusion `res` of a resolution
    /// step with the given premises and arguments is a singleton clause. `cargs` is the list of
    /// interleaved polarities and pivots `[pol1, piv1, pol2, piv2, ...]`.
    #[allow(clippy::nonminimal_bool)]
    fn is_singleton_clause(
        &mut self,
        res: &Rc<Term>,
        children: &[Option<Rc<Term>>],
        cargs: &[Rc<Term>],
    ) -> bool {
        if Self::or_elements(res).is_none() {
            return true;
        }
        let true_node = self.pool.bool_true();
        let not_res = self.negate(res);

        // Find the last child that introduced `res` as a subterm, if any
        let mut i = children.len();
        while i > 0 {
            let Some(child) = &children[i - 1] else {
                i -= 1;
                continue;
            };
            let Some(elements) = Self::or_elements(child) else {
                i -= 1;
                continue;
            };
            let pivot_index = if i != 1 { 2 * (i - 1) - 1 } else { 1 };
            let pivot = &cargs[pivot_index];
            let not_pivot = self.negate(pivot);
            if *pivot == *child || not_pivot == *child {
                i -= 1;
                continue;
            }
            if elements.contains(res) {
                break;
            }
            i -= 1;
        }

        // If `res` is a subterm of one of the children, we still need to check whether that
        // subterm is eliminated by one of the resolution steps
        if i > 0 {
            let pos_first = if i == 1 {
                cargs[0] == true_node
            } else {
                cargs[2 * (i - 1) - 2] == true_node
            };
            let pivot = if i == 1 {
                cargs[1].clone()
            } else {
                cargs[2 * (i - 1) - 1].clone()
            };
            let not_pivot = self.negate(&pivot);

            // Check if it is eliminated by the previous resolution step
            if (*res == pivot && !pos_first)
                || (not_res == pivot && pos_first)
                || (not_pivot == *res && pos_first)
            {
                i -= 1;
            } else {
                // Otherwise check if any subsequent premise eliminates it
                while i < children.len() {
                    let pos_first = cargs[2 * i - 2] == true_node;
                    let pivot = cargs[2 * i - 1].clone();
                    let not_pivot = self.negate(&pivot);
                    if (*res == pivot && pos_first)
                        || (not_res == pivot && !pos_first)
                        || (not_pivot == *res && !pos_first)
                    {
                        break;
                    }
                    i += 1;
                }
            }
        }
        i == children.len()
    }

    /// Mirrors cvc5's `updatePost` handling for resolution steps: for each premise, detects
    /// whether it is used as a clause but was concluded as a singleton `(cl (or ...))` (in which
    /// case an `or` step is added), or whether it is used as a singleton but was concluded as a
    /// clause (in which case steps are added to rebuild the singleton). Returns the fixed premise
    /// positions.
    ///
    /// `cargs` is the list of interleaved polarities and pivots, as in `is_singleton_clause`.
    fn fix_resolution_premises(
        &mut self,
        id: &str,
        premises: &[ResPremise],
        cargs: &[Rc<Term>],
    ) -> Vec<(usize, usize)> {
        let true_node = self.pool.bool_true();
        let false_node = self.pool.bool_false();
        let mut result = Vec::new();
        for (i, premise) in premises.iter().enumerate() {
            let Some(term) = &premise.term else {
                result.push(premise.position);
                continue;
            };
            if Self::or_elements(term).is_none() {
                result.push(premise.position);
                continue;
            }
            // Premise `i` is resolved using the pivot of pair `i - 1` (the first premise uses the
            // first pair). The premise is used as a singleton if it is the pivot itself: with
            // positive polarity for the first premise, and negative for the others.
            let pair = if i == 0 { 0 } else { i - 1 };
            let (pol, piv) = (&cargs[2 * pair], &cargs[2 * pair + 1]);
            let used_as_singleton = if i == 0 {
                *pol == true_node && piv == term
            } else {
                *pol == false_node && piv == term
            };
            if !used_as_singleton {
                // If the premise was concluded as a singleton `(cl (or ...))`, add an `or` step
                // to unfold it into a clause
                if let [single] = premise.clause.as_slice() {
                    if let Some(elements) = Self::or_elements(single) {
                        let aux = self.aux_id(id);
                        let position = self.push_step(
                            aux,
                            elements.to_vec(),
                            "or",
                            vec![premise.position],
                            Vec::new(),
                        );
                        result.push(position);
                        continue;
                    }
                }
                result.push(premise.position);
            } else {
                // If the premise was concluded as a clause `(cl t1 ... tn)` but is used as the
                // singleton `(cl (or t1 ... tn))`, rebuild the singleton with `or_neg` steps:
                //
                //             ----------------------  ...  -------------------- or_neg
                //   premise   (cl premise (not t1))   ...  (cl premise (not tn))
                //  ------------------------------------------------------------ resolution
                //                       (cl premise ... premise)
                //  ------------------------------------------------------------ contraction
                //                            (cl premise)
                if premise.clause.len() > 1 {
                    let mut res_premises = vec![premise.position];
                    for (j, literal) in premise.clause.clone().iter().enumerate() {
                        let not_literal = self.negate(literal);
                        let aux = self.aux_id(id);
                        let index_arg = self.new_int(j);
                        let position = self.push_step(
                            aux,
                            vec![term.clone(), not_literal],
                            "or_neg",
                            Vec::new(),
                            vec![index_arg],
                        );
                        res_premises.push(position);
                    }
                    let aux = self.aux_id(id);
                    let repeated = vec![term.clone(); premise.clause.len()];
                    let resolution =
                        self.push_step(aux, repeated, "resolution", res_premises, Vec::new());
                    let aux = self.aux_id(id);
                    let position = self.push_step(
                        aux,
                        vec![term.clone()],
                        "contraction",
                        vec![resolution],
                        Vec::new(),
                    );
                    result.push(position);
                } else {
                    result.push(premise.position);
                }
            }
        }
        result
    }

    /// If the (only) premise of a clause-operating rule (e.g. `contraction` or `reordering`) was
    /// concluded as a singleton `(cl (or ...))`, adds an `or` step to unfold it into a clause.
    fn fix_clause_premise(&mut self, id: &str, premise: &Info) -> (usize, usize) {
        if let [single] = premise.clause.as_slice() {
            if let Some(elements) = Self::or_elements(single) {
                let aux = self.aux_id(id);
                return self.push_step(
                    aux,
                    elements.to_vec(),
                    "or",
                    vec![premise.position],
                    Vec::new(),
                );
            }
        }
        premise.position
    }

    //==========================================================================================//
    // Scopes
    //==========================================================================================//

    /// Translates a chain of nested single-assumption CPC subproofs (printed by cvc5 for a single
    /// internal `SCOPE` step) into one Alethe subproof concluding
    /// `(cl (not F1) ... (not Fn) G)` with the `subproof` rule.
    fn translate_scope_subproof(&mut self, subproof: &Subproof) -> Result<Info> {
        let outer_id = subproof.commands.last().unwrap().id().to_owned();

        // Walk down the chain of nested scopes, collecting the assumptions
        let mut assumptions = Vec::new();
        let mut current = subproof;
        loop {
            let commands = &current.commands;
            let (Some(ProofCommand::Assume { id, term }), Some(ProofCommand::Step(last))) =
                (commands.first(), commands.last())
            else {
                return Err(TranslationError::MalformedScope(outer_id));
            };
            if last.rule != "scope" {
                return Err(TranslationError::MalformedScope(outer_id));
            }
            let converted = self.convert(term);
            assumptions.push((id.clone(), term.clone(), converted));

            // If this level only wraps another scope subproof, continue down the chain
            if commands.len() == 3 {
                if let ProofCommand::Subproof(inner) = &commands[1] {
                    if let Some(ProofCommand::Step(inner_last)) = inner.commands.last() {
                        if inner_last.rule == "scope" {
                            current = inner;
                            continue;
                        }
                    }
                }
            }
            break;
        }
        let body = &current.commands[1..current.commands.len() - 1];
        let ProofCommand::Step(final_step) = current.commands.last().unwrap() else {
            unreachable!()
        };

        // Open the Alethe subproof: a new output frame and one CPC frame per chain level. Each
        // level's frame gets the corresponding assumption as its first command, and the innermost
        // frame will also hold the translation data for the body commands.
        self.out.push(Vec::new());
        let sub_depth = self.out.len() - 1;
        for (k, (id, original, term)) in assumptions.iter().enumerate() {
            self.push_command(ProofCommand::Assume {
                id: id.clone(),
                term: term.clone(),
            });
            self.cpc_frames.push(CpcFrame {
                infos: vec![Some(Info {
                    position: (sub_depth, k),
                    clause: vec![term.clone()],
                    term: Some(term.clone()),
                    original: Some(original.clone()),
                })],
            });
        }

        self.translate_commands(body)?;

        // The conclusion of the body is the (converted) conclusion of the premise of the
        // innermost `step-pop`
        let &[premise] = final_step.premises.as_slice() else {
            return Err(TranslationError::MalformedScope(outer_id));
        };
        let premise_info = self.premise_info(premise, &final_step.id)?;
        let conclusion = match premise_info.clause.as_slice() {
            [] => self.pool.bool_false(),
            [term] => term.clone(),
            _ => {
                return Err(TranslationError::InvalidStep {
                    id: final_step.id.clone(),
                    rule: final_step.rule.clone(),
                    reason: "the conclusion of a scope must be a single formula".to_owned(),
                })
            }
        };

        // The `subproof` rule implicitly uses the previous command as its premise, so the
        // premise of the `step-pop` must be the last command in the subproof. If it is not
        // (which can happen when other steps of the proof DAG are printed inside the scope), we
        // re-state its conclusion with a trivial `reordering` step
        if premise_info.position != (sub_depth, self.out[sub_depth].len() - 1) {
            let aux = self.aux_id(&final_step.id);
            self.push_step(
                aux,
                premise_info.clause.clone(),
                "reordering",
                vec![premise_info.position],
                Vec::new(),
            );
        }

        // Build the `subproof` step concluding `(cl (not F1) ... (not Fn) G)`
        let mut clause: Vec<_> = assumptions
            .iter()
            .map(|(_, _, term)| self.negate(term))
            .collect();
        clause.push(conclusion.clone());
        let discharge = (0..assumptions.len()).map(|k| (sub_depth, k)).collect();
        let step = ProofStep {
            id: outer_id,
            clause: clause.clone(),
            rule: "subproof".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
            discharge,
        };
        self.out.last_mut().unwrap().push(ProofCommand::Step(step));

        // Close the subproof and the chain's CPC frames
        for _ in &assumptions {
            self.cpc_frames.pop();
        }
        let commands = self.out.pop().unwrap();
        let context_id = self.next_context_id;
        self.next_context_id += 1;
        let position = self.push_command(ProofCommand::Subproof(Subproof {
            commands,
            args: Vec::new(),
            context_id,
        }));

        let assumption_terms = assumptions
            .into_iter()
            .map(|(_, _, term)| term)
            .collect();
        self.scope_data
            .insert(position, (assumption_terms, conclusion));

        Ok(Info {
            position,
            clause,
            term: None,
            original: None,
        })
    }

    /// Translates a `process_scope` step, mirroring cvc5's translation of the `SCOPE` rule: from
    /// the subproof conclusion `(cl (not F1) ... (not Fn) G)`, derives `(=> (and F1 ... Fn) G)`,
    /// or `(not (and F1 ... Fn))` when `G` is `false`. When `n = 1`, the conjunction is just `F1`.
    fn translate_process_scope(&mut self, step: &ProofStep, res: Rc<Term>) -> Result<Info> {
        let id = &step.id;
        let &[premise] = step.premises.as_slice() else {
            return Err(TranslationError::InvalidStep {
                id: id.clone(),
                rule: step.rule.clone(),
                reason: "expected exactly one premise".to_owned(),
            });
        };
        let premise_info = self.premise_info(premise, id)?;
        let Some((assumptions, conclusion)) = self.scope_data.get(&premise_info.position).cloned()
        else {
            return Err(TranslationError::InvalidStep {
                id: id.clone(),
                rule: step.rule.clone(),
                reason: "the premise of `process_scope` must be a scope subproof".to_owned(),
            });
        };
        let false_node = self.pool.bool_false();
        let n = assumptions.len();

        let (and_node, vp3) = if n == 1 {
            (assumptions[0].clone(), premise_info.position)
        } else {
            let and_node = self.build_op(Operator::And, assumptions.clone());
            let not_and = self.negate(&and_node);

            // (cl (not (and F1 ... Fn)) Fi), for each i
            let mut res_premises = vec![premise_info.position];
            for (i, assumption) in assumptions.iter().enumerate() {
                let aux = self.aux_id(id);
                let index_arg = self.new_int(i);
                let position = self.push_step(
                    aux,
                    vec![not_and.clone(), assumption.clone()],
                    "and_pos",
                    Vec::new(),
                    vec![index_arg],
                );
                res_premises.push(position);
            }

            // (cl G (not (and F1 ... Fn))^n)
            let mut vp2a_clause = vec![conclusion.clone()];
            vp2a_clause.extend(std::iter::repeat_n(not_and.clone(), n));
            let aux = self.aux_id(id);
            let vp2a = self.push_step(aux, vp2a_clause, "resolution", res_premises, Vec::new());

            // (cl (not (and F1 ... Fn))^n G)
            let mut vp2b_clause = vec![not_and.clone(); n];
            vp2b_clause.push(conclusion.clone());
            let aux = self.aux_id(id);
            let vp2b = self.push_step(aux, vp2b_clause, "reordering", vec![vp2a], Vec::new());

            // (cl (not (and F1 ... Fn)) G)
            let vp3_clause = vec![not_and.clone(), conclusion.clone()];
            let aux = self.aux_id(id);
            let vp3 = self.push_step(aux, vp3_clause, "contraction", vec![vp2b], Vec::new());
            (and_node, vp3)
        };

        // (=> (and F1 ... Fn) G)
        let implies_node = self.build_op(
            Operator::Implies,
            vec![and_node.clone(), conclusion.clone()],
        );

        // VP4: (cl (=> (and F1 ... Fn) G) (and F1 ... Fn))
        let aux = self.aux_id(id);
        let vp4 = self.push_step(
            aux,
            vec![implies_node.clone(), and_node.clone()],
            "implies_neg1",
            Vec::new(),
            Vec::new(),
        );

        // VP5: (cl (=> (and F1 ... Fn) G) G)
        let aux = self.aux_id(id);
        let vp5 = self.push_step(
            aux,
            vec![implies_node.clone(), conclusion.clone()],
            "resolution",
            vec![vp4, vp3],
            Vec::new(),
        );

        // VP6: (cl (=> (and F1 ... Fn) G) (not G))
        let not_conclusion = self.negate(&conclusion);
        let aux = self.aux_id(id);
        let vp6 = self.push_step(
            aux,
            vec![implies_node.clone(), not_conclusion],
            "implies_neg2",
            Vec::new(),
            Vec::new(),
        );

        // VP7: (cl (=> (and F1 ... Fn) G) (=> (and F1 ... Fn) G))
        let aux = self.aux_id(id);
        let vp7 = self.push_step(
            aux,
            vec![implies_node.clone(), implies_node.clone()],
            "resolution",
            vec![vp5, vp6],
            Vec::new(),
        );

        let position = if conclusion != false_node {
            self.push_step(
                id.clone(),
                vec![implies_node],
                "contraction",
                vec![vp7],
                Vec::new(),
            )
        } else {
            // VP8: (cl (=> (and F1 ... Fn) false))
            let aux = self.aux_id(id);
            let vp8 = self.push_step(
                aux,
                vec![implies_node.clone()],
                "contraction",
                vec![vp7],
                Vec::new(),
            );

            // VP9: (cl (= (=> (and F1 ... Fn) false) (not (and F1 ... Fn))))
            let not_and = self.negate(&and_node);
            let vp9_term = self.build_op(
                Operator::Equals,
                vec![implies_node.clone(), not_and.clone()],
            );
            let aux = self.aux_id(id);
            let vp9 = self.push_step(
                aux,
                vec![vp9_term],
                "implies_simplify",
                Vec::new(),
                Vec::new(),
            );

            // VP10: (cl (not (=> (and F1 ... Fn) false)) (not (and F1 ... Fn)))
            let not_implies = self.negate(&implies_node);
            let aux = self.aux_id(id);
            let vp10 = self.push_step(
                aux,
                vec![not_implies, not_and],
                "equiv1",
                vec![vp9],
                Vec::new(),
            );

            self.push_step(
                id.clone(),
                vec![res.clone()],
                "resolution",
                vec![vp8, vp10],
                Vec::new(),
            )
        };

        Ok(Info {
            position,
            clause: vec![res.clone()],
            term: Some(res),
            original: None,
        })
    }

    //==========================================================================================//
    // Bind subproofs
    //==========================================================================================//

    /// Builds an Alethe `bind` subproof concluding `(cl (= lhs rhs))`, where `lhs` and `rhs` are
    /// binder terms over the same number of variables. The body of the subproof is a single step
    /// with the given rule and premises (which may reference steps outside the subproof),
    /// concluding the equality of the binder bodies.
    fn push_bind_subproof(
        &mut self,
        id: String,
        res: Rc<Term>,
        inner_rule: &str,
        inner_premises: Vec<(usize, usize)>,
    ) -> Result<Info> {
        let invalid = |reason: &str| TranslationError::InvalidStep {
            id: id.clone(),
            rule: "bind".to_owned(),
            reason: reason.to_owned(),
        };
        let Some((lhs, rhs)) = match_term!((= l r) = res) else {
            return Err(invalid("conclusion must be an equality"));
        };
        let (Term::Binder(_, x_bindings, f), Term::Binder(_, y_bindings, g)) =
            (lhs.as_ref(), rhs.as_ref())
        else {
            return Err(invalid("conclusion must equate two binder terms"));
        };
        if x_bindings.len() != y_bindings.len() {
            return Err(invalid("binders must have the same number of variables"));
        }

        // The anchor lists the right-hand side variables, and assigns each left-hand side
        // variable to the corresponding right-hand side one
        let mut args: Vec<_> = y_bindings
            .iter()
            .map(|var| AnchorArg::Variable(var.clone()))
            .collect();
        for (x_var, y_var) in x_bindings.iter().zip(y_bindings.iter()) {
            let y_term = self.pool.add(y_var.clone().into());
            args.push(AnchorArg::Assign(x_var.clone(), y_term));
        }

        let body_eq = self.build_op(Operator::Equals, vec![f.clone(), g.clone()]);

        self.out.push(Vec::new());
        let aux = self.aux_id(&id);
        self.push_step(aux, vec![body_eq], inner_rule, inner_premises, Vec::new());
        self.push_step(id, vec![res.clone()], "bind", Vec::new(), Vec::new());

        let commands = self.out.pop().unwrap();
        let context_id = self.next_context_id;
        self.next_context_id += 1;
        let position = self.push_command(ProofCommand::Subproof(Subproof {
            commands,
            args,
            context_id,
        }));
        Ok(Info {
            position,
            clause: vec![res.clone()],
            term: Some(res),
            original: None,
        })
    }

    //==========================================================================================//
    // Final step
    //==========================================================================================//

    /// Mirrors cvc5's `ensureFinalStep`: if the proof concludes `(cl false)` instead of the empty
    /// clause, adds a `false` step and a final resolution step to derive `(cl)`.
    fn ensure_final_step(&mut self) {
        let false_node = self.pool.bool_false();
        let Some(last) = self.out[0].last() else {
            return;
        };
        if last.clause().is_empty() {
            return;
        }
        // The command concluding `false` is usually the last one, but it may also appear earlier
        // (e.g. when it is one of the proof's assumptions)
        let Some(index) = self.out[0]
            .iter()
            .rposition(|command| command.clause() == [false_node.clone()])
        else {
            log::warn!("CPC proof does not conclude `false`");
            return;
        };
        let last_position = (0, index);
        let not_false = self.negate(&false_node);
        let position = self.push_step(
            "cpc.f1".to_owned(),
            vec![not_false],
            "false",
            Vec::new(),
            Vec::new(),
        );
        self.push_step(
            "cpc.f2".to_owned(),
            Vec::new(),
            "resolution",
            vec![last_position, position],
            Vec::new(),
        );
    }
}

#[cfg(test)]
mod tests {
    use crate::{checker, parser};

    fn check_cpc_instance(problem: &str, proof: &str) -> (bool, bool) {
        let (problem, proof, rules, mut pool) = parser::parse_cpc_instance(
            problem.as_bytes(),
            proof.as_bytes(),
            None,
            parser::Config::new(),
        )
        .expect("parsing failed");
        let proof =
            super::cpc_to_alethe(&proof, &mut pool, &rules).expect("translation failed");
        let mut checker =
            checker::ProofChecker::new(&mut pool, &rules, checker::Config::new());
        let result = checker.check(&problem, &proof);
        (result.is_ok(), result.unwrap_or(false))
    }

    #[test]
    fn test_simple_cpc_proof() {
        let problem = "
            (set-logic QF_UF)
            (declare-sort U 0)
            (declare-fun f (U) U)
            (declare-const a U)
            (declare-const b U)
            (assert (= a b))
            (assert (not (= (f a) (f b))))
            (check-sat)
        ";
        let proof = "(
            (define @t1 () (f b))
            (define @t2 () (f a))
            (define @t3 () (= @t2 @t1))
            (define @t4 () (not @t3))
            (assume @p1 (= a b))
            (assume @p2 @t4)
            (step @p3 @t3 :rule cong :premises (@p1) :args (@t2))
            (step @p4 false :rule contra :premises (@p3 @p2))
        )";
        let (is_valid, is_holey) = check_cpc_instance(problem, proof);
        assert!(is_valid);
        assert!(!is_holey);
    }

    #[test]
    fn test_cpc_proof_with_scope() {
        // A proof with an `assume-push`/`step-pop` subproof, which becomes an Alethe subproof
        let problem = "
            (set-logic QF_UF)
            (declare-const p Bool)
            (declare-const q Bool)
            (assert p)
            (assert (not q))
            (assert (=> p q))
            (check-sat)
        ";
        let proof = "(
            (assume @p1 p)
            (assume @p2 (not q))
            (assume @p3 (=> p q))
            (step @p4 q :rule modus_ponens :premises (@p1 @p3))
            (step @p5 false :rule contra :premises (@p4 @p2))
        )";
        let (is_valid, is_holey) = check_cpc_instance(problem, proof);
        assert!(is_valid);
        assert!(!is_holey);
    }
}
