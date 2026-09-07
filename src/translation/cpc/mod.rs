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
    CarcaraResult,
    ast::{rare_rules::Rules, *},
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
    // The short-circuits of the translation leave the steps they bypass unreferenced; like
    // cvc5's printer, only the derivation of the final step is kept
    let commands = prune_unreachable(commands);
    // The constant definitions of the original proof are dropped, since they may reference
    // cvc5-internal symbols that are eliminated by the translation (they are only used for
    // printing, so this only means that printed proofs will not use them for sharing)
    Ok(Proof {
        constant_definitions: Vec::new(),
        commands,
        filename: proof.filename.clone(),
    })
}

/// Keeps only the commands the last command of the proof depends on: the premises and discharged
/// assumptions of steps, the previous command of the closing step of a subproof (used implicitly
/// by the `subproof` and `bind` rules) and the whole of any subproof whose closing step is used.
/// Positions `(depth, index)` are renumbered accordingly.
fn prune_unreachable(commands: Vec<ProofCommand>) -> Vec<ProofCommand> {
    if commands.is_empty() {
        return commands;
    }
    let mut stack: Vec<Vec<bool>> = Vec::new();
    let mut work: Vec<Vec<usize>> = Vec::new();
    let tree = mark_frame(&commands, &mut stack, &mut work, vec![commands.len() - 1]);
    let mut remaps: Vec<Vec<usize>> = Vec::new();
    rebuild_frame(commands, &tree, &mut remaps)
}

/// The reachability flags of the commands of a frame, and those of its reached subproofs, by
/// index.
struct Reached {
    kept: Vec<bool>,
    subproofs: Vec<(usize, Reached)>,
}

/// Marks the commands of a frame reachable from `roots`. `stack` holds the flags of the open
/// frames (by depth), so that premises in enclosing frames can be marked; the work lists of
/// the enclosing frames may grow while a nested frame is processed.
fn mark_frame(
    commands: &[ProofCommand],
    stack: &mut Vec<Vec<bool>>,
    work: &mut Vec<Vec<usize>>,
    roots: Vec<usize>,
) -> Reached {
    let depth = stack.len();
    stack.push(vec![false; commands.len()]);
    work.push(Vec::new());
    for root in roots {
        if !stack[depth][root] {
            stack[depth][root] = true;
            work[depth].push(root);
        }
    }
    let mut subproofs = Vec::new();
    while let Some(index) = work[depth].pop() {
        match &commands[index] {
            ProofCommand::Assume { .. } => {}
            ProofCommand::Step(step) => {
                for &(d, i) in step.premises.iter().chain(step.discharge.iter()) {
                    if d <= depth && !stack[d][i] {
                        stack[d][i] = true;
                        work[d].push(i);
                    }
                }
            }
            ProofCommand::Subproof(subproof) => {
                // The closing step and the command it implicitly uses, plus every assumption
                let n = subproof.commands.len();
                let mut roots: Vec<usize> = (0..n)
                    .filter(|&i| matches!(subproof.commands[i], ProofCommand::Assume { .. }))
                    .collect();
                roots.push(n - 1);
                if n >= 2 {
                    roots.push(n - 2);
                }
                let reached = mark_frame(&subproof.commands, stack, work, roots);
                subproofs.push((index, reached));
            }
        }
    }
    work.pop();
    let kept = stack.pop().unwrap();
    Reached { kept, subproofs }
}

/// Rebuilds a frame from its reachability flags, renumbering the positions of premises and
/// discharged assumptions. `remaps` holds the old-to-new index maps of the open frames.
fn rebuild_frame(
    commands: Vec<ProofCommand>,
    reached: &Reached,
    remaps: &mut Vec<Vec<usize>>,
) -> Vec<ProofCommand> {
    let mut remap = vec![usize::MAX; commands.len()];
    let mut next = 0;
    for (i, &kept) in reached.kept.iter().enumerate() {
        if kept {
            remap[i] = next;
            next += 1;
        }
    }
    remaps.push(remap);
    let mut result = Vec::with_capacity(next);
    for (i, command) in commands.into_iter().enumerate() {
        if !reached.kept[i] {
            continue;
        }
        result.push(match command {
            ProofCommand::Assume { id, term } => ProofCommand::Assume { id, term },
            ProofCommand::Step(mut step) => {
                for (d, j) in step.premises.iter_mut().chain(step.discharge.iter_mut()) {
                    *j = remaps[*d][*j];
                }
                ProofCommand::Step(step)
            }
            ProofCommand::Subproof(subproof) => {
                let Subproof { commands, args, context_id } = subproof;
                let inner = &reached
                    .subproofs
                    .iter()
                    .find(|(j, _)| *j == i)
                    .expect("reached subproof without flags")
                    .1;
                let commands = rebuild_frame(commands, inner, remaps);
                ProofCommand::Subproof(Subproof { commands, args, context_id })
            }
        });
    }
    remaps.pop();
    result
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

    /// For each step concluding the implication `(cl (=> (and F1 ... Fn) G))` of a translated
    /// `process_scope`, the position and clause of the folded subproof clause
    /// `(cl (not (and F1 ... Fn)) G)` it was derived from (the subproof clause itself when
    /// `n = 1`). Consumers eliminating the implication again use that step directly, mirroring
    /// the implication round-trip short-circuit of cvc5's Alethe post-processor.
    scope_implication: HashMap<(usize, usize), ((usize, usize), Vec<Rc<Term>>)>,

    /// For each folded subproof clause `(cl (not (and F1 ... Fn)) G)` of a `process_scope`, the
    /// position and clause of the subproof step `(cl (not F1) ... (not Fn) G)` it folds, used by
    /// the conjunction round-trip short-circuit of `not_and` steps.
    scope_fold: HashMap<(usize, usize), ((usize, usize), Vec<Rc<Term>>)>,

    /// The top-level subproofs, keyed by the sorted literals of their clauses. A later top-level
    /// subproof, resolution, reordering or contraction concluding the same literals reuses the
    /// subproof (through a `reordering` step if the order differs), so that the steps rebuilding
    /// the clause become dead; this mirrors the clause round-trip short-circuit of cvc5's Alethe
    /// post-processor.
    subproof_by_literals: HashMap<Vec<Rc<Term>>, ((usize, usize), Vec<Rc<Term>>)>,

    /// Whether `absorb` steps are expanded into `ac_simp` and simplification steps instead of
    /// using Carcara's dedicated `absorb` rule (kept for reference, always `false`).
    expand_absorb: bool,

    /// Memoization cache for `convert`.
    cache: HashMap<Rc<Term>, Rc<Term>>,

    /// Memoization cache for `quantifiers_skolemize_choice`, keyed by the quantified formula and
    /// the variable index. Without it the choice term of the `i`-th variable is rebuilt once per
    /// later variable, which is exponential in the number of variables.
    skolem_choice_cache: HashMap<(Rc<Term>, usize), Rc<Term>>,

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
            scope_implication: HashMap::new(),
            scope_fold: HashMap::new(),
            subproof_by_literals: HashMap::new(),
            expand_absorb: false,
            cache: HashMap::new(),
            skolem_choice_cache: HashMap::new(),
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
                    let position = self
                        .push_command(ProofCommand::Assume { id: id.clone(), term: term.clone() });
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
        // A top-level step rebuilding the clause of an earlier top-level subproof is replaced by
        // that subproof (see `subproof_by_literals`)
        if self.out.len() == 1
            && matches!(rule, "resolution" | "reordering" | "contraction")
            && !clause.is_empty()
        {
            if let Some((position, subproof_clause)) = self
                .subproof_by_literals
                .get(&Self::literals_key(&clause))
                .cloned()
            {
                if subproof_clause == clause {
                    return position;
                }
                return self.push_command(ProofCommand::Step(ProofStep {
                    id,
                    clause,
                    rule: "reordering".to_owned(),
                    premises: vec![position],
                    args: Vec::new(),
                    discharge: Vec::new(),
                }));
            }
        }
        self.push_command(ProofCommand::Step(ProofStep {
            id,
            clause,
            rule: rule.to_owned(),
            premises,
            args,
            discharge: Vec::new(),
        }))
    }

    /// The literals of a clause as a sorted multiset, used to detect clauses equal up to order.
    fn literals_key(clause: &[Rc<Term>]) -> Vec<Rc<Term>> {
        let mut key = clause.to_vec();
        key.sort_by_key(|t| Rc::as_ptr(t) as usize);
        key
    }

    /// The step at an accessible position (in an open frame).
    fn step_at(&self, (depth, index): (usize, usize)) -> Option<&ProofStep> {
        match self.out.get(depth)?.get(index)? {
            ProofCommand::Step(step) => Some(step),
            _ => None,
        }
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

    /// Generates a fresh variable name, used when renaming variables.
    fn fresh_var_name(&mut self) -> String {
        self.next_aux_id += 1;
        format!("@cpc_x{}", self.next_aux_id)
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
                    // The quantifier skolem is converted to the corresponding choice term
                    if name == "@quantifiers_skolemize" {
                        let quant = self.convert(&args[0]);
                        let index = args[1].as_integer().and_then(|i| i.to_usize());
                        if let Some(result) =
                            index.and_then(|i| self.quantifiers_skolemize_choice(&quant, i))
                        {
                            self.cache.insert(term.clone(), result.clone());
                            return result;
                        }
                    }
                    // The skolems for the value of a division or modulo at a zero divisor are
                    // converted to the choice terms cvc5's Alethe printer uses:
                    // `(choice ((y T)) (= y (op a 0)))`
                    if let Some(op) = match name.as_str() {
                        "@int_div_by_zero" => Some(Operator::IntDiv),
                        "@mod_by_zero" => Some(Operator::Mod),
                        "@div_by_zero" => Some(Operator::RealDiv),
                        _ => None,
                    } {
                        let a = self.convert(&args[0]);
                        let result = self.build_by_zero_choice(op, &a);
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

    /// Builds the choice term corresponding to the quantifier skolem
    /// `(@quantifiers_skolemize Q i)`, where `Q` is `(forall ((x_1 T_1) ... (x_n T_n)) F)`:
    ///
    /// `(choice ((x_i T_i)) (not (forall ((x_i+1 T_i+1) ... (x_n T_n)) F)))`
    ///
    /// where the variables `x_1 ... x_i-1` are replaced by their own choice terms, and the inner
    /// quantifier is omitted if `i = n`. Note that the body of the choice is negated because
    /// cvc5 always skolemizes universal quantifiers, which in Alethe is done via the
    /// `sko_forall` rule.
    fn quantifiers_skolemize_choice(&mut self, quant: &Rc<Term>, index: usize) -> Option<Rc<Term>> {
        let key = (quant.clone(), index);
        if let Some(cached) = self.skolem_choice_cache.get(&key) {
            return Some(cached.clone());
        }
        let Term::Binder(Binder::Forall, bindings, body) = quant.as_ref() else {
            return None;
        };
        let var = bindings.0.get(index)?.clone();

        let inner = if index == bindings.len() - 1 {
            body.clone()
        } else {
            self.pool.add(Term::Binder(
                Binder::Forall,
                BindingList(bindings.0[index + 1..].to_vec()),
                body.clone(),
            ))
        };
        let mut choice_body = self.negate(&inner);

        // Replace the variables skolemized before this one by their own choice terms
        if index > 0 {
            let mut map = indexmap::IndexMap::new();
            for i in 0..index {
                let previous = self.quantifiers_skolemize_choice(quant, i)?;
                let var_term = self.pool.add(bindings.0[i].clone().into());
                map.insert(var_term, previous);
            }
            choice_body = Substitution::new(self.pool, map)
                .ok()?
                .apply(self.pool, &choice_body);
        }

        let result = self.pool.add(Term::Binder(
            Binder::Choice,
            BindingList(vec![var]),
            choice_body,
        ));
        self.skolem_choice_cache.insert(key, result.clone());
        Some(result)
    }

    /// Builds the choice term `(choice ((y T)) (= y (op a 0)))` denoting the value of the division
    /// or modulo operator `op` applied to `a` and a zero divisor, with `y` not free in `a`.
    fn build_by_zero_choice(&mut self, op: Operator, a: &Rc<Term>) -> Rc<Term> {
        let (sort, zero) = if op == Operator::RealDiv {
            (Sort::Real, Constant::Real(rug::Rational::new()))
        } else {
            (Sort::Int, Constant::Integer(rug::Integer::new()))
        };
        let free_names: Vec<String> = self
            .pool
            .free_vars(a)
            .iter()
            .filter_map(|v| v.as_var().map(str::to_owned))
            .collect();
        let mut name = "y".to_owned();
        let mut i = 0;
        while free_names.contains(&name) {
            name = format!("y{}", i);
            i += 1;
        }
        let sort = self.pool.add_sort(sort);
        let y = self.pool.add(Term::new_var(name.clone(), sort.clone()));
        let zero = self.pool.add(Term::Const(zero));
        let app = self.build_op(op, vec![a.clone(), zero]);
        let body = self.build_op(Operator::Equals, vec![y, app]);
        self.pool.add(Term::Binder(
            Binder::Choice,
            BindingList(vec![(name, sort)]),
            body,
        ))
    }

    /// Builds the choice term corresponding to the array diff skolem `(@array_deq_diff a b)`:
    /// `(choice ((x I)) (or (= a b) (not (= (select a x) (select b x)))))`, where `I` is the
    /// index sort of the arrays.
    fn build_array_deq_diff_choice(&mut self, a: &Rc<Term>, b: &Rc<Term>) -> Rc<Term> {
        let array_sort = self.pool.sort(a);
        let index_sort = match array_sort.as_ref() {
            Sort::Array(index_sort, _) => index_sort.clone(),
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
        self.pool.add(Term::Op(Operator::Not, vec![term.clone()]))
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
                    // Each distinct literal is resolved once, at its first occurrence: with
                    // explicit pivots a second resolution on the same literal would fail
                    let mut resolved = Vec::new();
                    for (j, literal) in premise.clause.clone().iter().enumerate() {
                        if resolved.contains(literal) {
                            continue;
                        }
                        resolved.push(literal.clone());
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
                    let repeated = vec![term.clone(); resolved.len()];
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
            self.push_command(ProofCommand::Assume { id: id.clone(), term: term.clone() });
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
                });
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
        let assumption_terms: Vec<_> = assumptions.into_iter().map(|(_, _, term)| term).collect();

        // A top-level subproof concluding the same literals as an earlier one is replaced by it
        // (the whole body of this one becomes dead), through a `reordering` step if the literal
        // order differs
        if self.out.len() == 1 {
            let key = Self::literals_key(&clause);
            if let Some((existing, existing_clause)) = self.subproof_by_literals.get(&key).cloned()
            {
                let position = if existing_clause == clause {
                    existing
                } else {
                    let position = self.push_command(ProofCommand::Step(ProofStep {
                        id: commands.last().unwrap().id().to_owned(),
                        clause: clause.clone(),
                        rule: "reordering".to_owned(),
                        premises: vec![existing],
                        args: Vec::new(),
                        discharge: Vec::new(),
                    }));
                    self.scope_data
                        .insert(position, (assumption_terms, conclusion));
                    position
                };
                return Ok(Info {
                    position,
                    clause,
                    term: None,
                    original: None,
                });
            }
        }

        let context_id = self.next_context_id;
        self.next_context_id += 1;
        let position = self.push_command(ProofCommand::Subproof(Subproof {
            commands,
            args: Vec::new(),
            context_id,
        }));
        if self.out.len() == 1 {
            self.subproof_by_literals
                .insert(Self::literals_key(&clause), (position, clause.clone()));
        }

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
            self.scope_fold
                .insert(vp3, (premise_info.position, premise_info.clause.clone()));
            (and_node, vp3)
        };
        let vp3_clause = vec![self.negate(&and_node), conclusion.clone()];

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
            let position = self.push_step(
                id.clone(),
                vec![implies_node],
                "contraction",
                vec![vp7],
                Vec::new(),
            );
            self.scope_implication.insert(position, (vp3, vp3_clause));
            position
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

    /// Builds an Alethe `bind` subproof concluding `(cl (= lhs rhs))` for a congruence over binder
    /// terms, deriving the equality of the bodies from the premises by congruence (see
    /// `derive_equality`).
    fn push_bind_subproof_cong(
        &mut self,
        id: String,
        res: Rc<Term>,
        premises: &[ResPremise],
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
        let mut args: Vec<_> = y_bindings
            .iter()
            .map(|var| AnchorArg::Variable(var.clone()))
            .collect();
        for (x_var, y_var) in x_bindings.iter().zip(y_bindings.iter()) {
            let y_term = self.pool.add(y_var.clone().into());
            args.push(AnchorArg::Assign(x_var.clone(), y_term));
        }
        let (f, g) = (f.clone(), g.clone());

        self.out.push(Vec::new());
        let depth = self.out.len() - 1;
        match self.derive_equality(&id, &f, &g, premises) {
            // The `bind` step uses the previous step of the subproof as its premise, so an
            // equality that is directly a premise outside the subproof is re-stated inside it
            Some(position) if position.0 != depth => {
                let body_eq = self.build_op(Operator::Equals, vec![f, g]);
                let aux = self.aux_id(&id);
                self.push_step(aux, vec![body_eq], "trans", vec![position], Vec::new());
            }
            Some(_) => {}
            None => {
                log::warn!(
                    "could not derive the body equality of a congruence over binders, using `hole`"
                );
                let body_eq = self.build_op(Operator::Equals, vec![f, g]);
                let aux = self.aux_id(&id);
                self.push_step(aux, vec![body_eq], "hole", Vec::new(), Vec::new());
            }
        }
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

    /// Derives `(= a b)` from the given premise equalities: directly if `a` and `b` are equal
    /// (`refl`) or a premise equates them (in either direction), otherwise by congruence over
    /// applications of the same head, deriving the equalities of the differing arguments
    /// recursively. Returns the position of the step concluding `(= a b)`, or `None` if the
    /// equality cannot be derived this way.
    fn derive_equality(
        &mut self,
        id: &str,
        a: &Rc<Term>,
        b: &Rc<Term>,
        premises: &[ResPremise],
    ) -> Option<(usize, usize)> {
        if a == b {
            let eq = self.build_op(Operator::Equals, vec![a.clone(), a.clone()]);
            let aux = self.aux_id(id);
            return Some(self.push_step(aux, vec![eq], "refl", Vec::new(), Vec::new()));
        }
        for premise in premises {
            if let Some((x, y)) = premise.term.as_ref().and_then(|t| match_term!((= x y) = t)) {
                if (x == a && y == b) || (x == b && y == a) {
                    return Some(premise.position);
                }
            }
        }
        let (a_args, b_args) = match (a.as_ref(), b.as_ref()) {
            (Term::App(f, a_args), Term::App(g, b_args)) if f == g => (a_args, b_args),
            (Term::Op(f, a_args), Term::Op(g, b_args)) if f == g => (a_args, b_args),
            (
                Term::ParamOp {
                    op: f,
                    op_args: f_op_args,
                    args: a_args,
                },
                Term::ParamOp {
                    op: g,
                    op_args: g_op_args,
                    args: b_args,
                },
            ) if f == g && f_op_args == g_op_args => (a_args, b_args),
            _ => return None,
        };
        if a_args.len() != b_args.len() {
            return None;
        }
        let mut positions = Vec::new();
        for (x, y) in a_args.clone().iter().zip(b_args.clone().iter()) {
            if x != y {
                positions.push(self.derive_equality(id, x, y, premises)?);
            }
        }
        let eq = self.build_op(Operator::Equals, vec![a.clone(), b.clone()]);
        let aux = self.aux_id(id);
        Some(self.push_step(aux, vec![eq], "cong", positions, Vec::new()))
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
    use std::path::Path;

    fn check_cpc_instance(problem: &str, proof: &str) -> (bool, bool) {
        let (problem, proof, rules, mut pool) = parser::parse_cpc_instance(
            parser::Source::new(Path::new("<problem>"), problem),
            parser::Source::new(Path::new("<proof>"), proof),
            None,
            parser::Config::new(),
        )
        .expect("parsing failed");
        let proof = super::cpc_to_alethe(&proof, &mut pool, &rules).expect("translation failed");
        let mut checker = checker::ProofChecker::new(&mut pool, &rules, checker::Config::new());
        let result = checker.check(&problem, &proof);
        (result.is_ok(), matches!(result, Ok(crate::Status::Holey)))
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
    fn test_cpc_assumptions_must_match_problem() {
        // The `assume` commands of the translated proof are checked against the assertions in
        // the original problem, so a proof making an assumption that is not among them must be
        // rejected
        let problem = "
            (set-logic QF_UF)
            (declare-const p Bool)
            (declare-const q Bool)
            (assert p)
            (check-sat)
        ";
        let proof = "(
            (assume @p1 q)
            (assume @p2 (not q))
            (step @p3 false :rule contra :premises (@p1 @p2))
        )";
        let (problem, proof, rules, mut pool) = crate::parser::parse_cpc_instance(
            parser::Source::new(Path::new("<problem>"), problem),
            parser::Source::new(Path::new("<proof>"), proof),
            None,
            crate::parser::Config::new(),
        )
        .expect("parsing failed");
        let proof = super::cpc_to_alethe(&proof, &mut pool, &rules).expect("translation failed");
        let mut checker =
            crate::checker::ProofChecker::new(&mut pool, &rules, crate::checker::Config::new());
        assert!(checker.check(&problem, &proof).is_err());
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
