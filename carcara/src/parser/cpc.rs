//! A parser for the CPC (Cooperating Proof Calculus) proof format, in the Eunoia syntax. This is
//! the format produced by cvc5 by default when passing `--dump-proofs`.
//!
//! CPC proofs are a series of commands, much like Alethe proofs. The main differences handled
//! here are:
//!
//! - Proofs carry their own `declare-sort`/`declare-const` commands, and use `define` commands for
//!   term sharing (e.g. `(define @t1 () (f x))`).
//! - Steps reference cvc5's internal proof rules, and their conclusions are single formulas
//!   instead of clauses. Conclusions are only printed when cvc5 is given the
//!   `--proof-print-conclusion` option, which is therefore required.
//! - Subproofs are introduced by `assume-push` commands and closed by `step-pop` commands, instead
//!   of `anchor` commands. A `step-pop` always uses the `scope` rule, whose conclusion is
//!   `(=> F G)`, for `F` the pushed assumption and `G` the conclusion of the premise.
//! - Some terms are printed using cvc5 internal symbols, like `@var`, `@list` and `@purify`, and
//!   binders are applied to variable lists, e.g. `(forall (@list (@var "x" Int)) ...)`.

use super::{Config, FunctionDef, Parser, ParserError, Position, Reserved, Token};
use crate::{
    ast::{rare_rules::RareStatements, *},
    utils::HashCache,
    CarcaraResult, Error,
};
use indexmap::IndexMap;
use std::io::BufRead;

/// Parses an SMT problem instance (in the SMT-LIB format) and its associated CPC proof (in the
/// Eunoia format), as well as an optional RARE rules file.
///
/// This returns the parsed problem and proof, as well as the `TermPool` used in parsing. Can take
/// any type that implements `BufRead`.
pub fn parse_cpc_instance<T: BufRead>(
    problem: T,
    proof: T,
    rules: Option<T>,
    mut config: Config,
) -> CarcaraResult<(Problem, Proof, rare_rules::Rules, PrimitivePool)> {
    // `let` bindings and function definitions are always expanded when parsing CPC proofs, so
    // they must also be expanded in the problem for the proof's `assume`s to match the problem's
    // assertions
    config.expand_lets = true;
    config.apply_function_defs = true;
    let mut pool = PrimitivePool::new();
    let mut parser = Parser::new(&mut pool, config, problem)?;
    // Some cvc5 internal constants (e.g. `piand`) may also appear in the problem
    parser.insert_cpc_internal_constants();
    let problem = parser.parse_problem()?;
    parser.reset(proof)?;
    let proof = parser.parse_cpc_proof()?;
    let rules = if let Some(rules) = rules {
        parser.reset(rules)?;
        parser.parse_rare()?
    } else {
        RareStatements { rules: IndexMap::new() }
    };
    Ok((problem, proof, rules, pool))
}

impl<R: BufRead> Parser<'_, R> {
    /// Parses a proof in the CPC format. All function, constant and sort declarations used in the
    /// problem should already be in the parser state.
    pub fn parse_cpc_proof(&mut self) -> CarcaraResult<Proof> {
        self.cpc_mode = true;
        self.insert_cpc_internal_constants();
        let result = self.parse_cpc_proof_inner();
        self.cpc_mode = false;
        result
    }

    /// Adds cvc5 internal constants that can appear in CPC proofs (e.g. the arithmetic
    /// division-by-zero skolems) to the symbol table.
    fn insert_cpc_internal_constants(&mut self) {
        let int = self.pool.add(Term::Sort(Sort::Int));
        let real = self.pool.add(Term::Sort(Sort::Real));
        let int_to_int = self
            .pool
            .add(Term::Sort(Sort::Function(vec![int.clone(), int.clone()])));
        let real_to_real = self
            .pool
            .add(Term::Sort(Sort::Function(vec![real.clone(), real.clone()])));

        let bool_sort = self.pool.add(Term::Sort(Sort::Bool));
        // (-> Int Int Int Int): the width and the two operands
        let piand_sort = self.pool.add(Term::Sort(Sort::Function(vec![
            int.clone(),
            int.clone(),
            int.clone(),
            int.clone(),
        ])));
        // (-> Int Bool Real Bool): the root index, the polynomial equality and the value
        let root_predicate_sort = self.pool.add(Term::Sort(Sort::Function(vec![
            int,
            bool_sort.clone(),
            real.clone(),
            bool_sort,
        ])));

        let constants = [
            ("@int_div_by_zero", int_to_int.clone()),
            ("@mod_by_zero", int_to_int),
            ("@div_by_zero", real_to_real),
            ("@arith_vts_delta", real.clone()),
            ("@arith_vts_delta_free", real),
            ("piand", piand_sort),
            ("@indexed_root_predicate", root_predicate_sort),
        ];
        for (name, sort) in constants {
            self.insert_sorted_var((name.to_owned(), sort));
        }
    }

    /// Returns `true` if `head` is a symbol that requires special handling when it appears as the
    /// head of an application in a CPC proof, i.e., it should be parsed by
    /// `parse_cpc_application`.
    pub(super) fn is_cpc_special_head(&self, head: &str) -> bool {
        use std::str::FromStr;

        // cvc5 uses the "totalized" versions of the division and modulo operators internally,
        // which we map to the regular operators (as does cvc5's own Alethe printer)
        if matches!(head, "div_total" | "mod_total" | "/_total") {
            return true;
        }
        head.starts_with('@')
            && Operator::from_str(head).is_err()
            && ParamOperator::from_str(head).is_err()
            && !self.state.function_defs.contains_key(head)
            && self
                .state
                .symbol_table
                .get(&HashCache::new(head.to_owned()))
                .is_none()
    }

    fn parse_cpc_proof_inner(&mut self) -> CarcaraResult<Proof> {
        // As in `parse_proof`, we parse subproofs iteratively, instead of recursively, and so we
        // need to manually keep a stack. Each frame holds the subproof that is being built. The
        // first frame in the stack represents the root proof. Subproofs in CPC are opened by
        // `assume-push` commands, and closed by `step-pop` commands.
        let mut stack: Vec<Subproof> = vec![Subproof::default()];

        let mut next_subproof_context_id = 0;

        let mut constant_definitions = Vec::new();

        // CPC proofs are wrapped in a set of surrounding parentheses. We use the same heuristic as
        // `parse_proof` to detect and consume them.
        let mut has_extra_surrounding_parens = false;
        let mut read_first_token = false;

        // cvc5 prints the satisfiability result (unsat) together with the proof, so we consume
        // this first "unsat" token if it exists
        if self.current_token == Token::Symbol("unsat".into()) {
            self.next_token()?;
        }

        while self.current_token != Token::Eof && self.current_token != Token::CloseParen {
            self.expect_token(Token::OpenParen)?;

            if !read_first_token
                && (self.current_token == Token::OpenParen
                    || self.current_token == Token::CloseParen)
            {
                has_extra_surrounding_parens = true;
                read_first_token = true;
                continue;
            }
            read_first_token = true;

            let (token, position) = self.next_token()?;

            let (id, command) = match token {
                Token::ReservedWord(Reserved::DeclareConst) => {
                    let name = self.expect_symbol()?;
                    let sort = self.parse_sort(false)?;
                    self.expect_token(Token::CloseParen)?;

                    // CPC proofs re-declare the problem's symbols, so this may shadow an existing
                    // (identical) declaration
                    self.insert_sorted_var((name, sort));
                    continue;
                }
                Token::ReservedWord(Reserved::DeclareSort) => {
                    let (name, arity) = self.parse_declare_sort()?;
                    self.state.sort_declarations.insert(name, arity);
                    continue;
                }
                Token::ReservedWord(Reserved::Define) => {
                    let (name, func_def) = self.parse_cpc_define()?;
                    if func_def.params.is_empty() {
                        constant_definitions.push((name.clone(), func_def.body.clone()));
                    }
                    self.state.function_defs.insert(name, func_def);
                    continue;
                }
                Token::ReservedWord(Reserved::Assume) => {
                    let (id, term) = self.parse_assume_command()?;
                    (id.clone(), ProofCommand::Assume { id, term })
                }
                Token::ReservedWord(Reserved::AssumePush) => {
                    let (id, term) = self.parse_assume_command()?;

                    // An `assume-push` opens a new subproof, with the assumption as its first
                    // command. As with `anchor`s in `parse_proof`, we push new scopes into the
                    // symbol and step id tables, which will be popped by the matching `step-pop`
                    self.state.symbol_table.push_scope();
                    self.state.step_ids.push_scope();
                    let mut subproof = Subproof {
                        commands: Vec::new(),
                        args: Vec::new(),
                        context_id: next_subproof_context_id,
                    };
                    next_subproof_context_id += 1;
                    subproof
                        .commands
                        .push(ProofCommand::Assume { id: id.clone(), term });
                    stack.push(subproof);
                    self.state.step_ids.insert(HashCache::new(id), 0);
                    continue;
                }
                Token::ReservedWord(Reserved::Step) => {
                    let step = self.parse_cpc_step(position)?;
                    (step.id.clone(), ProofCommand::Step(step))
                }
                Token::ReservedWord(Reserved::StepPop) => {
                    let step = self.parse_cpc_step_pop(&stack, position)?;
                    let id = step.id.clone();

                    if stack.len() < 2 {
                        return Err(Error::Parser(
                            ParserError::UnmatchedStepPop(id),
                            position,
                        ));
                    }

                    // A `step-pop` closes the current subproof, becoming its last step
                    self.state.symbol_table.pop_scope();
                    self.state.step_ids.pop_scope();
                    let mut subproof = stack.pop().unwrap();
                    subproof.commands.push(ProofCommand::Step(step));
                    (id, ProofCommand::Subproof(subproof))
                }
                _ => {
                    return Err(Error::Parser(ParserError::UnexpectedToken(token), position));
                }
            };

            // Note that, unlike in Alethe proofs, step ids in CPC proofs are not globally unique:
            // since proofs are DAGs, cvc5 re-prints steps that are shared between different
            // subproofs. Re-printed steps are identical, so we don't check for repeated ids, and
            // references simply resolve to the closest visible step with that id.
            let top = stack.last_mut().unwrap();
            top.commands.push(command);
            let index = top.commands.len() - 1;
            self.state.step_ids.insert(HashCache::new(id), index);
        }

        if has_extra_surrounding_parens {
            self.expect_token(Token::CloseParen)?;
        }
        self.expect_token(Token::Eof)?;

        let commands = match stack.len() {
            0 => unreachable!(),
            1 => stack.pop().unwrap().commands,

            // If there is more than one frame in the stack, an `assume-push` was not closed by a
            // matching `step-pop` before the end of the proof
            _ => {
                return Err(Error::Parser(
                    ParserError::UnclosedSubproof(
                        stack.pop().unwrap().commands[0].id().to_owned(),
                    ),
                    self.current_position,
                ))
            }
        };
        Ok(Proof { constant_definitions, commands })
    }

    /// Parses a `define` command in a CPC proof, of the form `(define <symbol> (<sorted var>*)
    /// <term>)`. This method assumes that the `(` and `define` tokens were already consumed.
    fn parse_cpc_define(&mut self) -> CarcaraResult<(String, FunctionDef)> {
        let name = self.expect_symbol()?;
        self.expect_token(Token::OpenParen)?;
        let params = self.parse_sequence(Self::parse_sorted_var, false)?;

        // In order to correctly parse the definition body, we push a new scope to the symbol table
        // and add the definition parameters to it
        self.state.symbol_table.push_scope();
        for var in &params {
            self.insert_sorted_var(var.clone());
        }
        let body = self.parse_term()?;
        self.state.symbol_table.pop_scope();

        self.ignore_remaining_attributes()?;
        self.expect_token(Token::CloseParen)?;

        Ok((name, FunctionDef { params, body }))
    }

    /// Parses a `step` command in a CPC proof. This method assumes that the `(` and `step` tokens
    /// were already consumed.
    ///
    /// Unlike in Alethe, the conclusion is a single formula instead of a clause, and is only
    /// present if the proof was produced with the cvc5 option `--proof-print-conclusion`. Since
    /// Carcara cannot compute the conclusions of CPC steps, we require that option to be used.
    fn parse_cpc_step(&mut self, position: Position) -> CarcaraResult<ProofStep> {
        let id = self.expect_symbol()?;

        let conclusion = if matches!(self.current_token, Token::Keyword(_)) {
            None
        } else {
            Some(self.parse_term_expecting_sort(&Sort::Bool)?)
        };

        let (rule, premises, args) = self.parse_cpc_step_attributes()?;

        let Some(conclusion) = conclusion else {
            return Err(Error::Parser(
                ParserError::CpcMissingConclusion(id),
                position,
            ));
        };

        Ok(ProofStep {
            id,
            clause: vec![conclusion],
            rule,
            premises,
            args,
            discharge: Vec::new(),
        })
    }

    /// Parses a `step-pop` command in a CPC proof. This method assumes that the `(` and `step-pop`
    /// tokens were already consumed.
    ///
    /// `step-pop` commands never have their conclusion printed, but their rule is always `scope`,
    /// which concludes `(=> F G)` for `F` the assumption pushed by the matching `assume-push` and
    /// `G` the conclusion of the premise. So we can compute the conclusion here.
    fn parse_cpc_step_pop(
        &mut self,
        stack: &[Subproof],
        position: Position,
    ) -> CarcaraResult<ProofStep> {
        let id = self.expect_symbol()?;

        // Just in case, we allow (and ignore) an explicit conclusion
        if !matches!(self.current_token, Token::Keyword(_)) {
            self.parse_term_expecting_sort(&Sort::Bool)?;
        }

        let (rule, premises, args) = self.parse_cpc_step_attributes()?;

        let current_frame = stack.last().unwrap();
        let assumption = match current_frame.commands.first() {
            Some(ProofCommand::Assume { term, .. }) => term.clone(),
            _ => {
                return Err(Error::Parser(ParserError::UnmatchedStepPop(id), position));
            }
        };

        // The conclusion of the premise. Premises of `step` commands in CPC proofs always conclude
        // a single formula
        let &[(premise_depth, premise_index)] = premises.as_slice() else {
            return Err(Error::Parser(
                ParserError::WrongNumberOfArgs(1.into(), premises.len()),
                position,
            ));
        };
        let premise_clause = stack[premise_depth].commands[premise_index].clause();
        let [premise_conclusion] = premise_clause else {
            return Err(Error::Parser(
                ParserError::WrongNumberOfArgs(1.into(), premise_clause.len()),
                position,
            ));
        };

        let conclusion = self.pool.add(Term::Op(
            Operator::Implies,
            vec![assumption, premise_conclusion.clone()],
        ));

        // The assumption discharged by this step is the first command of the subproof being closed
        let discharge = vec![(stack.len() - 1, 0)];

        Ok(ProofStep {
            id,
            clause: vec![conclusion],
            rule,
            premises,
            args,
            discharge,
        })
    }

    /// Parses the `:rule`, `:premises` and `:args` attributes of a `step` or `step-pop` command,
    /// including the closing `)` token.
    fn parse_cpc_step_attributes(
        &mut self,
    ) -> CarcaraResult<(String, Vec<(usize, usize)>, Vec<Rc<Term>>)> {
        self.expect_token(Token::Keyword("rule".into()))?;
        let rule = match self.next_token()? {
            (Token::Symbol(s), _) => s,
            (Token::ReservedWord(r), _) => format!("{}", r),
            (other, pos) => {
                return Err(Error::Parser(ParserError::UnexpectedToken(other), pos));
            }
        };

        // Unlike in Alethe proofs, the `:premises` and `:args` attributes may be empty
        let premises = if self.current_token == Token::Keyword("premises".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(Self::parse_step_premise, false)?
        } else {
            Vec::new()
        };

        let args = if self.current_token == Token::Keyword("args".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(Self::parse_term, false)?
        } else {
            Vec::new()
        };

        self.ignore_remaining_attributes()?;
        self.expect_token(Token::CloseParen)?;

        Ok((rule, premises, args))
    }

    /// Parses an application of a cvc5 internal symbol (e.g. `@list`, `@var`, `@purify`). This
    /// method assumes that the `(` token was already consumed, and that the current token is the
    /// internal symbol.
    pub(super) fn parse_cpc_application(&mut self) -> CarcaraResult<Rc<Term>> {
        let head_pos = self.current_position;
        let head = self.expect_symbol()?;
        match head.as_str() {
            // The "totalized" versions of division and modulo, which we map to the regular
            // operators (as does cvc5's own Alethe printer)
            "div_total" | "mod_total" | "/_total" => {
                let op = match head.as_str() {
                    "div_total" => Operator::IntDiv,
                    "mod_total" => Operator::Mod,
                    "/_total" => Operator::RealDiv,
                    _ => unreachable!(),
                };
                let args = self.parse_sequence(Self::parse_term, true)?;
                self.make_op(op, args)
                    .map_err(|err| Error::Parser(err, head_pos))
            }

            // A list of terms, e.g. `(@list a b)`. These appear as rule arguments and as the
            // variable lists of binders
            "@list" => {
                let args = self.parse_sequence(Self::parse_term, false)?;
                self.make_op(Operator::RareList, args)
                    .map_err(|err| Error::Parser(err, head_pos))
            }

            // A variable, e.g. `(@var "x" Int)`
            "@var" => {
                let name = match self.next_token()? {
                    (Token::String(s), _) => s,
                    (other, pos) => {
                        return Err(Error::Parser(ParserError::UnexpectedToken(other), pos));
                    }
                };
                let sort = self.parse_sort(false)?;
                self.expect_token(Token::CloseParen)?;
                Ok(self.pool.add(Term::Var(name, sort)))
            }

            // A purification skolem, e.g. `(@purify t)`, which abstracts the term `t`. We
            // represent it as an application of an uninterpreted function `@purify`, instantiated
            // at the sort of its argument
            "@purify" => {
                let arg = self.parse_term()?;
                self.expect_token(Token::CloseParen)?;
                let sort = self.pool.sort(&arg);
                Ok(self.make_cpc_skolem_app(&head, vec![sort.clone()], sort, vec![arg]))
            }

            // The skolem of the `i`-th variable of a quantified formula, e.g.
            // `(@quantifiers_skolemize F i)`
            "@quantifiers_skolemize" => {
                let quant = self.parse_term()?;
                let index = self.parse_term()?;
                self.expect_token(Token::CloseParen)?;

                // The sort of the skolem is the sort of the `i`-th bound variable
                let i = index
                    .as_integer()
                    .and_then(|i| i.to_usize())
                    .ok_or_else(|| {
                        Error::Parser(
                            ParserError::ExpectedIntegerConstant(index.clone()),
                            head_pos,
                        )
                    })?;
                let bindings = match quant.as_ref() {
                    Term::Binder(_, bindings, _) => bindings,
                    _ => {
                        return Err(Error::Parser(
                            ParserError::UnsupportedCpcSymbol(head),
                            head_pos,
                        ));
                    }
                };
                let var_sort = bindings
                    .0
                    .get(i)
                    .map(|(_, sort)| sort.clone())
                    .ok_or_else(|| {
                        Error::Parser(
                            ParserError::ExpectedIntegerConstant(index.clone()),
                            head_pos,
                        )
                    })?;

                let quant_sort = self.pool.sort(&quant);
                let index_sort = self.pool.sort(&index);
                Ok(self.make_cpc_skolem_app(
                    &head,
                    vec![quant_sort, index_sort],
                    var_sort,
                    vec![quant, index],
                ))
            }

            // The array diff skolem: `(@array_deq_diff a b)` denotes an index where the arrays
            // `a` and `b` differ, if they are not equal
            "@array_deq_diff" => {
                let a = self.parse_term()?;
                let b = self.parse_term()?;
                self.expect_token(Token::CloseParen)?;
                let array_sort = self.pool.sort(&a);
                let Some(Sort::Array(index_sort, _)) = array_sort.as_sort() else {
                    return Err(Error::Parser(
                        ParserError::UnsupportedCpcSymbol(head),
                        head_pos,
                    ));
                };
                let index_sort = index_sort.clone();
                Ok(self.make_cpc_skolem_app(
                    &head,
                    vec![array_sort.clone(), array_sort],
                    index_sort,
                    vec![a, b],
                ))
            }

            _ => Err(Error::Parser(
                ParserError::UnsupportedCpcSymbol(head),
                head_pos,
            )),
        }
    }

    /// Builds an application of a cvc5 internal skolem function. Since these functions are
    /// polymorphic, we instantiate a variable with the appropriate monomorphic function sort for
    /// each use.
    fn make_cpc_skolem_app(
        &mut self,
        name: &str,
        arg_sorts: Vec<Rc<Term>>,
        return_sort: Rc<Term>,
        args: Vec<Rc<Term>>,
    ) -> Rc<Term> {
        let mut sorts = arg_sorts;
        sorts.push(return_sort);
        let func_sort = self.pool.add(Term::Sort(Sort::Function(sorts)));
        let func = self.pool.add(Term::Var(name.to_owned(), func_sort));
        self.pool.add(Term::App(func, args))
    }

    /// Returns `true` if the current token is the head of an indexed operator, e.g. `extract` in
    /// `(_ extract 2 1)`.
    pub(super) fn current_is_indexed_op(&self) -> bool {
        use std::str::FromStr;
        match &self.current_token {
            Token::Symbol(s) => {
                let is_bv_value = s
                    .strip_prefix("bv")
                    .is_some_and(|v| v.parse::<rug::Integer>().is_ok());
                is_bv_value || ParamOperator::from_str(s).is_ok()
            }
            _ => false,
        }
    }

    /// Parses a higher-order function application, e.g. `(_ f x)`. This method assumes that the
    /// `(` and `_` tokens were already consumed. If the function term is a lambda (e.g. introduced
    /// by a function definition), the application is beta-reduced.
    pub(super) fn parse_cpc_ho_apply(&mut self) -> CarcaraResult<Rc<Term>> {
        let head_pos = self.current_position;
        let func = self.parse_term()?;
        let args = self.parse_sequence(Self::parse_term, true)?;
        if let Term::Binder(Binder::Lambda, bindings, inner) = func.as_ref() {
            let def = FunctionDef {
                params: bindings.0.clone(),
                body: inner.clone(),
            };
            def.apply(self.pool, args)
                .map_err(|err| Error::Parser(err, head_pos))
        } else {
            self.make_app(func, args)
                .map_err(|err| Error::Parser(err, head_pos))
        }
    }

    /// Parses a binder term in the CPC format, e.g. `(forall (@list (@var "x" Int)) <term>)`. This
    /// method assumes that the `(` and binder tokens were already consumed.
    pub(super) fn parse_cpc_binder(&mut self, binder: Binder) -> CarcaraResult<Rc<Term>> {
        let pos = self.current_position;
        let list = self.parse_term()?;
        let Term::Op(Operator::RareList, elements) = list.as_ref() else {
            return Err(Error::Parser(ParserError::ExpectedVarList(list), pos));
        };
        let bindings = elements
            .iter()
            .map(|element| match element.as_ref() {
                Term::Var(name, sort) => Ok((name.clone(), sort.clone())),
                _ => Err(Error::Parser(
                    ParserError::ExpectedVarList(list.clone()),
                    pos,
                )),
            })
            .collect::<Result<Vec<_>, _>>()?;

        let body = match binder {
            Binder::Lambda => self.parse_term()?,
            _ => self.parse_term_expecting_sort(&Sort::Bool)?,
        };
        self.expect_token(Token::CloseParen)?;
        Ok(self
            .pool
            .add(Term::Binder(binder, BindingList(bindings), body)))
    }
}
