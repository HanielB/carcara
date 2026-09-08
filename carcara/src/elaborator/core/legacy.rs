//! Reductions of the legacy quantifier rules `qnt_cnf` and `bfun_elim`.
//!
//! Both conclude one-directional implications, so no equivalence machinery is needed:
//!
//! - `qnt_cnf` concludes `(cl (or ¬(∀x̄.φ) (∀x̄ₖ.C)))` where `C` is one clause of the CNF of the
//!   prenexed negation normal form of `φ`. The reduction instantiates the left quantifier under
//!   an anchor over `x̄ₖ` (dropped variables at dummy `choice` witnesses) and derives the clause
//!   by a linear resolution chain against the CNF axioms — one decomposition step per connective
//!   on the path from `φ` to `C`'s literals, guided by the CNF of each candidate branch. The
//!   whole derivation is subproof-free except for the closing `bind`.
//! - `bfun_elim` (in its top-level form) expands a quantifier over Boolean variables into the
//!   conjunction of its `2^k` instances: `forall_inst` at each Boolean assignment, `and_neg` to
//!   repack, and a closing `bind` over the remaining variables.

use super::binder::{
    close_bind, connective_def_duality, double_negation, dummy_choice, excluded_middle, forall,
    forall_parts, instantiate, var_term,
};
use super::Builder;
use crate::checker::{
    apply_bfun_elim, conjunctive_normal_form, negation_normal_form, prenex_forall,
};
use crate::{ast::*, elaborator::error::ElaborationError};
use indexmap::IndexMap;
use std::collections::HashSet;

/// The CNF of a term at a polarity, mirroring the `qnt_cnf` checker (NNF, then `forall`
/// prenexing, then distribution), as clause literal-sets.
struct CnfOracle {
    memo: IndexMap<(Rc<Term>, bool), Vec<HashSet<Rc<Term>>>>,
}

impl CnfOracle {
    fn new() -> Self {
        Self { memo: IndexMap::new() }
    }

    fn clauses(
        &mut self,
        pool: &mut PrimitivePool,
        term: &Rc<Term>,
        polarity: bool,
    ) -> &[HashSet<Rc<Term>>] {
        let key = (term.clone(), polarity);
        if !self.memo.contains_key(&key) {
            let nnf = negation_normal_form(pool, term, polarity, &mut IndexMap::new());
            let mut vars: Vec<SortedVar> = Vec::new();
            let prenexed = prenex_forall(pool, &mut vars, &nnf);
            let cnf = conjunctive_normal_form(&prenexed);
            let clauses = cnf
                .into_iter()
                .map(|c| c.into_iter().collect::<HashSet<_>>())
                .collect();
            self.memo.insert(key.clone(), clauses);
        }
        &self.memo[&key]
    }

    /// Whether some CNF clause of the term (at the polarity) is contained in the target set.
    fn leads(
        &mut self,
        pool: &mut PrimitivePool,
        term: &Rc<Term>,
        polarity: bool,
        target: &HashSet<Rc<Term>>,
    ) -> bool {
        self.clauses(pool, term, polarity)
            .iter()
            .any(|c| c.is_subset(target))
    }
}

/// One decomposition step of the clausal descent: rewrites the element `e` of the current clause
/// through the appropriate CNF axiom, choosing branches whose CNF leads into the target.
/// Returns the updated clause node, or `None` when no rule applies.
#[allow(clippy::too_many_lines)]
fn decompose(
    b: &mut Builder,
    oracle: &mut CnfOracle,
    target: &HashSet<Rc<Term>>,
    rhs_vars: &HashSet<String>,
    current: Rc<ProofNode>,
    e: &Rc<Term>,
) -> Result<Option<Rc<ProofNode>>, ElaborationError> {
    let not_e = b.not(e);

    if let Some(f) = e.remove_negation() {
        let f = f.clone();
        // Negative-polarity decomposition
        if let Some(args) = match_term!((and ...) = f) {
            let mut clause = vec![f.clone()];
            for a in args {
                let na = b.not(a);
                clause.push(na);
            }
            let axiom = b.step(clause, "and_neg", Vec::new(), Vec::new());
            return Ok(Some(b.resolve(vec![current, axiom], vec![(f, false)])?));
        }
        if let Some(args) = match_term!((or ...) = f) {
            let args = args.to_vec();
            let Some(i) = args
                .iter()
                .position(|a| oracle.leads(b.pool, a, false, target))
            else {
                return Ok(None);
            };
            let na = b.not(&args[i]);
            let index = b.pool.add(Term::new_int(i));
            let axiom = b.step(vec![f.clone(), na], "or_neg", Vec::new(), vec![index]);
            return Ok(Some(b.resolve(vec![current, axiom], vec![(f, false)])?));
        }
        if let Some((p, q)) = match_term!((=> p q) = f) {
            let (p, q) = (p.clone(), q.clone());
            let axiom = if oracle.leads(b.pool, &p, true, target) {
                b.step(vec![f.clone(), p], "implies_neg1", Vec::new(), Vec::new())
            } else if oracle.leads(b.pool, &q, false, target) {
                let nq = b.not(&q);
                b.step(vec![f.clone(), nq], "implies_neg2", Vec::new(), Vec::new())
            } else {
                return Ok(None);
            };
            return Ok(Some(b.resolve(vec![current, axiom], vec![(f, false)])?));
        }
        if let Some((p, q)) = match_term!((= p q) = f) {
            if b.pool.sort(p).as_sort() != Some(&Sort::Bool) {
                return Ok(None);
            }
            let (p, q) = (p.clone(), q.clone());
            let (np, nq) = (b.not(&p), b.not(&q));
            let axiom = if oracle.leads(b.pool, &p, false, target)
                && oracle.leads(b.pool, &q, false, target)
            {
                b.step(
                    vec![f.clone(), np, nq],
                    "equiv_neg1",
                    Vec::new(),
                    Vec::new(),
                )
            } else if oracle.leads(b.pool, &p, true, target)
                && oracle.leads(b.pool, &q, true, target)
            {
                b.step(vec![f.clone(), p, q], "equiv_neg2", Vec::new(), Vec::new())
            } else {
                return Ok(None);
            };
            return Ok(Some(b.resolve(vec![current, axiom], vec![(f, false)])?));
        }
        if let Some((c, p, q)) = match_term!((ite c p q) = f) {
            let (c, p, q) = (c.clone(), p.clone(), q.clone());
            let axiom = if oracle.leads(b.pool, &c, true, target)
                && oracle.leads(b.pool, &q, false, target)
            {
                let nq = b.not(&q);
                b.step(vec![f.clone(), c, nq], "ite_neg1", Vec::new(), Vec::new())
            } else if oracle.leads(b.pool, &c, false, target)
                && oracle.leads(b.pool, &p, false, target)
            {
                let (nc, np) = (b.not(&c), b.not(&p));
                b.step(vec![f.clone(), nc, np], "ite_neg2", Vec::new(), Vec::new())
            } else {
                return Ok(None);
            };
            return Ok(Some(b.resolve(vec![current, axiom], vec![(f, false)])?));
        }
        if f.remove_negation().is_some() {
            // `e` is `¬¬g`: the `not_not` axiom `(cl ¬¬¬g g)` eliminates the double negation
            let g = f.remove_negation().unwrap().clone();
            let axiom = b.step(vec![not_e.clone(), g], "not_not", Vec::new(), Vec::new());
            return Ok(Some(
                b.resolve(vec![current, axiom], vec![(e.clone(), true)])?,
            ));
        }
        if let Some((Binder::Exists, bindings, inner)) =
            f.as_binder().map(|(q, bs, t)| (q, bs.clone(), t.clone()))
        {
            // ¬∃ becomes a ∀ through the duality, which the ∀ case then instantiates
            let ninner = b.not(&inner);
            let forall = b.pool.add(Term::Binder(Binder::Forall, bindings, ninner));
            let nforall = b.not(&forall);
            let equality = build_term!(b.pool, (= {f.clone()} {nforall.clone()}));
            let cd = b.step(
                vec![equality.clone()],
                "connective_def",
                Vec::new(),
                Vec::new(),
            );
            let nequality = b.not(&equality);
            let nnforall = b.not(&nforall);
            let equiv_pos1 = b.step(
                vec![nequality, f.clone(), nnforall.clone()],
                "equiv_pos1",
                Vec::new(),
                Vec::new(),
            );
            let f_nnf = b.resolve(vec![equiv_pos1, cd], vec![(equality, false)])?;
            // f_nnf: (cl f ¬¬(∀…)); not_not: (cl ¬¬¬(∀…) (∀…))
            let n3 = b.not(&nnforall);
            let not_not = b.step(vec![n3, forall.clone()], "not_not", Vec::new(), Vec::new());
            let f_forall = b.resolve(vec![f_nnf, not_not], vec![(nforall.clone(), true)])?;
            return Ok(Some(b.resolve(vec![current, f_forall], vec![(f, false)])?));
        }
        return Ok(None);
    }

    // Positive-polarity decomposition
    if let Some(args) = match_term!((and ...) = e) {
        let args = args.to_vec();
        let Some(i) = args
            .iter()
            .position(|a| oracle.leads(b.pool, a, true, target))
        else {
            return Ok(None);
        };
        let index = b.pool.add(Term::new_int(i));
        let axiom = b.step(
            vec![not_e, args[i].clone()],
            "and_pos",
            Vec::new(),
            vec![index],
        );
        return Ok(Some(
            b.resolve(vec![current, axiom], vec![(e.clone(), true)])?,
        ));
    }
    if let Some(args) = match_term!((or ...) = e) {
        let mut clause = vec![not_e];
        clause.extend(args.iter().cloned());
        let axiom = b.step(clause, "or_pos", Vec::new(), Vec::new());
        return Ok(Some(
            b.resolve(vec![current, axiom], vec![(e.clone(), true)])?,
        ));
    }
    if let Some((p, q)) = match_term!((=> p q) = e) {
        let (p, q) = (p.clone(), q.clone());
        let np = b.not(&p);
        let axiom = b.step(vec![not_e, np, q], "implies_pos", Vec::new(), Vec::new());
        return Ok(Some(
            b.resolve(vec![current, axiom], vec![(e.clone(), true)])?,
        ));
    }
    if let Some((p, q)) = match_term!((= p q) = e) {
        if b.pool.sort(p).as_sort() != Some(&Sort::Bool) {
            return Ok(None);
        }
        let (p, q) = (p.clone(), q.clone());
        let axiom = if oracle.leads(b.pool, &p, true, target)
            && oracle.leads(b.pool, &q, false, target)
        {
            let nq = b.not(&q);
            b.step(vec![not_e, p, nq], "equiv_pos1", Vec::new(), Vec::new())
        } else if oracle.leads(b.pool, &p, false, target) && oracle.leads(b.pool, &q, true, target)
        {
            let np = b.not(&p);
            b.step(vec![not_e, np, q], "equiv_pos2", Vec::new(), Vec::new())
        } else {
            return Ok(None);
        };
        return Ok(Some(
            b.resolve(vec![current, axiom], vec![(e.clone(), true)])?,
        ));
    }
    if let Some((c, p, q)) = match_term!((ite c p q) = e) {
        let (c, p, q) = (c.clone(), p.clone(), q.clone());
        let axiom = if oracle.leads(b.pool, &c, true, target)
            && oracle.leads(b.pool, &q, true, target)
        {
            b.step(vec![not_e, c, q], "ite_pos1", Vec::new(), Vec::new())
        } else if oracle.leads(b.pool, &c, false, target) && oracle.leads(b.pool, &p, true, target)
        {
            let nc = b.not(&c);
            b.step(vec![not_e, nc, p], "ite_pos2", Vec::new(), Vec::new())
        } else {
            return Ok(None);
        };
        return Ok(Some(
            b.resolve(vec![current, axiom], vec![(e.clone(), true)])?,
        ));
    }
    if let Some((Binder::Forall, bindings, _)) = e.as_binder().map(|(q, bs, t)| (q, bs.clone(), t))
    {
        // Instantiate at the same-named anchor variables (dummies for the dropped ones)
        let args: Vec<Rc<Term>> = bindings
            .iter()
            .map(|var| {
                if rhs_vars.contains(&var.0) {
                    var_term(b.pool, var)
                } else {
                    dummy_choice(b.pool, var)
                }
            })
            .collect();
        let (inst, _) = instantiate(b, e, args)?;
        return Ok(Some(
            b.resolve(vec![current, inst], vec![(e.clone(), true)])?,
        ));
    }
    Ok(None)
}

/// The legacy `qnt_cnf` rule.
pub fn qnt_cnf(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let keep = || Ok(Rc::new(ProofNode::Step(step.clone())));

    let Some((not_l, r)) = match_term!((or (not l) r) = &step.clause[0]) else {
        return keep();
    };
    let (l_term, r_term) = (not_l.clone(), r.clone());
    let Some((Binder::Forall, _, _)) = l_term.as_binder() else {
        return keep();
    };
    let Some((Binder::Forall, r_bindings, clause_term)) = r_term
        .as_binder()
        .map(|(q, bs, t)| (q, bs.0.clone(), t.clone()))
    else {
        return keep();
    };

    // The target literals: the clause's disjuncts (or the clause itself when unit)
    let target_literals: Vec<Rc<Term>> = match match_term!((or ...) = clause_term) {
        Some(args) => args.to_vec(),
        None => vec![clause_term.clone()],
    };
    let target: HashSet<Rc<Term>> = target_literals.iter().cloned().collect();
    let rhs_vars: HashSet<String> = r_bindings.iter().map(|(name, _)| name.clone()).collect();

    let mut b = Builder::new(pool, step);
    let mut oracle = CnfOracle::new();

    b.open();
    // Instantiate the left quantifier: kept variables at themselves, dropped ones at dummies
    let Some((_, l_bindings, _)) = l_term.as_binder().map(|(q, bs, t)| (q, bs.0.clone(), t)) else {
        return keep();
    };
    let inst_args: Vec<Rc<Term>> = l_bindings
        .iter()
        .map(|var| {
            if rhs_vars.contains(&var.0) {
                var_term(b.pool, var)
            } else {
                dummy_choice(b.pool, var)
            }
        })
        .collect();
    let (mut current, _) = instantiate(&mut b, &l_term, inst_args)?;
    let not_l_lit = b.not(&l_term);

    // The clausal descent: decompose every element outside the target until only target
    // literals (and the ¬L pass-through) remain
    let mut fuel = 10_000;
    loop {
        let next = current
            .clause()
            .iter()
            .find(|t| **t != not_l_lit && !target.contains(*t))
            .cloned();
        let Some(e) = next else { break };
        fuel -= 1;
        if fuel == 0 {
            return keep();
        }
        match decompose(&mut b, &mut oracle, &target, &rhs_vars, current, &e)? {
            Some(node) => current = node,
            None => return keep(),
        }
    }

    // Pack the target literals into the clause's `or` term (when it is a disjunction)
    if target_literals.len() > 1 || target_literals[0] != clause_term {
        for (i, lit) in target_literals.iter().enumerate() {
            if !current.clause().contains(lit) {
                continue;
            }
            let nl = b.not(lit);
            let index = b.pool.add(Term::new_int(i));
            let axiom = b.step(
                vec![clause_term.clone(), nl],
                "or_neg",
                Vec::new(),
                vec![index],
            );
            current = b.resolve(vec![current, axiom], vec![(lit.clone(), true)])?;
        }
    }
    if current.clause().len() != 2 {
        return keep();
    }

    // Close the clause over the right-hand bindings, then pack the conclusion's `or` term
    let index = current
        .clause()
        .iter()
        .position(|t| *t == clause_term)
        .unwrap();
    let closed = close_bind(&mut b, &r_bindings, &r_bindings, index, current);

    let conclusion_term = step.clause[0].clone();
    let mut packed = closed;
    for (i, lit) in [not_l_lit.clone(), r_term.clone()].iter().enumerate() {
        let nl = b.not(lit);
        let index = b.pool.add(Term::new_int(i));
        let axiom = b.step(
            vec![conclusion_term.clone(), nl],
            "or_neg",
            Vec::new(),
            vec![index],
        );
        packed = b.resolve(vec![packed, axiom], vec![(lit.clone(), true)])?;
    }
    Ok(b.relabel(step, packed))
}

/// The legacy `bfun_elim` rule. Its checker applies two independent transformations to the
/// premise: quantifiers over Boolean variables expand into the conjunction (or disjunction) of
/// their `2^k` instances — the *first step* — and applications with a non-constant Boolean
/// argument expand into an `ite` tree over that argument — the *second step*, which is applied
/// everywhere in the already-expanded term.
///
/// The reduction follows the same order. When the premise *is* a `forall` over Boolean variables,
/// its first step is derived as an implication by [`expand_bool_quantifier`], which is the cheaper
/// half of the equivalence and all this rule needs at that position. Everything below that — the
/// second step, and a first step at any other position — is an equivalence derived by [`rewrite`]
/// and crossed with the implication by one `equiv_pos2` axiom and a resolution. Either half may be
/// empty: a premise with nothing to expand at the top goes straight into the rewriting, and a
/// conclusion that the top-level expansion already reaches needs no rewriting.
///
/// What is not covered: an expansion under a `let` or a `choice`/`lambda` binder, and a
/// conclusion that is only *polyeq*-equal to the expansion (the `polyeq` pass normalizes that
/// upstream). In each case the rewriting does not reach the conclusion, and the step is kept.
pub fn bfun_elim(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let keep = || Ok(Rc::new(ProofNode::Step(step.clone())));

    let [premise] = step.premises.as_slice() else {
        return keep();
    };
    let premise = premise.clone();
    let [premise_term] = premise.clause() else {
        return keep();
    };
    let premise_term = premise_term.clone();
    let [conclusion] = step.clause.as_slice() else {
        return keep();
    };
    let conclusion = conclusion.clone();

    // The first step at the top of the premise, as an implication
    let expansion = bool_expansion(pool, &premise_term);
    let mut b = Builder::new(pool, step);
    let (first, first_term) = match &expansion {
        Some((non_bool, branches, expanded)) => {
            let node = expand_bool_quantifier(&mut b, &premise, &premise_term, non_bool, branches)?;
            (node, expanded.clone())
        }
        None => (premise, premise_term),
    };

    // Everything below it, as an equivalence between the expanded premise and the conclusion
    let rewriting = if first_term == conclusion {
        None
    } else {
        match rewrite(&mut b, &first_term)? {
            Some((node, target)) if target == conclusion => Some(node),
            _ => return keep(),
        }
    };

    let node = match rewriting {
        // The expansion concludes on its own; with no expansion either, there is nothing to reduce
        None if expansion.is_some() => first,
        None => return keep(),
        Some(rewriting) => {
            let equality = build_term!(b.pool, (= {first_term.clone()} {conclusion.clone()}));
            let not_equality = b.not(&equality);
            let not_first = b.not(&first_term);
            let equiv_pos2 = b.step(
                vec![not_equality, not_first, conclusion],
                "equiv_pos2",
                Vec::new(),
                Vec::new(),
            );
            let crossed = b.resolve(vec![equiv_pos2, rewriting], vec![(equality, false)])?;
            b.resolve(vec![crossed, first], vec![(first_term, false)])?
        }
    };
    Ok(b.relabel(step, node))
}

/// A quantifier's first step: the non-Boolean bindings that survive it, the Boolean assignments
/// paired with the instances they produce, and the term the expansion yields.
type Expansion = (
    Vec<SortedVar>,
    Vec<(IndexMap<Rc<Term>, Rc<Term>>, Rc<Term>)>,
    Rc<Term>,
);

/// The first step at the top of the premise. `None` when the premise is not a `forall` over
/// Boolean variables, and the first step therefore does nothing there.
fn bool_expansion(pool: &mut PrimitivePool, premise_term: &Rc<Term>) -> Option<Expansion> {
    let Some((Binder::Forall, bindings, body)) = premise_term
        .as_binder()
        .map(|(q, bs, t)| (q, bs.0.clone(), t.clone()))
    else {
        return None;
    };
    if !bindings.iter().any(is_bool_var) {
        return None;
    }
    let non_bool: Vec<SortedVar> = bindings
        .iter()
        .filter(|var| !is_bool_var(var))
        .cloned()
        .collect();

    let branches = assignments(pool, &bindings, &body);
    if branches.len() < 2 {
        return None;
    }
    let instances: Vec<Rc<Term>> = branches.iter().map(|(_, t)| t.clone()).collect();
    let conjunction = pool.add(Term::Op(Operator::And, instances));
    let expanded = if non_bool.is_empty() {
        conjunction
    } else {
        pool.add(Term::Binder(
            Binder::Forall,
            BindingList(non_bool.clone()),
            conjunction,
        ))
    };
    Some((non_bool, branches, expanded))
}

/// Derives the top-level first step's conclusion: the implication [`quantifier_implication`]
/// derives, resolved with the premise.
fn expand_bool_quantifier(
    b: &mut Builder,
    premise: &Rc<ProofNode>,
    premise_term: &Rc<Term>,
    non_bool: &[SortedVar],
    branches: &[(IndexMap<Rc<Term>, Rc<Term>>, Rc<Term>)],
) -> Result<Rc<ProofNode>, ElaborationError> {
    let instances: Vec<Rc<Term>> = branches.iter().map(|(_, t)| t.clone()).collect();
    let conjunction = b.pool.add(Term::Op(Operator::And, instances));
    let implication = quantifier_implication(
        b,
        premise_term,
        non_bool,
        branches,
        &conjunction,
        &Packing::Conjunction,
    )?;
    b.resolve(
        vec![implication, premise.clone()],
        vec![(premise_term.clone(), false)],
    )
}

/// The Boolean assignments of a binder list, paired with the instances of the body they produce,
/// in the checker's enumeration order (the last variable outermost, `false` before `true`).
fn assignments(
    pool: &mut PrimitivePool,
    bindings: &[SortedVar],
    body: &Rc<Term>,
) -> Vec<(IndexMap<Rc<Term>, Rc<Term>>, Rc<Term>)> {
    fn enumerate(
        pool: &mut PrimitivePool,
        bindings: &[SortedVar],
        term: &Rc<Term>,
        acc: &mut Vec<(IndexMap<Rc<Term>, Rc<Term>>, Rc<Term>)>,
        assignment: &mut IndexMap<Rc<Term>, Rc<Term>>,
    ) {
        match bindings {
            [] => {
                let mut substitution = Substitution::new(pool, assignment.clone()).unwrap();
                let instance = substitution.apply(pool, term);
                acc.push((assignment.clone(), instance));
            }
            [rest @ .., var] if var.1.as_sort() == Some(&Sort::Bool) => {
                let var_term = pool.add(var.clone().into());
                for value in [pool.bool_false(), pool.bool_true()] {
                    assignment.insert(var_term.clone(), value);
                    enumerate(pool, rest, term, acc, assignment);
                }
                assignment.swap_remove(&var_term);
            }
            [rest @ .., _] => enumerate(pool, rest, term, acc, assignment),
        }
    }

    let mut acc = Vec::new();
    enumerate(pool, bindings, body, &mut acc, &mut IndexMap::new());
    acc
}

/// The arguments that instantiate a quantifier at one Boolean assignment: the assigned value where
/// there is one, and the variable itself elsewhere.
fn instantiation_args(
    pool: &mut PrimitivePool,
    bindings: &[SortedVar],
    assignment: &IndexMap<Rc<Term>, Rc<Term>>,
) -> Vec<Rc<Term>> {
    bindings
        .iter()
        .map(|var| {
            let term = var_term(pool, var);
            assignment.get(&term).cloned().unwrap_or(term)
        })
        .collect()
}

/// Whether the sorted variable is Boolean, and so expanded by `bfun_elim`'s first step.
fn is_bool_var((_, sort): &SortedVar) -> bool {
    sort.as_sort() == Some(&Sort::Bool)
}

/// Whether `bfun_elim`'s second step expands an argument: it is Boolean, and not a constant.
fn is_expandable(pool: &mut PrimitivePool, term: &Rc<Term>) -> bool {
    let sort = pool.sort(term);
    sort.as_sort() == Some(&Sort::Bool) && !term.is_bool_true() && !term.is_bool_false()
}

/// The clause `(cl (= t ⊤) ¬t)` for `value = true`, and `(cl (= t ⊥) t)` for `value = false`: the
/// hypothesis a case split reasons under, as a *literal* rather than as an assumption. Built once
/// per reduction for each `(t, value)` at the base depth ([`Builder::leaf`]).
fn conditional_literal(
    b: &mut Builder,
    term: &Rc<Term>,
    value: bool,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let constant = if value {
        b.pool.bool_true()
    } else {
        b.pool.bool_false()
    };
    let equality = build_term!(b.pool, (= {term.clone()} {constant.clone()}));
    let literal = if value { b.not(term) } else { term.clone() };
    b.leaf(vec![equality.clone(), literal.clone()], |b| {
        let not_constant = b.not(&constant);
        if value {
            let neg = b.step(
                vec![equality, literal, not_constant],
                "equiv_neg1",
                Vec::new(),
                Vec::new(),
            );
            let axiom_term = constant.clone();
            let axiom = b.leaf(vec![constant.clone()], |b| {
                Ok(b.step(vec![axiom_term], "true", Vec::new(), Vec::new()))
            })?;
            b.resolve(vec![neg, axiom], vec![(constant, false)])
        } else {
            let neg = b.step(
                vec![equality, literal, constant.clone()],
                "equiv_neg2",
                Vec::new(),
                Vec::new(),
            );
            let axiom_term = not_constant.clone();
            let axiom = b.leaf(vec![not_constant], |b| {
                Ok(b.step(vec![axiom_term], "false", Vec::new(), Vec::new()))
            })?;
            b.resolve(vec![neg, axiom], vec![(constant, true)])
        }
    })
}

/// Derives `(cl (= lhs rhs) …)` for two applications, operations or indexed operations that differ
/// in some arguments, by the *clausal* congruence rule.
///
/// `eq_congruent` states one literal per argument pair, so every pair has to be discharged: the
/// ones that differ against the derivation given for them, the ones that do not against `refl`.
/// Whatever literals the given derivations carry — a case split's hypothesis, typically — end up
/// in the conclusion, which is the point of using `eq_congruent` over `cong`: `cong` would want
/// each hypothesis as a *unit* premise, and a conditional one only becomes a unit inside an
/// assumption.
fn clausal_congruence(
    b: &mut Builder,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
    args: &[Rc<Term>],
    new_args: &[Rc<Term>],
    justifications: Vec<Option<Rc<ProofNode>>>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let mut clause: Vec<Rc<Term>> = Vec::with_capacity(args.len() + 1);
    for (arg, new_arg) in args.iter().zip(new_args) {
        let equality = build_term!(b.pool, (= {arg.clone()} {new_arg.clone()}));
        clause.push(b.not(&equality));
    }
    clause.push(build_term!(b.pool, (= {lhs.clone()} {rhs.clone()})));
    let eq_congruent = b.step(clause, "eq_congruent", Vec::new(), Vec::new());

    let mut premises = vec![eq_congruent];
    let mut pivots = Vec::new();
    let mut discharged = HashSet::new();
    for ((arg, new_arg), justification) in args.iter().zip(new_args).zip(justifications) {
        let equality = build_term!(b.pool, (= {arg.clone()} {new_arg.clone()}));
        // Resolution reads the clause as a set, so a repeated argument pair is discharged once
        if !discharged.insert(equality.clone()) {
            continue;
        }
        let node = match justification {
            Some(node) => node,
            None => {
                let refl_eq = equality.clone();
                b.leaf(vec![equality.clone()], |b| {
                    Ok(b.step(vec![refl_eq], "refl", Vec::new(), Vec::new()))
                })?
            }
        };
        premises.push(node);
        pivots.push((equality, false));
    }
    b.resolve(premises, pivots)
}

/// Under the current anchor, derives `(cl L₁ … Lₖ (= ψ ψ[σ]))`: the body rewritten at the
/// assignment `σ` of Boolean variables to constants, under the hypothesis literals `Lᵢ` of the
/// variables that occur — `¬x` for `σ(x) = ⊤`, `x` for `σ(x) = ⊥`. Returns `None` when none
/// occurs, so that `ψ[σ]` is `ψ`.
///
/// The hypotheses are *assumed*, in a discharge subproof: that makes each `(= x v)` a unit,
/// which is what lets plain `cong` carry it up the body and the vanilla `bind` carry it through
/// a quantifier ([`unit_substitution`]). The clausal route the second step takes — hypothesis as
/// a literal, `eq_congruent` — cannot cross a binder, and its one advantage, that a *ground* case
/// split stays hoistable, does not apply here: this split is on the enclosing anchor's own
/// variables, so nothing in it is context-free to begin with.
fn case_split_substitution(
    b: &mut Builder,
    body: &Rc<Term>,
    assignment: &IndexMap<Rc<Term>, Rc<Term>>,
) -> Result<Option<(Rc<ProofNode>, Rc<Term>)>, ElaborationError> {
    let free = b.pool.free_vars_ref(body).clone();
    let split: Vec<(Rc<Term>, Rc<Term>)> = assignment
        .iter()
        .filter(|(var, _)| free.contains(*var))
        .map(|(var, value)| (var.clone(), value.clone()))
        .collect();
    if split.is_empty() {
        return Ok(None);
    }

    b.open();
    let mut assumptions = Vec::new();
    let mut units = IndexMap::new();
    for (var, value) in &split {
        let positive = value.is_bool_true();
        let hypothesis = if positive { var.clone() } else { b.not(var) };
        let assumption = b.assume(hypothesis);
        // `(cl (= x v) ∓x)` resolved with the assumption gives the unit `(cl (= x v))`
        let literal = conditional_literal(b, var, positive)?;
        let unit = b.resolve(
            vec![literal, assumption.clone()],
            vec![(var.clone(), !positive)],
        )?;
        assumptions.push(assumption);
        units.insert(var.clone(), (value.clone(), unit));
    }
    let (equality, target) =
        unit_substitution(b, body, &units)?.ok_or(ElaborationError::Inapplicable)?;
    let mut node = b.close_subproof(assumptions, equality);

    // A negative hypothesis comes back doubly negated: `not_not` turns `¬(not x)` into `x`
    for (var, value) in &split {
        if value.is_bool_true() {
            continue;
        }
        let not_var = b.not(var);
        let double = b.not(&not_var);
        let triple = b.not(&double);
        let not_not = b.step(vec![triple, var.clone()], "not_not", Vec::new(), Vec::new());
        node = b.resolve(vec![node, not_not], vec![(double, true)])?;
    }
    Ok(Some((node, target)))
}

/// Derives the unit `(cl (= t t[σ]))` from unit equalities `(cl (= x v))` for the substituted
/// variables: `cong` through applications, operations and indexed operations, with the changed
/// arguments' units as premises (`cong` skips the equal ones, so no `refl` is needed), and under a
/// `forall`/`exists` an anchor over its variables closed by the vanilla `bind` — unit in, unit
/// out. A binder that rebinds a substituted variable shadows it, and the walk drops that mapping
/// under it, as `Substitution::apply` does. Returns `None` when no substituted variable is free
/// in `t`.
///
/// A `choice`/`lambda` binder or a `let` with an occurrence under it is refused: `bind` over the
/// `choice` binder is what the core deliberately leaves out.
fn unit_substitution(
    b: &mut Builder,
    term: &Rc<Term>,
    units: &IndexMap<Rc<Term>, (Rc<Term>, Rc<ProofNode>)>,
) -> Result<Option<(Rc<ProofNode>, Rc<Term>)>, ElaborationError> {
    if let Some((value, unit)) = units.get(term) {
        return Ok(Some((unit.clone(), value.clone())));
    }
    let free = b.pool.free_vars_ref(term);
    if !units.keys().any(|var| free.contains(var)) {
        return Ok(None);
    }

    match term.as_ref() {
        Term::App(..) | Term::Op(..) | Term::ParamOp { .. } => {
            let args = match term.as_ref() {
                Term::App(_, args) | Term::Op(_, args) | Term::ParamOp { args, .. } => args.clone(),
                _ => unreachable!(),
            };
            let mut premises = Vec::new();
            let mut new_args = Vec::with_capacity(args.len());
            for arg in &args {
                match unit_substitution(b, arg, units)? {
                    Some((node, new_arg)) => {
                        premises.push(node);
                        new_args.push(new_arg);
                    }
                    None => new_args.push(arg.clone()),
                }
            }
            let rebuilt = match term.as_ref() {
                Term::App(func, _) => {
                    let func = func.clone();
                    b.pool.add(Term::App(func, new_args))
                }
                Term::Op(op, _) => {
                    let op = *op;
                    b.pool.add(Term::Op(op, new_args))
                }
                Term::ParamOp { op, op_args, .. } => {
                    let (op, op_args) = (*op, op_args.clone());
                    b.pool.add(Term::ParamOp { op, op_args, args: new_args })
                }
                _ => unreachable!(),
            };
            let clause = vec![build_term!(b.pool, (= {term.clone()} {rebuilt.clone()}))];
            Ok(Some((
                b.step(clause, "cong", premises, Vec::new()),
                rebuilt,
            )))
        }
        Term::Binder(binder, bindings, body)
            if matches!(binder, Binder::Forall | Binder::Exists) =>
        {
            let (binder, bindings, body) = (*binder, bindings.0.clone(), body.clone());
            let shadowed: HashSet<Rc<Term>> =
                bindings.iter().map(|var| var_term(b.pool, var)).collect();
            let inner_units: IndexMap<Rc<Term>, (Rc<Term>, Rc<ProofNode>)> = units
                .iter()
                .filter(|(var, _)| !shadowed.contains(*var))
                .map(|(var, unit)| (var.clone(), unit.clone()))
                .collect();
            b.open();
            let Some((inner, rewritten)) = unit_substitution(b, &body, &inner_units)? else {
                b.leave_scope();
                return Ok(None);
            };
            let rebuilt = b.pool.add(Term::Binder(
                binder,
                BindingList(bindings.clone()),
                rewritten,
            ));
            let clause = vec![build_term!(b.pool, (= {term.clone()} {rebuilt.clone()}))];
            let anchor_args = bindings
                .iter()
                .map(|var| AnchorArg::Variable(var.clone()))
                .collect();
            let node = b.close_with(anchor_args, "bind", clause, Vec::new(), inner);
            Ok(Some((node, rebuilt)))
        }
        _ => Err(ElaborationError::Inapplicable),
    }
}

/// How the instances of a Boolean-quantifier expansion are packed into the body of the expanded
/// quantifier.
enum Packing<'a> {
    /// `(and ψ[σ₁] … ψ[σₙ])`, the plain `forall` expansion.
    Conjunction,

    /// `(not (or φ[σ₁] … φ[σₙ]))`, where `ψ` is `(not φ)`: the shape the `exists` expansion needs
    /// on the other side of the quantifier duality. The disjuncts are the `φ[σⱼ]`, so that the
    /// branch bodies `ψ[σⱼ]` are their negations.
    NegatedDisjunction(&'a [Rc<Term>]),
}

/// The first step's implication at one quantifier: `(cl ¬(forall X. ψ) (forall ȳ. χ))`, where
/// `ȳ` are `X`'s non-Boolean variables and `χ` packs the `2^k` instances of `ψ`. One instantiation
/// per *distinct* instance — a binding that does not occur in the body makes two assignments
/// produce the same one, and the packing's clause is read as a set — packed by `and_neg` (or
/// `or_pos`, for the negated-disjunction packing) and closed over `ȳ` by the generalized `bind`.
fn quantifier_implication(
    b: &mut Builder,
    quant: &Rc<Term>,
    non_bool: &[SortedVar],
    branches: &[(IndexMap<Rc<Term>, Rc<Term>>, Rc<Term>)],
    packed: &Rc<Term>,
    packing: &Packing,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let (bindings, _) = forall_parts(quant).ok_or(ElaborationError::Inapplicable)?;
    if !non_bool.is_empty() {
        b.open();
    }
    let (packing_node, literals, polarity) = match packing {
        Packing::Conjunction => {
            let mut clause = vec![packed.clone()];
            for (_, instance) in branches {
                let negated = b.not(instance);
                clause.push(negated);
            }
            let literals: Vec<Rc<Term>> = branches.iter().map(|(_, i)| i.clone()).collect();
            (
                b.step(clause, "and_neg", Vec::new(), Vec::new()),
                literals,
                false,
            )
        }
        Packing::NegatedDisjunction(disjuncts) => {
            let mut clause = vec![packed.clone()];
            clause.extend(disjuncts.iter().cloned());
            let literals = disjuncts.to_vec();
            (
                b.step(clause, "or_pos", Vec::new(), Vec::new()),
                literals,
                true,
            )
        }
    };
    let mut premises = vec![packing_node];
    let mut pivots = Vec::new();
    let mut discharged = HashSet::new();
    for ((assignment, _), literal) in branches.iter().zip(literals) {
        if !discharged.insert(literal.clone()) {
            continue;
        }
        let args = instantiation_args(b.pool, &bindings, assignment);
        let (inst, _) = instantiate(b, quant, args)?;
        premises.push(inst);
        pivots.push((literal, polarity));
    }
    let packed_node = b.resolve(premises, pivots)?;
    if non_bool.is_empty() {
        return Ok(packed_node);
    }
    let index = packed_node
        .clause()
        .iter()
        .position(|t| t == packed)
        .ok_or(ElaborationError::Inapplicable)?;
    Ok(close_bind(b, non_bool, non_bool, index, packed_node))
}

/// The first step's equivalence at one quantifier: `(cl (= (forall X. ψ) (forall ȳ. χ)))`, where
/// `ȳ` are `X`'s non-Boolean variables and `χ` packs the `2^k` instances of `ψ`.
///
/// The → direction is [`quantifier_implication`], all `bfun_elim` needs at the top of a proof. The
/// ← direction is what an expansion at a *position inside* the premise costs, since a congruence
/// can only carry an equivalence: under an anchor over `X`, it takes each instance out of `χ` and
/// turns it back into `ψ` by a case split on the Boolean variables — [`case_split_substitution`]
/// rewrites `ψ` to `ψ[σ]` under the branch's hypotheses — and the `2^k` branches then resolve on
/// those variables and close over `X` with the generalized `bind`.
fn quantifier_equivalence(
    b: &mut Builder,
    quant: &Rc<Term>,
    non_bool: &[SortedVar],
    branches: &[(IndexMap<Rc<Term>, Rc<Term>>, Rc<Term>)],
    packed: &Rc<Term>,
    packing: &Packing,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let (bindings, body) = forall_parts(quant).ok_or(ElaborationError::Inapplicable)?;
    let rhs = forall(b.pool, non_bool.to_vec(), packed.clone());

    let forward = quantifier_implication(b, quant, non_bool, branches, packed, packing)?;

    // The ← direction, `(cl quant ¬rhs)`, under an anchor over all of `X`
    b.open();
    // `(cl ¬rhs χ)`: the instantiation of the expanded quantifier at the anchor's own variables.
    // With no quantifier left, `rhs` *is* `χ`: `and_pos` already concludes `(cl ¬rhs ψ[σ])` on
    // its own, and the negated-disjunction packing falls back on the excluded middle
    let available = match packing {
        _ if !non_bool.is_empty() => {
            let args = non_bool.iter().map(|var| var_term(b.pool, var)).collect();
            Some(instantiate(b, &rhs, args)?.0)
        }
        Packing::Conjunction => None,
        Packing::NegatedDisjunction(_) => Some(excluded_middle(b, &rhs)?),
    };
    let or_term = match packing {
        Packing::NegatedDisjunction(disjuncts) => {
            Some(b.pool.add(Term::Op(Operator::Or, disjuncts.to_vec())))
        }
        Packing::Conjunction => None,
    };

    let mut branch_nodes = Vec::new();
    for (index, (assignment, instance)) in branches.iter().enumerate() {
        // `(cl ψ[σ] ¬rhs)`: the instance selected out of the packing
        let position = b.pool.add(Term::new_int(index));
        let selected = match (packing, &or_term, &available) {
            (Packing::Conjunction, _, available) => {
                let not_packed = b.not(packed);
                let and_pos = b.step(
                    vec![not_packed, instance.clone()],
                    "and_pos",
                    Vec::new(),
                    vec![position],
                );
                match available {
                    Some(available) => b.resolve(
                        vec![available.clone(), and_pos],
                        vec![(packed.clone(), true)],
                    )?,
                    None => and_pos,
                }
            }
            (Packing::NegatedDisjunction(disjuncts), Some(or_term), Some(available)) => {
                let negated = b.not(&disjuncts[index]);
                let or_neg = b.step(
                    vec![or_term.clone(), negated],
                    "or_neg",
                    Vec::new(),
                    vec![position],
                );
                b.resolve(
                    vec![available.clone(), or_neg],
                    vec![(or_term.clone(), false)],
                )?
            }
            (Packing::NegatedDisjunction(_), _, _) => unreachable!(),
        };

        // `(cl ψ ¬rhs …)`: the case split turning the instance back into the body
        let node = match case_split_substitution(b, &body, assignment)? {
            None => selected,
            Some((equality_node, target)) => {
                if target != *instance {
                    return Err(ElaborationError::Inapplicable);
                }
                let equality = build_term!(b.pool, (= {body.clone()} {instance.clone()}));
                let (not_equality, not_instance) = (b.not(&equality), b.not(instance));
                let equiv_pos1 = b.step(
                    vec![not_equality, body.clone(), not_instance],
                    "equiv_pos1",
                    Vec::new(),
                    Vec::new(),
                );
                let lifted = b.resolve(vec![equiv_pos1, equality_node], vec![(equality, false)])?;
                b.resolve(vec![lifted, selected], vec![(instance.clone(), false)])?
            }
        };
        branch_nodes.push(node);
    }

    // Resolve the branches on the Boolean variables, in the order the enumeration varies them:
    // the first one fastest, so that adjacent branches differ in it alone
    let mut current = branch_nodes;
    for var in bindings.iter().filter(|var| is_bool_var(var)) {
        let variable = var_term(b.pool, var);
        let mut next = Vec::with_capacity(current.len() / 2);
        for pair in current.chunks(2) {
            let [on_false, on_true] = pair else {
                return Err(ElaborationError::Inapplicable);
            };
            // A variable that does not occur in the body leaves the two branches identical
            if on_false.clause().contains(&variable) {
                next.push(b.resolve(
                    vec![on_false.clone(), on_true.clone()],
                    vec![(variable.clone(), true)],
                )?);
            } else {
                next.push(on_false.clone());
            }
        }
        current = next;
    }
    let [last] = current.as_slice() else {
        return Err(ElaborationError::Inapplicable);
    };
    let index = last
        .clause()
        .iter()
        .position(|t| *t == body)
        .ok_or(ElaborationError::Inapplicable)?;
    let backward = close_bind(b, &bindings, &bindings, index, last.clone());

    b.equiv_intro(quant.clone(), rhs, forward, backward)
}

/// The first step at one quantifier, wherever it sits: derives `(cl (= (Q X. φ) (Q ȳ. op)))` for
/// the expansion the checker performs there, and composes it with the transformation of the
/// expansion itself.
///
/// A `forall` is [`quantifier_equivalence`] directly. An `exists` goes through the quantifier
/// duality: `(∃X.φ)` is `¬(∀X.¬φ)`, whose expansion is the same equivalence with the instances
/// packed as `(not (or φ[σ]))` — the shape that turns back into `(∃ȳ. (or φ[σ]))` under the
/// duality, with no De Morgan step in between.
fn bool_binder_rewrite(
    b: &mut Builder,
    term: &Rc<Term>,
    binder: Binder,
    bindings: &[SortedVar],
    body: &Rc<Term>,
) -> Result<Option<(Rc<ProofNode>, Rc<Term>)>, ElaborationError> {
    let non_bool: Vec<SortedVar> = bindings
        .iter()
        .filter(|var| !is_bool_var(var))
        .cloned()
        .collect();
    let branches = assignments(b.pool, bindings, body);
    if branches.len() < 2 {
        return Ok(None);
    }
    let instances: Vec<Rc<Term>> = branches.iter().map(|(_, t)| t.clone()).collect();
    let op = match binder {
        Binder::Forall => Operator::And,
        _ => Operator::Or,
    };
    let op_term = b.pool.add(Term::Op(op, instances.clone()));
    let expanded = if non_bool.is_empty() {
        op_term.clone()
    } else {
        b.pool.add(Term::Binder(
            binder,
            BindingList(non_bool.clone()),
            op_term.clone(),
        ))
    };

    let equivalence = if binder == Binder::Forall {
        quantifier_equivalence(
            b,
            term,
            &non_bool,
            &branches,
            &op_term,
            &Packing::Conjunction,
        )?
    } else {
        // `(= (∃X.φ) (not (∀X.¬φ)))`, and the same for the expanded side
        let not_body = b.not(body);
        let inner = forall(b.pool, bindings.to_vec(), not_body);
        let duality = connective_def_duality(b, term, &inner);

        // `(= (∀X.¬φ) (∀ȳ. ¬(or φ[σ])))`, whose branch bodies are the negated instances
        let negated: Vec<(IndexMap<Rc<Term>, Rc<Term>>, Rc<Term>)> = branches
            .iter()
            .map(|(assignment, instance)| (assignment.clone(), b.not(instance)))
            .collect();
        let packed = b.not(&op_term);
        let inner_equivalence = quantifier_equivalence(
            b,
            &inner,
            &non_bool,
            &negated,
            &packed,
            &Packing::NegatedDisjunction(&instances),
        )?;
        let expanded_inner = forall(b.pool, non_bool.clone(), packed);
        let (not_inner, not_expanded_inner) = (b.not(&inner), b.not(&expanded_inner));
        let clause = vec![build_term!(b.pool, (= {not_inner} {not_expanded_inner.clone()}))];
        let congruence = b.step(clause, "cong", vec![inner_equivalence], Vec::new());

        // Back through the duality: `(= ¬(∀ȳ. ¬(or φ[σ])) (∃ȳ. (or φ[σ])))`, which is a double
        // negation when there is no quantifier left
        let closing = if non_bool.is_empty() {
            double_negation(b, &op_term)?
        } else {
            let node = connective_def_duality(b, &expanded, &expanded_inner);
            b.symm(&node)
        };
        let clause = vec![build_term!(b.pool, (= {term.clone()} {expanded.clone()}))];
        b.step(
            clause,
            "trans",
            vec![duality, congruence, closing],
            Vec::new(),
        )
    };

    // The expansion is then transformed in turn: the second step, and any nested first step
    match rewrite(b, &expanded)? {
        None => Ok(Some((equivalence, expanded))),
        Some((node, target)) => {
            let clause = vec![build_term!(b.pool, (= {term.clone()} {target.clone()}))];
            let trans = b.step(clause, "trans", vec![equivalence, node], Vec::new());
            Ok(Some((trans, target)))
        }
    }
}

/// Derives `(cl (= t t'))`, where `t'` is the term `bfun_elim`'s checker computes from `t`: every
/// quantifier over Boolean variables expanded into its instances (the *first step*), and every
/// application of a non-constant Boolean argument replaced by its `ite` tree (the *second step*).
///
/// The expansions themselves come from [`bool_binder_rewrite`] and [`expand_app`]; this is the
/// congruence that carries them to the positions they sit at — `cong` through applications and
/// operations, `bind` through a quantifier that has nothing to expand. Returns `None` when nothing
/// in `t` changes.
///
/// A `let` body, and a `choice`/`lambda` body, are left alone: the equality would have to cross a
/// binder that `bind` does not close over here. Since the caller compares the term this returns
/// with the step's conclusion, an expansion missed that way costs the reduction, never soundness.
fn rewrite(
    b: &mut Builder,
    term: &Rc<Term>,
) -> Result<Option<(Rc<ProofNode>, Rc<Term>)>, ElaborationError> {
    match term.as_ref() {
        Term::App(func, args) => {
            let (func, args) = (func.clone(), args.clone());
            let (nodes, rewritten) = rewrite_args(b, &args)?;
            let applied = b.pool.add(Term::App(func.clone(), rewritten.clone()));
            let congruence = if nodes.is_empty() {
                None
            } else {
                let clause = vec![build_term!(b.pool, (= {term.clone()} {applied.clone()}))];
                Some(b.step(clause, "cong", nodes, Vec::new()))
            };
            match (congruence, expand_app(b, &func, &rewritten, 0)?) {
                (None, None) => Ok(None),
                (Some(congruence), None) => Ok(Some((congruence, applied))),
                (None, Some(expansion)) => Ok(Some(expansion)),
                (Some(congruence), Some((expansion, expanded))) => {
                    let clause = vec![build_term!(b.pool, (= {term.clone()} {expanded.clone()}))];
                    let trans = b.step(clause, "trans", vec![congruence, expansion], Vec::new());
                    Ok(Some((trans, expanded)))
                }
            }
        }
        Term::Op(op, args) => {
            let (op, args) = (*op, args.clone());
            let (nodes, rewritten) = rewrite_args(b, &args)?;
            if nodes.is_empty() {
                return Ok(None);
            }
            let rebuilt = b.pool.add(Term::Op(op, rewritten));
            let clause = vec![build_term!(b.pool, (= {term.clone()} {rebuilt.clone()}))];
            Ok(Some((b.step(clause, "cong", nodes, Vec::new()), rebuilt)))
        }
        Term::Binder(binder, bindings, body)
            if matches!(binder, Binder::Forall | Binder::Exists) =>
        {
            let (binder, bindings, body) = (*binder, bindings.0.clone(), body.clone());
            if bindings.iter().any(is_bool_var) {
                return bool_binder_rewrite(b, term, binder, &bindings, &body);
            }
            b.open();
            let Some((inner, rewritten)) = rewrite(b, &body)? else {
                b.leave_scope();
                return Ok(None);
            };
            let rebuilt = b.pool.add(Term::Binder(
                binder,
                BindingList(bindings.clone()),
                rewritten,
            ));
            let clause = vec![build_term!(b.pool, (= {term.clone()} {rebuilt.clone()}))];
            let anchor_args = bindings
                .iter()
                .map(|var| AnchorArg::Variable(var.clone()))
                .collect();
            let node = b.close_with(anchor_args, "bind", clause, Vec::new(), inner);
            Ok(Some((node, rebuilt)))
        }
        // A `let`, `choice` or `lambda` is not crossed; if the checker transforms something under
        // it, say so rather than let the conclusion mismatch downstream
        Term::Binder(..) | Term::Let(..) => {
            let transformed = apply_bfun_elim(b.pool, term, &mut IndexMap::new())
                .map_err(|_| ElaborationError::Inapplicable)?;
            if transformed == *term {
                Ok(None)
            } else {
                Err(ElaborationError::Inapplicable)
            }
        }
        _ => Ok(None),
    }
}

/// Rewrites the arguments of an application or an operation, returning the derivations of the ones
/// that changed, in argument order — which is the order `cong` consumes its premises in — and the
/// rewritten argument list.
fn rewrite_args(
    b: &mut Builder,
    args: &[Rc<Term>],
) -> Result<(Vec<Rc<ProofNode>>, Vec<Rc<Term>>), ElaborationError> {
    let mut nodes = Vec::new();
    let mut rewritten = Vec::with_capacity(args.len());
    for arg in args {
        match rewrite(b, arg)? {
            Some((node, term)) => {
                nodes.push(node);
                rewritten.push(term);
            }
            None => rewritten.push(arg.clone()),
        }
    }
    Ok((nodes, rewritten))
}

/// Derives `(cl (= (f args) T))`, where `T` is the `ite` tree that `bfun_elim`'s second step
/// builds for the arguments from `start` on: the first non-constant Boolean argument becomes the
/// condition of an `ite` whose branches are the expansions of the application with that argument
/// fixed to `⊤` and to `⊥`. Returns `None` when there is no such argument, and the application
/// stands as it is.
fn expand_app(
    b: &mut Builder,
    func: &Rc<Term>,
    args: &[Rc<Term>],
    start: usize,
) -> Result<Option<(Rc<ProofNode>, Rc<Term>)>, ElaborationError> {
    let Some(index) = (start..args.len()).find(|&i| is_expandable(b.pool, &args[i])) else {
        return Ok(None);
    };
    let cond = args[index].clone();
    let lhs = b.pool.add(Term::App(func.clone(), args.to_vec()));

    // The two branches, whose targets the `ite` is built from
    let mut branches = Vec::new();
    for value in [true, false] {
        let constant = if value {
            b.pool.bool_true()
        } else {
            b.pool.bool_false()
        };
        let mut branch_args = args.to_vec();
        branch_args[index] = constant;
        let applied = b.pool.add(Term::App(func.clone(), branch_args.clone()));
        let inner = expand_app(b, func, &branch_args, index + 1)?;
        let target = inner
            .as_ref()
            .map_or_else(|| applied.clone(), |(_, target)| target.clone());
        let inner = inner.map(|(node, _)| node);
        branches.push((value, branch_args, applied, inner, target));
    }
    let (then_target, else_target) = (branches[0].4.clone(), branches[1].4.clone());
    let ite = build_term!(b.pool, (ite {cond.clone()} {then_target} {else_target}));

    let mut sides = Vec::new();
    for (value, branch_args, applied, inner, target) in branches {
        sides.push(expand_branch(
            b,
            &lhs,
            &cond,
            value,
            args,
            &branch_args,
            &applied,
            inner,
            &target,
            &ite,
        )?);
    }
    let node = b.resolve(sides, vec![(cond, false)])?;
    Ok(Some((node, ite)))
}

/// One branch of [`expand_app`]: `(cl (= lhs T) ¬c)` under the condition, `(cl (= lhs T) c)` under
/// its negation.
///
/// The branch is subproof-free. The hypothesis it reasons under is only available as a *literal*
/// (see [`conditional_literal`]), and `cong`/`trans` take their hypotheses as unit premises —
/// which is what would force an assumption and a discharge. Their clausal variants `eq_congruent`
/// and `eq_transitive` state the same judgments as premise-free clauses, so the hypothesis stays a
/// literal and the whole branch is resolution: the selection axiom `ite_then_intro`/
/// `ite_else_intro` picks the branch out of the `ite`, and `eq_transitive` chains it with the
/// congruence. Staying subproof-free is also what lets a ground branch be shared: the sharing memo
/// only hoists a derivation that reaches no assumption and no subproof.
#[allow(clippy::too_many_arguments)]
fn expand_branch(
    b: &mut Builder,
    lhs: &Rc<Term>,
    cond: &Rc<Term>,
    value: bool,
    args: &[Rc<Term>],
    branch_args: &[Rc<Term>],
    applied: &Rc<Term>,
    inner: Option<Rc<ProofNode>>,
    target: &Rc<Term>,
    ite: &Rc<Term>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    // `(cl (= lhs (f args[i ↦ v])) ¬c)`, the conditional hypothesis carried into the application
    let conditional = conditional_literal(b, cond, value)?;
    let mut justifications: Vec<Option<Rc<ProofNode>>> = vec![None; args.len()];
    let position = args
        .iter()
        .zip(branch_args)
        .position(|(arg, branch_arg)| arg != branch_arg)
        .ok_or(ElaborationError::Inapplicable)?;
    justifications[position] = Some(conditional);
    let congruence = clausal_congruence(b, lhs, applied, args, branch_args, justifications)?;

    // The selection axiom, and the chain `lhs = (f args[i ↦ v]) = target = T`
    let rule = if value {
        "ite_then_intro"
    } else {
        "ite_else_intro"
    };
    let literal = if value { b.not(cond) } else { cond.clone() };
    let selection_eq = build_term!(b.pool, (= {ite.clone()} {target.clone()}));
    let selection = b.step(
        vec![literal, selection_eq.clone()],
        rule,
        Vec::new(),
        Vec::new(),
    );

    let applied_eq = build_term!(b.pool, (= {lhs.clone()} {applied.clone()}));
    let inner_eq = build_term!(b.pool, (= {applied.clone()} {target.clone()}));
    let mut chain = vec![b.not(&applied_eq)];
    if inner.is_some() {
        chain.push(b.not(&inner_eq));
    }
    chain.push(b.not(&selection_eq));
    chain.push(build_term!(b.pool, (= {lhs.clone()} {ite.clone()})));
    let eq_transitive = b.step(chain, "eq_transitive", Vec::new(), Vec::new());

    let mut premises = vec![eq_transitive, congruence];
    let mut pivots = vec![(applied_eq, false)];
    if let Some(inner) = inner {
        premises.push(inner);
        pivots.push((inner_eq, false));
    }
    premises.push(selection);
    pivots.push((selection_eq, false));
    b.resolve(premises, pivots)
}

/// Derives the selection tautology `(cl u)` for `u = (ite c e₁ e₂)`, where `e₁`/`e₂` are the
/// equalities `(= s r₁)`/`(= s r₂)` (either possibly flipped) for `s = (ite c r₁ r₂)`. The
/// selection axioms state the two branches outright — `ite_then_intro` is `(cl ¬c (= s r₁))`,
/// `ite_else_intro` is `(cl c (= s r₂))` — and the `ite_neg2`/`ite_neg1` axioms cross them into
/// `u`: five steps, subproof-free, plus two (`refl` + `cong`, then `equiv_pos2`) for an equality
/// the rule wrote the other way round.
#[allow(clippy::too_many_arguments)]
fn ite_selection_tautology(
    b: &mut Builder,
    u: &Rc<Term>,
    cond: &Rc<Term>,
    s: &Rc<Term>,
    r1: &Rc<Term>,
    r2: &Rc<Term>,
    e1: &Rc<Term>,
    e2: &Rc<Term>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let not_cond = b.not(cond);

    // `(cl ¬c e₁)`, then `(cl u ¬c)`
    let then_eq = build_term!(b.pool, (= {s.clone()} {r1.clone()}));
    let then_intro = b.step(
        vec![not_cond.clone(), then_eq.clone()],
        "ite_then_intro",
        Vec::new(),
        Vec::new(),
    );
    let then_side = oriented(b, then_intro, &then_eq, e1)?;
    let not_e1 = b.not(e1);
    let ite_neg2 = b.step(
        vec![u.clone(), not_cond, not_e1],
        "ite_neg2",
        Vec::new(),
        Vec::new(),
    );
    let true_side = b.resolve(vec![ite_neg2, then_side], vec![(e1.clone(), false)])?;

    // `(cl c e₂)`, then `(cl u c)`
    let else_eq = build_term!(b.pool, (= {s.clone()} {r2.clone()}));
    let else_intro = b.step(
        vec![cond.clone(), else_eq.clone()],
        "ite_else_intro",
        Vec::new(),
        Vec::new(),
    );
    let else_side = oriented(b, else_intro, &else_eq, e2)?;
    let not_e2 = b.not(e2);
    let ite_neg1 = b.step(
        vec![u.clone(), cond.clone(), not_e2],
        "ite_neg1",
        Vec::new(),
        Vec::new(),
    );
    let false_side = b.resolve(vec![ite_neg1, else_side], vec![(e2.clone(), false)])?;

    b.resolve(vec![true_side, false_side], vec![(cond.clone(), false)])
}

/// Turns a clause containing the equality `(= a b)` into the same clause with `target`, which is
/// either that equality itself (nothing to do) or its flip `(= b a)`. The flip goes through the
/// equivalence `(= (= a b) (= b a))`, which `cong` proves from one `refl` — its checker tries the
/// four orientations of a two-argument equality pair — and `equiv_pos2` applies.
fn oriented(
    b: &mut Builder,
    node: Rc<ProofNode>,
    equality: &Rc<Term>,
    target: &Rc<Term>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    if equality == target {
        return Ok(node);
    }
    let (a, _) = match_term_err!((= a b) = equality)?;
    let refl_eq = build_term!(b.pool, (= {a.clone()} {a.clone()}));
    let equivalence = build_term!(b.pool, (= {equality.clone()} {target.clone()}));
    if crate::checker::cong_equal(b.pool, &[refl_eq.clone()], &equivalence).is_err() {
        return Err(ElaborationError::Inapplicable);
    }
    let refl = b.leaf(vec![refl_eq.clone()], |b| {
        Ok(b.step(vec![refl_eq], "refl", Vec::new(), Vec::new()))
    })?;
    let cong = b.step(vec![equivalence.clone()], "cong", vec![refl], Vec::new());
    let (not_equivalence, not_equality) = (b.not(&equivalence), b.not(equality));
    let equiv_pos2 = b.step(
        vec![not_equivalence, not_equality, target.clone()],
        "equiv_pos2",
        Vec::new(),
        Vec::new(),
    );
    b.resolve(
        vec![equiv_pos2, cong, node],
        vec![(equivalence, false), (equality.clone(), false)],
    )
}

/// The legacy `ite_intro` rule: `(= t (and t u_1 … u_n))`, each `u_i` the selection tautology
/// `(ite c (= s r₁) (= s r₂))` (equalities possibly flipped) for an `ite` subterm
/// `s = (ite c r₁ r₂)` of `t`. Each `u_i` is derived by [`ite_selection_tautology`] from the
/// term-`ite` selection axioms, and the equivalence is packed by `and_neg`/`and_pos` and the
/// iff-introduction pattern.
pub fn ite_intro(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let keep = || Ok(Rc::new(ProofNode::Step(step.clone())));

    let Some((t, rhs)) = match_term!((= l r) = &step.clause[0]) else {
        return keep();
    };
    let (t, rhs) = (t.clone(), rhs.clone());
    // Degenerate instance concluding `(= t t)`
    if t == rhs {
        let b = Builder::new(pool, step);
        return Ok(b.finish(step, "refl", Vec::new(), Vec::new()));
    }
    let Some(us) = match_term!((and ...) = rhs) else {
        return keep();
    };
    let us = us.to_vec();
    if us[0] != t {
        return keep();
    }

    let mut b = Builder::new(pool, step);
    let mut units = Vec::new();
    for u in &us[1..] {
        let Some((cond, a1, a2, b1, b2)) = match_term!((ite cond (= a1 a2) (= b1 b2)) = u) else {
            return keep();
        };
        let (cond, a1, a2, b1, b2) = (cond.clone(), a1.clone(), a2.clone(), b1.clone(), b2.clone());
        // Find the shared `ite` term among the four sides
        let mut found = None;
        for (s, r1) in [(&a1, &a2), (&a2, &a1)] {
            for (other_s, r2) in [(&b1, &b2), (&b2, &b1)] {
                let expected: Rc<Term> =
                    build_term!(b.pool, (ite {cond.clone()} {(*r1).clone()} {(*r2).clone()}));
                if s == other_s && **s == *expected {
                    found = Some(((*s).clone(), (*r1).clone(), (*r2).clone()));
                }
            }
        }
        let Some((s, r1, r2)) = found else {
            return keep();
        };
        let e1 = build_term!(b.pool, (= {a1.clone()} {a2.clone()}));
        let e2 = build_term!(b.pool, (= {b1.clone()} {b2.clone()}));
        units.push(ite_selection_tautology(
            &mut b, u, &cond, &s, &r1, &r2, &e1, &e2,
        )?);
    }

    // `(cl rhs ¬t)` by `and_neg` + one resolution per tautology, then the iff-introduction
    let mut clause = vec![rhs.clone()];
    let mut pivots = Vec::new();
    for l in &us {
        let negated = b.not(l);
        clause.push(negated);
    }
    for u in &us[1..] {
        pivots.push((u.clone(), false));
    }
    let and_neg = b.step(clause, "and_neg", Vec::new(), Vec::new());
    let mut premises = vec![and_neg];
    premises.extend(units);
    let right = b.resolve(premises, pivots)?;

    let not_rhs = b.not(&rhs);
    let index = b.pool.add(Term::new_int(0));
    let left = b.step(vec![not_rhs, t.clone()], "and_pos", Vec::new(), vec![index]);
    let equivalence = b.equiv_intro(t, rhs, right, left)?;
    Ok(b.relabel(step, equivalence))
}
