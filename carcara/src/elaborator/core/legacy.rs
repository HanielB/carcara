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

use super::binder::{close_bind, dummy_choice, instantiate, var_term};
use super::Builder;
use crate::checker::{conjunctive_normal_form, negation_normal_form, prenex_forall};
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

/// Applies the Boolean assignments to the quantifier body in the checker's enumeration order
/// (the last variable outermost, `false` before `true`), collecting the instances.
fn enumerate(
    pool: &mut PrimitivePool,
    bindings: &[SortedVar],
    term: &Rc<Term>,
    acc: &mut Vec<Rc<Term>>,
    assignment: &mut IndexMap<Rc<Term>, Rc<Term>>,
) {
    match bindings {
        [] => {
            let mut substitution = Substitution::new(pool, assignment.clone()).unwrap();
            acc.push(substitution.apply(pool, term));
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

/// Collects the Boolean assignments themselves (name -> value), in the same order as
/// [`enumerate`].
fn build_assignments(
    pool: &mut PrimitivePool,
    bindings: &[SortedVar],
    out: &mut Vec<IndexMap<String, Rc<Term>>>,
    acc: &mut IndexMap<String, Rc<Term>>,
) {
    match bindings {
        [] => out.push(acc.clone()),
        [rest @ .., var] if var.1.as_sort() == Some(&Sort::Bool) => {
            for value in [pool.bool_false(), pool.bool_true()] {
                acc.insert(var.0.clone(), value);
                build_assignments(pool, rest, out, acc);
            }
            acc.swap_remove(&var.0);
        }
        [rest @ .., _] => build_assignments(pool, rest, out, acc),
    }
}

/// The legacy `bfun_elim` rule, in its top-level form: the premise is a `forall` over a mix of
/// Boolean and other variables, and the conclusion expands the Boolean ones into the conjunction
/// of the `2^k` instances (quantified over the rest).
pub fn bfun_elim(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let keep = || Ok(Rc::new(ProofNode::Step(step.clone())));

    let premise = match step.premises.as_slice() {
        [p] => p.clone(),
        _ => return keep(),
    };
    let [premise_term] = premise.clause() else {
        return keep();
    };
    let premise_term = premise_term.clone();
    let Some((Binder::Forall, bindings, body)) = premise_term
        .as_binder()
        .map(|(q, bs, t)| (q, bs.0.clone(), t.clone()))
    else {
        return keep();
    };
    let has_bool = bindings
        .iter()
        .any(|(_, sort)| sort.as_sort() == Some(&Sort::Bool));
    if !has_bool {
        return keep();
    }
    let non_bool: Vec<SortedVar> = bindings
        .iter()
        .filter(|(_, sort)| sort.as_sort() != Some(&Sort::Bool))
        .cloned()
        .collect();

    let mut instances = Vec::new();
    enumerate(pool, &bindings, &body, &mut instances, &mut IndexMap::new());
    if instances.len() < 2 {
        return keep();
    }

    // The expected conclusion, for the top-level-only form
    let conjunction = pool.add(Term::Op(Operator::And, instances.clone()));
    let expected = if non_bool.is_empty() {
        conjunction.clone()
    } else {
        pool.add(Term::Binder(
            Binder::Forall,
            BindingList(non_bool.clone()),
            conjunction.clone(),
        ))
    };
    if step.clause.as_slice() != [expected.clone()] {
        return keep();
    }

    let mut b = Builder::new(pool, step);
    let use_anchor = !non_bool.is_empty();
    if use_anchor {
        b.open();
    }

    // One instantiation per Boolean assignment; note the argument order follows the binding
    // list, with the checker's assignment enumeration
    let mut assignments: Vec<Vec<Rc<Term>>> = Vec::new();
    let mut maps = Vec::new();
    build_assignments(b.pool, &bindings, &mut maps, &mut IndexMap::new());
    for map in &maps {
        let args: Vec<Rc<Term>> = bindings
            .iter()
            .map(|var| match map.get(&var.0) {
                Some(value) => value.clone(),
                None => var_term(b.pool, var),
            })
            .collect();
        assignments.push(args);
    }

    let mut inst_nodes = Vec::new();
    for args in assignments {
        let (inst, _) = instantiate(&mut b, &premise_term, args)?;
        inst_nodes.push(inst);
    }

    // Repack with `and_neg` and close over the remaining variables
    let mut clause = vec![conjunction.clone()];
    let mut pivots = Vec::new();
    for i in &instances {
        let ni = b.not(i);
        clause.push(ni);
        pivots.push((i.clone(), false));
    }
    let and_neg = b.step(clause, "and_neg", Vec::new(), Vec::new());
    let mut premises = vec![and_neg];
    premises.extend(inst_nodes);
    let packed = b.resolve(premises, pivots)?;

    let closed = if use_anchor {
        let index = packed
            .clause()
            .iter()
            .position(|t| *t == conjunction)
            .unwrap();
        close_bind(&mut b, &non_bool, &non_bool, index, packed)
    } else {
        packed
    };

    // Resolve with the premise to conclude
    let node = b.resolve(vec![closed, premise], vec![(premise_term, false)])?;
    Ok(b.relabel(step, node))
}
