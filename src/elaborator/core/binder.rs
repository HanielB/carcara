//! Reductions of the quantifier rewrites, through the generalized `bind` (divergence 8 of the
//! core-fragment proposal): quantifiers are eliminated by `forall_inst` at the anchor's own
//! variables and reintroduced by the generalization's closure, so the derivations are witness-free
//! and linear.
//!
//! Only the `forall` versions are covered — the `exists` versions route through the quantifier
//! duality and are left untouched for now.

use super::Builder;
use crate::{ast::*, elaborator::error::ElaborationError};
use indexmap::IndexMap;

/// Deconstructs a `forall` term into its bindings and body.
pub(super) fn forall_parts(term: &Rc<Term>) -> Option<(Vec<SortedVar>, Rc<Term>)> {
    match term.as_ref() {
        Term::Binder(Binder::Forall, bindings, body) => Some((bindings.0.clone(), body.clone())),
        _ => None,
    }
}

pub(super) fn forall(
    pool: &mut PrimitivePool,
    bindings: Vec<SortedVar>,
    body: Rc<Term>,
) -> Rc<Term> {
    if bindings.is_empty() {
        body
    } else {
        pool.add(Term::Binder(Binder::Forall, BindingList(bindings), body))
    }
}

pub(super) fn var_term(pool: &mut PrimitivePool, var: &SortedVar) -> Rc<Term> {
    pool.add(var.clone().into())
}

/// A canonical inhabitant of the variable's sort, for instantiating a quantifier over a variable
/// that does not occur in its body: `(choice ((x S)) true)`.
pub(super) fn dummy_choice(pool: &mut PrimitivePool, var: &SortedVar) -> Rc<Term> {
    let body = pool.bool_true();
    pool.add(Term::Binder(
        Binder::Choice,
        BindingList(vec![var.clone()]),
        body,
    ))
}

/// Emits the instantiation of `quant = (forall bindings. body)` at the given argument terms
/// (aligned with the bindings): a `forall_inst` step followed by its `or_pos` unpacking,
/// concluding `(cl (not quant) body[args])`. Returns the concluding node and the instantiated
/// body.
pub(super) fn instantiate(
    b: &mut Builder,
    quant: &Rc<Term>,
    args: Vec<Rc<Term>>,
) -> Result<(Rc<ProofNode>, Rc<Term>), ElaborationError> {
    let (bindings, body) = forall_parts(quant).unwrap();
    assert_eq!(bindings.len(), args.len());

    let mut substitution = IndexMap::new();
    for (var, value) in bindings.iter().zip(&args) {
        // Identity entries are skipped: the variable is instantiated at itself
        let (name, sort) = var;
        let is_identity = value.as_var() == Some(name.as_str()) && b.pool.sort(value) == *sort;
        if !is_identity {
            substitution.insert(var_term(b.pool, var), value.clone());
        }
    }
    let instantiated = if substitution.is_empty() {
        body
    } else {
        let mut substitution = Substitution::new(b.pool, substitution)
            .map_err(crate::checker::error::CheckerError::from)?;
        substitution.apply(b.pool, &body)
    };

    let not_quant = b.not(quant);
    let or_term = b.pool.add(Term::Op(
        Operator::Or,
        vec![not_quant.clone(), instantiated.clone()],
    ));
    let forall_inst = b.step(vec![or_term.clone()], "forall_inst", Vec::new(), args);
    let not_or_term = b.not(&or_term);
    let or_pos = b.step(
        vec![not_or_term, not_quant, instantiated.clone()],
        "or_pos",
        Vec::new(),
        Vec::new(),
    );
    let node = b.resolve(vec![or_pos, forall_inst], vec![(or_term, false)])?;
    Ok((node, instantiated))
}

/// Closes the current anchor with a generalized `bind` step: the literal at `closure_index` of
/// `last_inner`'s clause is wrapped as `(forall closure_vars. l)`, the others pass through.
pub(super) fn close_bind(
    b: &mut Builder,
    anchor_vars: &[SortedVar],
    closure_vars: &[SortedVar],
    closure_index: usize,
    last_inner: Rc<ProofNode>,
) -> Rc<ProofNode> {
    let mut clause = last_inner.clause().to_vec();
    clause[closure_index] = forall(b.pool, closure_vars.to_vec(), clause[closure_index].clone());
    let anchor_args = anchor_vars
        .iter()
        .map(|var| AnchorArg::Variable(var.clone()))
        .collect();
    b.close_with(anchor_args, "bind", clause, Vec::new(), last_inner)
}

pub(super) fn has_duplicate_names(bindings: &[SortedVar]) -> bool {
    let mut seen = std::collections::HashSet::new();
    bindings.iter().any(|(name, _)| !seen.insert(name))
}

/// Emits the excluded-middle clause `(cl (not phi) phi)`, via `refl` and `equiv_pos2`.
pub(super) fn excluded_middle(
    b: &mut Builder,
    phi: &Rc<Term>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let eq = build_term!(b.pool, (= {phi.clone()} {phi.clone()}));
    let refl = b.step(vec![eq.clone()], "refl", Vec::new(), Vec::new());
    let (not_eq, not_phi) = (b.not(&eq), b.not(phi));
    let equiv_pos2 = b.step(
        vec![not_eq, not_phi, phi.clone()],
        "equiv_pos2",
        Vec::new(),
        Vec::new(),
    );
    b.resolve(vec![equiv_pos2, refl], vec![(eq, false)])
}

/// `qnt_simplify` rewrites `(forall X. c) ≈ c` for a constant `c`: the `true` case derives both
/// sides outright (the left by a unit closure), the `false` case refutes both (the left by
/// instantiation at dummy `choice` witnesses).
pub fn qnt_simplify(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let Some((lhs, rhs)) = match_term!((= l r) = &step.clause[0]) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    let (lhs, rhs) = (lhs.clone(), rhs.clone());
    let Some((bindings, body)) = forall_parts(&lhs) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };

    let mut b = Builder::new(pool, step);
    let equivalence = build_term!(b.pool, (= {lhs.clone()} {rhs.clone()}));

    let node = if body.is_bool_true() {
        // Derive both sides: `(cl (forall X. true))` by unit closure, `(cl true)` directly
        b.open();
        let t = b.pool.bool_true();
        let inner_true = b.step(vec![t], "true", Vec::new(), Vec::new());
        let closed = close_bind(&mut b, &bindings, &bindings, 0, inner_true);
        let t = b.pool.bool_true();
        let outer_true = b.step(vec![t], "true", Vec::new(), Vec::new());
        let (not_lhs, not_rhs) = (b.not(&lhs), b.not(&rhs));
        let equiv_neg1 = b.step(
            vec![equivalence, not_lhs, not_rhs],
            "equiv_neg1",
            Vec::new(),
            Vec::new(),
        );
        b.resolve(
            vec![equiv_neg1, closed, outer_true],
            vec![(lhs, false), (rhs, false)],
        )?
    } else if body.is_bool_false() {
        // Refute both sides: `(cl (not (forall X. false)))` by instantiation at dummies,
        // `(cl (not false))` directly
        let not_false = {
            let f = b.pool.bool_false();
            let clause = vec![b.not(&f)];
            b.step(clause, "false", Vec::new(), Vec::new())
        };
        let dummies = bindings.iter().map(|v| dummy_choice(b.pool, v)).collect();
        let (inst, _) = instantiate(&mut b, &lhs, dummies)?;
        let f = b.pool.bool_false();
        let not_lhs_step = b.resolve(vec![inst, not_false.clone()], vec![(f, true)])?;
        let equiv_neg2 = b.step(
            vec![equivalence, lhs.clone(), rhs.clone()],
            "equiv_neg2",
            Vec::new(),
            Vec::new(),
        );
        b.resolve(
            vec![equiv_neg2, not_lhs_step, not_false],
            vec![(lhs, true), (rhs, true)],
        )?
    } else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    Ok(b.relabel(step, node))
}

/// The binder list with the shadowed occurrences dropped, in order of first occurrence.
///
/// A repeated name in a binder list only ever binds through its *last* occurrence, so the earlier
/// ones are vacuous: `(Q L. phi)` and `(Q dedup(L). phi)` are the same quantifier, and the rule's
/// checker sees no difference either — it collects both binder lists into sets. Returns `None`
/// when a name occurs at two different sorts, since the two occurrences are then different
/// variables and dropping either would change the term.
fn dedup_bindings(bindings: &[SortedVar]) -> Option<Vec<SortedVar>> {
    let mut distinct: Vec<SortedVar> = Vec::new();
    for var in bindings {
        if let Some(seen) = distinct.iter().find(|(name, _)| *name == var.0) {
            if seen.1 != var.1 {
                return None;
            }
        } else {
            distinct.push(var.clone());
        }
    }
    Some(distinct)
}

fn quantify(
    pool: &mut PrimitivePool,
    binder: Binder,
    bindings: &[SortedVar],
    body: &Rc<Term>,
) -> Rc<Term> {
    pool.add(Term::Binder(
        binder,
        BindingList(bindings.to_vec()),
        body.clone(),
    ))
}

/// Rewrites the binder list of a quantifier into an equivalent one — the same variables, with the
/// repetitions dropped — with a plain `bind` step over a `refl`. The rule compares the two binder
/// lists as sets, so this is exactly the normalization it licenses.
fn normalize_bindings(
    b: &mut Builder,
    from: &Rc<Term>,
    to: &Rc<Term>,
    bindings: &[SortedVar],
) -> Rc<ProofNode> {
    let body = from.as_quant().unwrap().2.clone();
    let anchor_args = bindings
        .iter()
        .map(|var| AnchorArg::Variable(var.clone()))
        .collect();
    b.open();
    let equality = build_term!(b.pool, (= {body.clone()} {body}));
    let refl = b.step(vec![equality], "refl", Vec::new(), Vec::new());
    let clause = vec![build_term!(b.pool, (= {from.clone()} {to.clone()}))];
    b.close_with(anchor_args, "bind", clause, Vec::new(), refl)
}

/// `qnt_rm_unused` rewrites `(Q L. phi) ≈ (Q R. phi)` where `R` and `L` have the same variables
/// but for some that do not occur in `phi` (the right side may be `phi` itself, when they all go).
///
/// The rule reads both binder lists as *sets*, so `L` and `R` may repeat variables and may list
/// the survivors in any order. The repetitions are normalized away first, by a `bind` step on
/// either side; between the normalized quantifiers, both directions of the equivalence instantiate
/// at anchor variables and close over the appropriate subset.
pub fn qnt_rm_unused(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let keep = || Ok(Rc::new(ProofNode::Step(step.clone())));

    let Some((lhs, rhs)) = match_term!((= l r) = &step.clause[0]) else {
        return keep();
    };
    let (lhs, rhs) = (lhs.clone(), rhs.clone());
    let Some((quant, left_bindings, body)) = lhs
        .as_quant()
        .map(|(q, bindings, body)| (q, bindings.0.clone(), body.clone()))
    else {
        return keep();
    };
    if !matches!(quant, Binder::Forall | Binder::Exists) {
        return keep();
    }
    let right_bindings = match rhs.as_quant() {
        Some((q, bindings, right_body)) => {
            if q != quant || *right_body != body {
                return keep();
            }
            bindings.0.clone()
        }
        None if rhs == body => Vec::new(),
        None => return keep(),
    };
    let (Some(left_distinct), Some(right_distinct)) = (
        dedup_bindings(&left_bindings),
        dedup_bindings(&right_bindings),
    ) else {
        return keep();
    };
    if right_distinct
        .iter()
        .any(|var| !left_distinct.contains(var))
    {
        return keep();
    }

    let mut b = Builder::new(pool, step);
    let left_normal = quantify(b.pool, quant, &left_distinct, &body);
    let right_normal = if right_bindings.is_empty() {
        rhs.clone()
    } else {
        quantify(b.pool, quant, &right_distinct, &body)
    };

    // The reduction is a chain of up to three links: normalize the left binder list, remove the
    // unused variables, normalize the right binder list back
    let normalize_left = left_normal != lhs;
    let normalize_right = right_normal != rhs;
    let remove = left_normal != right_normal;
    match (normalize_left, remove, normalize_right) {
        // The two sides are the same quantifier written the same way
        (false, false, false) => Ok(b.finish(step, "refl", Vec::new(), Vec::new())),

        // A single link, which takes the step's own identity
        (true, false, false) | (false, false, true) => {
            let bindings = if normalize_left {
                &left_distinct
            } else {
                &right_distinct
            };
            let anchor_args = bindings
                .iter()
                .map(|var| AnchorArg::Variable(var.clone()))
                .collect();
            b.open();
            let equality = build_term!(b.pool, (= {body.clone()} {body.clone()}));
            let refl = b.step(vec![equality], "refl", Vec::new(), Vec::new());
            Ok(b.close_finish(
                step,
                anchor_args,
                "bind",
                Vec::new(),
                Vec::new(),
                Vec::new(),
                refl,
            ))
        }
        (false, true, false) => {
            let node = rm_unused_equality(
                &mut b,
                quant,
                &lhs,
                &rhs,
                &left_distinct,
                &right_distinct,
                &body,
            )?;
            Ok(b.relabel(step, node))
        }

        _ => {
            let mut links = Vec::new();
            if normalize_left {
                links.push(normalize_bindings(
                    &mut b,
                    &lhs,
                    &left_normal,
                    &left_distinct,
                ));
            }
            if remove {
                links.push(rm_unused_equality(
                    &mut b,
                    quant,
                    &left_normal,
                    &right_normal,
                    &left_distinct,
                    &right_distinct,
                    &body,
                )?);
            }
            if normalize_right {
                links.push(normalize_bindings(
                    &mut b,
                    &right_normal,
                    &rhs,
                    &right_distinct,
                ));
            }
            let clause = vec![build_term!(b.pool, (= {lhs.clone()} {rhs.clone()}))];
            let node = b.step(clause, "trans", links, Vec::new());
            Ok(b.relabel(step, node))
        }
    }
}

/// Derives `(cl (= lhs rhs))` for the binder-list removal proper, both binder lists being free of
/// repetitions. The `exists` case routes through the quantifier duality of `connective_def`, so
/// that the removal itself always happens on a `forall`.
fn rm_unused_equality(
    b: &mut Builder,
    quant: Binder,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
    left_bindings: &[SortedVar],
    right_bindings: &[SortedVar],
    body: &Rc<Term>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    if quant == Binder::Forall {
        return rm_unused_derivation(b, lhs, rhs, left_bindings, right_bindings, body);
    }

    let not_body = b.not(body);
    let left_dual = quantify(b.pool, Binder::Forall, left_bindings, &not_body);
    let duality = connective_def_duality(b, lhs, &left_dual);
    // When every variable goes, the right-hand side is `phi` itself and its dual is just `¬phi`,
    // which the double-negation equivalence closes; otherwise the duality closes it
    let (right_dual, closing) = if right_bindings.is_empty() {
        (not_body.clone(), None)
    } else {
        let dual = quantify(b.pool, Binder::Forall, right_bindings, &not_body);
        let duality = connective_def_duality(b, rhs, &dual);
        let flipped = b.symm(&duality);
        (dual, Some(flipped))
    };

    let removal = rm_unused_derivation(
        b,
        &left_dual,
        &right_dual,
        left_bindings,
        right_bindings,
        &not_body,
    )?;
    let (not_left_dual, not_right_dual) = (b.not(&left_dual), b.not(&right_dual));
    let clause = vec![build_term!(b.pool, (= {not_left_dual} {not_right_dual}))];
    let congruence = b.step(clause, "cong", vec![removal], Vec::new());

    let closing = match closing {
        Some(closing) => closing,
        None => double_negation(b, body)?,
    };
    let clause = vec![build_term!(b.pool, (= {lhs.clone()} {rhs.clone()}))];
    Ok(b.step(
        clause,
        "trans",
        vec![duality, congruence, closing],
        Vec::new(),
    ))
}

/// The `connective_def` duality instance `(= (exists X. phi) (not (forall X. (not phi))))`.
pub(super) fn connective_def_duality(
    b: &mut Builder,
    exists: &Rc<Term>,
    dual: &Rc<Term>,
) -> Rc<ProofNode> {
    let not_dual = b.not(dual);
    let clause = vec![build_term!(b.pool, (= {exists.clone()} {not_dual}))];
    b.step(clause, "connective_def", Vec::new(), Vec::new())
}

/// The equivalence `(= (not (not phi)) phi)`: `not_not` one way, the excluded middle the other.
fn double_negation(b: &mut Builder, phi: &Rc<Term>) -> Result<Rc<ProofNode>, ElaborationError> {
    let not_phi = b.not(phi);
    let not_not_phi = b.not(&not_phi);
    let triple = b.not(&not_not_phi);
    let forward = b.step(vec![triple, phi.clone()], "not_not", Vec::new(), Vec::new());
    let backward = excluded_middle(b, &not_phi)?;
    b.equiv_intro(not_not_phi, phi.clone(), forward, backward)
}

/// The anchor variables to declare so that a closure over `closure` is legal: the generalized
/// `bind` wants the closure to be a subsequence of the anchor, so the anchor is `vars` itself when
/// that already holds, and `closure` moved to the front otherwise — the rule puts no order on the
/// surviving binder list.
fn anchor_covering(vars: &[SortedVar], closure: &[SortedVar]) -> Vec<SortedVar> {
    let mut remaining = vars.iter();
    if closure
        .iter()
        .all(|var| remaining.any(|declared| declared == var))
    {
        return vars.to_vec();
    }
    let mut anchor = closure.to_vec();
    anchor.extend(vars.iter().filter(|var| !closure.contains(var)).cloned());
    anchor
}

/// Derives `(cl (= lhs rhs))` for a `forall` binder-list removal, neither list repeating a
/// variable: both directions instantiate at anchor variables and close over the appropriate
/// subset.
fn rm_unused_derivation(
    b: &mut Builder,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
    left_bindings: &[SortedVar],
    right_bindings: &[SortedVar],
    body: &Rc<Term>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    // Direction →: instantiate the left side at the anchor variables and close over `R`
    let forward = if right_bindings.is_empty() {
        // The right side is `phi` itself: instantiate at dummy witnesses, no anchor needed
        let dummies = left_bindings
            .iter()
            .map(|v| dummy_choice(b.pool, v))
            .collect();
        let (inst, _) = instantiate(b, lhs, dummies)?;
        inst
    } else {
        b.open();
        let anchor_vars = anchor_covering(left_bindings, right_bindings);
        let args = left_bindings.iter().map(|v| var_term(b.pool, v)).collect();
        let (inst, _) = instantiate(b, lhs, args)?;
        // The instantiated clause is `(cl (not lhs) phi)`; close `phi` over `R`
        close_bind(b, &anchor_vars, right_bindings, 1, inst)
    };

    // Direction ←: instantiate the right side (or take the excluded middle) and close over `L`
    let backward = {
        b.open();
        let inner = if right_bindings.is_empty() {
            excluded_middle(b, body)?
        } else {
            let args = right_bindings.iter().map(|v| var_term(b.pool, v)).collect();
            let (inst, _) = instantiate(b, rhs, args)?;
            inst
        };
        // The clause is `(cl (not rhs) phi)`; close `phi` over all of `L`
        close_bind(b, left_bindings, left_bindings, 1, inner)
    };

    b.equiv_intro(lhs.clone(), rhs.clone(), forward, backward)
}

/// `qnt_join` rewrites `(forall X. (forall Y. phi)) ≈ (forall XY. phi)`.
pub fn qnt_join(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let Some((lhs, rhs)) = match_term!((= l r) = &step.clause[0]) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    let (lhs, rhs) = (lhs.clone(), rhs.clone());
    let (Some((outer_bindings, inner_quant)), Some((joined_bindings, body))) =
        (forall_parts(&lhs), forall_parts(&rhs))
    else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    let Some((inner_bindings, inner_body)) = forall_parts(&inner_quant) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    // Only the variable-disjoint case is handled: the joined prefix is the concatenation
    let concatenated: Vec<_> = outer_bindings
        .iter()
        .chain(&inner_bindings)
        .cloned()
        .collect();
    if inner_body != body || joined_bindings != concatenated || has_duplicate_names(&concatenated) {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    let mut b = Builder::new(pool, step);

    // Direction →: eliminate both quantifiers at the anchor variables, close over the whole prefix
    let forward = {
        b.open();
        let args = outer_bindings.iter().map(|v| var_term(b.pool, v)).collect();
        let (outer_inst, _) = instantiate(&mut b, &lhs, args)?;
        let args = inner_bindings.iter().map(|v| var_term(b.pool, v)).collect();
        let (inner_inst, _) = instantiate(&mut b, &inner_quant, args)?;
        let merged = b.resolve(
            vec![outer_inst, inner_inst],
            vec![(inner_quant.clone(), true)],
        )?;
        close_bind(&mut b, &concatenated, &concatenated, 1, merged)
    };

    // Direction ←: eliminate the joined quantifier, rebuild the nesting with two closures
    let backward = {
        b.open();
        b.open();
        let args = concatenated.iter().map(|v| var_term(b.pool, v)).collect();
        let (inst, _) = instantiate(&mut b, &rhs, args)?;
        let inner_closed = close_bind(&mut b, &inner_bindings, &inner_bindings, 1, inst);
        close_bind(&mut b, &outer_bindings, &outer_bindings, 1, inner_closed)
    };

    let node = b.equiv_intro(lhs, rhs, forward, backward)?;
    Ok(b.relabel(step, node))
}

/// `miniscope_distribute` rewrites `(forall X. (and phi_1 … phi_k)) ≈ (and (forall X. phi_1) …
/// (forall X. phi_k))`.
pub fn miniscope_distribute(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let Some((lhs, rhs)) = match_term!((= l r) = &step.clause[0]) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    let (lhs, rhs) = (lhs.clone(), rhs.clone());
    let Some((bindings, body)) = forall_parts(&lhs) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    let (Some(conjuncts), Some(quantified)) = (
        match_term!((and ...) = body).map(<[_]>::to_vec),
        match_term!((and ...) = rhs).map(<[_]>::to_vec),
    ) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    if conjuncts.len() != quantified.len() || has_duplicate_names(&bindings) {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    let distinct: indexmap::IndexSet<_> = conjuncts.iter().collect();
    if distinct.len() != conjuncts.len() {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    for (conjunct, quant) in conjuncts.iter().zip(&quantified) {
        if *quant != forall(pool, bindings.clone(), conjunct.clone()) {
            return Ok(Rc::new(ProofNode::Step(step.clone())));
        }
    }

    let mut b = Builder::new(pool, step);
    let not_body = b.not(&body);
    let not_rhs = b.not(&rhs);

    // Direction →: each conjunct's quantifier by its own closure, then `and_neg` re-packs
    let mut closed = Vec::new();
    for (i, conjunct) in conjuncts.iter().enumerate() {
        b.open();
        let args = bindings.iter().map(|v| var_term(b.pool, v)).collect();
        let (inst, _) = instantiate(&mut b, &lhs, args)?;
        let index = b.pool.add(Term::new_int(i));
        let and_pos = b.step(
            vec![not_body.clone(), conjunct.clone()],
            "and_pos",
            Vec::new(),
            vec![index],
        );
        let extracted = b.resolve(vec![inst, and_pos], vec![(body.clone(), true)])?;
        closed.push(close_bind(&mut b, &bindings, &bindings, 1, extracted));
    }
    let mut and_neg_clause = vec![rhs.clone()];
    let mut pivots = Vec::new();
    for q in &quantified {
        let not_q = b.not(q);
        and_neg_clause.push(not_q);
        pivots.push((q.clone(), false));
    }
    let and_neg = b.step(and_neg_clause, "and_neg", Vec::new(), Vec::new());
    let mut premises = vec![and_neg];
    premises.extend(closed);
    let forward = b.resolve(premises, pivots)?;

    // Direction ←: extract each quantified conjunct, instantiate it, and rebuild the body
    let backward = {
        b.open();
        let mut extracted = Vec::new();
        for (i, (conjunct, quant)) in conjuncts.iter().zip(&quantified).enumerate() {
            let index = b.pool.add(Term::new_int(i));
            let and_pos = b.step(
                vec![not_rhs.clone(), quant.clone()],
                "and_pos",
                Vec::new(),
                vec![index],
            );
            let args = bindings.iter().map(|v| var_term(b.pool, v)).collect();
            let (inst, instantiated) = instantiate(&mut b, quant, args)?;
            if instantiated != *conjunct {
                return Ok(Rc::new(ProofNode::Step(step.clone())));
            }
            extracted.push(b.resolve(vec![and_pos, inst], vec![(quant.clone(), true)])?);
        }
        let mut and_neg_clause = vec![body.clone()];
        let mut pivots = Vec::new();
        for c in &conjuncts {
            let not_c = b.not(c);
            and_neg_clause.push(not_c);
            pivots.push((c.clone(), false));
        }
        let and_neg = b.step(and_neg_clause, "and_neg", Vec::new(), Vec::new());
        let mut premises = vec![and_neg];
        premises.extend(extracted);
        let rebuilt = b.resolve(premises, pivots)?;
        // The clause is `(cl (and phis) (not rhs))`; close the body over `X`
        close_bind(&mut b, &bindings, &bindings, 0, rebuilt)
    };

    let node = b.equiv_intro(lhs, rhs, forward, backward)?;
    Ok(b.relabel(step, node))
}

/// `miniscope_split` rewrites `(forall X. (or phi_1 … phi_k)) ≈ (or psi_1 … psi_k)`, where each
/// `psi_i` is either `(forall B_i. phi_i)` for pairwise-disjoint `B_i ⊆ X`, or `phi_i` itself.
pub fn miniscope_split(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let Some((lhs, rhs)) = match_term!((= l r) = &step.clause[0]) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    let (lhs, rhs) = (lhs.clone(), rhs.clone());
    let Some((bindings, body)) = forall_parts(&lhs) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    let (Some(disjuncts), Some(split)) = (
        match_term!((or ...) = body).map(<[_]>::to_vec),
        match_term!((or ...) = rhs).map(<[_]>::to_vec),
    ) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    if disjuncts.len() != split.len() || has_duplicate_names(&bindings) {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    let distinct: indexmap::IndexSet<_> = disjuncts.iter().collect();
    if distinct.len() != disjuncts.len() {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    // For each disjunct, its binder subset (empty for the pass-through case)
    let subsets: Vec<Vec<SortedVar>> = disjuncts
        .iter()
        .zip(&split)
        .map(|(phi, psi)| {
            if psi == phi {
                Some(Vec::new())
            } else {
                let (subset, inner) = forall_parts(psi)?;
                (inner == *phi).then_some(subset)
            }
        })
        .collect::<Option<_>>()
        .unwrap_or_default();
    if subsets.len() != disjuncts.len() {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    let in_some_subset: std::collections::HashSet<_> = subsets.iter().flatten().cloned().collect();

    let mut b = Builder::new(pool, step);

    // Direction →: nested anchors, one per non-trivial disjunct, closed innermost-first
    let forward = {
        let closing: Vec<(usize, &Vec<SortedVar>)> = subsets
            .iter()
            .enumerate()
            .filter(|(_, s)| !s.is_empty())
            .collect();
        for _ in &closing {
            b.open();
        }
        let args = bindings
            .iter()
            .map(|v| {
                if in_some_subset.contains(v) {
                    var_term(b.pool, v)
                } else {
                    dummy_choice(b.pool, v)
                }
            })
            .collect();
        let (inst, instantiated) = instantiate(&mut b, &lhs, args)?;
        if instantiated != body {
            return Ok(Rc::new(ProofNode::Step(step.clone())));
        }
        let not_body = b.not(&body);
        let mut or_pos_clause = vec![not_body];
        or_pos_clause.extend(disjuncts.iter().cloned());
        let or_pos = b.step(or_pos_clause, "or_pos", Vec::new(), Vec::new());
        // `(cl (not lhs) phi_1 … phi_k)`; literal `i` of the clause is disjunct `i - 1`
        let mut current = b.resolve(vec![inst, or_pos], vec![(body.clone(), true)])?;
        for &(i, subset) in closing.iter().rev() {
            current = close_bind(&mut b, subset, subset, i + 1, current);
        }
        // Pack the split literals into the `or` term
        for (i, psi) in split.iter().enumerate() {
            let not_psi = b.not(psi);
            let index = b.pool.add(Term::new_int(i));
            let or_neg = b.step(
                vec![rhs.clone(), not_psi],
                "or_neg",
                Vec::new(),
                vec![index],
            );
            current = b.resolve(vec![current, or_neg], vec![(psi.clone(), true)])?;
        }
        current
    };

    // Direction ←: unpack the split, instantiate each quantified disjunct, re-pack and close
    let backward = {
        b.open();
        let not_rhs = b.not(&rhs);
        let mut or_pos_clause = vec![not_rhs];
        or_pos_clause.extend(split.iter().cloned());
        let or_pos = b.step(or_pos_clause, "or_pos", Vec::new(), Vec::new());
        let mut current = or_pos;
        // Resolve the `(cl (not (or psis)) psi_1 … psi_k)` clause with the `(cl rhs)`-shaped
        // unpacking of each non-trivial `psi_i`
        for (subset, (phi, psi)) in subsets.iter().zip(disjuncts.iter().zip(&split)) {
            if subset.is_empty() {
                continue;
            }
            let args = subset.iter().map(|v| var_term(b.pool, v)).collect();
            let (inst, instantiated) = instantiate(&mut b, psi, args)?;
            if instantiated != *phi {
                return Ok(Rc::new(ProofNode::Step(step.clone())));
            }
            current = b.resolve(vec![current, inst], vec![(psi.clone(), true)])?;
        }
        // Pack the disjuncts back into the body
        for (i, phi) in disjuncts.iter().enumerate() {
            let not_phi = b.not(phi);
            let index = b.pool.add(Term::new_int(i));
            let or_neg = b.step(
                vec![body.clone(), not_phi],
                "or_neg",
                Vec::new(),
                vec![index],
            );
            current = b.resolve(vec![current, or_neg], vec![(phi.clone(), true)])?;
        }
        // `(cl (not rhs) (or phis))`; close the body over `X`
        close_bind(&mut b, &bindings, &bindings, 1, current)
    };

    let node = b.equiv_intro(lhs, rhs, forward, backward)?;
    Ok(b.relabel(step, node))
}

/// `miniscope_ite` rewrites `(forall X. (ite c P Q)) ≈ (ite c (forall X. P) (forall X. Q))` for
/// an `X`-free condition `c`: both directions case split on `c` through the (core) `ite` CNF
/// axioms, with one anchor per branch.
pub fn miniscope_ite(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let Some((lhs, rhs)) = match_term!((= l r) = &step.clause[0]) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    let (lhs, rhs) = (lhs.clone(), rhs.clone());
    let Some((bindings, body)) = forall_parts(&lhs) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    let Some((cond, p, q)) = match_term!((ite c p q) = body) else {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    };
    let (cond, p, q) = (cond.clone(), p.clone(), q.clone());
    let (forall_p, forall_q) = {
        let Some((c2, fp, fq)) = match_term!((ite c p q) = rhs) else {
            return Ok(Rc::new(ProofNode::Step(step.clone())));
        };
        if *c2 != cond {
            return Ok(Rc::new(ProofNode::Step(step.clone())));
        }
        (fp.clone(), fq.clone())
    };
    if has_duplicate_names(&bindings) {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    let mut b = Builder::new(pool, step);
    let not_cond = b.not(&cond);

    // Direction →: two anchors, one per branch of the case split on `c`
    let forward = {
        let branch = |b: &mut Builder,
                      extract_rule: &str,
                      extract_clause_tail: Vec<Rc<Term>>,
                      branch_body: &Rc<Term>|
         -> Result<Rc<ProofNode>, ElaborationError> {
            b.open();
            let args = bindings.iter().map(|v| var_term(b.pool, v)).collect();
            let (inst, _) = instantiate(b, &lhs, args)?;
            let not_body = b.not(&body);
            let mut clause = vec![not_body];
            clause.extend(extract_clause_tail);
            let ite_axiom = b.step(clause, extract_rule, Vec::new(), Vec::new());
            let extracted = b.resolve(vec![inst, ite_axiom], vec![(body.clone(), true)])?;
            // `(cl (not lhs) (not? c) branch_body)`; close the branch body over `X`
            let index = extracted
                .clause()
                .iter()
                .position(|t| t == branch_body)
                .unwrap();
            Ok(close_bind(b, &bindings, &bindings, index, extracted))
        };
        // Branch `(not c)` holds: `ite_pos1` extracts `Q`
        let closed_q = branch(&mut b, "ite_pos1", vec![cond.clone(), q.clone()], &q)?;
        // Branch `c` holds: `ite_pos2` extracts `P`
        let closed_p = branch(&mut b, "ite_pos2", vec![not_cond.clone(), p.clone()], &p)?;

        let not_forall_q = b.not(&forall_q);
        let ite_neg1 = b.step(
            vec![rhs.clone(), cond.clone(), not_forall_q],
            "ite_neg1",
            Vec::new(),
            Vec::new(),
        );
        let not_forall_p = b.not(&forall_p);
        let ite_neg2 = b.step(
            vec![rhs.clone(), not_cond.clone(), not_forall_p],
            "ite_neg2",
            Vec::new(),
            Vec::new(),
        );
        let r1 = b.resolve(vec![closed_q, ite_neg1], vec![(forall_q.clone(), true)])?;
        let r2 = b.resolve(vec![closed_p, ite_neg2], vec![(forall_p.clone(), true)])?;
        b.resolve(vec![r1, r2], vec![(cond.clone(), true)])?
    };

    // Direction ←: symmetric, extracting from the `ite` of quantifiers
    let backward = {
        let not_rhs = b.not(&rhs);
        let ite_pos1 = b.step(
            vec![not_rhs.clone(), cond.clone(), forall_q.clone()],
            "ite_pos1",
            Vec::new(),
            Vec::new(),
        );
        let ite_pos2 = b.step(
            vec![not_rhs, not_cond.clone(), forall_p.clone()],
            "ite_pos2",
            Vec::new(),
            Vec::new(),
        );
        let branch = |b: &mut Builder,
                      unpacked: Rc<ProofNode>,
                      quant: &Rc<Term>,
                      branch_body: &Rc<Term>,
                      rebuild_rule: &str,
                      rebuild_tail: Vec<Rc<Term>>|
         -> Result<Rc<ProofNode>, ElaborationError> {
            b.open();
            let args = bindings.iter().map(|v| var_term(b.pool, v)).collect();
            let (inst, _) = instantiate(b, quant, args)?;
            let with_body = b.resolve(vec![unpacked, inst], vec![(quant.clone(), true)])?;
            let not_branch_body = b.not(branch_body);
            let mut clause = vec![body.clone()];
            clause.extend(rebuild_tail);
            clause.push(not_branch_body);
            let ite_axiom = b.step(clause, rebuild_rule, Vec::new(), Vec::new());
            let rebuilt = b.resolve(
                vec![with_body, ite_axiom],
                vec![(branch_body.clone(), true)],
            )?;
            let index = rebuilt.clause().iter().position(|t| t == &body).unwrap();
            Ok(close_bind(b, &bindings, &bindings, index, rebuilt))
        };
        let closed_q = branch(
            &mut b,
            ite_pos1,
            &forall_q,
            &q,
            "ite_neg1",
            vec![cond.clone()],
        )?;
        let closed_p = branch(&mut b, ite_pos2, &forall_p, &p, "ite_neg2", vec![not_cond])?;
        b.resolve(vec![closed_q, closed_p], vec![(cond, true)])?
    };

    let node = b.equiv_intro(lhs, rhs, forward, backward)?;
    Ok(b.relabel(step, node))
}
