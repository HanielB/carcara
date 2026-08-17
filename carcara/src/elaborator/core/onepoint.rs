//! Reduction of `onepoint`.
//!
//! An `onepoint` step closes a subproof whose anchor substitutes the *point* variables by the
//! terms their guarded equalities force, concluding `(= (Q x̄. φ) (Q x̄ₖ. φ'))` with
//! `φ' = σ(φ)`. The reduction derives the two implications and closes with the iff-introduction
//! pattern:
//!
//! - the → direction of a `forall` (and the ← direction of an `exists`) is a `forall_inst` at
//!   the points (plus the anchor variables for the kept prefix);
//! - the opposite direction re-derives `φ` from `φ'` (or vice versa) under discharge subproofs
//!   that assume the guard equalities and transport the substituted positions by `symm`/`cong`
//!   (the *transport* engine below), with the `implies`/`and` structure rebuilt through the CNF
//!   axioms;
//! - the `exists` forms route through the quantifier duality instance of `connective_def`.
//!
//! The replacement derivation lives *inside* the original subproof (whose anchor becomes
//! vacuous), so the surrounding proof structure is untouched. Instances whose points occur under
//! inner binders, or whose bodies fall outside the guard grammar handled here, are kept
//! unchanged.

use super::binder::{close_bind, instantiate, var_term};
use super::Builder;
use crate::{ast::*, elaborator::error::ElaborationError};
use indexmap::IndexMap;

/// Derives `(= from to)` where `to` is `from` with each point variable `x` replaced by its value
/// `t` (or the reverse, when `reversed`), given unit facts for the (possibly reversed) point
/// equalities. Returns `None` when `from == to` (no step needed); bails with `Err(())` when the
/// substitution reaches under a binder.
pub(super) fn transport(
    b: &mut Builder,
    facts: &IndexMap<Rc<Term>, Rc<ProofNode>>,
    from: &Rc<Term>,
    to: &Rc<Term>,
) -> Result<Option<Rc<ProofNode>>, ()> {
    if from == to {
        return Ok(None);
    }
    if let Some(node) = facts.get(from) {
        // A point-variable position (or a whole guarded subterm covered by a fact)
        if node.clause()[0] == build_term!(b.pool, (= {from.clone()} {to.clone()})) {
            return Ok(Some(node.clone()));
        }
    }
    let (from_args, to_args) = match (from.as_ref(), to.as_ref()) {
        (Term::Op(f, fa), Term::Op(g, ga)) if f == g && fa.len() == ga.len() => {
            (fa.clone(), ga.clone())
        }
        (Term::App(f, fa), Term::App(g, ga)) if f == g && fa.len() == ga.len() => {
            (fa.clone(), ga.clone())
        }
        _ => return Err(()),
    };
    let mut premises = Vec::new();
    for (u, v) in from_args.iter().zip(&to_args) {
        if let Some(node) = transport(b, facts, u, v)? {
            premises.push(node);
        }
    }
    let clause = vec![build_term!(b.pool, (= {from.clone()} {to.clone()}))];
    Ok(Some(b.step(clause, "cong", premises, Vec::new())))
}

/// Derives the equivalence `(= (= x y) (= y x))` — equality symmetry as a formula — by two
/// `symm` discharge subproofs closed with the iff-introduction pattern.
pub(super) fn eq_symmetry(
    b: &mut Builder,
    x: &Rc<Term>,
    y: &Rc<Term>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let xy = build_term!(b.pool, (= {x.clone()} {y.clone()}));
    let yx = build_term!(b.pool, (= {y.clone()} {x.clone()}));
    let direction = |b: &mut Builder, from: &Rc<Term>| {
        b.open();
        let assumption = b.assume(from.clone());
        let symm_step = b.symm(&assumption);
        b.close_subproof(vec![assumption], symm_step)
    };
    let forward = direction(b, &xy);
    let backward = direction(b, &yx);
    b.equiv_intro(xy, yx, forward, backward)
}

/// Derives `(= from to)` when the two terms differ only by the orientation of equality subterms
/// (veriT's implicit reordering): flipped equalities are bridged by [`eq_symmetry`], composed
/// with `cong`/`trans`. Returns `None` when the terms are identical; `Err(())` when they differ
/// in any other way.
fn orientation_bridge(
    b: &mut Builder,
    from: &Rc<Term>,
    to: &Rc<Term>,
) -> Result<Option<Rc<ProofNode>>, ()> {
    if from == to {
        return Ok(None);
    }
    // A flipped equality: bridge the children pairwise to the *swapped* sides, then apply
    // equality symmetry
    if let (Some((a, bb)), Some((c, d))) = (match_term!((= a b) = from), match_term!((= a b) = to))
    {
        let (a, bb, c, d) = (a.clone(), bb.clone(), c.clone(), d.clone());
        if let (Ok(left), Ok(right)) = (
            orientation_bridge(b, &a, &d),
            orientation_bridge(b, &bb, &c),
        ) {
            // from = (= a b) ≈ (= d c) by congruence, and (= d c) ≈ (= c d) by symmetry
            let mid = build_term!(b.pool, (= {d.clone()} {c.clone()}));
            let premises: Vec<_> = [left, right].into_iter().flatten().collect();
            let cong_node = if premises.is_empty() && mid == *from {
                None
            } else {
                let clause = vec![build_term!(b.pool, (= {from.clone()} {mid.clone()}))];
                Some(b.step(clause, "cong", premises, Vec::new()))
            };
            let symmetry = eq_symmetry(b, &d, &c).map_err(|_| ())?;
            return Ok(Some(match cong_node {
                Some(cong_node) => {
                    let clause = vec![build_term!(b.pool, (= {from.clone()} {to.clone()}))];
                    b.step(clause, "trans", vec![cong_node, symmetry], Vec::new())
                }
                None => symmetry,
            }));
        }
    }
    let (from_args, to_args) = match (from.as_ref(), to.as_ref()) {
        (Term::Op(f, fa), Term::Op(g, ga)) if f == g && fa.len() == ga.len() => {
            (fa.clone(), ga.clone())
        }
        (Term::App(f, fa), Term::App(g, ga)) if f == g && fa.len() == ga.len() => {
            (fa.clone(), ga.clone())
        }
        _ => return Err(()),
    };
    let mut premises = Vec::new();
    for (u, v) in from_args.iter().zip(&to_args) {
        if let Some(node) = orientation_bridge(b, u, v)? {
            premises.push(node);
        }
    }
    let clause = vec![build_term!(b.pool, (= {from.clone()} {to.clone()}))];
    Ok(Some(b.step(clause, "cong", premises, Vec::new())))
}

/// Replaces the literal `from` by `to` in a clause node, given an equality node `(= from to)`:
/// `equiv_pos2` turns the equality into the two-literal implication clause, which resolves in.
fn replace_literal(
    b: &mut Builder,
    clause_node: Rc<ProofNode>,
    eq_node: &Rc<ProofNode>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let equality = eq_node.clause()[0].clone();
    let (from, to) = match_term!((= p q) = equality).unwrap();
    let (from, to) = (from.clone(), to.clone());
    let (not_eq, not_from) = (b.not(&equality), b.not(&from));
    let equiv_pos2 = b.step(
        vec![not_eq, not_from, to],
        "equiv_pos2",
        Vec::new(),
        Vec::new(),
    );
    let implication = b.resolve(vec![equiv_pos2, eq_node.clone()], vec![(equality, false)])?;
    b.resolve(vec![clause_node, implication], vec![(from, true)])
}

/// The `eq_mp` pattern: from a unit fact `phi` and an equality node `(= phi psi)`, concludes
/// `(cl psi)`.
fn eq_mp(
    b: &mut Builder,
    phi_node: Rc<ProofNode>,
    eq_node: Rc<ProofNode>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let equality = eq_node.clause()[0].clone();
    let (phi, psi) = match_term!((= p q) = equality).unwrap();
    let (phi, psi) = (phi.clone(), psi.clone());
    let (not_eq, not_phi) = (b.not(&equality), b.not(&phi));
    let equiv_pos2 = b.step(
        vec![not_eq, not_phi, psi],
        "equiv_pos2",
        Vec::new(),
        Vec::new(),
    );
    b.resolve(
        vec![equiv_pos2, eq_node, phi_node],
        vec![(equality, false), (phi, false)],
    )
}

/// The points of the anchor: pairs `(x, t)` from its `:=` arguments, plus the kept variables.
pub(super) fn anchor_points(
    context: &ContextStack,
) -> Option<(Vec<(SortedVar, Rc<Term>)>, Vec<SortedVar>)> {
    let context = context.last()?;
    let context = context.as_ref()?;
    let mut points = Vec::new();
    let mut kept = Vec::new();
    for arg in &context.args {
        match arg {
            AnchorArg::Variable(var) => kept.push(var.clone()),
            AnchorArg::Assign(var, value) => points.push((var.clone(), value.clone())),
        }
    }
    Some((points, kept))
}

/// Classifies the body of a `forall` onepoint: an implication whose antecedent's conjunction
/// spine carries (some of) the guard equalities — possibly with a negated guard as the
/// consequent — or `(or l1 … ln)` with negated guard equalities among the literals.
enum ForallBody {
    Implies {
        antecedent: Rc<Term>,
        consequent: Rc<Term>,
    },
    Or {
        literals: Vec<Rc<Term>>,
    },
}

fn classify_forall_body(body: &Rc<Term>, point_vars: &[Rc<Term>]) -> Option<ForallBody> {
    let is_guard = |t: &Rc<Term>| {
        match_term!((= a b) = t)
            .is_some_and(|(a, b)| point_vars.contains(a) || point_vars.contains(b))
    };
    if let Some((g, c)) = match_term!((=> g c) = body) {
        // The guards may sit in the antecedent's conjunction spine or as the negated consequent
        let mut spine = vec![g.clone()];
        let mut has_guard = false;
        while let Some(t) = spine.pop() {
            if is_guard(&t) {
                has_guard = true;
                break;
            }
            if let Some(args) = match_term!((and ...) = t) {
                spine.extend(args.iter().cloned());
            }
        }
        let consequent_guard = c.remove_negation().is_some_and(is_guard);
        if has_guard || consequent_guard {
            return Some(ForallBody::Implies {
                antecedent: g.clone(),
                consequent: c.clone(),
            });
        }
        return None;
    }
    if let Some(args) = match_term!((or ...) = body) {
        let has_guard = args
            .iter()
            .any(|l| l.remove_negation().is_some_and(is_guard));
        if has_guard {
            return Some(ForallBody::Or { literals: args.to_vec() });
        }
    }
    None
}

/// Orients a guard equality into a fact for `x → t` transport, adding a `symm` step if the guard
/// was written `(= t x)`. `fact` concludes the guard as written.
fn orient_guard(
    b: &mut Builder,
    guard: &Rc<Term>,
    point_vars: &[Rc<Term>],
    fact: Rc<ProofNode>,
) -> Option<(Rc<Term>, Rc<ProofNode>)> {
    let (a, bb) = match_term!((= a b) = guard)?;
    if point_vars.contains(a) {
        Some((a.clone(), fact))
    } else if point_vars.contains(bb) {
        let flipped = b.symm(&fact);
        Some((bb.clone(), flipped))
    } else {
        None
    }
}

pub fn onepoint(
    pool: &mut PrimitivePool,
    context: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let keep = || Ok(Rc::new(ProofNode::Step(step.clone())));

    let Some((lhs, rhs)) = match_term!((= l r) = &step.clause[0]) else {
        return keep();
    };
    let (lhs, rhs) = (lhs.clone(), rhs.clone());
    let Some((points, _)) = anchor_points(context) else {
        return keep();
    };
    if points.is_empty() {
        return keep();
    }

    let Some((quant, bindings, body)) = lhs.as_quant().map(|(q, b, t)| (q, b.0.clone(), t.clone()))
    else {
        return keep();
    };
    // The kept prefix is the right-hand side's binder list (empty if it is not quantified)
    let (kept, rhs_body) = match rhs.as_quant() {
        Some((q, b, t)) if q == quant => (b.0.clone(), t.clone()),
        Some(_) => return keep(),
        None => (Vec::new(), rhs.clone()),
    };

    // Compute the substitution and check that the right-hand side is exactly σ(φ)
    let point_map: IndexMap<Rc<Term>, Rc<Term>> = points
        .iter()
        .map(|(var, value)| (pool.add(var.clone().into()), value.clone()))
        .collect();
    let expected = {
        let map = point_map.clone();
        let Ok(mut substitution) = Substitution::new(pool, map) else {
            return keep();
        };
        substitution.apply(pool, &body)
    };
    // The right-hand side may differ from σ(φ) by the orientation of equality subterms
    // (veriT's implicit reordering); the case functions bridge that difference when needed
    let point_vars: Vec<Rc<Term>> = point_map.keys().cloned().collect();

    let args = OnepointArgs {
        lhs: &lhs,
        rhs: &rhs,
        bindings: &bindings,
        kept: &kept,
        body: &body,
        sigma_body: &expected,
        rhs_body: &rhs_body,
        points: &points,
        point_vars: &point_vars,
    };
    let result = match quant {
        Binder::Forall => forall_onepoint(pool, step, &args),
        Binder::Exists => exists_onepoint(pool, step, &args),
        _ => return keep(),
    };
    match result {
        Ok(Some(node)) => Ok(node),
        Ok(None) | Err(_) => keep(),
    }
}

/// The pieces of an `onepoint` instance, shared by the two quantifier cases.
struct OnepointArgs<'a> {
    lhs: &'a Rc<Term>,
    rhs: &'a Rc<Term>,
    bindings: &'a [SortedVar],
    kept: &'a [SortedVar],
    body: &'a Rc<Term>,
    /// σ(φ), the point substitution applied to the body
    sigma_body: &'a Rc<Term>,
    /// The right-hand side's body — σ(φ) up to equality orientation
    rhs_body: &'a Rc<Term>,
    points: &'a [(SortedVar, Rc<Term>)],
    point_vars: &'a [Rc<Term>],
}

/// The instantiation arguments for the full binder list: kept variables at themselves, point
/// variables at their values.
fn full_instantiation_args(
    b: &mut Builder,
    bindings: &[SortedVar],
    points: &[(SortedVar, Rc<Term>)],
) -> Option<Vec<Rc<Term>>> {
    bindings
        .iter()
        .map(|var| {
            if let Some((_, value)) = points.iter().find(|(p, _)| p == var) {
                Some(value.clone())
            } else {
                Some(var_term(b.pool, var))
            }
        })
        .collect()
}

fn forall_onepoint(
    pool: &mut PrimitivePool,
    step: &StepNode,
    args: &OnepointArgs,
) -> Result<Option<Rc<ProofNode>>, ElaborationError> {
    let Some(shape) = classify_forall_body(args.body, args.point_vars) else {
        return Ok(None);
    };

    let mut b = Builder::new(pool, step);
    // Bridge between σ(φ) and the right-hand side's body, when their equality orientations
    // differ (derived once, outside the anchors)
    let Ok(e_corr) = orientation_bridge(&mut b, args.sigma_body, args.rhs_body) else {
        return Ok(None);
    };

    // Direction →: instantiate at the points (and the kept variables at themselves)
    let forward = {
        let use_anchor = !args.kept.is_empty();
        if use_anchor {
            b.open();
        }
        let Some(inst_args) = full_instantiation_args(&mut b, args.bindings, args.points) else {
            return Ok(None);
        };
        let (inst, _) = instantiate(&mut b, args.lhs, inst_args)?;
        let inst = match &e_corr {
            Some(eq) => replace_literal(&mut b, inst, eq)?,
            None => inst,
        };
        if use_anchor {
            close_bind(&mut b, args.kept, args.kept, 1, inst)
        } else {
            inst
        }
    };

    // Direction ←: under an anchor over the full prefix, derive `(cl ¬φ' φ)` and close
    let backward = {
        b.open();
        // `(cl ¬rhs φ')`: instantiate the kept prefix, or the excluded middle when unquantified
        let start = if args.kept.is_empty() {
            super::binder::excluded_middle(&mut b, args.rhs)?
        } else {
            let inst_args = args.kept.iter().map(|v| var_term(b.pool, v)).collect();
            let (inst, _) = instantiate(&mut b, args.rhs, inst_args)?;
            inst
        };
        let phi_prime = start.clause()[1].clone();

        // `(cl ¬φ' φ)` by a discharge subproof
        let implication =
            derive_body_from_substituted(&mut b, args, &phi_prime, &shape, e_corr.as_ref())?;
        let Some(implication) = implication else {
            return Ok(None);
        };

        let with_body = b.resolve(vec![start, implication], vec![(phi_prime, true)])?;
        // clause: `(cl ¬rhs φ)`; close `φ` over the full prefix
        close_bind(&mut b, args.bindings, args.bindings, 1, with_body)
    };

    let node = b.equiv_intro(args.lhs.clone(), args.rhs.clone(), forward, backward)?;
    Ok(Some(relabel_dropping_previous(step, &node)))
}

/// Derives `(cl ¬φ' φ)` for a `forall` body: a discharge subproof assumes `φ'`, rebuilds `φ`
/// through its guard structure, transporting the payload with the guard equalities.
fn derive_body_from_substituted(
    b: &mut Builder,
    args: &OnepointArgs,
    phi_prime: &Rc<Term>,
    shape: &ForallBody,
    e_corr: Option<&Rc<ProofNode>>,
) -> Result<Option<Rc<ProofNode>>, ElaborationError> {
    let body = args.body;
    let points = args.points;
    let point_vars: Vec<Rc<Term>> = points
        .iter()
        .map(|(var, _)| b.pool.add(var.clone().into()))
        .collect();
    b.open();
    let assumed = b.assume(phi_prime.clone());
    // Bridge the assumption to σ(φ) when the orientation differs; everything below works on
    // σ(φ) (`sigma_apply` of the pieces)
    let outer_assumption = match e_corr {
        Some(eq) => {
            let flipped = b.symm(eq);
            eq_mp(b, assumed.clone(), flipped)?
        }
        None => assumed.clone(),
    };
    let working_term = args.sigma_body.clone();

    let result = match shape {
        ForallBody::Implies { antecedent, consequent } => {
            let sigma = |b: &mut Builder, t: &Rc<Term>| sigma_apply(b, t, points);
            let sigma_antecedent = sigma(b, antecedent);
            let sigma_consequent = sigma(b, consequent);

            // Discharge subproof: assume the antecedent whole, extract the guard facts from its
            // conjunction spine, and derive the consequent
            b.open();
            let g_assumption = b.assume(antecedent.clone());
            let mut facts: IndexMap<Rc<Term>, Rc<ProofNode>> = IndexMap::new();
            let mut stack = vec![(antecedent.clone(), g_assumption.clone())];
            while let Some((term, node)) = stack.pop() {
                if let Some(and_args) = match_term!((and ...) = term) {
                    for (i, arg) in and_args.iter().enumerate() {
                        let not_term = b.not(&term);
                        let index = b.pool.add(Term::new_int(i));
                        let and_pos = b.step(
                            vec![not_term, arg.clone()],
                            "and_pos",
                            Vec::new(),
                            vec![index],
                        );
                        let arg_node =
                            b.resolve(vec![and_pos, node.clone()], vec![(term.clone(), false)])?;
                        stack.push((arg.clone(), arg_node));
                    }
                } else if let Some((var, oriented)) =
                    orient_guard(b, &term, &point_vars, node.clone())
                {
                    let value = points
                        .iter()
                        .find(|(pv, _)| b.pool.add(pv.clone().into()) == var)
                        .map(|(_, v)| v.clone());
                    let matches = value.is_some_and(|v| {
                        match_term!((= a b) = oriented.clause()[0])
                            .is_some_and(|(_, rhs)| *rhs == v)
                    });
                    if matches {
                        facts.entry(var).or_insert(oriented);
                    }
                }
            }

            // When the consequent is a negated guard equality, its guard fact is only
            // available under an inner subproof assuming the equality — and the antecedent's
            // substituted positions may need that same fact
            let consequent_guard = match (
                consequent.remove_negation(),
                sigma_consequent.remove_negation(),
            ) {
                (Some(g), Some(sg))
                    if match_term!((= a b) = g).is_some_and(|(a, bb)| {
                        point_vars.contains(a) || point_vars.contains(bb)
                    }) =>
                {
                    Some((g.clone(), sg.clone()))
                }
                _ => None,
            };

            let consequent_node = if let Some((g, sg)) = consequent_guard {
                // Inner subproof: assume g, transport G to σG, extract ¬(t ≈ t), refute by refl
                b.open();
                let g_assumed = b.assume(g.clone());
                let mut inner_facts = facts.clone();
                if let Some((var, oriented)) = orient_guard(b, &g, &point_vars, g_assumed.clone()) {
                    inner_facts.entry(var).or_insert(oriented);
                }
                let sigma_g_node = {
                    let Ok(eq) = transport(b, &inner_facts, antecedent, &sigma_antecedent) else {
                        return Ok(None);
                    };
                    match eq {
                        Some(eq_node) => eq_mp(b, g_assumption.clone(), eq_node)?,
                        None => g_assumption.clone(),
                    }
                };
                let (not_working, not_sigma_g) = (b.not(&working_term), b.not(&sigma_antecedent));
                let implies_pos = b.step(
                    vec![not_working, not_sigma_g, sigma_consequent.clone()],
                    "implies_pos",
                    Vec::new(),
                    Vec::new(),
                );
                let sigma_c_node = b.resolve(
                    vec![implies_pos, outer_assumption.clone(), sigma_g_node],
                    vec![
                        (working_term.clone(), false),
                        (sigma_antecedent.clone(), false),
                    ],
                )?;
                let refl = b.step(vec![sg.clone()], "refl", Vec::new(), Vec::new());
                let empty = b.resolve(vec![sigma_c_node, refl], vec![(sg, false)])?;
                let sub = b.close_subproof(vec![g_assumed], empty);
                // sub: (cl ¬g false); eliminate the `false` literal
                let f = b.pool.bool_false();
                let not_false = b.not(&f);
                let false_step = b.step(vec![not_false], "false", Vec::new(), Vec::new());
                b.resolve(vec![sub, false_step], vec![(f, true)])?
            } else {
                // σG from G by transport over the antecedent's own guard facts
                let sigma_g_node = {
                    let Ok(eq) = transport(b, &facts, antecedent, &sigma_antecedent) else {
                        return Ok(None);
                    };
                    match eq {
                        Some(eq_node) => eq_mp(b, g_assumption.clone(), eq_node)?,
                        None => g_assumption.clone(),
                    }
                };
                let (not_working, not_sigma_g) = (b.not(&working_term), b.not(&sigma_antecedent));
                let implies_pos = b.step(
                    vec![not_working, not_sigma_g, sigma_consequent.clone()],
                    "implies_pos",
                    Vec::new(),
                    Vec::new(),
                );
                let sigma_c_node = b.resolve(
                    vec![implies_pos, outer_assumption.clone(), sigma_g_node],
                    vec![
                        (working_term.clone(), false),
                        (sigma_antecedent.clone(), false),
                    ],
                )?;
                // The consequent by reverse transport
                let reverse_facts = {
                    let mut m = IndexMap::new();
                    for (_, node) in &facts {
                        let flipped = b.symm(node);
                        let key = match_term!((= a b) = flipped.clause()[0])
                            .unwrap()
                            .0
                            .clone();
                        m.insert(key, flipped);
                    }
                    m
                };
                let Ok(eq) = transport(b, &reverse_facts, &sigma_consequent, consequent) else {
                    return Ok(None);
                };
                match eq {
                    Some(eq_node) => eq_mp(b, sigma_c_node, eq_node)?,
                    None => sigma_c_node,
                }
            };

            let inner = b.close_subproof(vec![g_assumption], consequent_node);

            // Package `φ = (=> G C)` from `(cl ¬G C)`
            let not_consequent = b.not(consequent);
            let implies_neg1 = b.step(
                vec![body.clone(), antecedent.clone()],
                "implies_neg1",
                Vec::new(),
                Vec::new(),
            );
            let implies_neg2 = b.step(
                vec![body.clone(), not_consequent],
                "implies_neg2",
                Vec::new(),
                Vec::new(),
            );
            let r1 = b.resolve(vec![inner, implies_neg2], vec![(consequent.clone(), true)])?;
            b.resolve(vec![r1, implies_neg1], vec![(antecedent.clone(), false)])?
        }
        ForallBody::Or { literals } => {
            let sigma = |b: &mut Builder, t: &Rc<Term>| sigma_apply(b, t, points);
            // Unpack φ' into its literals
            let sigma_literals: Vec<Rc<Term>> = literals.iter().map(|l| sigma(b, l)).collect();
            let not_working = b.not(&working_term);
            let mut or_pos_clause = vec![not_working];
            or_pos_clause.extend(sigma_literals.iter().cloned());
            let or_pos = b.step(or_pos_clause, "or_pos", Vec::new(), Vec::new());
            let mut current = b.resolve(
                vec![or_pos, outer_assumption.clone()],
                vec![(working_term.clone(), false)],
            )?;

            // Eliminate the reflexive negated guards `¬(= t t)` by `refl`
            for (l, sl) in literals.iter().zip(&sigma_literals) {
                let Some(g) = l.remove_negation() else {
                    continue;
                };
                let Some(sg) = sl.remove_negation() else {
                    continue;
                };
                if match_term!((= a b) = g)
                    .is_some_and(|(a, bb)| point_vars.contains(a) || point_vars.contains(bb))
                {
                    let refl = b.step(vec![sg.clone()], "refl", Vec::new(), Vec::new());
                    current = b.resolve(vec![current, refl], vec![(sg.clone(), false)])?;
                }
            }

            // Transport each remaining payload literal under discharge subproofs assuming the
            // guards
            let guards: Vec<Rc<Term>> = literals
                .iter()
                .filter_map(|l| l.remove_negation())
                .filter(|g| {
                    match_term!((= a b) = *g)
                        .is_some_and(|(a, bb)| point_vars.contains(a) || point_vars.contains(bb))
                })
                .cloned()
                .collect();
            for (l, sl) in literals.iter().zip(&sigma_literals) {
                let is_guard_literal = l.remove_negation().is_some_and(|g| guards.contains(g));
                if l == sl || is_guard_literal {
                    continue;
                }
                // subproof: assume σl and the guards, conclude l
                b.open();
                let sl_assumption = b.assume(sl.clone());
                let mut assumptions = vec![sl_assumption.clone()];
                let mut facts = IndexMap::new();
                for g in &guards {
                    let a = b.assume(g.clone());
                    assumptions.push(a.clone());
                    let Some((_, oriented)) = orient_guard(b, g, &point_vars, a) else {
                        return Ok(None);
                    };
                    let flipped = b.symm(&oriented);
                    let key = match_term!((= a b) = flipped.clause()[0])
                        .unwrap()
                        .0
                        .clone();
                    facts.insert(key, flipped);
                }
                let Ok(eq) = transport(b, &facts, sl, l) else {
                    return Ok(None);
                };
                let l_node = match eq {
                    Some(eq_node) => eq_mp(b, sl_assumption, eq_node)?,
                    None => sl_assumption,
                };
                let sub = b.close_subproof(assumptions, l_node);
                // `(cl ¬σl ¬g1 … l)`: resolve into the current clause
                current = b.resolve(vec![current, sub], vec![(sl.clone(), true)])?;
            }

            // Pack the clause back into `φ = (or l1 … ln)`. The current clause now holds, for
            // each literal position, either the literal itself or the negation of a guard
            let mut packed = current;
            for (i, l) in literals.iter().enumerate() {
                let not_l = b.not(l);
                let index = b.pool.add(Term::new_int(i));
                let or_neg = b.step(vec![body.clone(), not_l], "or_neg", Vec::new(), vec![index]);
                if packed.clause().contains(l) {
                    packed = b.resolve(vec![packed, or_neg], vec![(l.clone(), true)])?;
                }
            }
            packed
        }
    };

    // Result should conclude `(cl … φ)` with possibly guard negations; the caller expects the
    // unit-`φ` shape, so anything else bails
    let final_ok = result.clause() == [body.clone()];
    if !final_ok {
        return Ok(None);
    }
    Ok(Some(b.close_subproof(vec![assumed], result)))
}

/// Gives the derivation's last node the step's identity, like [`Builder::relabel`], but sets the
/// implicit previous step to one of the derivation's own nodes: the step closes its (now vacuous)
/// subproof, and the subproof's original inner derivation is no longer referenced by it.
pub(super) fn relabel_dropping_previous(step: &StepNode, node: &Rc<ProofNode>) -> Rc<ProofNode> {
    let last = node
        .as_step()
        .expect("last node of a reduction must be a step");
    Rc::new(ProofNode::Step(StepNode {
        id: step.id.clone(),
        depth: step.depth,
        clause: step.clause.clone(),
        rule: last.rule.clone(),
        premises: last.premises.clone(),
        args: last.args.clone(),
        discharge: Vec::new(),
        previous_step: last.premises.last().cloned(),
    }))
}

/// Applies the point substitution to a term (plain term-level substitution).
fn sigma_apply(b: &mut Builder, term: &Rc<Term>, points: &[(SortedVar, Rc<Term>)]) -> Rc<Term> {
    let map: IndexMap<Rc<Term>, Rc<Term>> = points
        .iter()
        .map(|(var, value)| (b.pool.add(var.clone().into()), value.clone()))
        .collect();
    match Substitution::new(b.pool, map) {
        Ok(mut substitution) => substitution.apply(b.pool, term),
        Err(_) => term.clone(),
    }
}

fn exists_onepoint(
    pool: &mut PrimitivePool,
    step: &StepNode,
    args: &OnepointArgs,
) -> Result<Option<Rc<ProofNode>>, ElaborationError> {
    let mut b = Builder::new(pool, step);

    // Bridge between σ(φ) and the right-hand side's body, when their equality orientations
    // differ (derived once, outside the anchors)
    let Ok(e_corr) = orientation_bridge(&mut b, args.sigma_body, args.rhs_body) else {
        return Ok(None);
    };

    // The duality bridges: A ≈ ¬F with F = (∀x̄. ¬φ), and B ≈ ¬F' with F' = (∀x̄ₖ. ¬φ') when the
    // right-hand side is quantified
    let not_body = b.not(args.body);
    let f_term = forall_term(&mut b, args.bindings, &not_body);
    let cd_a = connective_def_duality(&mut b, args.lhs, &f_term);

    let f_prime = if args.kept.is_empty() {
        None
    } else {
        let not_rhs_body = b.not(args.rhs_body);
        let f = forall_term(&mut b, args.kept, &not_rhs_body);
        let cd = connective_def_duality(&mut b, args.rhs, &f);
        Some((f, cd))
    };

    // Direction →: `(cl ¬A B)` = resolve `(cl ¬A ¬F)` with `(cl F B)`
    let forward = {
        // (cl ¬A ¬F) from the duality
        let not_a_not_f = {
            let equality = cd_a.clause()[0].clone();
            let not_lhs = b.not(args.lhs);
            let not_f = b.not(&f_term);
            let not_equality = b.not(&equality);
            let equiv_pos2 = b.step(
                vec![not_equality, not_lhs, not_f],
                "equiv_pos2",
                Vec::new(),
                Vec::new(),
            );
            b.resolve(vec![equiv_pos2, cd_a.clone()], vec![(equality, false)])?
        };

        // (cl B F): anchor over the full prefix, derive `(cl ¬φ B)` by a discharge subproof
        b.open();
        let sub = derive_substituted_from_body(&mut b, args, f_prime.as_ref(), e_corr.as_ref())?;
        let Some(sub) = sub else {
            return Ok(None);
        };
        // sub: (cl ¬φ B); close ¬φ over x̄ passing B, matching F's body
        let closed = close_bind(&mut b, args.bindings, args.bindings, 0, sub);
        // closed: (cl (∀x̄.¬φ) B) = (cl F B)
        b.resolve(vec![not_a_not_f, closed], vec![(f_term.clone(), false)])?
    };

    // Direction ←: `(cl A ¬B)` = resolve `(cl A ¬¬F)` with `(cl ¬F ¬B)`
    let backward = {
        let not_f = b.not(&f_term);
        // (cl A ¬¬F) from the duality
        let a_nnf = {
            let equality = cd_a.clause()[0].clone();
            let not_not_f = b.not(&not_f);
            let not_equality = b.not(&equality);
            let equiv_pos1 = b.step(
                vec![not_equality, args.lhs.clone(), not_not_f],
                "equiv_pos1",
                Vec::new(),
                Vec::new(),
            );
            b.resolve(vec![equiv_pos1, cd_a.clone()], vec![(equality, false)])?
        };

        // (cl ¬F ¬B): instantiate F at the points (kept at themselves)
        let use_anchor = !args.kept.is_empty();
        if use_anchor {
            b.open();
        }
        let Some(inst_args) = full_instantiation_args(&mut b, args.bindings, args.points) else {
            return Ok(None);
        };
        let (inst, instantiated) = instantiate(&mut b, &f_term, inst_args)?;
        // inst: (cl ¬F ¬σφ); bridge the instantiated literal to ¬φ' when needed
        let (inst, neg_rhs_body) = match &e_corr {
            Some(eq) => {
                let eq_not = {
                    let not_sigma = b.not(args.sigma_body);
                    let not_rhs_body = b.not(args.rhs_body);
                    let clause = vec![build_term!(b.pool, (= {not_sigma} {not_rhs_body.clone()}))];
                    let node = b.step(clause, "cong", vec![(*eq).clone()], Vec::new());
                    (node, not_rhs_body)
                };
                (replace_literal(&mut b, inst, &eq_not.0)?, eq_not.1)
            }
            None => {
                let neg = instantiated.clone();
                (inst, neg)
            }
        };
        let not_f_not_b = if let Some((f_p, cd_b)) = &f_prime {
            // close ¬φ' over the kept prefix → (cl ¬F F'), then bridge to ¬B
            let index = inst
                .clause()
                .iter()
                .position(|t| *t == neg_rhs_body)
                .unwrap();
            let closed = close_bind(&mut b, args.kept, args.kept, index, inst);
            let equality = cd_b.clause()[0].clone();
            let not_rhs = b.not(args.rhs);
            let not_f_p = b.not(f_p);
            let not_equality = b.not(&equality);
            let equiv_pos2 = b.step(
                vec![not_equality, not_rhs, not_f_p],
                "equiv_pos2",
                Vec::new(),
                Vec::new(),
            );
            let not_b_not_fp =
                b.resolve(vec![equiv_pos2, cd_b.clone()], vec![(equality, false)])?;
            b.resolve(vec![closed, not_b_not_fp], vec![(f_p.clone(), true)])?
        } else {
            // B is φ' itself: the (bridged) instantiated body is ¬B already
            inst
        };
        b.resolve(vec![a_nnf, not_f_not_b], vec![(not_f, false)])?
    };

    let node = b.equiv_intro(args.lhs.clone(), args.rhs.clone(), forward, backward)?;
    Ok(Some(relabel_dropping_previous(step, &node)))
}

fn forall_term(b: &mut Builder, bindings: &[SortedVar], body: &Rc<Term>) -> Rc<Term> {
    b.pool.add(Term::Binder(
        Binder::Forall,
        BindingList(bindings.to_vec()),
        body.clone(),
    ))
}

/// The `connective_def` duality instance `(= (∃x̄. φ) ¬(∀x̄. ¬φ))`.
fn connective_def_duality(b: &mut Builder, exists: &Rc<Term>, f: &Rc<Term>) -> Rc<ProofNode> {
    let not_f = b.not(f);
    let clause = vec![build_term!(b.pool, (= {exists.clone()} {not_f}))];
    b.step(clause, "connective_def", Vec::new(), Vec::new())
}

/// For the `exists` → direction: a discharge subproof assuming `φ`, extracting the guard
/// equalities from its conjunction spine, transporting `φ` to `φ'`, and introducing the
/// existential when the right-hand side is quantified. Concludes `(cl ¬φ B)`.
fn derive_substituted_from_body(
    b: &mut Builder,
    args: &OnepointArgs,
    f_prime: Option<&(Rc<Term>, Rc<ProofNode>)>,
    e_corr: Option<&Rc<ProofNode>>,
) -> Result<Option<Rc<ProofNode>>, ElaborationError> {
    let (body, rhs, rhs_body) = (args.body, args.rhs, args.rhs_body);
    let (kept, points, point_vars) = (args.kept, args.points, args.point_vars);
    b.open();
    let assumption = b.assume(body.clone());

    // Extract every guard equality reachable through the conjunction spine
    let mut facts = IndexMap::new();
    let mut stack = vec![(body.clone(), assumption.clone())];
    while let Some((term, node)) = stack.pop() {
        if let Some(args) = match_term!((and ...) = term) {
            for (i, arg) in args.iter().enumerate() {
                let not_term = b.not(&term);
                let index = b.pool.add(Term::new_int(i));
                let and_pos = b.step(
                    vec![not_term, arg.clone()],
                    "and_pos",
                    Vec::new(),
                    vec![index],
                );
                let arg_node =
                    b.resolve(vec![and_pos, node.clone()], vec![(term.clone(), false)])?;
                stack.push((arg.clone(), arg_node));
            }
        } else if match_term!((= a b) = term)
            .is_some_and(|(a, bb)| point_vars.contains(a) || point_vars.contains(bb))
        {
            if let Some((var, oriented)) = orient_guard(b, &term, point_vars, node) {
                // Several guards may mention the same point variable; only the one matching the
                // anchor's substitution value is usable as the transport fact
                let value = points
                    .iter()
                    .find(|(p, _)| b.pool.add(p.clone().into()) == var)
                    .map(|(_, v)| v.clone());
                let matches = value.is_some_and(|v| {
                    match_term!((= a b) = oriented.clause()[0]).is_some_and(|(_, rhs)| *rhs == v)
                });
                if matches {
                    facts.entry(var).or_insert(oriented);
                }
            }
        }
    }
    if facts.len() < points.len() {
        return Ok(None);
    }

    // Transport φ to σ(φ), then bridge to the (possibly reoriented) right-hand side body
    let sigma_body = sigma_apply(b, body, points);
    debug_assert_eq!(&sigma_body, args.sigma_body);
    let facts_by_var: IndexMap<Rc<Term>, Rc<ProofNode>> = facts.into_iter().collect();
    let Ok(eq) = transport(b, &facts_by_var, body, &sigma_body) else {
        return Ok(None);
    };
    let sigma_node = match eq {
        Some(eq_node) => eq_mp(b, assumption.clone(), eq_node)?,
        None => assumption.clone(),
    };
    let phi_prime_node = match e_corr {
        Some(eq_node) => eq_mp(b, sigma_node, (*eq_node).clone())?,
        None => sigma_node,
    };

    // Introduce the existential if needed
    let b_node = if let Some((f_p, cd_b)) = f_prime {
        // (cl B ¬¬F') from the duality; (cl ¬F' ¬φ') from instantiating F' at the kept prefix
        let equality = cd_b.clause()[0].clone();
        let not_f_p = b.not(f_p);
        let not_not_f_p = b.not(&not_f_p);
        let not_equality = b.not(&equality);
        let equiv_pos1 = b.step(
            vec![not_equality, rhs.clone(), not_not_f_p],
            "equiv_pos1",
            Vec::new(),
            Vec::new(),
        );
        let b_nnf = b.resolve(vec![equiv_pos1, cd_b.clone()], vec![(equality, false)])?;
        let args = kept.iter().map(|v| var_term(b.pool, v)).collect();
        let (inst, _) = instantiate(b, f_p, args)?;
        // inst: (cl ¬F' ¬φ')
        let b_not_phi = b.resolve(vec![b_nnf, inst], vec![(not_f_p, false)])?;
        b.resolve(
            vec![b_not_phi, phi_prime_node],
            vec![(rhs_body.clone(), false)],
        )?
    } else {
        let _ = rhs_body;
        phi_prime_node
    };

    Ok(Some(b.close_subproof(vec![assumption], b_node)))
}
