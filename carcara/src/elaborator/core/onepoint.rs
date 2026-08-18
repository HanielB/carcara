//! Reduction of `onepoint`.
//!
//! An `onepoint` step closes a subproof whose anchor substitutes the *point* variables by the
//! terms their guard equalities force, concluding `(= (Q x̄. φ) (Q x̄ₖ. φ'))`. The reduction
//! derives the two implications and closes with the iff-introduction pattern:
//!
//! - the → direction of a `forall` (and the ← direction of an `exists`) is a `forall_inst` at
//!   the points (plus the anchor variables for the kept prefix);
//! - the opposite direction re-derives `φ` from `σ(φ)` (or vice versa) under discharge subproofs
//!   that assume the guard equalities and transport the substituted positions by `symm`/`cong`
//!   (the *transport* engine below), with the case where a guard fails discharged by
//!   [`guard_escape`];
//! - the `exists` forms route through the quantifier duality instance of `connective_def`.
//!
//! What counts as a guard is not guessed from a template: the rule's own [`extract_points`]
//! traversal is what the recipe reads them off, and [`guard_escape`] mirrors that traversal
//! production by production. So the reduction covers every body the rule accepts. What it does
//! not cover is the other half of the rule's freedom: the right-hand side `φ'` need only be
//! *provably* equal to `σ(φ)` under the anchor, and the subproof's own derivation of that
//! equality is not reusable outside the context. The recipe therefore bridges `φ'` to `σ(φ)`
//! itself, and handles the differences that arise in practice — the orientation of equality
//! subterms, and the multiplicity of an `or`'s disjuncts — keeping the step otherwise.
//!
//! The replacement derivation lives *inside* the original subproof (whose anchor becomes
//! vacuous), so the surrounding proof structure is untouched.

use super::binder::{close_bind, connective_def_duality, instantiate, var_term};
use super::Builder;
use crate::{
    ast::*, checker::rules::subproof::extract_points, elaborator::error::ElaborationError,
};
use indexmap::{IndexMap, IndexSet};
use std::collections::HashSet;

/// Derives `(= from to)` where the two terms differ only at the positions a point substitution
/// touches, given unit facts `(= u v)` for those replacements. Returns `None` when `from == to`
/// (no step needed); bails with `Err(())` when the two terms cannot be aligned.
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
    // A substituted position under a quantifier: congruence through a `bind` subproof over the
    // — unchanged — binder list, with the facts crossing into it as outbound premises
    if let (Term::Binder(f, f_bindings, f_body), Term::Binder(g, g_bindings, g_body)) =
        (from.as_ref(), to.as_ref())
    {
        if f != g || f_bindings != g_bindings || !matches!(f, Binder::Forall | Binder::Exists) {
            return Err(());
        }
        if captures_facts(b, f_bindings, facts) {
            return Err(());
        }
        let (f_body, g_body) = (f_body.clone(), g_body.clone());
        let anchor_args = f_bindings
            .iter()
            .map(|var| AnchorArg::Variable(var.clone()))
            .collect();
        b.open();
        let Some(inner) = transport(b, facts, &f_body, &g_body)? else {
            return Err(());
        };
        let clause = vec![build_term!(b.pool, (= {from.clone()} {to.clone()}))];
        return Ok(Some(b.close_with(
            anchor_args,
            "bind",
            clause,
            Vec::new(),
            inner,
        )));
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

/// Whether any of the transport facts mentions a variable the binder list would capture, in which
/// case the equality cannot be carried under the binder.
fn captures_facts(
    b: &mut Builder,
    bindings: &BindingList,
    facts: &IndexMap<Rc<Term>, Rc<ProofNode>>,
) -> bool {
    let bound: Vec<Rc<Term>> = bindings
        .iter()
        .map(|var| b.pool.add(var.clone().into()))
        .collect();
    facts.values().any(|node| {
        let free = b.pool.free_vars(&node.clause()[0]);
        bound.iter().any(|var| free.contains(var))
    })
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

/// Derives `(= from to)` when the two terms differ only by the orientation of equality subterms:
/// flipped equalities are bridged by [`eq_symmetry`], composed
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

/// Derives `(= from to)` when `from` is an `or` whose disjuncts are, as a set, exactly `to`'s
/// (`to` being either an `or` or a single literal).
///
/// Substituting the points can make two disjuncts of a body coincide — two guards for the same
/// point variable, written in opposite orientations, both become the same reflexive equality — and
/// the right-hand side of the step is then the substituted body with the repetition dropped. The
/// derivation is pure clause reasoning: `or_pos` unpacks one side and `or_neg` packs the other,
/// with the resolution steps merging the repetitions.
fn disjunct_bridge(
    b: &mut Builder,
    from: &Rc<Term>,
    to: &Rc<Term>,
) -> Result<Option<Rc<ProofNode>>, ElaborationError> {
    let Some(from_literals) = match_term!((or ...) = from).map(<[_]>::to_vec) else {
        return Ok(None);
    };
    if from_literals.len() < 2 {
        return Ok(None);
    }
    let to_literals = match match_term!((or ...) = to) {
        Some(literals) => literals.to_vec(),
        None => vec![to.clone()],
    };
    let from_set: IndexSet<&Rc<Term>> = from_literals.iter().collect();
    let to_set: IndexSet<&Rc<Term>> = to_literals.iter().collect();
    if from_set != to_set {
        return Ok(None);
    }

    // `(cl (not p) l₁ … lₙ)` for an `or` term `p`, or the excluded middle for a single literal
    let unpack = |b: &mut Builder, term: &Rc<Term>, literals: &[Rc<Term>]| {
        if literals.len() == 1 {
            return super::binder::excluded_middle(b, term);
        }
        let not_term = b.not(term);
        let mut clause = vec![not_term];
        clause.extend(literals.iter().cloned());
        Ok(b.step(clause, "or_pos", Vec::new(), Vec::new()))
    };
    // Packs the literals of `term` into it, one `or_neg` per literal still in the clause
    let pack = |b: &mut Builder,
                mut current: Rc<ProofNode>,
                term: &Rc<Term>,
                literals: &[Rc<Term>]|
     -> Result<Rc<ProofNode>, ElaborationError> {
        if literals.len() == 1 {
            // `term` is the literal itself; the clause may still carry repetitions of it
            if current.clause().len() > 2 {
                let clause = vec![current.clause()[0].clone(), term.clone()];
                current = b.step(clause, "contraction", vec![current], Vec::new());
            }
            return Ok(current);
        }
        for (i, literal) in literals.iter().enumerate() {
            if !current.clause().contains(literal) {
                continue;
            }
            let not_literal = b.not(literal);
            let index = b.pool.add(Term::new_int(i));
            let or_neg = b.step(
                vec![term.clone(), not_literal],
                "or_neg",
                Vec::new(),
                vec![index],
            );
            current = b.resolve(vec![current, or_neg], vec![(literal.clone(), true)])?;
        }
        Ok(current)
    };

    let forward = {
        let unpacked = unpack(b, from, &from_literals)?;
        pack(b, unpacked, to, &to_literals)?
    };
    let backward = {
        let unpacked = unpack(b, to, &to_literals)?;
        pack(b, unpacked, from, &from_literals)?
    };
    Ok(Some(b.equiv_intro(
        from.clone(),
        to.clone(),
        forward,
        backward,
    )?))
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

/// The guard equalities of a quantified body, one per anchor point, in the anchor's order.
///
/// The rule's own [`extract_points`] traversal is what defines a guard, so the recipe reads the
/// guards off it rather than off a template: `None` means some point of the anchor is not one the
/// rule would have accepted, and the step is left alone.
fn point_guards(
    quant: Binder,
    body: &Rc<Term>,
    points: &[(SortedVar, Rc<Term>)],
) -> Option<Vec<Rc<Term>>> {
    let extracted = extract_points(quant, body);
    points
        .iter()
        .map(|((name, _), value)| extracted.get(&(name.clone(), value.clone())).cloned())
        .collect()
}

/// Derives the clause that lets a guard equality escape its body, following the same polarity
/// walk that [`extract_points`] took to find it. `polarity` is the polarity `term` sits at, in the
/// rule's convention (the walk starts at `quant == Exists`); the node returned concludes
/// `(cl (not term) guard)` at positive polarity and `(cl term guard)` at negative polarity.
///
/// The two readings are the two halves of the same fact: at positive polarity the guard is a
/// conjunct of `term`, so `term` entails it; at negative polarity its negation is a disjunct of
/// `term`, so `term` follows from the guard failing. Each production of the walk is discharged by
/// the corresponding CNF axiom — `and_pos` for a conjunct, `or_neg` for a disjunct,
/// `implies_neg1`/`implies_neg2` for the two sides of an implication, and the excluded middle for
/// the negations. The one production not covered is the walk through a quantifier: the guard is
/// then under a binder, and carrying it out needs an instantiation of that binder, which the
/// clause reasoning here cannot express.
fn guard_escape(
    b: &mut Builder,
    term: &Rc<Term>,
    polarity: bool,
    guard: &Rc<Term>,
    failed: &mut HashSet<(Rc<Term>, bool)>,
) -> Result<Option<Rc<ProofNode>>, ElaborationError> {
    if failed.contains(&(term.clone(), polarity)) {
        return Ok(None);
    }
    let escape = guard_escape_step(b, term, polarity, guard, failed)?;
    if escape.is_none() {
        failed.insert((term.clone(), polarity));
    }
    Ok(escape)
}

fn guard_escape_step(
    b: &mut Builder,
    term: &Rc<Term>,
    polarity: bool,
    guard: &Rc<Term>,
    failed: &mut HashSet<(Rc<Term>, bool)>,
) -> Result<Option<Rc<ProofNode>>, ElaborationError> {
    if let Some(inner) = term.remove_negation() {
        let inner = inner.clone();
        let Some(escape) = guard_escape(b, &inner, !polarity, guard, failed)? else {
            return Ok(None);
        };
        if !polarity {
            // `(cl (not inner) guard)` already is the clause wanted for `(cl term guard)`
            return Ok(Some(escape));
        }
        // `(cl inner guard)`, and `(not term)` is `(not (not inner))`: the excluded middle for
        // `(not inner)` turns the one into the other
        let not_inner = b.not(&inner);
        let excluded = super::binder::excluded_middle(b, &not_inner)?;
        return Ok(Some(
            b.resolve(vec![escape, excluded], vec![(inner, true)])?,
        ));
    }
    if term.as_quant().is_some() {
        return guard_escape_quantifier(b, term, polarity, guard, failed);
    }
    if polarity {
        if term == guard {
            return Ok(Some(super::binder::excluded_middle(b, guard)?));
        }
        let Some(conjuncts) = match_term!((and ...) = term).map(<[_]>::to_vec) else {
            return Ok(None);
        };
        for (i, conjunct) in conjuncts.iter().enumerate() {
            let Some(escape) = guard_escape(b, conjunct, true, guard, failed)? else {
                continue;
            };
            let not_term = b.not(term);
            let index = b.pool.add(Term::new_int(i));
            let and_pos = b.step(
                vec![not_term, conjunct.clone()],
                "and_pos",
                Vec::new(),
                vec![index],
            );
            return Ok(Some(b.resolve(
                vec![escape, and_pos],
                vec![(conjunct.clone(), false)],
            )?));
        }
        return Ok(None);
    }
    if let Some((antecedent, consequent)) = match_term!((=> p q) = term) {
        let (antecedent, consequent) = (antecedent.clone(), consequent.clone());
        if let Some(escape) = guard_escape(b, &antecedent, true, guard, failed)? {
            let implies_neg1 = b.step(
                vec![term.clone(), antecedent.clone()],
                "implies_neg1",
                Vec::new(),
                Vec::new(),
            );
            return Ok(Some(
                b.resolve(vec![escape, implies_neg1], vec![(antecedent, false)])?,
            ));
        }
        if let Some(escape) = guard_escape(b, &consequent, false, guard, failed)? {
            let not_consequent = b.not(&consequent);
            let implies_neg2 = b.step(
                vec![term.clone(), not_consequent],
                "implies_neg2",
                Vec::new(),
                Vec::new(),
            );
            return Ok(Some(
                b.resolve(vec![escape, implies_neg2], vec![(consequent, true)])?,
            ));
        }
        return Ok(None);
    }
    let Some(disjuncts) = match_term!((or ...) = term).map(<[_]>::to_vec) else {
        return Ok(None);
    };
    for (i, disjunct) in disjuncts.iter().enumerate() {
        let Some(escape) = guard_escape(b, disjunct, false, guard, failed)? else {
            continue;
        };
        let not_disjunct = b.not(disjunct);
        let index = b.pool.add(Term::new_int(i));
        let or_neg = b.step(
            vec![term.clone(), not_disjunct],
            "or_neg",
            Vec::new(),
            vec![index],
        );
        return Ok(Some(
            b.resolve(vec![escape, or_neg], vec![(disjunct.clone(), true)])?,
        ));
    }
    Ok(None)
}

/// The quantifier production of [`guard_escape`]. A guard reached under a binder is one the
/// binder does not bind, so it crosses it in both readings: at positive polarity the quantified
/// formula entails the guard, by instantiating it (a `forall` directly, an `exists` through its
/// dual); at negative polarity the guard's failure entails the quantified formula, by generalizing
/// (a `forall` by the generalized `bind`, an `exists` again through its dual).
fn guard_escape_quantifier(
    b: &mut Builder,
    term: &Rc<Term>,
    polarity: bool,
    guard: &Rc<Term>,
    failed: &mut HashSet<(Rc<Term>, bool)>,
) -> Result<Option<Rc<ProofNode>>, ElaborationError> {
    let (binder, bindings, inner) = term.as_quant().unwrap();
    let (bindings, inner) = (bindings.clone(), inner.clone());
    if !matches!(binder, Binder::Forall | Binder::Exists) {
        return Ok(None);
    }
    // The guard must survive the binder to be usable outside it
    let free = b.pool.free_vars(guard);
    if bindings
        .iter()
        .any(|var| free.contains(&b.pool.add(var.clone().into())))
    {
        return Ok(None);
    }

    // The `forall` the reasoning runs on, and the duality bridging it to an `exists`
    let (universal, body, duality) = match binder {
        Binder::Forall => (term.clone(), inner.clone(), None),
        _ => {
            let negated = b.not(&inner);
            let dual = b.pool.add(Term::Binder(
                Binder::Forall,
                bindings.clone(),
                negated.clone(),
            ));
            let duality = connective_def_duality(b, term, &dual);
            (dual, negated, Some(duality))
        }
    };
    // `exists` flips the reading: the dual `forall` is worked at the opposite polarity
    let inner_polarity = polarity == matches!(binder, Binder::Forall);

    let escape = if inner_polarity {
        // `(cl (not universal) guard)`: instantiate at dummy witnesses and let the body entail it
        let dummies = bindings
            .iter()
            .map(|var| super::binder::dummy_choice(b.pool, var))
            .collect();
        let (inst, instantiated) = instantiate(b, &universal, dummies)?;
        let Some(escape) = guard_escape(b, &instantiated, true, guard, failed)? else {
            return Ok(None);
        };
        b.resolve(vec![inst, escape], vec![(instantiated, true)])?
    } else {
        // `(cl universal guard)`: derive the body under an anchor and close it over the binder
        b.open();
        let Some(escape) = guard_escape(b, &body, false, guard, failed)? else {
            return Ok(None);
        };
        let Some(index) = escape.clause().iter().position(|t| *t == body) else {
            return Ok(None);
        };
        close_bind(b, &bindings.0, &bindings.0, index, escape)
    };

    let Some(duality) = duality else {
        return Ok(Some(escape));
    };
    // `escape` speaks of the dual `forall`; the duality carries it back to the `exists`
    let equality = duality.clause()[0].clone();
    let not_equality = b.not(&equality);
    let not_universal = b.not(&universal);
    let not_term = b.not(term);
    let bridged = if polarity {
        // `(cl (not term) (not universal))` from `(= term (not universal))`
        let equiv_pos2 = b.step(
            vec![not_equality, not_term, not_universal.clone()],
            "equiv_pos2",
            Vec::new(),
            Vec::new(),
        );
        let implication = b.resolve(vec![equiv_pos2, duality], vec![(equality, false)])?;
        b.resolve(vec![escape, implication], vec![(universal, true)])?
    } else {
        // `(cl term (not (not universal)))` from `(= term (not universal))`, with `not_not`
        // stripping the double negation
        let not_not_universal = b.not(&not_universal);
        let equiv_pos1 = b.step(
            vec![not_equality, term.clone(), not_not_universal.clone()],
            "equiv_pos1",
            Vec::new(),
            Vec::new(),
        );
        let implication = b.resolve(vec![equiv_pos1, duality], vec![(equality, false)])?;
        let triple = b.not(&not_not_universal);
        let not_not = b.step(
            vec![triple, universal.clone()],
            "not_not",
            Vec::new(),
            Vec::new(),
        );
        let with_universal =
            b.resolve(vec![implication, not_not], vec![(not_not_universal, true)])?;
        b.resolve(vec![with_universal, escape], vec![(universal, true)])?
    };
    Ok(Some(bridged))
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
    // The right-hand side need not be σ(φ) verbatim; the case functions bridge the difference
    // when they can
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
    let Some(guards) = point_guards(Binder::Forall, args.body, args.points) else {
        return Ok(None);
    };

    let mut b = Builder::new(pool, step);
    // Bridge between σ(φ) and the right-hand side's body, when it is not σ(φ) verbatim: the two
    // may differ by the orientation of equality subterms or by repeated disjuncts of an `or`
    let e_corr = match orientation_bridge(&mut b, args.sigma_body, args.rhs_body) {
        Ok(bridge) => bridge,
        Err(()) => match disjunct_bridge(&mut b, args.sigma_body, args.rhs_body)? {
            Some(bridge) => Some(bridge),
            None => return Ok(None),
        },
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
            derive_body_from_substituted(&mut b, args, &phi_prime, &guards, e_corr.as_ref())?;
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

/// Derives `(cl ¬φ' φ)` for a `forall` body.
///
/// A discharge subproof assumes `φ'` and rebuilds `φ` by cases on the guards: under a second,
/// nested discharge subproof that assumes them all, `φ` is just `σ(φ)` transported back along the
/// guard equalities, which the (bridged) assumption gives; and if any guard fails, `φ` holds
/// outright, since the guard's negation is one of its disjuncts — that is what [`guard_escape`]
/// derives. Resolving the two on each guard leaves `(cl φ)`.
fn derive_body_from_substituted(
    b: &mut Builder,
    args: &OnepointArgs,
    phi_prime: &Rc<Term>,
    guards: &[Rc<Term>],
    e_corr: Option<&Rc<ProofNode>>,
) -> Result<Option<Rc<ProofNode>>, ElaborationError> {
    let body = args.body;
    let point_vars = args.point_vars;
    b.open();
    let assumed = b.assume(phi_prime.clone());
    // Bridge the assumption to σ(φ), which is what the transport below starts from
    let outer_assumption = match e_corr {
        Some(eq) => {
            let flipped = b.symm(eq);
            eq_mp(b, assumed.clone(), flipped)?
        }
        None => assumed.clone(),
    };

    // The guards hold: transport σ(φ) back to φ
    b.open();
    let mut assumptions = Vec::new();
    let mut facts: IndexMap<Rc<Term>, Rc<ProofNode>> = IndexMap::new();
    for guard in guards {
        let assumption = b.assume(guard.clone());
        assumptions.push(assumption.clone());
        let Some((_, oriented)) = orient_guard(b, guard, point_vars, assumption) else {
            return Ok(None);
        };
        // `(= x t)` oriented; the transport replaces the values by the variables, so it is the
        // flipped equality that keys the facts
        let flipped = b.symm(&oriented);
        let key = match_term!((= a b) = flipped.clause()[0])
            .unwrap()
            .0
            .clone();
        facts.insert(key, flipped);
    }
    let Ok(eq) = transport(b, &facts, args.sigma_body, body) else {
        return Ok(None);
    };
    let body_node = match eq {
        Some(eq_node) => eq_mp(b, outer_assumption, eq_node)?,
        None => outer_assumption,
    };
    // `(cl ¬g₁ … ¬gₘ φ)`
    let mut result = b.close_subproof(assumptions, body_node);

    // Some guard fails: `φ` holds outright
    for guard in guards {
        if !result
            .clause()
            .iter()
            .any(|literal| literal.remove_negation() == Some(guard))
        {
            // A guard shared by two points, already discharged
            continue;
        }
        let mut failed = HashSet::new();
        let Some(escape) = guard_escape(b, body, false, guard, &mut failed)? else {
            return Ok(None);
        };
        result = b.resolve(vec![result, escape], vec![(guard.clone(), false)])?;
    }

    if result.clause() != [body.clone()] {
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

fn exists_onepoint(
    pool: &mut PrimitivePool,
    step: &StepNode,
    args: &OnepointArgs,
) -> Result<Option<Rc<ProofNode>>, ElaborationError> {
    let Some(guards) = point_guards(Binder::Exists, args.body, args.points) else {
        return Ok(None);
    };

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
        let sub =
            derive_substituted_from_body(&mut b, args, &guards, f_prime.as_ref(), e_corr.as_ref())?;
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

/// For the `exists` → direction: a discharge subproof assuming `φ`, extracting the guard
/// equalities out of it, transporting `φ` to `φ'`, and introducing the existential when the
/// right-hand side is quantified. Concludes `(cl ¬φ B)`.
fn derive_substituted_from_body(
    b: &mut Builder,
    args: &OnepointArgs,
    guards: &[Rc<Term>],
    f_prime: Option<&(Rc<Term>, Rc<ProofNode>)>,
    e_corr: Option<&Rc<ProofNode>>,
) -> Result<Option<Rc<ProofNode>>, ElaborationError> {
    let (body, rhs, rhs_body) = (args.body, args.rhs, args.rhs_body);
    let (kept, point_vars) = (args.kept, args.point_vars);
    b.open();
    let assumption = b.assume(body.clone());

    // Every guard is a conjunct of the body — that is what its positive polarity means — so
    // `guard_escape` carries it out of the assumption
    let mut facts: IndexMap<Rc<Term>, Rc<ProofNode>> = IndexMap::new();
    for guard in guards {
        let mut failed = HashSet::new();
        let Some(escape) = guard_escape(b, body, true, guard, &mut failed)? else {
            return Ok(None);
        };
        let fact = b.resolve(
            vec![escape, assumption.clone()],
            vec![(body.clone(), false)],
        )?;
        let Some((var, oriented)) = orient_guard(b, guard, point_vars, fact) else {
            return Ok(None);
        };
        facts.insert(var, oriented);
    }

    // Transport φ to σ(φ), then bridge to the (possibly reoriented) right-hand side body
    let Ok(eq) = transport(b, &facts, body, args.sigma_body) else {
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
