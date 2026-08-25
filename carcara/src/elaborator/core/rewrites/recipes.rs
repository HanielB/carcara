//! Core recipes for the rewrite rules: each derives `(cl (= lhs rhs))` for one rewrite-rule
//! instance, over the core fragment (plus the term-`ite` selection axioms `ite_then_intro` and
//! `ite_else_intro`, and `distinct_elim` as the definitional rule for `distinct`).
//!
//! The recipes cover the rules of `rewrites.eo` that the evaluation corpus exercises, plus every
//! rewrite the `*_simplify` traces can emit. A rule outside this set makes the reduction fail,
//! which keeps the original step (the pass is best-effort).

use super::super::Builder;
use super::rare_list;
use crate::{ast::*, checker::error::CheckerError, elaborator::error::ElaborationError};
use rug::Rational;

type Res = Result<Rc<ProofNode>, ElaborationError>;

fn explanation(msg: impl Into<String>) -> ElaborationError {
    CheckerError::Explanation(msg.into()).into()
}

fn eq(pool: &mut PrimitivePool, a: &Rc<Term>, b: &Rc<Term>) -> Rc<Term> {
    build_term!(pool, (= {a.clone()} {b.clone()}))
}

pub(super) fn true_ax(b: &mut Builder) -> Rc<ProofNode> {
    let t = b.pool.bool_true();
    b.step(vec![t], "true", Vec::new(), Vec::new())
}

pub(super) fn false_ax(b: &mut Builder) -> Rc<ProofNode> {
    let f = b.pool.bool_false();
    let nf = b.not(&f);
    b.step(vec![nf], "false", Vec::new(), Vec::new())
}

/// A `refl` step concluding `(cl (= t t))`. The caller has already checked that no anchor in
/// scope binds a variable of the conclusion, so the context substitution is the identity on it.
fn refl(b: &mut Builder, t: &Rc<Term>) -> Rc<ProofNode> {
    let clause = vec![eq(b.pool, t, t)];
    b.step(clause, "refl", Vec::new(), Vec::new())
}

/// Excluded middle: `(cl ¬x x)`, from `refl` and `equiv_pos2`.
fn em(b: &mut Builder, x: &Rc<Term>) -> Res {
    let e = eq(b.pool, x, x);
    let refl = refl(b, x);
    let not_e = b.not(&e);
    let not_x = b.not(x);
    let pos2 = b.step(
        vec![not_e, not_x, x.clone()],
        "equiv_pos2",
        Vec::new(),
        Vec::new(),
    );
    b.resolve(vec![pos2, refl], vec![(e, false)])
}

/// Double-negation introduction as a clause: `(cl ¬x ¬¬x)` — excluded middle at `¬x`.
pub(super) fn nn_intro(b: &mut Builder, x: &Rc<Term>) -> Res {
    let not_x = b.not(x);
    em(b, &not_x)
}

/// The `not_not` axiom `(cl ¬¬¬p p)`.
fn not_not_ax(b: &mut Builder, p: &Rc<Term>) -> Rc<ProofNode> {
    let n1 = b.not(p);
    let n2 = b.not(&n1);
    let n3 = b.not(&n2);
    b.step(vec![n3, p.clone()], "not_not", Vec::new(), Vec::new())
}

/// From a derivation of `(cl A)`, derives `(cl (= A true))`.
pub(super) fn bridge_true(b: &mut Builder, lit: Rc<ProofNode>, a: &Rc<Term>) -> Res {
    let t = b.pool.bool_true();
    let goal = eq(b.pool, a, &t);
    let not_a = b.not(a);
    let not_t = b.not(&t);
    let neg1 = b.step(
        vec![goal, not_a, not_t],
        "equiv_neg1",
        Vec::new(),
        Vec::new(),
    );
    let ta = true_ax(b);
    let r = b.resolve(vec![neg1, ta], vec![(t, false)])?;
    b.resolve(vec![r, lit], vec![(a.clone(), false)])
}

/// From a derivation of `(cl ¬A)`, derives `(cl (= A false))`.
pub(super) fn bridge_false(b: &mut Builder, not_lit: Rc<ProofNode>, a: &Rc<Term>) -> Res {
    let f = b.pool.bool_false();
    let goal = eq(b.pool, a, &f);
    let neg2 = b.step(
        vec![goal, a.clone(), f.clone()],
        "equiv_neg2",
        Vec::new(),
        Vec::new(),
    );
    let fa = false_ax(b);
    let r = b.resolve(vec![neg2, fa], vec![(f, true)])?;
    b.resolve(vec![r, not_lit], vec![(a.clone(), true)])
}

/// Closes an equivalence `(cl (= a b))` from direction clauses in *collapsed* literal form:
/// `dir1` concludes `(cl ¬̃a b)` and `dir2` concludes `(cl a ¬̃b)`, where `¬̃x` is `c` when
/// `x = ¬c` and `¬x` otherwise — the form `la_generic` can conclude directly. The assembly
/// resolves against the `equiv_neg` axioms, using the fact that `¬c` and `c` (and `¬¬c` and
/// `¬c`) are already syntactic complements.
fn equiv_collapsed(
    b: &mut Builder,
    a: &Rc<Term>,
    bt: &Rc<Term>,
    dir1: Rc<ProofNode>,
    dir2: Rc<ProofNode>,
) -> Res {
    let equiv = eq(b.pool, a, bt);
    let (not_a, not_b) = (b.not(a), b.not(bt));
    let neg2 = b.step(
        vec![equiv.clone(), a.clone(), bt.clone()],
        "equiv_neg2",
        Vec::new(),
        Vec::new(),
    );
    let neg1 = b.step(
        vec![equiv.clone(), not_a, not_b],
        "equiv_neg1",
        Vec::new(),
        Vec::new(),
    );
    let pivot_a = match a.remove_negation() {
        Some(c) => (c.clone(), false),
        None => (a.clone(), true),
    };
    let s1 = b.resolve(vec![neg2, dir1], vec![pivot_a])?;
    let s2 = b.resolve(vec![neg1, dir2], vec![(a.clone(), false)])?;
    match bt.remove_negation() {
        None => b.resolve(vec![s1, s2], vec![(bt.clone(), true)]),
        Some(d) => {
            let d = d.clone();
            let not_d = b.not(&d);
            let r3 = b.resolve(vec![s2, s1.clone()], vec![(not_d, false)])?;
            b.resolve(vec![r3, s1], vec![(d, true)])
        }
    }
}

/// An `la_generic` clause validated before emission, trying a few coefficient sign choices.
pub(super) fn la_clause(b: &mut Builder, literals: Vec<Rc<Term>>) -> Res {
    let n = literals.len();
    let candidates: Vec<Vec<Rational>> = match n {
        1 => vec![vec![Rational::from(1)]],
        2 => vec![
            vec![Rational::from(1), Rational::from(1)],
            vec![Rational::from(1), Rational::from(-1)],
            vec![Rational::from(-1), Rational::from(1)],
            vec![Rational::from(-1), Rational::from(-1)],
        ],
        _ => return Err(explanation("unsupported la_generic clause size")),
    };
    for coeffs in candidates {
        if let Ok(node) = super::super::arithmetic::farkas(b, literals.clone(), coeffs) {
            return Ok(node);
        }
    }
    Err(explanation(
        "no Farkas certificate for the atom equivalence",
    ))
}

/// The collapsed negation of a literal: `c` for `¬c`, `¬x` otherwise.
fn collapse_not(b: &mut Builder, x: &Rc<Term>) -> Rc<Term> {
    match x.remove_negation() {
        Some(c) => c.clone(),
        None => b.not(x),
    }
}

/// `(= (= t c) false)`, where `t` is integer-valued and `c` is a constant that is not an integer.
///
/// No axiom about rounding is needed: `la_generic`'s strengthening already knows that an integer
/// cannot sit strictly between two consecutive integers, so `(cl ¬(t <= c) ¬(c <= t))` is a Farkas
/// clause. What the recipe has to supply is the step from the equality to the two bounds, which is
/// `la_rw_eq` — the core's definitional rule for an arithmetic equality — split with `and_pos`.
fn int_eq_conflict(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    if !rhs.is_bool_false() {
        return Err(explanation("`arith-int-eq-conflict` does not conclude `false`"));
    }
    let (t, c) = match_term_err!((= t c) = lhs)?;
    let (t, c) = (t.clone(), c.clone());
    let le_tc = build_term!(b.pool, (<= {t.clone()} {c.clone()}));
    let le_ct = build_term!(b.pool, (<= {c.clone()} {t.clone()}));
    let conj = build_term!(b.pool, (and {le_tc.clone()} {le_ct.clone()}));

    // The two bounds cannot both hold: that is the whole content of the rewrite
    let (n_tc, n_ct) = (b.not(&le_tc), b.not(&le_ct));
    let conflict = la_clause(b, vec![n_tc, n_ct])?;

    // `(= t c)` gives the conjunction of the two bounds, and `and_pos` gives each conjunct
    let rw = eq(b.pool, lhs, &conj);
    let rw = b.step(vec![rw], "la_rw_eq", Vec::new(), Vec::new());
    let not_lhs = b.not(lhs);
    let split = b.step(
        vec![not_lhs, conj.clone()],
        "equiv1",
        vec![rw],
        Vec::new(),
    );
    let not_conj = b.not(&conj);
    let mut bounds = Vec::new();
    for (i, bound) in [le_tc.clone(), le_ct.clone()].into_iter().enumerate() {
        let index = b.pool.add(Term::new_int(i));
        let pos = b.step(
            vec![not_conj.clone(), bound],
            "and_pos",
            Vec::new(),
            vec![index],
        );
        bounds.push(b.resolve(vec![split.clone(), pos], vec![(conj.clone(), true)])?);
    }
    let [lower, upper]: [Rc<ProofNode>; 2] = bounds.try_into().unwrap();
    let unit = b.resolve(
        vec![conflict, lower, upper],
        vec![(le_tc, false), (le_ct, false)],
    )?;
    bridge_false(b, unit, lhs)
}

/// An equivalence `(= A B)` between two (possibly negated) linear-arithmetic atoms, by one
/// Farkas certificate per direction.
fn atom_equiv(b: &mut Builder, a: &Rc<Term>, bt: &Rc<Term>) -> Res {
    let ca = collapse_not(b, a);
    let cb = collapse_not(b, bt);
    let dir1 = la_clause(b, vec![ca, bt.clone()])?;
    let dir2 = la_clause(b, vec![a.clone(), cb])?;
    equiv_collapsed(b, a, bt, dir1, dir2)
}

/// The `ite_then_intro` axiom for an ite term: `(cl ¬c, I ≈ then)`.
pub(super) fn sel_then(
    b: &mut Builder,
    ite: &Rc<Term>,
) -> Result<(Rc<ProofNode>, Rc<Term>), ElaborationError> {
    let (c, t, _) = match_term_err!((ite c t s) = ite)?;
    let (c, t) = (c.clone(), t.clone());
    let e = eq(b.pool, ite, &t);
    let not_c = b.not(&c);
    let node = b.step(
        vec![not_c, e.clone()],
        "ite_then_intro",
        Vec::new(),
        Vec::new(),
    );
    Ok((node, e))
}

/// The `ite_else_intro` axiom for an ite term: `(cl c, I ≈ else)`.
pub(super) fn sel_else(
    b: &mut Builder,
    ite: &Rc<Term>,
) -> Result<(Rc<ProofNode>, Rc<Term>), ElaborationError> {
    let (c, _, s) = match_term_err!((ite c t s) = ite)?;
    let (c, s) = (c.clone(), s.clone());
    let e = eq(b.pool, ite, &s);
    let node = b.step(
        vec![c.clone(), e.clone()],
        "ite_else_intro",
        Vec::new(),
        Vec::new(),
    );
    Ok((node, e))
}

/// From clauses `(cl gᵢ eqᵢ)` (each pairing one guard literal with a unit equality), derives
/// `(cl g₁ … gₙ target)` where `target` is assembled from the assumed equalities by the closure
/// (typically `trans`/`symm`/`cong`). Guard literals repeated across parts are merged by the
/// resolutions' set semantics.
fn guarded(
    b: &mut Builder,
    parts: Vec<(Rc<ProofNode>, Rc<Term>)>,
    assemble: impl FnOnce(&mut Builder, Vec<Rc<ProofNode>>) -> Res,
) -> Res {
    b.open();
    // Two parts can carry the same equality (e.g. when a lookahead's inner `ite` is the
    // right-hand side itself): assume each distinct equality once
    let mut distinct: indexmap::IndexMap<Rc<Term>, Rc<ProofNode>> = indexmap::IndexMap::new();
    for (_, e) in &parts {
        if !distinct.contains_key(e) {
            let h = b.assume(e.clone());
            distinct.insert(e.clone(), h);
        }
    }
    let assumes: Vec<_> = parts.iter().map(|(_, e)| distinct[e].clone()).collect();
    let inner = assemble(b, assumes)?;
    let discharge: Vec<_> = distinct.values().cloned().collect();
    let mut node = b.close_subproof(discharge, inner);
    let mut resolved = std::collections::HashSet::new();
    for (part, e) in parts {
        if !resolved.insert(e.clone()) {
            continue;
        }
        node = b.resolve(vec![node, part], vec![(e, false)])?;
    }
    Ok(node)
}

/// `trans` over unit-equality nodes, flipping the ones marked with `true` by `symm`.
#[allow(clippy::unnecessary_wraps)]
fn trans_chain(b: &mut Builder, links: Vec<(Rc<ProofNode>, bool)>) -> Res {
    let nodes: Vec<_> = links
        .into_iter()
        .map(|(node, flip)| if flip { b.symm(&node) } else { node })
        .collect();
    if nodes.len() == 1 {
        return Ok(nodes.into_iter().next().unwrap());
    }
    let (first, _) = match_term!((= a b) = nodes.first().unwrap().clause()[0]).unwrap();
    let (_, last) = match_term!((= a b) = nodes.last().unwrap().clause()[0]).unwrap();
    let clause = vec![build_term!(b.pool, (= {first.clone()} {last.clone()}))];
    Ok(b.step(clause, "trans", nodes, Vec::new()))
}

pub(super) fn and_pos_step(b: &mut Builder, and_term: &Rc<Term>, i: usize) -> Res {
    let args = match_term_err!((and ...) = and_term)?;
    let arg = args[i].clone();
    let not_and = b.not(and_term);
    let index = b.pool.add(Term::new_int(i as i64));
    Ok(b.step(vec![not_and, arg], "and_pos", Vec::new(), vec![index]))
}

fn and_neg_step(b: &mut Builder, and_term: &Rc<Term>) -> Res {
    let args = match_term_err!((and ...) = and_term)?.to_vec();
    let mut clause = vec![and_term.clone()];
    for arg in args {
        clause.push(b.not(&arg));
    }
    Ok(b.step(clause, "and_neg", Vec::new(), Vec::new()))
}

pub(super) fn or_pos_step(b: &mut Builder, or_term: &Rc<Term>) -> Res {
    let args = match_term_err!((or ...) = or_term)?.to_vec();
    let not_or = b.not(or_term);
    let mut clause = vec![not_or];
    clause.extend(args);
    Ok(b.step(clause, "or_pos", Vec::new(), Vec::new()))
}

pub(super) fn or_neg_step(b: &mut Builder, or_term: &Rc<Term>, i: usize) -> Res {
    let args = match_term_err!((or ...) = or_term)?;
    let not_arg = b.not(&args[i].clone());
    let index = b.pool.add(Term::new_int(i as i64));
    Ok(b.step(
        vec![or_term.clone(), not_arg],
        "or_neg",
        Vec::new(),
        vec![index],
    ))
}

/// Packs the literals `lits` (each an argument of `or_term`, at the given indices) occurring in
/// `node`'s clause into the `or` term, by one `or_neg` + resolution per literal.
fn pack_or(
    b: &mut Builder,
    mut node: Rc<ProofNode>,
    or_term: &Rc<Term>,
    lits: &[(Rc<Term>, usize)],
) -> Res {
    // Resolution has set semantics: a duplicated literal is gone after its first packing
    let mut seen = std::collections::HashSet::new();
    for (lit, i) in lits {
        if !seen.insert(lit.clone()) {
            continue;
        }
        let neg = or_neg_step(b, or_term, *i)?;
        node = b.resolve(vec![node, neg], vec![(lit.clone(), true)])?;
    }
    Ok(node)
}

/// The recipe dispatcher: derives `(cl (= lhs rhs))` for the named rewrite rule.
pub fn rewrite_lemma(b: &mut Builder, name: &str, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    match name {
        // ------------------------------------------------------------------ arithmetic atoms
        "arith-elim-lt"
        | "arith-elim-gt"
        | "arith-elim-leq"
        | "arith-elim-int-gt"
        | "arith-elim-int-lt"
        | "arith-leq-norm"
        | "arith-geq-tighten"
        | "arith-int-geq-tighten"
        | "arith-geq-norm1-int"
        | "arith-geq-norm1-real"
        | "comp-lt-elim"
        | "comp-gt-elim"
        | "comp-geq-flip" => atom_equiv(b, lhs, rhs),
        "comp-lt-irrefl" => {
            // `(= (< t t) false)`
            let not_lhs = b.not(lhs);
            let unit = la_clause(b, vec![not_lhs])?;
            bridge_false(b, unit, lhs)
        }
        "comp-leq-refl" => {
            // `(= (<= t t) true)`
            let unit = la_clause(b, vec![lhs.clone()])?;
            bridge_true(b, unit, lhs)
        }
        "arith-eq-elim-int" | "arith-eq-elim-real" => arith_eq_elim(b, lhs, rhs),
        "arith-int-eq-conflict" => int_eq_conflict(b, lhs, rhs),

        // ------------------------------------------------------------------ equality logic
        "eq-refl" => {
            // `(= (= t t) true)`
            let r = refl(b, match_term_err!((= t t) = lhs)?.0);
            bridge_true(b, r, lhs)
        }
        "eq-symm" => {
            // `(= (= t s) (= s t))`
            let dir1 = {
                b.open();
                let h = b.assume(lhs.clone());
                let s = b.symm(&h);
                b.close_subproof(vec![h], s)
            };
            let dir2 = {
                b.open();
                let h = b.assume(rhs.clone());
                let s = b.symm(&h);
                b.close_subproof(vec![h], s)
            };
            b.equiv_intro(lhs.clone(), rhs.clone(), dir1, dir2)
        }
        "bool-not-eq-false" => {
            // `(= (not (= t t)) false)`
            let (t, _) = match_term_err!((not (= t t)) = lhs)?;
            let t = t.clone();
            let e = eq(b.pool, &t, &t);
            let r = refl(b, &t);
            let nn = nn_intro(b, &e)?;
            let unit = b.resolve(vec![nn, r], vec![(e, false)])?;
            bridge_false(b, unit, lhs)
        }

        // ------------------------------------------------------------------ propositional
        "bool-double-not-elim" => {
            // `(= ¬¬t t)`
            let t = match_term_err!((not (not t)) = lhs)?.clone();
            let dir1 = not_not_ax(b, &t);
            let dir2 = nn_intro(b, &t)?;
            b.equiv_intro(lhs.clone(), t, dir1, dir2)
        }
        "bool-eq-true" | "equiv-true-l" => {
            // `(= (= t true) t)` / `(= (= true t) t)`
            let (p1, p2) = match_term_err!((= p1 p2) = lhs)?;
            let (p1, p2) = (p1.clone(), p2.clone());
            let tt = b.pool.bool_true();
            let flip = p1 == tt;
            let phi = if flip { p2.clone() } else { p1.clone() };
            let not_lhs = b.not(lhs);
            let np1 = b.not(&p1);
            let np2 = b.not(&p2);
            let ta1 = true_ax(b);
            let ta2 = true_ax(b);
            // equiv_pos1: (cl ¬lhs p1 ¬p2); equiv_pos2: (cl ¬lhs ¬p1 p2)
            // equiv_neg1: (cl lhs ¬p1 ¬p2)
            let (dir1, dir2) = if flip {
                // p1 = true, p2 = phi: dir1 = (cl ¬lhs phi) from pos2 + true axiom;
                // dir2 = (cl lhs ¬phi) from neg1 + true axiom
                let pos2 = b.step(
                    vec![not_lhs, np1.clone(), p2.clone()],
                    "equiv_pos2",
                    Vec::new(),
                    Vec::new(),
                );
                let d1 = b.resolve(vec![pos2, ta1], vec![(p1.clone(), false)])?;
                let neg1 = b.step(
                    vec![lhs.clone(), np1, np2],
                    "equiv_neg1",
                    Vec::new(),
                    Vec::new(),
                );
                let d2 = b.resolve(vec![neg1, ta2], vec![(p1.clone(), false)])?;
                (d1, d2)
            } else {
                // p1 = phi, p2 = true: dir1 = (cl ¬lhs phi) from pos1 + true axiom;
                // dir2 = (cl lhs ¬phi) from neg1 + true axiom
                let pos1 = b.step(
                    vec![not_lhs, p1.clone(), np2.clone()],
                    "equiv_pos1",
                    Vec::new(),
                    Vec::new(),
                );
                let d1 = b.resolve(vec![pos1, ta1], vec![(p2.clone(), false)])?;
                let neg1 = b.step(
                    vec![lhs.clone(), np1, np2],
                    "equiv_neg1",
                    Vec::new(),
                    Vec::new(),
                );
                let d2 = b.resolve(vec![neg1, ta2], vec![(p2.clone(), false)])?;
                (d1, d2)
            };
            b.equiv_intro(lhs.clone(), phi, dir1, dir2)
        }
        "bool-eq-false" | "equiv-false-l" => {
            // `(= (= t false) ¬t)` / `(= (= false t) ¬t)`
            let (p1, p2) = match_term_err!((= p1 p2) = lhs)?;
            let (p1, p2) = (p1.clone(), p2.clone());
            let ff = b.pool.bool_false();
            let flip = p1 == ff;
            let phi = if flip { p2.clone() } else { p1.clone() };
            let not_lhs = b.not(lhs);
            let np1 = b.not(&p1);
            let np2 = b.not(&p2);
            let fa1 = false_ax(b);
            let fa2 = false_ax(b);
            let (dir1, dir2) = if flip {
                // p1 = false, p2 = phi: dir1 = (cl ¬lhs ¬phi) from pos1 + false axiom;
                // dir2 collapsed = (cl lhs phi) from neg2 + false axiom
                let pos1 = b.step(
                    vec![not_lhs, p1.clone(), np2],
                    "equiv_pos1",
                    Vec::new(),
                    Vec::new(),
                );
                let d1 = b.resolve(vec![pos1, fa1], vec![(p1.clone(), true)])?;
                let neg2 = b.step(
                    vec![lhs.clone(), p1.clone(), p2.clone()],
                    "equiv_neg2",
                    Vec::new(),
                    Vec::new(),
                );
                let d2 = b.resolve(vec![neg2, fa2], vec![(p1.clone(), true)])?;
                (d1, d2)
            } else {
                // p1 = phi, p2 = false: dir1 = (cl ¬lhs ¬phi) from pos2 + false axiom;
                // dir2 collapsed = (cl lhs phi) from neg2 + false axiom
                let pos2 = b.step(
                    vec![not_lhs, np1, p2.clone()],
                    "equiv_pos2",
                    Vec::new(),
                    Vec::new(),
                );
                let d1 = b.resolve(vec![pos2, fa1], vec![(p2.clone(), true)])?;
                let neg2 = b.step(
                    vec![lhs.clone(), p1.clone(), p2.clone()],
                    "equiv_neg2",
                    Vec::new(),
                    Vec::new(),
                );
                let d2 = b.resolve(vec![neg2, fa2], vec![(p2.clone(), true)])?;
                (d1, d2)
            };
            let not_phi = b.not(&phi);
            debug_assert_eq!(not_phi, *rhs);
            equiv_collapsed(b, lhs, &not_phi, dir1, dir2)
        }
        "bool-eq-nrefl" | "equiv-neg-l" => {
            // `(= (= x ¬x) false)` / `(= (= ¬x x) false)`
            let (p1, p2) = match_term_err!((= p1 p2) = lhs)?;
            let (p1, p2) = (p1.clone(), p2.clone());
            let not_lhs = b.not(lhs);
            let (x, x_first) = match p2.remove_negation() {
                Some(inner) if *inner == p1 => (p1.clone(), true),
                _ => (p2.clone(), false),
            };
            let nx = b.not(&x);
            let nnx = b.not(&nx);
            // equiv_pos1: (cl ¬lhs p1 ¬p2); equiv_pos2: (cl ¬lhs ¬p1 p2)
            let (with_nn, with_dup) = if x_first {
                // p1 = x, p2 = ¬x: pos1 = (cl ¬lhs x ¬¬x); pos2 = (cl ¬lhs ¬x ¬x)
                let pos1 = b.step(
                    vec![not_lhs.clone(), x.clone(), nnx.clone()],
                    "equiv_pos1",
                    Vec::new(),
                    Vec::new(),
                );
                let pos2 = b.step(
                    vec![not_lhs.clone(), nx.clone(), nx.clone()],
                    "equiv_pos2",
                    Vec::new(),
                    Vec::new(),
                );
                (pos1, pos2)
            } else {
                // p1 = ¬x, p2 = x: pos1 = (cl ¬lhs ¬x ¬x); pos2 = (cl ¬lhs ¬¬x x)
                let pos1 = b.step(
                    vec![not_lhs.clone(), nx.clone(), nx.clone()],
                    "equiv_pos1",
                    Vec::new(),
                    Vec::new(),
                );
                let pos2 = b.step(
                    vec![not_lhs.clone(), nnx.clone(), x.clone()],
                    "equiv_pos2",
                    Vec::new(),
                    Vec::new(),
                );
                (pos2, pos1)
            };
            // `with_nn` = (cl ¬lhs {x ¬¬x} or {¬¬x x}); `with_dup` = (cl ¬lhs ¬x ¬x)
            let contracted = b.step(
                vec![not_lhs.clone(), nx.clone()],
                "contraction",
                vec![with_dup],
                Vec::new(),
            );
            let nn = not_not_ax(b, &x);
            let no_nn = b.resolve(vec![with_nn, nn], vec![(nnx, true)])?;
            // no_nn = (cl ¬lhs x); contracted = (cl ¬lhs ¬x)
            let unit = b.resolve(vec![no_nn, contracted], vec![(x, true)])?;
            bridge_false(b, unit, lhs)
        }
        "equiv-neg-both" => equiv_neg_both(b, lhs, rhs),

        // ------------------------------------------------------------------ implication
        "bool-impl-elim" => bool_impl_elim(b, lhs, rhs),
        "bool-impl-true2" => {
            // `(= (=> true t) t)`
            let (_, t) = match_term_err!((=> c t) = lhs)?;
            let t = t.clone();
            let not_lhs = b.not(lhs);
            let tt = b.pool.bool_true();
            let ntt = b.not(&tt);
            let pos = b.step(
                vec![not_lhs, ntt, t.clone()],
                "implies_pos",
                Vec::new(),
                Vec::new(),
            );
            let ta = true_ax(b);
            let dir1 = b.resolve(vec![pos, ta], vec![(tt, false)])?;
            let nt = b.not(&t);
            let dir2 = b.step(
                vec![lhs.clone(), nt],
                "implies_neg2",
                Vec::new(),
                Vec::new(),
            );
            b.equiv_intro(lhs.clone(), t, dir1, dir2)
        }
        "bool-impl-true1" => {
            // `(= (=> t true) true)`
            let tt = b.pool.bool_true();
            let ntt = b.not(&tt);
            let neg2 = b.step(
                vec![lhs.clone(), ntt],
                "implies_neg2",
                Vec::new(),
                Vec::new(),
            );
            let ta = true_ax(b);
            let unit = b.resolve(vec![neg2, ta], vec![(tt, false)])?;
            bridge_true(b, unit, lhs)
        }
        "bool-impl-false2" => {
            // `(= (=> false t) true)`
            let ff = b.pool.bool_false();
            let neg1 = b.step(
                vec![lhs.clone(), ff.clone()],
                "implies_neg1",
                Vec::new(),
                Vec::new(),
            );
            let fa = false_ax(b);
            let unit = b.resolve(vec![neg1, fa], vec![(ff, true)])?;
            bridge_true(b, unit, lhs)
        }
        "bool-impl-false1" => {
            // `(= (=> t false) ¬t)`
            let (t, _) = match_term_err!((=> t f) = lhs)?;
            let t = t.clone();
            let not_lhs = b.not(lhs);
            let nt = b.not(&t);
            let ff = b.pool.bool_false();
            let pos = b.step(
                vec![not_lhs, nt.clone(), ff.clone()],
                "implies_pos",
                Vec::new(),
                Vec::new(),
            );
            let fa = false_ax(b);
            let dir1 = b.resolve(vec![pos, fa], vec![(ff, true)])?;
            let dir2 = b.step(vec![lhs.clone(), t], "implies_neg1", Vec::new(), Vec::new());
            debug_assert_eq!(nt, *rhs);
            equiv_collapsed(b, lhs, &nt, dir1, dir2)
        }
        "implies-refl" => {
            // `(= (=> t t) true)`
            let (t, _) = match_term_err!((=> t t) = lhs)?;
            let t = t.clone();
            let neg1 = b.step(
                vec![lhs.clone(), t.clone()],
                "implies_neg1",
                Vec::new(),
                Vec::new(),
            );
            let nt = b.not(&t);
            let neg2 = b.step(
                vec![lhs.clone(), nt],
                "implies_neg2",
                Vec::new(),
                Vec::new(),
            );
            let unit = b.resolve(vec![neg1, neg2], vec![(t, true)])?;
            bridge_true(b, unit, lhs)
        }
        "implies-neg" | "implies-neg-l" | "implies-neg-r" => {
            let (p1, p2) = match_term_err!((=> p1 p2) = lhs)?;
            let (p1, p2) = (p1.clone(), p2.clone());
            let not_lhs = b.not(lhs);
            let np1 = b.not(&p1);
            let pos = b.step(
                vec![not_lhs, np1.clone(), p2.clone()],
                "implies_pos",
                Vec::new(),
                Vec::new(),
            );
            if p1.remove_negation() == Some(&p2) {
                // `(= (=> ¬t t) t)`
                let nn = not_not_ax(b, &p2);
                let dir1 = b.resolve(vec![pos, nn], vec![(np1, true)])?;
                let np2 = b.not(&p2);
                let dir2 = b.step(
                    vec![lhs.clone(), np2],
                    "implies_neg2",
                    Vec::new(),
                    Vec::new(),
                );
                b.equiv_intro(lhs.clone(), p2, dir1, dir2)
            } else {
                // `(= (=> t ¬t) ¬t)`: `pos` is (cl ¬lhs ¬t ¬t)
                let nl = b.not(lhs);
                let contracted =
                    b.step(vec![nl, np1.clone()], "contraction", vec![pos], Vec::new());
                let dir2 = b.step(
                    vec![lhs.clone(), p1.clone()],
                    "implies_neg1",
                    Vec::new(),
                    Vec::new(),
                );
                equiv_collapsed(b, lhs, &p2, contracted, dir2)
            }
        }
        "implies-contra" => implies_contra(b, lhs, rhs),
        "bool-implies-peirce" => peirce(b, lhs, rhs),
        "bool-implies-uncurry" => uncurry(b, lhs, rhs),
        "bool-and-mp-r" | "bool-and-mp-l" => and_mp(b, lhs, rhs),
        "bool-implies-de-morgan" => implies_de_morgan(b, lhs, rhs),
        "bool-or-de-morgan" => or_de_morgan(b, lhs, rhs),
        "bool-and-de-morgan" => and_de_morgan(b, lhs, rhs),
        "bool-implies-or-distrib" => implies_or_distrib(b, lhs, rhs),
        "bool-or-and-distrib" => or_and_distrib(b, lhs, rhs),

        // ------------------------------------------------------------------ n-ary and/or
        "and-flatten" | "or-flatten" => flatten(b, lhs, rhs),
        "and-true-elim" | "or-false-elim" => elim_neutral(b, lhs, rhs),
        "and-dup-elim" | "or-dup-elim" => elim_dup(b, lhs, rhs),
        "and-false" => {
            // `(= (and xs false ys) false)`
            let args = match_term_err!((and ...) = lhs)?;
            let pos = args
                .iter()
                .position(|t| t.is_bool_false())
                .ok_or_else(|| explanation("no false conjunct"))?;
            let ap = and_pos_step(b, lhs, pos)?;
            let fa = false_ax(b);
            let ff = b.pool.bool_false();
            let unit = b.resolve(vec![ap, fa], vec![(ff, true)])?;
            bridge_false(b, unit, lhs)
        }
        "or-true" => {
            // `(= (or xs true ys) true)`
            let args = match_term_err!((or ...) = lhs)?;
            let pos = args
                .iter()
                .position(|t| t.is_bool_true())
                .ok_or_else(|| explanation("no true disjunct"))?;
            let on = or_neg_step(b, lhs, pos)?;
            let ta = true_ax(b);
            let tt = b.pool.bool_true();
            let unit = b.resolve(vec![on, ta], vec![(tt, false)])?;
            bridge_true(b, unit, lhs)
        }
        "bool-and-conf" | "bool-and-conf2" => {
            // `(= (and xs w ys ¬w zs) false)` (and the flipped variant)
            let args = match_term_err!((and ...) = lhs)?.to_vec();
            let (i, k) = complementary_pair(&args)
                .ok_or_else(|| explanation("no complementary conjuncts"))?;
            let a1 = and_pos_step(b, lhs, i)?;
            let a2 = and_pos_step(b, lhs, k)?;
            let (pos_lit, positive_first) = match args[i].remove_negation() {
                Some(inner) => (inner.clone(), false),
                None => (args[i].clone(), true),
            };
            let unit = if positive_first {
                b.resolve(vec![a1, a2], vec![(pos_lit, true)])?
            } else {
                b.resolve(vec![a2, a1], vec![(pos_lit, true)])?
            };
            bridge_false(b, unit, lhs)
        }
        "bool-or-taut" | "bool-or-taut2" => {
            // `(= (or xs w ys ¬w zs) true)` (and the flipped variant)
            let args = match_term_err!((or ...) = lhs)?.to_vec();
            let (i, k) = complementary_pair(&args)
                .ok_or_else(|| explanation("no complementary disjuncts"))?;
            let o1 = or_neg_step(b, lhs, i)?;
            let o2 = or_neg_step(b, lhs, k)?;
            let (neg_lit, positive_first) = match args[i].remove_negation() {
                Some(_) => (args[i].clone(), false),
                None => (args[k].clone(), true),
            };
            // o1 = (cl A ¬w), o2 = (cl A ¬¬w) (in some order); resolve on the complement pair
            let unit = if positive_first {
                b.resolve(vec![o2, o1], vec![(neg_lit, false)])?
            } else {
                b.resolve(vec![o1, o2], vec![(neg_lit, false)])?
            };
            bridge_true(b, unit, lhs)
        }
        "or-not-refl" => or_not_refl(b, lhs, rhs),
        "distinct-false" => distinct_false(b, lhs, rhs),

        // ------------------------------------------------------------------ term-level ite
        "ite-true-cond" => {
            let (sel, e) = sel_then(b, lhs)?;
            let ta = true_ax(b);
            let tt = b.pool.bool_true();
            let node = b.resolve(vec![sel, ta], vec![(tt, false)])?;
            let _ = e;
            Ok(node)
        }
        "ite-false-cond" => {
            let (sel, _) = sel_else(b, lhs)?;
            let fa = false_ax(b);
            let ff = b.pool.bool_false();
            b.resolve(vec![sel, fa], vec![(ff, true)])
        }
        "ite-eq-branch" => {
            // `(= (ite c x x) x)`
            let (c, _, _) = match_term_err!((ite c t s) = lhs)?;
            let c = c.clone();
            let (s1, _) = sel_then(b, lhs)?;
            let (s2, _) = sel_else(b, lhs)?;
            b.resolve(vec![s2, s1], vec![(c, true)])
        }
        "ite-eq" => ite_eq(b, lhs, rhs),
        "ite-not-cond" => ite_not_cond(b, lhs, rhs),
        "ite-then-lookahead" | "ite-else-lookahead" => ite_lookahead(b, lhs, rhs),
        "ite-then-true" | "ite-else-false" | "ite-then-false" | "ite-else-true" => {
            bool_ite_shape(b, lhs, rhs)
        }
        "ite-then-true-else-false" => {
            // `(= (ite c true false) c)`
            let (c, _, _) = match_term_err!((ite c t s) = lhs)?;
            let c = c.clone();
            let nc = b.not(&c);
            let ff = b.pool.bool_false();
            let tt = b.pool.bool_true();
            let not_lhs = b.not(lhs);
            // dir1 = (cl ¬lhs c): ite_pos1 = (cl ¬lhs c ¬... wait: ite_pos1 = (cl ¬(ite c a b) c b)
            let pos1 = b.step(
                vec![not_lhs, c.clone(), ff.clone()],
                "ite_pos1",
                Vec::new(),
                Vec::new(),
            );
            let fa = false_ax(b);
            let dir1 = b.resolve(vec![pos1, fa], vec![(ff, true)])?;
            // dir2 = (cl lhs ¬c): ite_neg2 = (cl (ite c a b) ¬c ¬a)
            let ntt = b.not(&tt);
            let neg2 = b.step(
                vec![lhs.clone(), nc, ntt],
                "ite_neg2",
                Vec::new(),
                Vec::new(),
            );
            let ta = true_ax(b);
            let dir2 = b.resolve(vec![neg2, ta], vec![(tt, false)])?;
            b.equiv_intro(lhs.clone(), c, dir1, dir2)
        }
        "ite-then-false-else-true" => {
            // `(= (ite c false true) ¬c)`
            let (c, _, _) = match_term_err!((ite c t s) = lhs)?;
            let c = c.clone();
            let nc = b.not(&c);
            let ff = b.pool.bool_false();
            let tt = b.pool.bool_true();
            let not_lhs = b.not(lhs);
            // dir1 = (cl ¬lhs ¬c): ite_pos2 = (cl ¬(ite c a b) ¬c a)
            let pos2 = b.step(
                vec![not_lhs, nc.clone(), ff.clone()],
                "ite_pos2",
                Vec::new(),
                Vec::new(),
            );
            let fa = false_ax(b);
            let dir1 = b.resolve(vec![pos2, fa], vec![(ff, true)])?;
            // dir2 collapsed = (cl lhs c): ite_neg1 = (cl (ite c a b) c ¬b)
            let ntt = b.not(&tt);
            let neg1 = b.step(
                vec![lhs.clone(), c.clone(), ntt],
                "ite_neg1",
                Vec::new(),
                Vec::new(),
            );
            let ta = true_ax(b);
            let dir2 = b.resolve(vec![neg1, ta], vec![(tt, false)])?;
            equiv_collapsed(b, lhs, &nc, dir1, dir2)
        }
        "arith-geq-ite-lift" | "arith-leq-ite-lift" | "eq-ite-lift" => rel_ite_lift(b, lhs, rhs),

        _ => Err(explanation(format!(
            "no core recipe for rewrite rule '{name}'"
        ))),
    }
}

/// Finds the first pair `(i, k)`, `i < k`, of complementary literals (one the negation of the
/// other, syntactically).
fn complementary_pair(args: &[Rc<Term>]) -> Option<(usize, usize)> {
    for i in 0..args.len() {
        for k in (i + 1)..args.len() {
            if args[i].remove_negation() == Some(&args[k])
                || args[k].remove_negation() == Some(&args[i])
            {
                return Some((i, k));
            }
        }
    }
    None
}

/// `(= (= t s) (and (>= t s) (<= t s)))` — the `arith-eq-elim` rules.
fn arith_eq_elim(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let conj = rhs;
    let (le_1, le_2) = match_term_err!((and l r) = conj)?;
    let (le_1, le_2) = (le_1.clone(), le_2.clone());

    // Direction →, under a discharge subproof
    b.open();
    let assumption = b.assume(lhs.clone());
    let not_eq = b.not(lhs);
    let g1 = la_clause(b, vec![not_eq.clone(), le_1.clone()])?;
    let g2 = la_clause(b, vec![not_eq, le_2.clone()])?;
    let r1 = b.resolve(vec![g1, assumption.clone()], vec![(lhs.clone(), false)])?;
    let r2 = b.resolve(vec![g2, assumption.clone()], vec![(lhs.clone(), false)])?;
    let and_step = b.and_intro(vec![r1, r2])?;
    let forward = b.close_subproof(vec![assumption], and_step);

    // Direction ←, from the `la_disequality` axiom. Its clause uses `<=` in both directions, so
    // the conjuncts (which may be `>=`/`<=`) are bridged by one Farkas step each where needed.
    let (t, s) = match_term_err!((= t s) = lhs)?;
    let (t, s) = (t.clone(), s.clone());
    let le_ts = build_term!(b.pool, (<= {t.clone()} {s.clone()}));
    let le_st = build_term!(b.pool, (<= {s.clone()} {t.clone()}));
    b.open();
    let assumption = b.assume(conj.clone());
    let not_conj = b.not(conj);
    let p1 = and_pos_step(b, conj, 0)?;
    let p2 = and_pos_step(b, conj, 1)?;
    let u1 = b.resolve(vec![p1, assumption.clone()], vec![(conj.clone(), false)])?;
    let u2 = b.resolve(vec![p2, assumption.clone()], vec![(conj.clone(), false)])?;
    let _ = not_conj;
    // From the two conjuncts derive the two `<=` bounds
    let mut bounds = Vec::new();
    // The first conjunct is `(>= t s)`, i.e. the bound `s ≤ t`; the second is `(<= t s)`
    for (conjunct_node, conjunct, bound) in [
        (u1, le_1.clone(), le_st.clone()),
        (u2, le_2.clone(), le_ts.clone()),
    ] {
        if conjunct == bound {
            bounds.push((bound, conjunct_node));
        } else {
            let nc = b.not(&conjunct);
            let bridge = la_clause(b, vec![nc, bound.clone()])?;
            let node = b.resolve(vec![bridge, conjunct_node], vec![(conjunct, false)])?;
            bounds.push((bound, node));
        }
    }
    let (not_le_ts, not_le_st) = (b.not(&le_ts), b.not(&le_st));
    let axiom_term = build_term!(
        b.pool,
        (or {lhs.clone()} {not_le_ts.clone()} {not_le_st.clone()})
    );
    let axiom = b.step(
        vec![axiom_term.clone()],
        "la_disequality",
        Vec::new(),
        Vec::new(),
    );
    let not_axiom_term = b.not(&axiom_term);
    let or_pos = b.step(
        vec![not_axiom_term, lhs.clone(), not_le_ts, not_le_st],
        "or_pos",
        Vec::new(),
        Vec::new(),
    );
    let mut eq_node = b.resolve(vec![or_pos, axiom], vec![(axiom_term, false)])?;
    for (bound, node) in bounds {
        eq_node = b.resolve(vec![eq_node, node], vec![(bound, false)])?;
    }
    let backward = b.close_subproof(vec![assumption], eq_node);

    b.equiv_intro(lhs.clone(), conj.clone(), forward, backward)
}

/// `(= (= ¬a ¬b) (= a b))`.
fn equiv_neg_both(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let (na, nb) = match_term_err!((= na nb) = lhs)?;
    let (a, bb) = (
        na.remove_negation_err()
            .map_err(ElaborationError::from)?
            .clone(),
        nb.remove_negation_err()
            .map_err(ElaborationError::from)?
            .clone(),
    );
    let (na, nb) = (na.clone(), nb.clone());

    // dir1: assume (= ¬a ¬b) ⊢ (= a b)
    b.open();
    let h = b.assume(lhs.clone());
    let nna_t = b.not(&na);
    let nnb_t = b.not(&nb);
    let c1 = b.step(
        vec![nna_t, nb.clone()],
        "equiv1",
        vec![h.clone()],
        Vec::new(),
    );
    let c2 = b.step(
        vec![na.clone(), nnb_t],
        "equiv2",
        vec![h.clone()],
        Vec::new(),
    );
    let neg2 = b.step(
        vec![rhs.clone(), a.clone(), bb.clone()],
        "equiv_neg2",
        Vec::new(),
        Vec::new(),
    );
    let na_t = b.not(&a);
    let nbb_t = b.not(&bb);
    let neg1 = b.step(
        vec![rhs.clone(), na_t, nbb_t],
        "equiv_neg1",
        Vec::new(),
        Vec::new(),
    );
    let r1 = b.resolve(vec![neg2, c2], vec![(a.clone(), true)])?;
    // r1 = (cl rhs b ¬¬b)
    let nn_b = not_not_ax(b, &bb);
    let nnb = {
        let n1 = b.not(&bb);
        b.not(&n1)
    };
    let r2 = b.resolve(vec![r1, nn_b], vec![(nnb, true)])?;
    // r2 = (cl rhs b)
    let na_pivot = b.not(&a);
    let r3 = b.resolve(vec![neg1, c1], vec![(na_pivot, true)])?;
    // r3 = (cl rhs ¬b): `neg1` = (cl rhs ¬a ¬b) and `c1` = (cl ¬¬a ¬b) resolve on the
    // complement pair (¬a, ¬¬a)
    let inner = b.resolve(vec![r3, r2], vec![(bb.clone(), false)])?;
    let sub1 = b.close_subproof(vec![h], inner);

    // dir2: assume (= a b) ⊢ (= ¬a ¬b)
    b.open();
    let h = b.assume(rhs.clone());
    let na_t = b.not(&a);
    let nbb_t = b.not(&bb);
    let c1 = b.step(
        vec![na_t, bb.clone()],
        "equiv1",
        vec![h.clone()],
        Vec::new(),
    );
    let c2 = b.step(
        vec![a.clone(), nbb_t],
        "equiv2",
        vec![h.clone()],
        Vec::new(),
    );
    let neg2 = b.step(
        vec![lhs.clone(), na.clone(), nb.clone()],
        "equiv_neg2",
        Vec::new(),
        Vec::new(),
    );
    let nna_t = b.not(&na);
    let nnb_t = b.not(&nb);
    let neg1 = b.step(
        vec![lhs.clone(), nna_t, nnb_t],
        "equiv_neg1",
        Vec::new(),
        Vec::new(),
    );
    // neg2 = (cl lhs ¬a ¬b): kill ¬b against c1's b (complementary), then ¬a against c2's a
    let r1 = b.resolve(vec![neg2, c1.clone()], vec![(bb.clone(), false)])?;
    let r2 = b.resolve(vec![r1, c2.clone()], vec![(a.clone(), false)])?;
    // r2 = (cl lhs ¬b... : (cl lhs) once both killed; c1 brings ¬a, c2 brings ¬b — recheck:
    // neg2=(cl lhs ¬a ¬b) ⊗ c1=(cl ¬a b) on (b,false): ¬b∈neg2, b∈c1 → (cl lhs ¬a ¬a) = (cl lhs ¬a)
    // ⊗ c2=(cl a ¬b) on (a,false): ¬a∈current, a∈c2 → (cl lhs ¬b)
    // Still ¬b left; neg1 = (cl lhs ¬¬a ¬¬b): kill ¬¬a with not_not, ¬¬b with not_not, then
    // resolve the two partial results.
    let nn_a = not_not_ax(b, &a);
    let nn_b = not_not_ax(b, &bb);
    let nna = {
        let n1 = b.not(&a);
        b.not(&n1)
    };
    let nnb = {
        let n1 = b.not(&bb);
        b.not(&n1)
    };
    let r3 = b.resolve(vec![neg1, nn_a], vec![(nna, true)])?;
    let r4 = b.resolve(vec![r3, nn_b], vec![(nnb, true)])?;
    // r4 = (cl lhs a b): kill b with c2, then close against r2
    let r5 = b.resolve(vec![r4, c2], vec![(bb.clone(), true)])?;
    // r5 = (cl lhs a): resolve with r2 = (cl lhs ¬b)... r2 has ¬b, r5 has a: no complement.
    // Kill a in r5 with c1: c1 = (cl ¬a b): (cl lhs b); then with r2 on (b,true)
    let r6 = b.resolve(vec![r5, c1], vec![(a.clone(), true)])?;
    let inner = b.resolve(vec![r6, r2], vec![(bb.clone(), true)])?;
    let sub2 = b.close_subproof(vec![h], inner);

    b.equiv_intro(lhs.clone(), rhs.clone(), sub1, sub2)
}

/// `(= (=> t s) (or ¬t s))`.
fn bool_impl_elim(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let (t, s) = match_term_err!((=> t s) = lhs)?;
    let (t, s) = (t.clone(), s.clone());
    let nt = b.not(&t);
    let not_lhs = b.not(lhs);
    // dir1 = (cl ¬lhs rhs)
    let pos = b.step(
        vec![not_lhs.clone(), nt.clone(), s.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let dir1 = pack_or(b, pos, rhs, &[(nt.clone(), 0), (s.clone(), 1)])?;
    // dir2 = (cl lhs ¬rhs)
    let or_pos = or_pos_step(b, rhs)?;
    let neg1 = b.step(
        vec![lhs.clone(), t.clone()],
        "implies_neg1",
        Vec::new(),
        Vec::new(),
    );
    let ns = b.not(&s);
    let neg2 = b.step(
        vec![lhs.clone(), ns],
        "implies_neg2",
        Vec::new(),
        Vec::new(),
    );
    let r1 = b.resolve(vec![or_pos, neg1], vec![(t, false)])?;
    let dir2 = b.resolve(vec![r1, neg2], vec![(s, true)])?;
    let _ = nt;
    b.equiv_intro(lhs.clone(), rhs.clone(), dir1, dir2)
}

/// `(= (=> ¬a ¬b) (=> b a))`.
fn implies_contra(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let (na, nb) = match_term_err!((=> na nb) = lhs)?;
    let a = na
        .remove_negation_err()
        .map_err(ElaborationError::from)?
        .clone();
    let bb = nb
        .remove_negation_err()
        .map_err(ElaborationError::from)?
        .clone();
    let (na, nb) = (na.clone(), nb.clone());

    // dir1: assume lhs ⊢ rhs
    b.open();
    let h = b.assume(lhs.clone());
    let not_lhs = b.not(lhs);
    let __n1 = b.not(&na);
    let pos = b.step(
        vec![not_lhs, __n1.clone(), nb.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let u = b.resolve(vec![pos, h.clone()], vec![(lhs.clone(), false)])?;
    // u = (cl ¬¬a ¬b)
    let neg1 = b.step(
        vec![rhs.clone(), bb.clone()],
        "implies_neg1",
        Vec::new(),
        Vec::new(),
    );
    let __n2 = b.not(&a);
    let neg2 = b.step(
        vec![rhs.clone(), __n2.clone()],
        "implies_neg2",
        Vec::new(),
        Vec::new(),
    );
    let r1 = b.resolve(vec![u, neg2], vec![(na.clone(), false)])?;
    // r1 = (cl ¬b rhs)
    let inner = b.resolve(vec![r1, neg1], vec![(bb.clone(), false)])?;
    let sub1 = b.close_subproof(vec![h], inner);

    // dir2: assume rhs ⊢ lhs
    b.open();
    let h = b.assume(rhs.clone());
    let not_rhs = b.not(rhs);
    let __n3 = b.not(&bb);
    let pos = b.step(
        vec![not_rhs, __n3.clone(), a.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let u = b.resolve(vec![pos, h.clone()], vec![(rhs.clone(), false)])?;
    // u = (cl ¬b a)
    let neg1 = b.step(
        vec![lhs.clone(), na.clone()],
        "implies_neg1",
        Vec::new(),
        Vec::new(),
    );
    let __n4 = b.not(&nb);
    let neg2 = b.step(
        vec![lhs.clone(), __n4.clone()],
        "implies_neg2",
        Vec::new(),
        Vec::new(),
    );
    // neg1 = (cl lhs ¬a): kill ¬a against u's a
    let r1 = b.resolve(vec![neg1, u], vec![(a.clone(), false)])?;
    // r1 = (cl lhs ¬b); neg2 = (cl lhs ¬¬b): resolve on the complement pair
    let inner = b.resolve(vec![neg2, r1], vec![(nb.clone(), false)])?;
    let sub2 = b.close_subproof(vec![h], inner);

    b.equiv_intro(lhs.clone(), rhs.clone(), sub1, sub2)
}

/// `(= (=> (=> a b) b) (or a b))`.
fn peirce(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let (inner_impl, _) = match_term_err!((=> i c) = lhs)?;
    let inner_impl = inner_impl.clone();
    let (a, bb) = match_term_err!((=> a b) = &inner_impl)?;
    let (a, bb) = (a.clone(), bb.clone());

    // dir1: assume lhs ⊢ (or a b)
    b.open();
    let h = b.assume(lhs.clone());
    let not_lhs = b.not(lhs);
    let not_inner = b.not(&inner_impl);
    let pos = b.step(
        vec![not_lhs, not_inner, bb.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let u = b.resolve(vec![pos, h.clone()], vec![(lhs.clone(), false)])?;
    // u = (cl ¬(=> a b) b)
    let ineg1 = b.step(
        vec![inner_impl.clone(), a.clone()],
        "implies_neg1",
        Vec::new(),
        Vec::new(),
    );
    let r1 = b.resolve(vec![u, ineg1], vec![(inner_impl.clone(), false)])?;
    // r1 = (cl b a)
    let packed = pack_or(b, r1, rhs, &[(a.clone(), 0), (bb.clone(), 1)])?;
    let sub1 = b.close_subproof(vec![h], packed);

    // dir2: assume (or a b) ⊢ lhs
    b.open();
    let h = b.assume(rhs.clone());
    let op = or_pos_step(b, rhs)?;
    let u0 = b.resolve(vec![op, h.clone()], vec![(rhs.clone(), false)])?;
    // u0 = (cl a b)
    let __n5 = b.not(&inner_impl);
    let __n6 = b.not(&a);
    let ipos = b.step(
        vec![__n5.clone(), __n6.clone(), bb.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let r1 = b.resolve(vec![ipos, u0], vec![(a.clone(), false)])?;
    // r1 = (cl ¬(=> a b) b)
    let sneg1 = b.step(
        vec![lhs.clone(), inner_impl.clone()],
        "implies_neg1",
        Vec::new(),
        Vec::new(),
    );
    let r2 = b.resolve(vec![r1, sneg1], vec![(inner_impl.clone(), false)])?;
    // r2 = (cl b lhs)
    let __n7 = b.not(&bb);
    let sneg2 = b.step(
        vec![lhs.clone(), __n7.clone()],
        "implies_neg2",
        Vec::new(),
        Vec::new(),
    );
    let inner = b.resolve(vec![r2, sneg2], vec![(bb.clone(), true)])?;
    let sub2 = b.close_subproof(vec![h], inner);

    b.equiv_intro(lhs.clone(), rhs.clone(), sub1, sub2)
}

/// `(= (=> a (=> b c)) (=> (and a b) c))`.
fn uncurry(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let (a, inner_impl) = match_term_err!((=> a i) = lhs)?;
    let (a, inner_impl) = (a.clone(), inner_impl.clone());
    let (bb, c) = match_term_err!((=> b c) = &inner_impl)?;
    let (bb, c) = (bb.clone(), c.clone());
    let (and_term, _) = match_term_err!((=> a c) = rhs)?;
    let and_term = and_term.clone();

    // dir1: assume lhs ⊢ rhs
    b.open();
    let h = b.assume(lhs.clone());
    let __n8 = b.not(lhs);
    let __n9 = b.not(&a);
    let pos = b.step(
        vec![__n8.clone(), __n9.clone(), inner_impl.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let u = b.resolve(vec![pos, h.clone()], vec![(lhs.clone(), false)])?;
    let __n10 = b.not(&inner_impl);
    let __n11 = b.not(&bb);
    let ipos = b.step(
        vec![__n10.clone(), __n11.clone(), c.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let r1 = b.resolve(vec![u, ipos], vec![(inner_impl.clone(), true)])?;
    // r1 = (cl ¬a ¬b c)
    // With `a == b` the two negated antecedents are one literal, gone after one resolution
    let ap0 = and_pos_step(b, &and_term, 0)?;
    let r2 = b.resolve(vec![r1, ap0], vec![(a.clone(), false)])?;
    let r3 = if a == bb {
        r2
    } else {
        let ap1 = and_pos_step(b, &and_term, 1)?;
        b.resolve(vec![r2, ap1], vec![(bb.clone(), false)])?
    };
    // r3 = (cl c ¬(and a b) ¬(and a b)) → deduped = (cl c ¬(and a b))
    let rneg1 = b.step(
        vec![rhs.clone(), and_term.clone()],
        "implies_neg1",
        Vec::new(),
        Vec::new(),
    );
    let r4 = b.resolve(vec![r3, rneg1], vec![(and_term.clone(), false)])?;
    let __n12 = b.not(&c);
    let rneg2 = b.step(
        vec![rhs.clone(), __n12.clone()],
        "implies_neg2",
        Vec::new(),
        Vec::new(),
    );
    let inner = b.resolve(vec![r4, rneg2], vec![(c.clone(), true)])?;
    let sub1 = b.close_subproof(vec![h], inner);

    // dir2: assume rhs ⊢ lhs
    b.open();
    let h = b.assume(rhs.clone());
    let __n13 = b.not(rhs);
    let __n14 = b.not(&and_term);
    let pos = b.step(
        vec![__n13.clone(), __n14.clone(), c.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let u = b.resolve(vec![pos, h.clone()], vec![(rhs.clone(), false)])?;
    // u = (cl ¬(and a b) c)
    let an = and_neg_step(b, &and_term)?;
    let r1 = b.resolve(vec![u, an], vec![(and_term.clone(), false)])?;
    // r1 = (cl c ¬a ¬b)
    let ineg1 = b.step(
        vec![inner_impl.clone(), bb.clone()],
        "implies_neg1",
        Vec::new(),
        Vec::new(),
    );
    let __n15 = b.not(&c);
    let ineg2 = b.step(
        vec![inner_impl.clone(), __n15.clone()],
        "implies_neg2",
        Vec::new(),
        Vec::new(),
    );
    let r2 = b.resolve(vec![r1, ineg1], vec![(bb.clone(), false)])?;
    let r3 = b.resolve(vec![r2, ineg2], vec![(c.clone(), true)])?;
    // r3 = (cl ¬a (=> b c))
    let __n16 = b.not(&inner_impl);
    let sneg2 = b.step(
        vec![lhs.clone(), __n16.clone()],
        "implies_neg2",
        Vec::new(),
        Vec::new(),
    );
    let r4 = b.resolve(vec![r3, sneg2], vec![(inner_impl.clone(), true)])?;
    // With `a == b`, ¬a was already consumed when the inner implication was introduced
    let inner = if a == bb {
        r4
    } else {
        let sneg1 = b.step(
            vec![lhs.clone(), a.clone()],
            "implies_neg1",
            Vec::new(),
            Vec::new(),
        );
        b.resolve(vec![r4, sneg1], vec![(a.clone(), false)])?
    };
    let sub2 = b.close_subproof(vec![h], inner);

    b.equiv_intro(lhs.clone(), rhs.clone(), sub1, sub2)
}

/// `(= (and a (=> a b)) (and a b))` and `(= (and (=> a b) a) (and a b))`.
fn and_mp(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let args = match_term_err!((and ...) = lhs)?.to_vec();
    let [x, y] = args.as_slice() else {
        return Err(explanation("expected binary conjunction"));
    };
    let (impl_idx, impl_term, a) = if match_term!((=> a b) = x).is_some() {
        (0, x.clone(), y.clone())
    } else {
        (1, y.clone(), x.clone())
    };
    let (ia, ib) = match_term_err!((=> a b) = &impl_term)?;
    let (ia, ib) = (ia.clone(), ib.clone());
    if ia != a {
        return Err(explanation("modus-ponens shape mismatch"));
    }

    // dir1: assume lhs ⊢ (and a b)
    b.open();
    let h = b.assume(lhs.clone());
    let ap_a = and_pos_step(b, lhs, 1 - impl_idx)?;
    let ap_i = and_pos_step(b, lhs, impl_idx)?;
    let ua = b.resolve(vec![ap_a, h.clone()], vec![(lhs.clone(), false)])?;
    let ui = b.resolve(vec![ap_i, h.clone()], vec![(lhs.clone(), false)])?;
    let __n17 = b.not(&impl_term);
    let __n18 = b.not(&ia);
    let pos = b.step(
        vec![__n17.clone(), __n18.clone(), ib.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let r1 = b.resolve(vec![pos, ui], vec![(impl_term.clone(), false)])?;
    let ub = b.resolve(vec![r1, ua.clone()], vec![(ia.clone(), false)])?;
    let and_node = b.and_intro(vec![ua, ub])?;
    let sub1 = b.close_subproof(vec![h], and_node);

    // dir2: assume (and a b) ⊢ lhs
    b.open();
    let h = b.assume(rhs.clone());
    let ap_a = and_pos_step(b, rhs, 0)?;
    let ap_b = and_pos_step(b, rhs, 1)?;
    let ua = b.resolve(vec![ap_a, h.clone()], vec![(rhs.clone(), false)])?;
    let ub = b.resolve(vec![ap_b, h.clone()], vec![(rhs.clone(), false)])?;
    let __n19 = b.not(&ib);
    let ineg2 = b.step(
        vec![impl_term.clone(), __n19.clone()],
        "implies_neg2",
        Vec::new(),
        Vec::new(),
    );
    let ui = b.resolve(vec![ineg2, ub], vec![(ib.clone(), false)])?;
    let parts = if impl_idx == 0 {
        vec![ui, ua]
    } else {
        vec![ua, ui]
    };
    let and_node = b.and_intro(parts)?;
    let sub2 = b.close_subproof(vec![h], and_node);

    b.equiv_intro(lhs.clone(), rhs.clone(), sub1, sub2)
}

/// `(= (not (=> p q)) (and p ¬q))`.
fn implies_de_morgan(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let impl_term = lhs
        .remove_negation_err()
        .map_err(ElaborationError::from)?
        .clone();
    let (p, q) = match_term_err!((=> p q) = &impl_term)?;
    let (p, q) = (p.clone(), q.clone());

    // dir1: assume ¬(=> p q) ⊢ (and p ¬q)
    b.open();
    let h = b.assume(lhs.clone());
    let neg1 = b.step(
        vec![impl_term.clone(), p.clone()],
        "implies_neg1",
        Vec::new(),
        Vec::new(),
    );
    let up = b.resolve(vec![neg1, h.clone()], vec![(impl_term.clone(), true)])?;
    let nq = b.not(&q);
    let neg2 = b.step(
        vec![impl_term.clone(), nq],
        "implies_neg2",
        Vec::new(),
        Vec::new(),
    );
    let unq = b.resolve(vec![neg2, h.clone()], vec![(impl_term.clone(), true)])?;
    let and_node = b.and_intro(vec![up, unq])?;
    let sub1 = b.close_subproof(vec![h], and_node);

    // dir2: assume (and p ¬q) ⊢ ¬(=> p q)
    b.open();
    let h = b.assume(rhs.clone());
    let ap0 = and_pos_step(b, rhs, 0)?;
    let ap1 = and_pos_step(b, rhs, 1)?;
    let up = b.resolve(vec![ap0, h.clone()], vec![(rhs.clone(), false)])?;
    let unq = b.resolve(vec![ap1, h.clone()], vec![(rhs.clone(), false)])?;
    let __n20 = b.not(&impl_term);
    let __n21 = b.not(&p);
    let pos = b.step(
        vec![__n20.clone(), __n21.clone(), q.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let r1 = b.resolve(vec![pos, up], vec![(p.clone(), false)])?;
    let inner = b.resolve(vec![r1, unq], vec![(q.clone(), true)])?;
    let sub2 = b.close_subproof(vec![h], inner);

    b.equiv_intro(lhs.clone(), rhs.clone(), sub1, sub2)
}

/// The head form of `bool-or-de-morgan`: `(= ¬(or x rest…) (and ¬x R))` where `R` is `¬(or
/// rest…)` (or `¬y` for the binary case).
fn or_de_morgan(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let or_term = lhs
        .remove_negation_err()
        .map_err(ElaborationError::from)?
        .clone();
    let or_args = match_term_err!((or ...) = &or_term)?.to_vec();
    let conj = match_term_err!((and a r) = rhs)?;
    let (c1, c2) = (conj.0.clone(), conj.1.clone());
    let x = c1
        .remove_negation_err()
        .map_err(ElaborationError::from)?
        .clone();
    let rest_term = c2
        .remove_negation_err()
        .map_err(ElaborationError::from)?
        .clone();
    if or_args.first() != Some(&x) {
        return Err(explanation("de-morgan head mismatch"));
    }
    // The elements of the tail, as they occur in `or_term` (positions 1..)
    let tail: Vec<Rc<Term>> = or_args[1..].to_vec();
    let tail_is_app = tail.len() > 1;
    if tail_is_app && match_term!((or ...) = &rest_term).map(<[_]>::to_vec) != Some(tail.clone()) {
        return Err(explanation("de-morgan tail mismatch"));
    }
    if !tail_is_app && rest_term != tail[0] {
        return Err(explanation("de-morgan tail mismatch"));
    }

    // dir1: assume ¬O ⊢ (and ¬x R)
    b.open();
    let h = b.assume(lhs.clone());
    let on0 = or_neg_step(b, &or_term, 0)?;
    let ux = b.resolve(vec![on0, h.clone()], vec![(or_term.clone(), true)])?;
    let urest = if tail_is_app {
        // (cl ¬R O): from or_pos(R) and one or_neg(O) per tail element
        let op = or_pos_step(b, &rest_term)?;
        let lits: Vec<(Rc<Term>, usize)> = tail
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, t)| (t, i + 1))
            .collect();
        let bridged = pack_or(b, op, &or_term, &lits)?;
        b.resolve(vec![bridged, h.clone()], vec![(or_term.clone(), true)])?
    } else {
        let on1 = or_neg_step(b, &or_term, 1)?;
        b.resolve(vec![on1, h.clone()], vec![(or_term.clone(), true)])?
    };
    let and_node = b.and_intro(vec![ux, urest])?;
    let sub1 = b.close_subproof(vec![h], and_node);

    // dir2: assume (and ¬x R) ⊢ ¬O
    b.open();
    let h = b.assume(rhs.clone());
    let ap0 = and_pos_step(b, rhs, 0)?;
    let ap1 = and_pos_step(b, rhs, 1)?;
    let unx = b.resolve(vec![ap0, h.clone()], vec![(rhs.clone(), false)])?;
    let unrest = b.resolve(vec![ap1, h.clone()], vec![(rhs.clone(), false)])?;
    let op = or_pos_step(b, &or_term)?;
    let mut node = b.resolve(vec![op, unx], vec![(x.clone(), true)])?;
    if tail_is_app {
        // kill each tail element via (cl R ¬tᵢ) + the unit ¬R
        for (i, t) in tail.iter().enumerate() {
            let on = or_neg_step(b, &rest_term, i)?;
            let ut = b.resolve(vec![on, unrest.clone()], vec![(rest_term.clone(), true)])?;
            node = b.resolve(vec![node, ut], vec![(t.clone(), true)])?;
        }
    } else {
        node = b.resolve(vec![node, unrest], vec![(tail[0].clone(), true)])?;
    }
    let sub2 = b.close_subproof(vec![h], node);

    b.equiv_intro(lhs.clone(), rhs.clone(), sub1, sub2)
}

/// The head form of `bool-and-de-morgan`: `(= ¬(and x rest…) (or ¬x R))` where `R` is `¬(and
/// rest…)` (or `¬y` for the binary case).
fn and_de_morgan(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let and_term = lhs
        .remove_negation_err()
        .map_err(ElaborationError::from)?
        .clone();
    let and_args = match_term_err!((and ...) = &and_term)?.to_vec();
    let disj = match_term_err!((or a r) = rhs)?;
    let (d1, d2) = (disj.0.clone(), disj.1.clone());
    let x = d1
        .remove_negation_err()
        .map_err(ElaborationError::from)?
        .clone();
    let rest_term = d2
        .remove_negation_err()
        .map_err(ElaborationError::from)?
        .clone();
    if and_args.first() != Some(&x) {
        return Err(explanation("de-morgan head mismatch"));
    }
    let tail: Vec<Rc<Term>> = and_args[1..].to_vec();
    let tail_is_app = tail.len() > 1;
    if tail_is_app && match_term!((and ...) = &rest_term).map(<[_]>::to_vec) != Some(tail.clone()) {
        return Err(explanation("de-morgan tail mismatch"));
    }
    if !tail_is_app && rest_term != tail[0] {
        return Err(explanation("de-morgan tail mismatch"));
    }

    // dir1: assume ¬A ⊢ (or ¬x R)
    b.open();
    let h = b.assume(lhs.clone());
    let an = and_neg_step(b, &and_term)?;
    let mut node = b.resolve(vec![an, h.clone()], vec![(and_term.clone(), true)])?;
    // node = (cl ¬x ¬t₁ … ¬tₖ)
    if tail_is_app {
        for (i, t) in tail.iter().enumerate() {
            let ap = and_pos_step(b, &rest_term, i)?;
            node = b.resolve(vec![node, ap], vec![(t.clone(), false)])?;
        }
        // node = (cl ¬x ¬R)
    }
    let nx = b.not(&x);
    let nr = b.not(&rest_term);
    let packed = pack_or(b, node, rhs, &[(nx, 0), (nr, 1)])?;
    let sub1 = b.close_subproof(vec![h], packed);

    // dir2: assume (or ¬x R') ⊢ ¬A, where R' = ¬R
    b.open();
    let h = b.assume(rhs.clone());
    let op = or_pos_step(b, rhs)?;
    let u0 = b.resolve(vec![op, h.clone()], vec![(rhs.clone(), false)])?;
    // u0 = (cl ¬x ¬R)
    let ap0 = and_pos_step(b, &and_term, 0)?;
    let mut node = b.resolve(vec![u0, ap0], vec![(x.clone(), false)])?;
    // node = (cl ¬R ¬A)
    if tail_is_app {
        let rn = and_neg_step(b, &rest_term)?;
        let mut r_node = rn;
        for (i, t) in tail.iter().enumerate() {
            // `r_node` carries `¬t` (from `and_neg` on the tail) and `and_pos` supplies `t`, so the
            // pivot is negative on the accumulated side
            let ap = and_pos_step(b, &and_term, i + 1)?;
            r_node = b.resolve(vec![r_node, ap], vec![(t.clone(), false)])?;
        }
        // r_node = (cl R ¬A)
        node = b.resolve(vec![node, r_node], vec![(rest_term.clone(), false)])?;
    } else {
        let ap1 = and_pos_step(b, &and_term, 1)?;
        node = b.resolve(vec![node, ap1], vec![(tail[0].clone(), false)])?;
    }
    let sub2 = b.close_subproof(vec![h], node);

    b.equiv_intro(lhs.clone(), rhs.clone(), sub1, sub2)
}

/// `(= (=> (or y1 rest…) z) (and (=> y1 z) (=> (or rest…) z)))`.
fn implies_or_distrib(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let (or_term, z) = match_term_err!((=> o z) = lhs)?;
    let (or_term, z) = (or_term.clone(), z.clone());
    let or_args = match_term_err!((or ...) = &or_term)?.to_vec();
    let (t1, t2) = match_term_err!((and t1 t2) = rhs)?;
    let (t1, t2) = (t1.clone(), t2.clone());
    let (y1, _) = match_term_err!((=> y z) = &t1)?;
    let y1 = y1.clone();
    let (rest_term, _) = match_term_err!((=> r z) = &t2)?;
    let rest_term = rest_term.clone();
    if or_args.first() != Some(&y1) {
        return Err(explanation("distrib head mismatch"));
    }
    let tail: Vec<Rc<Term>> = or_args[1..].to_vec();
    let tail_is_app = tail.len() > 1;

    // dir1: assume lhs ⊢ (and (=> y1 z) (=> R z))
    b.open();
    let h = b.assume(lhs.clone());
    let __n22 = b.not(lhs);
    let __n23 = b.not(&or_term);
    let pos = b.step(
        vec![__n22.clone(), __n23.clone(), z.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let u = b.resolve(vec![pos, h.clone()], vec![(lhs.clone(), false)])?;
    // u = (cl ¬O z)
    // Conjunct 1: (=> y1 z)
    let on0 = or_neg_step(b, &or_term, 0)?;
    let r1 = b.resolve(vec![u.clone(), on0], vec![(or_term.clone(), false)])?;
    // r1 = (cl z ¬y1)
    let t1neg1 = b.step(
        vec![t1.clone(), y1.clone()],
        "implies_neg1",
        Vec::new(),
        Vec::new(),
    );
    let r2 = b.resolve(vec![r1, t1neg1], vec![(y1.clone(), false)])?;
    let __n24 = b.not(&z);
    let t1neg2 = b.step(
        vec![t1.clone(), __n24.clone()],
        "implies_neg2",
        Vec::new(),
        Vec::new(),
    );
    let c1 = b.resolve(vec![r2, t1neg2], vec![(z.clone(), true)])?;
    // Conjunct 2: (=> R z)
    let rest_to_or = if tail_is_app {
        let op = or_pos_step(b, &rest_term)?;
        let lits: Vec<(Rc<Term>, usize)> = tail
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, t)| (t, i + 1))
            .collect();
        pack_or(b, op, &or_term, &lits)?
    } else {
        // (cl O ¬y2): read as (cl ¬R O) with R = y2
        or_neg_step(b, &or_term, 1)?
    };
    // rest_to_or = (cl ¬R O)
    let r3 = b.resolve(vec![u, rest_to_or], vec![(or_term.clone(), false)])?;
    // r3 = (cl z ¬R)
    let t2neg1 = b.step(
        vec![t2.clone(), rest_term.clone()],
        "implies_neg1",
        Vec::new(),
        Vec::new(),
    );
    let r4 = b.resolve(vec![r3, t2neg1], vec![(rest_term.clone(), false)])?;
    let __n25 = b.not(&z);
    let t2neg2 = b.step(
        vec![t2.clone(), __n25.clone()],
        "implies_neg2",
        Vec::new(),
        Vec::new(),
    );
    let c2 = b.resolve(vec![r4, t2neg2], vec![(z.clone(), true)])?;
    let and_node = b.and_intro(vec![c1, c2])?;
    let sub1 = b.close_subproof(vec![h], and_node);

    // dir2: assume rhs ⊢ lhs
    b.open();
    let h = b.assume(rhs.clone());
    let ap0 = and_pos_step(b, rhs, 0)?;
    let ap1 = and_pos_step(b, rhs, 1)?;
    let u1 = b.resolve(vec![ap0, h.clone()], vec![(rhs.clone(), false)])?;
    let u2 = b.resolve(vec![ap1, h.clone()], vec![(rhs.clone(), false)])?;
    let __n26 = b.not(&t1);
    let __n27 = b.not(&y1);
    let pos1 = b.step(
        vec![__n26.clone(), __n27.clone(), z.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let c1 = b.resolve(vec![pos1, u1], vec![(t1.clone(), false)])?;
    // c1 = (cl ¬y1 z)
    let __n28 = b.not(&t2);
    let __n29 = b.not(&rest_term);
    let pos2 = b.step(
        vec![__n28.clone(), __n29.clone(), z.clone()],
        "implies_pos",
        Vec::new(),
        Vec::new(),
    );
    let c2 = b.resolve(vec![pos2, u2], vec![(t2.clone(), false)])?;
    // c2 = (cl ¬R z)
    let op = or_pos_step(b, &or_term)?;
    let mut node = b.resolve(vec![op, c1], vec![(y1.clone(), true)])?;
    // node = (cl ¬O rest… z)
    if tail_is_app {
        for (i, t) in tail.iter().enumerate() {
            let on = or_neg_step(b, &rest_term, i)?;
            node = b.resolve(vec![node, on], vec![(t.clone(), true)])?;
        }
        // node = (cl ¬O z R)
        node = b.resolve(vec![node, c2], vec![(rest_term.clone(), true)])?;
    } else {
        node = b.resolve(vec![node, c2], vec![(tail[0].clone(), true)])?;
    }
    // node = (cl ¬O z)
    let sneg1 = b.step(
        vec![lhs.clone(), or_term.clone()],
        "implies_neg1",
        Vec::new(),
        Vec::new(),
    );
    let r = b.resolve(vec![node, sneg1], vec![(or_term.clone(), false)])?;
    let __n30 = b.not(&z);
    let sneg2 = b.step(
        vec![lhs.clone(), __n30.clone()],
        "implies_neg2",
        Vec::new(),
        Vec::new(),
    );
    let inner = b.resolve(vec![r, sneg2], vec![(z.clone(), true)])?;
    let sub2 = b.close_subproof(vec![h], inner);

    b.equiv_intro(lhs.clone(), rhs.clone(), sub1, sub2)
}

/// `(= (or (and y1 rest…) z zs…) (and (or y1 z zs…) (or R z zs…)))` where `R` is `(and rest…)`
/// (or `y2` alone).
fn or_and_distrib(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let lhs_args = match_term_err!((or ...) = lhs)?.to_vec();
    let and_term = lhs_args
        .first()
        .ok_or_else(|| explanation("empty disjunction"))?
        .clone();
    let and_args = match_term_err!((and ...) = &and_term)?.to_vec();
    let zs: Vec<Rc<Term>> = lhs_args[1..].to_vec();
    let (c1, c2) = match_term_err!((and c1 c2) = rhs)?;
    let (c1, c2) = (c1.clone(), c2.clone());
    let c2_args = match_term_err!((or ...) = &c2)?.to_vec();
    let rest_term = c2_args
        .first()
        .ok_or_else(|| explanation("empty disjunction"))?
        .clone();
    let tail: Vec<Rc<Term>> = and_args[1..].to_vec();
    let tail_is_app = tail.len() > 1;
    let y1 = and_args[0].clone();

    // dir1: assume O = (or A z zs) ⊢ (and C1 C2)
    b.open();
    let h = b.assume(lhs.clone());
    let op = or_pos_step(b, lhs)?;
    let u = b.resolve(vec![op, h.clone()], vec![(lhs.clone(), false)])?;
    // u = (cl A z zs…)
    // C1 = (or y1 z zs…): A → y1
    let ap0 = and_pos_step(b, &and_term, 0)?;
    let r1 = b.resolve(vec![u.clone(), ap0], vec![(and_term.clone(), true)])?;
    // r1 = (cl y1 z zs…)
    let mut lits: Vec<(Rc<Term>, usize)> = vec![(y1.clone(), 0)];
    for (i, z) in zs.iter().enumerate() {
        lits.push((z.clone(), i + 1));
    }
    let c1_node = pack_or(b, r1, &c1, &lits)?;
    // C2 = (or R z zs…): A → R
    let a_to_r = if tail_is_app {
        let rn = and_neg_step(b, &rest_term)?;
        let mut node = rn;
        for (i, t) in tail.iter().enumerate() {
            // As in `and_de_morgan`: `and_neg` on the tail carries `¬t`, `and_pos` supplies `t`
            let ap = and_pos_step(b, &and_term, i + 1)?;
            node = b.resolve(vec![node, ap], vec![(t.clone(), false)])?;
        }
        node
    } else {
        and_pos_step(b, &and_term, 1)?
    };
    // a_to_r = (cl R ¬A) / (cl ¬A y2)
    let r2 = b.resolve(vec![u, a_to_r], vec![(and_term.clone(), true)])?;
    // r2 = (cl z zs… R)
    let mut lits: Vec<(Rc<Term>, usize)> = vec![(rest_term.clone(), 0)];
    for (i, z) in zs.iter().enumerate() {
        lits.push((z.clone(), i + 1));
    }
    let c2_node = pack_or(b, r2, &c2, &lits)?;
    let and_node = b.and_intro(vec![c1_node, c2_node])?;
    let sub1 = b.close_subproof(vec![h], and_node);

    // dir2: assume (and C1 C2) ⊢ O
    b.open();
    let h = b.assume(rhs.clone());
    let ap0 = and_pos_step(b, rhs, 0)?;
    let ap1 = and_pos_step(b, rhs, 1)?;
    let u1 = b.resolve(vec![ap0, h.clone()], vec![(rhs.clone(), false)])?;
    let u2 = b.resolve(vec![ap1, h.clone()], vec![(rhs.clone(), false)])?;
    let op1 = or_pos_step(b, &c1)?;
    let d1 = b.resolve(vec![op1, u1], vec![(c1.clone(), false)])?;
    // d1 = (cl y1 z zs…)
    let op2 = or_pos_step(b, &c2)?;
    let d2 = b.resolve(vec![op2, u2], vec![(c2.clone(), false)])?;
    // d2 = (cl R z zs…)
    let an = and_neg_step(b, &and_term)?;
    let mut node = b.resolve(vec![an, d1], vec![(y1.clone(), false)])?;
    // node = (cl A ¬t₁ … ¬tₖ z zs…)
    if tail_is_app {
        for (i, t) in tail.iter().enumerate() {
            let ap = and_pos_step(b, &rest_term, i)?;
            let dt = b.resolve(vec![d2.clone(), ap], vec![(rest_term.clone(), true)])?;
            // dt = (cl z zs… tᵢ)
            node = b.resolve(vec![node, dt], vec![(t.clone(), false)])?;
        }
    } else {
        node = b.resolve(vec![node, d2], vec![(tail[0].clone(), false)])?;
    }
    // node = (cl A z zs…)
    let mut lits: Vec<(Rc<Term>, usize)> = vec![(and_term.clone(), 0)];
    for (i, z) in zs.iter().enumerate() {
        lits.push((z.clone(), i + 1));
    }
    let packed = pack_or(b, node, lhs, &lits)?;
    let sub2 = b.close_subproof(vec![h], packed);

    b.equiv_intro(lhs.clone(), rhs.clone(), sub1, sub2)
}

/// `(= (op (op args…)) (op args…))` and `(= (op x) x)` — the singleton unwrap/collapse. In both
/// shapes the left side is a one-argument application of the operator and the right side is what
/// its argument list stands for, so one positive and one negative axiom close the equivalence.
fn flatten(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    match lhs.as_ref() {
        Term::Op(Operator::And, args) if args.len() == 1 => {
            let dir1 = and_pos_step(b, lhs, 0)?;
            let an = and_neg_step(b, lhs)?;
            b.equiv_intro(lhs.clone(), rhs.clone(), dir1, an)
        }
        Term::Op(Operator::Or, args) if args.len() == 1 => {
            let op = or_pos_step(b, lhs)?;
            let on = or_neg_step(b, lhs, 0)?;
            b.equiv_intro(lhs.clone(), rhs.clone(), op, on)
        }
        _ => Err(explanation("expected a singleton application")),
    }
}

/// `(= (and xs true ys) (and xs ys))` and `(= (or xs false ys) (or xs ys))` — with the
/// right-hand side possibly a singleton application or a bare term.
fn elim_neutral(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let (rhs_args, rhs_is_app) = rhs_arguments(rhs);
    if let Some(args) = match_term!((and ...) = lhs) {
        let args = args.to_vec();
        let pos = removed_position(&args, rhs, true)
            .ok_or_else(|| explanation("no removed constant found"))?;
        // dir1: assume lhs ⊢ rhs (units of every conjunct but the constant)
        b.open();
        let h = b.assume(lhs.clone());
        let mut units = Vec::new();
        for (i, _) in args.iter().enumerate() {
            if i == pos {
                continue;
            }
            let ap = and_pos_step(b, lhs, i)?;
            units.push(b.resolve(vec![ap, h.clone()], vec![(lhs.clone(), false)])?);
        }
        let inner = if !rhs_is_app && units.len() == 1 {
            units.into_iter().next().unwrap()
        } else {
            b.and_intro(units)?
        };
        let sub1 = b.close_subproof(vec![h], inner);
        // dir2: assume rhs ⊢ lhs (units of rhs plus the `true` axiom)
        b.open();
        let h = b.assume(rhs.clone());
        let mut rhs_units = Vec::new();
        if rhs_is_app {
            for j in 0..rhs_args.len() {
                let ap = and_pos_step(b, rhs, j)?;
                rhs_units.push(b.resolve(vec![ap, h.clone()], vec![(rhs.clone(), false)])?);
            }
        } else {
            rhs_units.push(h.clone());
        }
        let mut units = Vec::new();
        for (i, _) in args.iter().enumerate() {
            if i == pos {
                units.push(true_ax(b));
            } else {
                let j = if i < pos { i } else { i - 1 };
                units.push(rhs_units[j].clone());
            }
        }
        let inner = b.and_intro(units)?;
        let sub2 = b.close_subproof(vec![h], inner);
        b.equiv_intro(lhs.clone(), rhs.clone(), sub1, sub2)
    } else if let Some(args) = match_term!((or ...) = lhs) {
        let args = args.to_vec();
        let pos = removed_position(&args, rhs, false)
            .ok_or_else(|| explanation("no removed constant found"))?;
        // dir1 = (cl ¬lhs rhs): or_pos, then per *distinct* argument either pack it into `rhs`
        // (if it survives) or kill it with the `false` axiom (the removed constant)
        let mut node = or_pos_step(b, lhs)?;
        let mut seen = std::collections::HashSet::new();
        for arg in &args {
            if !seen.insert(arg.clone()) {
                continue;
            }
            if let Some(j) = rhs_args.iter().position(|t| t == arg) {
                if rhs_is_app {
                    let neg = or_neg_step(b, rhs, j)?;
                    node = b.resolve(vec![node, neg], vec![(arg.clone(), true)])?;
                }
                // With a bare right-hand side the surviving literal *is* `rhs`: leave it
            } else {
                let fa = false_ax(b);
                let ff = b.pool.bool_false();
                node = b.resolve(vec![node, fa], vec![(ff, true)])?;
            }
        }
        let dir1 = node;
        // dir2 = (cl lhs ¬rhs)
        let dir2 = if !rhs_is_app {
            // `rhs` is the bare surviving term: one or_neg of `lhs` at its position
            let keep = args
                .iter()
                .position(|t| t == rhs)
                .ok_or_else(|| explanation("surviving term not found"))?;
            or_neg_step(b, lhs, keep)?
        } else {
            let op = or_pos_step(b, rhs)?;
            let mut lits = Vec::new();
            for (i, arg) in args.iter().enumerate() {
                if i == pos {
                    continue;
                }
                lits.push((arg.clone(), i));
            }
            pack_or(b, op, lhs, &lits)?
        };
        b.equiv_intro(lhs.clone(), rhs.clone(), dir1, dir2)
    } else {
        Err(explanation("expected an and/or application"))
    }
}

/// `(= (and xs b ys b zs) (and xs b ys zs))` and the `or` version.
fn elim_dup(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let (rhs_args, rhs_is_app) = rhs_arguments(rhs);
    if let Some(args) = match_term!((and ...) = lhs) {
        let args = args.to_vec();
        let (_, j) =
            dup_positions(&args, rhs).ok_or_else(|| explanation("no removed duplicate found"))?;
        // dir1: assume lhs ⊢ rhs
        b.open();
        let h = b.assume(lhs.clone());
        let mut units = Vec::new();
        for (i, _) in args.iter().enumerate() {
            if i == j {
                continue;
            }
            let ap = and_pos_step(b, lhs, i)?;
            units.push(b.resolve(vec![ap, h.clone()], vec![(lhs.clone(), false)])?);
        }
        let inner = if !rhs_is_app && units.len() == 1 {
            units.into_iter().next().unwrap()
        } else {
            b.and_intro(units)?
        };
        let sub1 = b.close_subproof(vec![h], inner);
        // dir2: assume rhs ⊢ lhs (the duplicate reuses its first copy's unit)
        b.open();
        let h = b.assume(rhs.clone());
        let mut rhs_units = Vec::new();
        if rhs_is_app {
            for k in 0..rhs_args.len() {
                let ap = and_pos_step(b, rhs, k)?;
                rhs_units.push(b.resolve(vec![ap, h.clone()], vec![(rhs.clone(), false)])?);
            }
        } else {
            rhs_units.push(h.clone());
        }
        let mut units = Vec::new();
        for (i, _) in args.iter().enumerate() {
            let k = if i < j {
                i
            } else if i == j {
                dup_source(&args, j)
            } else {
                i - 1
            };
            units.push(rhs_units[k].clone());
        }
        let inner = b.and_intro(units)?;
        let sub2 = b.close_subproof(vec![h], inner);
        b.equiv_intro(lhs.clone(), rhs.clone(), sub1, sub2)
    } else if let Some(args) = match_term!((or ...) = lhs) {
        let args = args.to_vec();
        let (i0, j) =
            dup_positions(&args, rhs).ok_or_else(|| explanation("no removed duplicate found"))?;
        // dir1 = (cl ¬lhs rhs): or_pos, both copies pack to the same slot
        let op = or_pos_step(b, lhs)?;
        let dir1 = if !rhs_is_app {
            // rhs is the bare duplicated term: or_pos concludes (cl ¬lhs t t), whose set
            // form is already (cl ¬lhs t); make it explicit with a contraction
            let nl = b.not(lhs);
            b.step(vec![nl, rhs.clone()], "contraction", vec![op], Vec::new())
        } else {
            let mut lits = Vec::new();
            for (k, arg) in args.iter().enumerate() {
                let slot = if k < j {
                    k
                } else if k == j {
                    i0
                } else {
                    k - 1
                };
                lits.push((arg.clone(), slot));
            }
            pack_or(b, op, rhs, &lits)?
        };
        // dir2 = (cl lhs ¬rhs)
        let dir2 = if !rhs_is_app {
            or_neg_step(b, lhs, i0)?
        } else {
            let op = or_pos_step(b, rhs)?;
            let mut lits = Vec::new();
            let mut seen = std::collections::HashSet::new();
            for (k, arg) in args.iter().enumerate() {
                if k == j {
                    continue;
                }
                if seen.insert(arg.clone()) {
                    lits.push((arg.clone(), k));
                }
            }
            pack_or(b, op, lhs, &lits)?
        };
        b.equiv_intro(lhs.clone(), rhs.clone(), dir1, dir2)
    } else {
        Err(explanation("expected an and/or application"))
    }
}

/// The argument list a right-hand side stands for: the arguments of an `and`/`or` application
/// (a singleton application included), or the term itself as a one-element list.
fn rhs_arguments(rhs: &Rc<Term>) -> (Vec<Rc<Term>>, bool) {
    match rhs.as_ref() {
        Term::Op(Operator::And | Operator::Or, rhs_args) => (rhs_args.clone(), true),
        _ => (vec![rhs.clone()], false),
    }
}

/// The position of the element of `args` whose removal yields `rhs`'s argument list, where the
/// removed element is the neutral constant.
fn removed_position(args: &[Rc<Term>], rhs: &Rc<Term>, neutral: bool) -> Option<usize> {
    let (rhs_args, _) = rhs_arguments(rhs);
    for (i, arg) in args.iter().enumerate() {
        if !arg.is_bool_constant(neutral) {
            continue;
        }
        let mut remaining = args.to_vec();
        remaining.remove(i);
        if remaining == rhs_args {
            return Some(i);
        }
    }
    None
}

/// The positions `(i, j)` of a duplicated element and of the copy whose removal yields `rhs`'s
/// argument list.
fn dup_positions(args: &[Rc<Term>], rhs: &Rc<Term>) -> Option<(usize, usize)> {
    let (rhs_args, _) = rhs_arguments(rhs);
    for j in 1..args.len() {
        if let Some(i) = args[..j].iter().position(|t| *t == args[j]) {
            let mut remaining = args.to_vec();
            remaining.remove(j);
            if remaining == rhs_args {
                return Some((i, j));
            }
        }
    }
    None
}

fn dup_source(args: &[Rc<Term>], j: usize) -> usize {
    args[..j].iter().position(|t| *t == args[j]).unwrap()
}

/// `(= (or ¬(t ≈ t) xs…) (or xs…))` — with the right side possibly a singleton application or
/// a bare term, and the reflexive disequality possibly occurring more than once (the rule
/// removes one occurrence, so another copy can survive on the right).
fn or_not_refl(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let (rhs_args, rhs_is_app) = rhs_arguments(rhs);
    let args = match_term_err!((or ...) = lhs)?.to_vec();
    let pos = args
        .iter()
        .position(|t| match_term!((not (= a b)) = t).is_some_and(|(a, b)| a == b))
        .ok_or_else(|| explanation("no reflexive disequality"))?;
    let (t, _) = match_term!((not (= a b)) = &args[pos]).unwrap();
    let t = t.clone();
    let e = eq(b.pool, &t, &t);

    // dir1 = (cl ¬lhs rhs): from `or_pos`, each *distinct* disjunct is either packed into the
    // right-hand side (if it survives there — which the disequality does when it occurs twice,
    // since the rule removes only one copy) or killed by `refl`
    let mut node = or_pos_step(b, lhs)?;
    let mut seen = std::collections::HashSet::new();
    for arg in &args {
        if !seen.insert(arg.clone()) {
            continue;
        }
        if let Some(j) = rhs_args.iter().position(|x| x == arg) {
            if rhs_is_app {
                let neg = or_neg_step(b, rhs, j)?;
                node = b.resolve(vec![node, neg], vec![(arg.clone(), true)])?;
            }
            // A bare right-hand side *is* the surviving literal: nothing to pack
        } else {
            let r = refl(b, &t);
            node = b.resolve(vec![node, r], vec![(e.clone(), false)])?;
        }
    }
    let dir1 = node;

    // dir2 = (cl lhs ¬rhs): every disjunct of the right-hand side occurs in the left one
    let dir2 = if !rhs_is_app {
        let keep = args
            .iter()
            .position(|x| x == rhs)
            .ok_or_else(|| explanation("surviving term not found"))?;
        or_neg_step(b, lhs, keep)?
    } else {
        let op = or_pos_step(b, rhs)?;
        let mut lits = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for arg in &rhs_args {
            if !seen.insert(arg.clone()) {
                continue;
            }
            let j = args
                .iter()
                .position(|x| x == arg)
                .ok_or_else(|| explanation("right-hand disjunct not on the left"))?;
            lits.push((arg.clone(), j));
        }
        pack_or(b, op, lhs, &lits)?
    };
    b.equiv_intro(lhs.clone(), rhs.clone(), dir1, dir2)
}

/// `(= (distinct xs t ys t zs) false)` — through `distinct_elim` as the definitional rule for
/// `distinct`, plus `refl` on the repeated element.
fn distinct_false(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let args = match lhs.as_ref() {
        Term::Op(Operator::Distinct, args) => args.clone(),
        _ => return Err(explanation("expected a distinct application")),
    };
    let n = args.len();
    let (i, j) = complementary_none(&args).ok_or_else(|| explanation("no repeated element"))?;
    let t = args[i].clone();
    let e = eq(b.pool, &t, &t);
    let not_e = b.not(&e);

    let is_bool = n > 2 && {
        let sort = b.pool.sort(&args[0]);
        sort.as_sort() == Some(&Sort::Bool)
    };
    if is_bool {
        // The checker accepts `(= (distinct …) false)` directly for >2 Boolean arguments
        let clause = vec![eq(b.pool, lhs, rhs)];
        return Ok(b.step(clause, "distinct_elim", Vec::new(), Vec::new()));
    }

    // The expansion the `distinct_elim` checker computes
    let expansion = if n == 2 {
        not_e.clone()
    } else {
        let mut conjuncts = Vec::new();
        for a in 0..n {
            for c in (a + 1)..n {
                let pair = eq(b.pool, &args[a], &args[c]);
                conjuncts.push(b.not(&pair));
            }
        }
        b.pool.add(Term::Op(Operator::And, conjuncts))
    };
    let eq_term = eq(b.pool, lhs, &expansion);
    let de = b.step(
        vec![eq_term.clone()],
        "distinct_elim",
        Vec::new(),
        Vec::new(),
    );
    // ¬expansion (or directly ¬(t ≈ t) for the binary case)
    let refl_node = refl(b, &t);
    let not_exp = if n == 2 {
        let nn = nn_intro(b, &e)?;
        b.resolve(vec![nn, refl_node], vec![(e.clone(), false)])?
    } else {
        // index of the (i, j) pair in the expansion
        let mut k = 0;
        let mut index = 0;
        'outer: for a in 0..n {
            for c in (a + 1)..n {
                if (a, c) == (i, j) {
                    index = k;
                    break 'outer;
                }
                k += 1;
            }
        }
        let ap = and_pos_step(b, &expansion, index)?;
        b.resolve(vec![ap, refl_node], vec![(e.clone(), false)])?
    };
    // From (= lhs expansion) and ¬expansion, derive ¬lhs
    let not_lhs_node = {
        let not_eq_term = b.not(&eq_term);
        let not_lhs = b.not(lhs);
        let pos2 = b.step(
            vec![not_eq_term, not_lhs, expansion.clone()],
            "equiv_pos2",
            Vec::new(),
            Vec::new(),
        );
        let r = b.resolve(vec![pos2, de], vec![(eq_term, false)])?;
        b.resolve(vec![r, not_exp], vec![(expansion, true)])?
    };
    bridge_false(b, not_lhs_node, lhs)
}

fn complementary_none(args: &[Rc<Term>]) -> Option<(usize, usize)> {
    for i in 0..args.len() {
        for j in (i + 1)..args.len() {
            if args[i] == args[j] {
                return Some((i, j));
            }
        }
    }
    None
}

/// `(= (ite C (I ≈ t1) (I ≈ t2)) true)` where `I = (ite C t1 t2)` — the `ite-eq` tautology.
fn ite_eq(b: &mut Builder, lhs: &Rc<Term>, _rhs: &Rc<Term>) -> Res {
    let (c, e1, e2) = match_term_err!((ite c e1 e2) = lhs)?;
    let (c, e1, e2) = (c.clone(), e1.clone(), e2.clone());
    let (ite_term, _) = match_term_err!((= i t) = &e1)?;
    let ite_term = ite_term.clone();

    let (s_then, then_eq) = sel_then(b, &ite_term)?;
    let (s_else, else_eq) = sel_else(b, &ite_term)?;
    if then_eq != e1 || else_eq != e2 {
        return Err(explanation("ite-eq shape mismatch"));
    }
    let ne1 = b.not(&e1);
    let ne2 = b.not(&e2);
    let __n31 = b.not(&c);
    let neg2 = b.step(
        vec![lhs.clone(), __n31.clone(), ne1],
        "ite_neg2",
        Vec::new(),
        Vec::new(),
    );
    let neg1 = b.step(
        vec![lhs.clone(), c.clone(), ne2],
        "ite_neg1",
        Vec::new(),
        Vec::new(),
    );
    let r1 = b.resolve(vec![neg2, s_then], vec![(e1, false)])?;
    // r1 = (cl lhs ¬c)
    let r2 = b.resolve(vec![neg1, s_else], vec![(e2, false)])?;
    // r2 = (cl lhs c)
    let unit = b.resolve(vec![r2, r1], vec![(c, true)])?;
    bridge_true(b, unit, lhs)
}

/// `(= (ite ¬c x y) (ite c y x))`.
fn ite_not_cond(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let (nc, _, _) = match_term_err!((ite c t s) = lhs)?;
    let c = nc
        .remove_negation_err()
        .map_err(ElaborationError::from)?
        .clone();
    let target = eq(b.pool, lhs, rhs);

    // Case `c`: lhs's condition ¬c is false → lhs = y; rhs's condition is true → rhs = y
    let (l_else, l_else_eq) = sel_else(b, lhs)?; // (cl ¬c (= lhs y))
    let (r_then, r_then_eq) = sel_then(b, rhs)?; // (cl ¬c (= rhs y))
    let case_c = guarded(
        b,
        vec![(l_else, l_else_eq), (r_then, r_then_eq)],
        |b, assumes| {
            let l = assumes[0].clone();
            let r = assumes[1].clone();
            trans_chain(b, vec![(l, false), (r, true)])
        },
    )?;
    // case_c = (cl ¬c (= lhs rhs))

    // Case `¬c`: lhs = x (then, guarded by ¬¬c), rhs = x (else, guarded by c)
    let (l_then, l_then_eq) = sel_then(b, lhs)?; // (cl ¬¬c (= lhs x))
    let (r_else, r_else_eq) = sel_else(b, rhs)?; // (cl c (= rhs x))
    let case_nc = guarded(
        b,
        vec![(l_then, l_then_eq), (r_else, r_else_eq)],
        |b, assumes| {
            let l = assumes[0].clone();
            let r = assumes[1].clone();
            trans_chain(b, vec![(l, false), (r, true)])
        },
    )?;
    // case_nc = (cl ¬¬c c (= lhs rhs))

    let nc_term = b.not(&c);
    let r1 = b.resolve(vec![case_c.clone(), case_nc], vec![(nc_term, true)])?;
    // r1 = (cl (= lhs rhs) c)
    let node = b.resolve(vec![r1, case_c], vec![(c, true)])?;
    debug_assert_eq!(node.clause(), &[target]);
    Ok(node)
}

/// `(= (ite c (ite c x y) z) (ite c x z))` and `(= (ite c x (ite c y z)) (ite c x z))`.
fn ite_lookahead(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let (c, _, _) = match_term_err!((ite c t s) = lhs)?;
    let c = c.clone();

    // Case `c`: both sides select their then-branches (twice on the nested side)
    let (l_then, l_then_eq) = sel_then(b, lhs)?;
    let (r_then, r_then_eq) = sel_then(b, rhs)?;
    let l_then_val = match_term!((= i t) = &l_then_eq).unwrap().1.clone();
    let mut parts = vec![(l_then, l_then_eq)];
    let mut chain_flags = vec![false];
    if match_term!((ite c t s) = &l_then_val).is_some_and(|(ic, _, _)| *ic == c) {
        let (inner_sel, inner_eq) = sel_then(b, &l_then_val)?;
        parts.push((inner_sel, inner_eq));
        chain_flags.push(false);
    }
    parts.push((r_then, r_then_eq));
    chain_flags.push(true);
    let case_c = guarded(b, parts, |b, assumes| {
        let links = assumes.into_iter().zip(chain_flags).collect();
        trans_chain(b, links)
    })?;

    // Case `¬c`: both sides select their else-branches (twice on the nested side)
    let (l_else, l_else_eq) = sel_else(b, lhs)?;
    let (r_else, r_else_eq) = sel_else(b, rhs)?;
    let l_else_val = match_term!((= i t) = &l_else_eq).unwrap().1.clone();
    let mut parts = vec![(l_else, l_else_eq)];
    let mut chain_flags = vec![false];
    if match_term!((ite c t s) = &l_else_val).is_some_and(|(ic, _, _)| *ic == c) {
        let (inner_sel, inner_eq) = sel_else(b, &l_else_val)?;
        parts.push((inner_sel, inner_eq));
        chain_flags.push(false);
    }
    parts.push((r_else, r_else_eq));
    chain_flags.push(true);
    let case_nc = guarded(b, parts, |b, assumes| {
        let links = assumes.into_iter().zip(chain_flags).collect();
        trans_chain(b, links)
    })?;

    b.resolve(vec![case_nc, case_c], vec![(c, true)])
}

/// The Boolean-`ite` shapes `ite-then-true`, `ite-else-false`, `ite-then-false`, `ite-else-true`
/// (e.g. `(= (ite c true p) (or c p))`), by the `ite` axioms and the `or`/`and` axioms.
fn bool_ite_shape(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let (c, x, y) = match_term_err!((ite c x y) = lhs)?;
    let (c, x, y) = (c.clone(), x.clone(), y.clone());
    let nc = b.not(&c);
    let not_lhs = b.not(lhs);

    // dir1: (cl ¬lhs rhs); dir2: (cl lhs ¬rhs)
    // ite_pos1 = (cl ¬lhs c y); ite_pos2 = (cl ¬lhs ¬c x)
    // ite_neg1 = (cl lhs c ¬y); ite_neg2 = (cl lhs ¬c ¬x)
    let pos1 = b.step(
        vec![not_lhs.clone(), c.clone(), y.clone()],
        "ite_pos1",
        Vec::new(),
        Vec::new(),
    );
    let pos2 = b.step(
        vec![not_lhs.clone(), nc.clone(), x.clone()],
        "ite_pos2",
        Vec::new(),
        Vec::new(),
    );
    let ny = b.not(&y);
    let nx = b.not(&x);
    let neg1 = b.step(
        vec![lhs.clone(), c.clone(), ny.clone()],
        "ite_neg1",
        Vec::new(),
        Vec::new(),
    );
    let neg2 = b.step(
        vec![lhs.clone(), nc.clone(), nx.clone()],
        "ite_neg2",
        Vec::new(),
        Vec::new(),
    );

    if x.is_bool_true() {
        // `(= (ite c true p) (or c p))`
        let ta = true_ax(b);
        let tt = b.pool.bool_true();
        // dir1: pos1 = (cl ¬lhs c p): pack into (or c p)
        let dir1 = pack_or(b, pos1, rhs, &[(c.clone(), 0), (y.clone(), 1)])?;
        // dir2: or_pos(rhs) = (cl ¬rhs c p); neg1 = (cl lhs c ¬p): resolve on p, then kill c
        // with neg2+true: neg2 = (cl lhs ¬c ¬true) + true axiom → (cl lhs ¬c)
        let n2 = b.resolve(vec![neg2, ta], vec![(tt, false)])?;
        let op = or_pos_step(b, rhs)?;
        let r1 = b.resolve(vec![op, neg1], vec![(y.clone(), true)])?;
        // r1 = (cl ¬rhs c lhs): kill c with n2
        let dir2 = b.resolve(vec![r1, n2], vec![(c.clone(), true)])?;
        b.equiv_intro(lhs.clone(), rhs.clone(), dir1, dir2)
    } else if y.is_bool_false() {
        // `(= (ite c p false) (and c p))`
        let fa = false_ax(b);
        let ff = b.pool.bool_false();
        // dir1: assume-free: p1 = (cl ¬lhs c false) + false axiom → (cl ¬lhs c)... need
        // (cl ¬lhs (and c p)): from (cl ¬lhs c) and (cl ¬lhs p) via and_neg
        let u_c = b.resolve(vec![pos1, fa], vec![(ff.clone(), true)])?;
        // pos2 = (cl ¬lhs ¬c x): kill ¬c against u_c's c
        let u_p = b.resolve(vec![pos2, u_c.clone()], vec![(c.clone(), false)])?;
        // u_p = (cl ¬lhs x)
        let an = and_neg_step(b, rhs)?;
        let r1 = b.resolve(vec![an, u_c], vec![(c.clone(), false)])?;
        let dir1 = b.resolve(vec![r1, u_p], vec![(x.clone(), false)])?;
        // dir2: (cl lhs ¬rhs): and_pos units against neg2
        let ap0 = and_pos_step(b, rhs, 0)?;
        let ap1 = and_pos_step(b, rhs, 1)?;
        // neg2 = (cl lhs ¬c ¬p): kill ¬c with ap0's c, ¬p with ap1's p
        let r1 = b.resolve(vec![neg2, ap0], vec![(c.clone(), false)])?;
        let dir2 = b.resolve(vec![r1, ap1], vec![(x.clone(), false)])?;
        b.equiv_intro(lhs.clone(), rhs.clone(), dir1, dir2)
    } else if x.is_bool_false() {
        // `(= (ite c false p) (and ¬c p))`
        let fa = false_ax(b);
        let ff = b.pool.bool_false();
        let u_nc = b.resolve(vec![pos2, fa], vec![(ff.clone(), true)])?;
        // u_nc = (cl ¬lhs ¬c)
        let u_p = b.resolve(vec![pos1, u_nc.clone()], vec![(c.clone(), true)])?;
        // u_p = (cl ¬lhs p)
        let an = and_neg_step(b, rhs)?;
        let r1 = b.resolve(vec![an, u_nc], vec![(nc.clone(), false)])?;
        let dir1 = b.resolve(vec![r1, u_p], vec![(y.clone(), false)])?;
        let ap0 = and_pos_step(b, rhs, 0)?;
        let ap1 = and_pos_step(b, rhs, 1)?;
        // neg1 = (cl lhs c ¬p): kill c against ap0's ¬c (complement), ¬p against ap1's p
        let r1 = b.resolve(vec![neg1, ap0], vec![(c.clone(), true)])?;
        let dir2 = b.resolve(vec![r1, ap1], vec![(y.clone(), false)])?;
        b.equiv_intro(lhs.clone(), rhs.clone(), dir1, dir2)
    } else if y.is_bool_true() {
        // `(= (ite c p true) (or ¬c p))`
        let ta = true_ax(b);
        let tt = b.pool.bool_true();
        // pos2 = (cl ¬lhs ¬c p): pack into (or ¬c p)
        let dir1 = pack_or(b, pos2, rhs, &[(nc.clone(), 0), (x.clone(), 1)])?;
        // dir2: neg1 = (cl lhs c ¬true) + true axiom → (cl lhs c); or_pos(rhs) = (cl ¬rhs ¬c p);
        // neg2 = (cl lhs ¬c ¬p)
        let n1 = b.resolve(vec![neg1, ta], vec![(tt, false)])?;
        let op = or_pos_step(b, rhs)?;
        let r1 = b.resolve(vec![op, neg2], vec![(x.clone(), true)])?;
        // r1 = (cl ¬rhs ¬c lhs ¬c) = (cl ¬rhs ¬c lhs)
        let dir2 = b.resolve(vec![r1, n1], vec![(c.clone(), false)])?;
        b.equiv_intro(lhs.clone(), rhs.clone(), dir1, dir2)
    } else {
        Err(explanation("unrecognized Boolean ite shape"))
    }
}

/// `(= (⋈ (ite C t s) r) (ite C (⋈ t r) (⋈ s r)))` for a relation or equality `⋈` — the
/// `*-ite-lift` rules.
fn rel_ite_lift(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let (c, rx, ry) = match_term_err!((ite c x y) = rhs)?;
    let (c, rx, ry) = (c.clone(), rx.clone(), ry.clone());
    // The ite term inside the left atom
    let ite_term = match lhs.as_ref() {
        Term::Op(_, args) => args
            .iter()
            .find(|a| match_term!((ite c t s) = a).is_some_and(|(ic, _, _)| *ic == c))
            .cloned()
            .ok_or_else(|| explanation("no lifted ite argument"))?,
        _ => return Err(explanation("left side is not an operation")),
    };

    let mut sides = Vec::new();
    for is_then in [true, false] {
        // Selection on the inner ite: (cl ±c, ite ≈ branch), and on the right ite:
        // (cl ±c, rhs ≈ atom); under both equalities, `cong` gives (= lhs atom) and `trans`
        // with the flipped right selection gives (= lhs rhs).
        let (sel_i, sel_i_eq) = if is_then {
            sel_then(b, &ite_term)?
        } else {
            sel_else(b, &ite_term)?
        };
        let (sel_r, sel_r_eq) = if is_then {
            sel_then(b, rhs)?
        } else {
            sel_else(b, rhs)?
        };
        let atom = if is_then { rx.clone() } else { ry.clone() };
        let lhs_c = lhs.clone();
        let combined = guarded(
            b,
            vec![(sel_i, sel_i_eq), (sel_r, sel_r_eq)],
            |b, assumes| {
                let clause = vec![eq(b.pool, &lhs_c, &atom)];
                let cong = b.step(clause, "cong", vec![assumes[0].clone()], Vec::new());
                trans_chain(b, vec![(cong, false), (assumes[1].clone(), true)])
            },
        )?;
        sides.push(combined);
    }
    let mut iter = sides.into_iter();
    let (side_then, side_else) = (iter.next().unwrap(), iter.next().unwrap());
    b.resolve(vec![side_else, side_then], vec![(c, true)])
}

/// Extracts the instantiation values for a RARE rule from a rewrite instance, in the order of
/// the rule's declared `:args`. Only the rules the `*_simplify` traces can emit are covered.
pub fn extract_rare_args(
    pool: &mut PrimitivePool,
    label: &str,
    before: &Rc<Term>,
    after: &Rc<Term>,
) -> Option<Vec<Rc<Term>>> {
    let two = |a: &Rc<Term>, b: &Rc<Term>| Some(vec![a.clone(), b.clone()]);
    match label {
        "ite-true-cond" | "ite-false-cond" => {
            let (_, t, s) = match_term!((ite c t s) = before)?;
            two(t, s)
        }
        "ite-eq-branch" => {
            let (c, t, _) = match_term!((ite c t s) = before)?;
            two(c, t)
        }
        "ite-not-cond" => {
            let (nc, t, s) = match_term!((ite c t s) = before)?;
            let c = nc.remove_negation()?;
            Some(vec![c.clone(), t.clone(), s.clone()])
        }
        "ite-then-lookahead" => {
            let (c, inner, z) = match_term!((ite c i z) = before)?;
            let (_, x, y) = match_term!((ite c x y) = inner)?;
            Some(vec![c.clone(), x.clone(), y.clone(), z.clone()])
        }
        "ite-else-lookahead" => {
            let (c, x, inner) = match_term!((ite c x i) = before)?;
            let (_, y, z) = match_term!((ite c y z) = inner)?;
            Some(vec![c.clone(), x.clone(), y.clone(), z.clone()])
        }
        "ite-then-true" | "ite-then-false" => {
            let (c, _, p) = match_term!((ite c x p) = before)?;
            two(c, p)
        }
        "ite-else-false" | "ite-else-true" => {
            let (c, p, _) = match_term!((ite c p x) = before)?;
            two(c, p)
        }
        "ite-then-true-else-false" | "ite-then-false-else-true" => {
            let (c, _, _) = match_term!((ite c x y) = before)?;
            Some(vec![c.clone()])
        }
        "eq-refl" => {
            let (t, _) = match_term!((= t t) = before)?;
            Some(vec![t.clone()])
        }
        "bool-double-not-elim" => Some(vec![after.clone()]),
        "bool-impl-false2" | "bool-impl-true2" => {
            let (_, t) = match_term!((=> c t) = before)?;
            Some(vec![t.clone()])
        }
        "bool-impl-true1" | "bool-impl-false1" => {
            let (t, _) = match_term!((=> t c) = before)?;
            Some(vec![t.clone()])
        }
        "implies-contra" => {
            let (np, nq) = match_term!((=> np nq) = before)?;
            two(np.remove_negation()?, nq.remove_negation()?)
        }
        "implies-refl" => {
            let (p, _) = match_term!((=> p p) = before)?;
            Some(vec![p.clone()])
        }
        "implies-neg-l" => {
            let (_, p) = match_term!((=> np p) = before)?;
            Some(vec![p.clone()])
        }
        "implies-neg-r" => {
            let (p, _) = match_term!((=> p np) = before)?;
            Some(vec![p.clone()])
        }
        "bool-implies-peirce" => {
            let (inner, _) = match_term!((=> i q) = before)?;
            let (p, q) = match_term!((=> p q) = inner)?;
            two(p, q)
        }
        "bool-implies-uncurry" => {
            let (p, inner) = match_term!((=> p i) = before)?;
            let (q, r) = match_term!((=> q r) = inner)?;
            Some(vec![p.clone(), q.clone(), r.clone()])
        }
        "bool-and-mp-r" => {
            let args = match_term!((and ...) = before)?;
            let [p, i] = args else { return None };
            let (_, q) = match_term!((=> p q) = i)?;
            two(p, q)
        }
        "bool-and-mp-l" => {
            let args = match_term!((and ...) = before)?;
            let [i, p] = args else { return None };
            let (_, q) = match_term!((=> p q) = i)?;
            two(p, q)
        }
        "equiv-neg-both" => {
            let (np, nq) = match_term!((= np nq) = before)?;
            two(np.remove_negation()?, nq.remove_negation()?)
        }
        "bool-eq-nrefl" => {
            let (x, _) = match_term!((= x nx) = before)?;
            Some(vec![x.clone()])
        }
        "equiv-neg-l" => {
            let (_, x) = match_term!((= nx x) = before)?;
            Some(vec![x.clone()])
        }
        "equiv-true-l" | "equiv-false-l" => {
            let (_, p) = match_term!((= c p) = before)?;
            Some(vec![p.clone()])
        }
        "bool-eq-true" | "bool-eq-false" => {
            let (p, _) = match_term!((= p c) = before)?;
            Some(vec![p.clone()])
        }
        "bool-implies-de-morgan" => {
            let inner = before.remove_negation()?;
            let (p, q) = match_term!((=> p q) = inner)?;
            two(p, q)
        }
        "bool-or-de-morgan" => {
            let inner = before.remove_negation()?;
            let args = match_term!((or ...) = inner)?;
            if args.len() < 2 {
                return None;
            }
            let zs = rare_list(pool, args[2..].to_vec());
            Some(vec![args[0].clone(), args[1].clone(), zs])
        }
        "bool-and-de-morgan" => {
            let inner = before.remove_negation()?;
            let args = match_term!((and ...) = inner)?;
            if args.len() < 2 {
                return None;
            }
            let zs = rare_list(pool, args[2..].to_vec());
            Some(vec![args[0].clone(), args[1].clone(), zs])
        }
        "comp-lt-elim" | "comp-gt-elim" | "comp-geq-flip" => {
            let (op_args,) = match before.as_ref() {
                Term::Op(_, args) if args.len() == 2 => (args.clone(),),
                _ => return None,
            };
            two(&op_args[0], &op_args[1])
        }
        "comp-lt-irrefl" | "comp-leq-refl" => {
            let (args,) = match before.as_ref() {
                Term::Op(_, args) if args.len() == 2 => (args.clone(),),
                _ => return None,
            };
            Some(vec![args[0].clone()])
        }
        "and-flatten" | "or-flatten" => {
            let args = match before.as_ref() {
                Term::Op(Operator::And | Operator::Or, args) if args.len() == 1 => args,
                _ => return None,
            };
            let inner_args = match args[0].as_ref() {
                Term::Op(Operator::And | Operator::Or, inner) => inner.clone(),
                _ => return None,
            };
            let empty = rare_list(pool, Vec::new());
            let ys = rare_list(pool, inner_args);
            Some(vec![empty.clone(), ys, empty])
        }
        "and-true-elim" | "or-false-elim" => {
            let neutral = label == "and-true-elim";
            let args = match before.as_ref() {
                Term::Op(Operator::And | Operator::Or, args) => args.clone(),
                _ => return None,
            };
            let pos = removed_position(&args, after, neutral)?;
            let xs = rare_list(pool, args[..pos].to_vec());
            let ys = rare_list(pool, args[pos + 1..].to_vec());
            Some(vec![xs, ys])
        }
        "and-dup-elim" | "or-dup-elim" => {
            let args = match before.as_ref() {
                Term::Op(Operator::And | Operator::Or, args) => args.clone(),
                _ => return None,
            };
            let (i, j) = dup_positions(&args, after)?;
            let xs = rare_list(pool, args[..i].to_vec());
            let bt = args[i].clone();
            let ys = rare_list(pool, args[i + 1..j].to_vec());
            let zs = rare_list(pool, args[j + 1..].to_vec());
            Some(vec![xs, bt, ys, zs])
        }
        "and-false" | "or-true" => {
            let constant = label == "or-true";
            let args = match before.as_ref() {
                Term::Op(Operator::And | Operator::Or, args) => args.clone(),
                _ => return None,
            };
            let pos = args.iter().position(|t| t.is_bool_constant(constant))?;
            let xs = rare_list(pool, args[..pos].to_vec());
            let ys = rare_list(pool, args[pos + 1..].to_vec());
            Some(vec![xs, ys])
        }
        "bool-and-conf" | "bool-and-conf2" | "bool-or-taut" | "bool-or-taut2" => {
            let args = match before.as_ref() {
                Term::Op(Operator::And | Operator::Or, args) => args.clone(),
                _ => return None,
            };
            let (i, k) = complementary_pair(&args)?;
            // The `2` variants match `(op xs (not w) ys w zs)`, so `w` is the positive literal
            // (at position `k`); the plain variants match `(op xs w ys (not w) zs)` (at `i`)
            let w = if label.ends_with('2') {
                args[k].clone()
            } else {
                args[i].clone()
            };
            let xs = rare_list(pool, args[..i].to_vec());
            let ys = rare_list(pool, args[i + 1..k].to_vec());
            let zs = rare_list(pool, args[k + 1..].to_vec());
            Some(vec![xs, w, ys, zs])
        }
        _ => None,
    }
}

/// Resolves an ambiguous trace label to the concrete rule name it stands for, by the shape of
/// the rewritten term. Today only `implies-neg` is ambiguous (it stands for the two
/// implication-negation rules).
pub fn resolve_label(label: &'static str, before: &Rc<Term>) -> &'static str {
    if label == "implies-neg" {
        if match_term!((=> np p) = before).is_some_and(|(np, p)| np.remove_negation() == Some(p)) {
            return "implies-neg-l";
        }
        return "implies-neg-r";
    }
    label
}
