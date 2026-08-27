//! The `evaluate` recipe: constant evaluation reduced to the computational core.
//!
//! An `evaluate` step concludes `(= t v)` for a ground interpreted term `t` and its value `v`.
//! The reduction lands entirely on rules already in the core: a *numeric* `t` is a ring identity
//! and becomes one `poly_simp` step; a *Boolean* `t` is derived as a literal by structural
//! recursion (the CNF axioms select the branch each connective's value came from, `la_generic`
//! decides constant relational atoms, `poly_simp`/`la_generic` decide constant equalities), and
//! a final `equiv_neg1`/`equiv_neg2` bridge converts the literal into `(= t true)`/`(= t false)`.
//! Branches are decided by the checker's own evaluation function (`Rc<Term>::evaluate`), so the
//! recipe follows exactly the semantics the `evaluate` checker implements.
//!
//! The one genuine gap is integer `div`/`mod`, which no core rule characterizes; those instances
//! fail the `poly_simp` validation and are kept unreduced.

use super::super::Builder;
use crate::{ast::*, checker::error::CheckerError, elaborator::error::ElaborationError};

type Res = Result<Rc<ProofNode>, ElaborationError>;

fn explanation(msg: impl Into<String>) -> ElaborationError {
    CheckerError::Explanation(msg.into()).into()
}

fn eq(pool: &mut PrimitivePool, a: &Rc<Term>, b: &Rc<Term>) -> Rc<Term> {
    build_term!(pool, (= {a.clone()} {b.clone()}))
}

/// Derives `(cl (= term value))` for an `evaluate` instance.
/// Derives `(cl (= lhs rhs))` for two *ground* terms that evaluate to the same value, by evaluating
/// each side and joining them.
///
/// This is the fallback for a rewrite instance whose recipe does not apply because the instance is
/// degenerate. cvc5 emits `(= (= false false) (not false))` as a `bool-eq-false` instance, for
/// example: the recipe expects a `phi` distinct from the `false` it is paired with, and the two
/// coinciding makes its `equiv_neg2` clause carry a duplicate literal that resolution's set
/// semantics then removes twice over. A ground instance needs none of that reasoning — both sides
/// have a value, and it is the same one.
pub fn ground_equal(b: &mut Builder, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    let value = lhs.evaluate(b.pool);
    if value != rhs.evaluate(b.pool)
        || (!value.is_bool_constant(true)
            && !value.is_bool_constant(false)
            && value.as_fraction().is_none())
    {
        return Err(explanation(
            "the two sides are not ground with a common value",
        ));
    }
    let left = evaluation(b, lhs, &value)?;
    if *rhs == value {
        return Ok(left);
    }
    let right = evaluation(b, rhs, &value)?;
    let flipped = vec![eq(b.pool, &value, rhs)];
    let flipped = b.step(flipped, "symm", vec![right], Vec::new());
    let clause = vec![eq(b.pool, lhs, rhs)];
    Ok(b.step(clause, "trans", vec![left, flipped], Vec::new()))
}

/// Derives `(cl (= (to_int c) k))` for a rational constant `c`, where `k` is its floor.
///
/// This is the one place the core needs to know what `to_int` *is*, and it gets it from the two
/// floor axioms rather than from an evaluator: `to_int c <= c` and `c < to_int c + 1` bound the
/// value to a half-open unit interval, `la_generic`'s integer strengthening turns each bound into
/// the corresponding bound on `k`, and `la_disequality` closes the two into the equality.
fn to_int_value(b: &mut Builder, arg: &Rc<Term>) -> Res {
    let floor_term = build_term!(b.pool, (to_int {arg.clone()}));
    let k = floor_term.evaluate(b.pool);
    if k.as_fraction().is_none() {
        return Err(explanation("`to_int` of a non-constant argument"));
    }
    let real_floor = build_term!(b.pool, (to_real {floor_term.clone()}));
    let one = b.pool.add(Term::new_int(1));

    // The two axioms
    let lower_lit = build_term!(b.pool, (<= {real_floor.clone()} {arg.clone()}));
    let lower = b.step(
        vec![lower_lit.clone()],
        "to_int_lower",
        Vec::new(),
        Vec::new(),
    );
    let bound = build_term!(b.pool, (+ {real_floor.clone()} {one}));
    let upper_lit = build_term!(b.pool, (< {arg.clone()} {bound}));
    let upper = b.step(
        vec![upper_lit.clone()],
        "to_int_upper",
        Vec::new(),
        Vec::new(),
    );

    // Each axiom tightens to the corresponding bound on `k`
    let le = build_term!(b.pool, (<= {floor_term.clone()} {k.clone()}));
    let ge = build_term!(b.pool, (<= {k.clone()} {floor_term.clone()}));
    let (n_lower, n_upper) = (b.not(&lower_lit), b.not(&upper_lit));
    let le_cl = super::recipes::la_clause(b, vec![n_lower, le.clone()])?;
    let ge_cl = super::recipes::la_clause(b, vec![n_upper, ge.clone()])?;
    let le_unit = b.resolve(vec![le_cl, lower], vec![(lower_lit, false)])?;
    let ge_unit = b.resolve(vec![ge_cl, upper], vec![(upper_lit, false)])?;

    // Antisymmetry, which `la_disequality` states as a unit clause holding a disjunction
    let goal = eq(b.pool, &floor_term, &k);
    let (n_le, n_ge) = (b.not(&le), b.not(&ge));
    let disj = build_term!(b.pool, (or {goal.clone()} {n_le.clone()} {n_ge.clone()}));
    let anti = b.step(vec![disj], "la_disequality", Vec::new(), Vec::new());
    let split = b.step(vec![goal, n_le, n_ge], "or", vec![anti], Vec::new());
    b.resolve(
        vec![split, le_unit, ge_unit],
        vec![(le, false), (ge, false)],
    )
}

/// Replaces every `(to_int c)` subterm of a ground term by its value, returning a derivation of
/// `(cl (= term folded))` together with the folded term, or `None` when there is nothing to fold.
///
/// The ring normalization behind `poly_simp` treats `(to_int c)` as an atom, so a term that mixes
/// it with arithmetic — cvc5 emits `(= (+ (to_int -3/2) 1) -1)` — is not a ring identity until the
/// application is folded away. Congruence carries the folding through the surrounding term.
fn fold_to_int(
    b: &mut Builder,
    term: &Rc<Term>,
) -> Result<Option<(Rc<ProofNode>, Rc<Term>)>, ElaborationError> {
    if let Some(arg) = match_term!((to_int a) = term) {
        if arg.as_fraction().is_none() {
            return Ok(None);
        }
        let arg = arg.clone();
        let node = to_int_value(b, &arg)?;
        let value = build_term!(b.pool, (to_int { arg })).evaluate(b.pool);
        return Ok(Some((node, value)));
    }
    let Term::Op(op, args) = term.as_ref() else {
        return Ok(None);
    };
    let (op, args) = (*op, args.clone());
    let mut premises = Vec::new();
    let mut new_args = Vec::new();
    for arg in &args {
        match fold_to_int(b, arg)? {
            Some((node, folded)) => {
                premises.push(node);
                new_args.push(folded);
            }
            None => new_args.push(arg.clone()),
        }
    }
    if premises.is_empty() {
        return Ok(None);
    }
    let folded = b.pool.add(Term::Op(op, new_args));
    let clause = vec![eq(b.pool, term, &folded)];
    let node = b.step(clause, "cong", premises, Vec::new());
    Ok(Some((node, folded)))
}

pub fn evaluation(b: &mut Builder, term: &Rc<Term>, value: &Rc<Term>) -> Res {
    // Validate against the checker's own semantics first
    if term.evaluate(b.pool) != *value {
        return Err(explanation("the term does not evaluate to the value"));
    }
    if value.is_bool_true() {
        let lit = literal(b, term, true)?;
        super::recipes::bridge_true(b, lit, term)
    } else if value.is_bool_false() {
        let lit = literal(b, term, false)?;
        super::recipes::bridge_false(b, lit, term)
    } else if crate::checker::poly_simp_equal(b.pool, term, value).is_ok() {
        // A numeric value: the conclusion is a ring identity, i.e. one `poly_simp` step
        let clause = vec![eq(b.pool, term, value)];
        Ok(b.step(clause, "poly_simp", Vec::new(), Vec::new()))
    } else if let Some((c, x, y)) = match_term!((ite c x y) = term) {
        // A term-level `ite` over a decided condition: the selection axiom picks the branch,
        // and the branch's own evaluation closes by transitivity
        let (c, x, y) = (c.clone(), x.clone(), y.clone());
        let cv = c.evaluate(b.pool).is_bool_true();
        let uc = literal(b, &c, cv)?;
        let (sel, _) = if cv {
            super::recipes::sel_then(b, term)?
        } else {
            super::recipes::sel_else(b, term)?
        };
        let branch = if cv { x } else { y };
        let selected = if cv {
            let nc = b.not(&c);
            let _ = nc;
            b.resolve(vec![sel, uc], vec![(c, false)])?
        } else {
            b.resolve(vec![sel, uc], vec![(c, true)])?
        };
        if branch == *value {
            return Ok(selected);
        }
        let rest = evaluation(b, &branch, value)?;
        let clause = vec![eq(b.pool, term, value)];
        Ok(b.step(clause, "trans", vec![selected, rest], Vec::new()))
    } else if let Some((folded, rest_term)) = fold_to_int(b, term)? {
        // A ground `to_int` application, which the ring normalization treats as an atom: fold it to
        // its value first, and the remainder is an ordinary numeric evaluation
        let rest = evaluation(b, &rest_term, value)?;
        let clause = vec![eq(b.pool, term, value)];
        Ok(b.step(clause, "trans", vec![folded, rest], Vec::new()))
    } else {
        crate::checker::poly_simp_equal(b.pool, term, value)?;
        unreachable!()
    }
}

/// Derives the literal `(cl t)` (for `want = true`) or `(cl ¬t)` (for `want = false`) for a
/// ground Boolean term, by structural recursion.
fn literal(b: &mut Builder, t: &Rc<Term>, want: bool) -> Res {
    // A ground `to_int` application anywhere inside is folded away first: the arithmetic recipes
    // below all go through `la_generic` or `poly_simp`, and both treat it as an opaque atom
    if let Some((folded, rest_term)) = fold_to_int(b, t)? {
        let inner = literal(b, &rest_term, want)?;
        let equiv = eq(b.pool, t, &rest_term);
        let (nt, n_rest) = (b.not(t), b.not(&rest_term));
        return if want {
            let e2 = b.step(vec![t.clone(), n_rest], "equiv2", vec![folded], Vec::new());
            b.resolve(vec![e2, inner], vec![(rest_term, false)])
        } else {
            let _ = equiv;
            let e1 = b.step(
                vec![nt, rest_term.clone()],
                "equiv1",
                vec![folded],
                Vec::new(),
            );
            b.resolve(vec![e1, inner], vec![(rest_term, true)])
        };
    }
    // Guard against the recursion disagreeing with the evaluator
    let val = t.evaluate(b.pool);
    if val.is_bool_true() != want || !(val.is_bool_true() || val.is_bool_false()) {
        return Err(explanation("evaluation mismatch in the literal recursion"));
    }

    if t.is_bool_true() {
        return Ok(super::recipes::true_ax(b));
    }
    if t.is_bool_false() {
        return Ok(super::recipes::false_ax(b));
    }

    if let Some(u) = match_term!((not u) = t) {
        let u = u.clone();
        if want {
            // (cl ¬u) is the literal (cl t)
            return literal(b, &u, false);
        }
        // want ¬t = ¬¬u: from (cl u) and (cl ¬u ¬¬u)
        let inner = literal(b, &u, true)?;
        let nn = super::recipes::nn_intro(b, &u)?;
        return b.resolve(vec![nn, inner], vec![(u, false)]);
    }

    match t.as_ref() {
        Term::Op(Operator::And, args) => {
            let args = args.clone();
            if want {
                let mut units = Vec::new();
                for arg in &args {
                    units.push(literal(b, arg, true)?);
                }
                b.and_intro(units)
            } else {
                let pos = args
                    .iter()
                    .position(|a| a.evaluate(b.pool).is_bool_false())
                    .ok_or_else(|| explanation("no false conjunct"))?;
                let unit = literal(b, &args[pos], false)?;
                let ap = super::recipes::and_pos_step(b, t, pos)?;
                b.resolve(vec![ap, unit], vec![(args[pos].clone(), true)])
            }
        }
        Term::Op(Operator::Or, args) => {
            let args = args.clone();
            if want {
                let pos = args
                    .iter()
                    .position(|a| a.evaluate(b.pool).is_bool_true())
                    .ok_or_else(|| explanation("no true disjunct"))?;
                let unit = literal(b, &args[pos], true)?;
                let on = super::recipes::or_neg_step(b, t, pos)?;
                b.resolve(vec![on, unit], vec![(args[pos].clone(), false)])
            } else {
                let op = super::recipes::or_pos_step(b, t)?;
                let mut node = op;
                let mut seen = std::collections::HashSet::new();
                for arg in &args {
                    if !seen.insert(arg.clone()) {
                        continue;
                    }
                    let unit = literal(b, arg, false)?;
                    node = b.resolve(vec![node, unit], vec![(arg.clone(), true)])?;
                }
                Ok(node)
            }
        }
        Term::Op(Operator::Implies, args) => {
            let [a, c] = args.as_slice() else {
                return Err(explanation("non-binary implication"));
            };
            let (a, c) = (a.clone(), c.clone());
            if want {
                if c.evaluate(b.pool).is_bool_true() {
                    let uc = literal(b, &c, true)?;
                    let nc = b.not(&c);
                    let neg2 = b.step(vec![t.clone(), nc], "implies_neg2", Vec::new(), Vec::new());
                    b.resolve(vec![neg2, uc], vec![(c, false)])
                } else {
                    let ua = literal(b, &a, false)?;
                    let neg1 = b.step(
                        vec![t.clone(), a.clone()],
                        "implies_neg1",
                        Vec::new(),
                        Vec::new(),
                    );
                    b.resolve(vec![neg1, ua], vec![(a, true)])
                }
            } else {
                let ua = literal(b, &a, true)?;
                let uc = literal(b, &c, false)?;
                let nt = b.not(t);
                let na = b.not(&a);
                let pos = b.step(
                    vec![nt, na, c.clone()],
                    "implies_pos",
                    Vec::new(),
                    Vec::new(),
                );
                let r = b.resolve(vec![pos, ua], vec![(a, false)])?;
                b.resolve(vec![r, uc], vec![(c, true)])
            }
        }
        Term::Op(Operator::Xor, args) => {
            let [x, y] = args.as_slice() else {
                return Err(explanation("non-binary xor"));
            };
            let (x, y) = (x.clone(), y.clone());
            let xv = x.evaluate(b.pool).is_bool_true();
            let ux = literal(b, &x, xv)?;
            let yv = y.evaluate(b.pool).is_bool_true();
            let uy = literal(b, &y, yv)?;
            let (nx, ny) = (b.not(&x), b.not(&y));
            let nt = b.not(t);
            match (want, xv, yv) {
                (true, true, false) => {
                    // xor_neg2 = (cl X ¬x y)
                    let ax = b.step(
                        vec![t.clone(), nx, y.clone()],
                        "xor_neg2",
                        Vec::new(),
                        Vec::new(),
                    );
                    let r = b.resolve(vec![ax, ux], vec![(x, false)])?;
                    b.resolve(vec![r, uy], vec![(y, true)])
                }
                (true, false, true) => {
                    // xor_neg1 = (cl X x ¬y)
                    let ax = b.step(
                        vec![t.clone(), x.clone(), ny],
                        "xor_neg1",
                        Vec::new(),
                        Vec::new(),
                    );
                    let r = b.resolve(vec![ax, ux], vec![(x, true)])?;
                    b.resolve(vec![r, uy], vec![(y, false)])
                }
                (false, true, true) => {
                    // xor_pos2 = (cl ¬X ¬x ¬y)
                    let ax = b.step(vec![nt, nx, ny], "xor_pos2", Vec::new(), Vec::new());
                    let r = b.resolve(vec![ax, ux], vec![(x, false)])?;
                    b.resolve(vec![r, uy], vec![(y, false)])
                }
                (false, false, false) => {
                    // xor_pos1 = (cl ¬X x y)
                    let ax = b.step(
                        vec![nt, x.clone(), y.clone()],
                        "xor_pos1",
                        Vec::new(),
                        Vec::new(),
                    );
                    let r = b.resolve(vec![ax, ux], vec![(x, true)])?;
                    b.resolve(vec![r, uy], vec![(y, true)])
                }
                _ => Err(explanation("xor evaluation mismatch")),
            }
        }
        Term::Op(Operator::Ite, args) => {
            let [c, x, y] = args.as_slice() else {
                return Err(explanation("non-ternary ite"));
            };
            let (c, x, y) = (c.clone(), x.clone(), y.clone());
            let cv = c.evaluate(b.pool).is_bool_true();
            let uc = literal(b, &c, cv)?;
            let branch = if cv { x } else { y };
            let ub = literal(b, &branch, want)?;
            let nc = b.not(&c);
            let nt = b.not(t);
            match (want, cv) {
                (true, true) => {
                    // ite_neg2 = (cl T ¬c ¬x)
                    let nb = b.not(&branch);
                    let ax = b.step(vec![t.clone(), nc, nb], "ite_neg2", Vec::new(), Vec::new());
                    let r = b.resolve(vec![ax, uc], vec![(c, false)])?;
                    b.resolve(vec![r, ub], vec![(branch, false)])
                }
                (true, false) => {
                    // ite_neg1 = (cl T c ¬y)
                    let nb = b.not(&branch);
                    let ax = b.step(
                        vec![t.clone(), c.clone(), nb],
                        "ite_neg1",
                        Vec::new(),
                        Vec::new(),
                    );
                    let r = b.resolve(vec![ax, uc], vec![(c, true)])?;
                    b.resolve(vec![r, ub], vec![(branch, false)])
                }
                (false, true) => {
                    // ite_pos2 = (cl ¬T ¬c x)
                    let ax = b.step(
                        vec![nt, nc, branch.clone()],
                        "ite_pos2",
                        Vec::new(),
                        Vec::new(),
                    );
                    let r = b.resolve(vec![ax, uc], vec![(c, false)])?;
                    b.resolve(vec![r, ub], vec![(branch, true)])
                }
                (false, false) => {
                    // ite_pos1 = (cl ¬T c y)
                    let ax = b.step(
                        vec![nt, c.clone(), branch.clone()],
                        "ite_pos1",
                        Vec::new(),
                        Vec::new(),
                    );
                    let r = b.resolve(vec![ax, uc], vec![(c, true)])?;
                    b.resolve(vec![r, ub], vec![(branch, true)])
                }
            }
        }
        Term::Op(Operator::Equals, args) => {
            let [x, y] = args.as_slice() else {
                return Err(explanation("non-binary equality"));
            };
            let (x, y) = (x.clone(), y.clone());
            let sort = b.pool.sort(&x);
            if sort.as_sort() == Some(&Sort::Bool) {
                let xv = x.evaluate(b.pool).is_bool_true();
                let yv = y.evaluate(b.pool).is_bool_true();
                let ux = literal(b, &x, xv)?;
                let uy = literal(b, &y, yv)?;
                let (nx, ny) = (b.not(&x), b.not(&y));
                let nt = b.not(t);
                match (want, xv, yv) {
                    (true, true, true) => {
                        // equiv_neg2 = (cl T x y)... needs ¬x ¬y? No: (cl T x y) resolves with
                        // nothing. The right axiom: equiv_neg1 = (cl T ¬x ¬y): kill with units
                        let ax = b.step(
                            vec![t.clone(), nx, ny],
                            "equiv_neg1",
                            Vec::new(),
                            Vec::new(),
                        );
                        let r = b.resolve(vec![ax, ux], vec![(x.clone(), false)])?;
                        // With `x` and `y` the same term the axiom's two literals are one, and
                        // resolution's set semantics has already removed both
                        if x == y {
                            return Ok(r);
                        }
                        b.resolve(vec![r, uy], vec![(y, false)])
                    }
                    (true, false, false) => {
                        // equiv_neg2 = (cl T x y): kill with the negative units
                        let ax = b.step(
                            vec![t.clone(), x.clone(), y.clone()],
                            "equiv_neg2",
                            Vec::new(),
                            Vec::new(),
                        );
                        let r = b.resolve(vec![ax, ux], vec![(x.clone(), true)])?;
                        if x == y {
                            return Ok(r);
                        }
                        b.resolve(vec![r, uy], vec![(y, true)])
                    }
                    (false, true, false) => {
                        // equiv_pos1 = (cl ¬T x ¬y): x is true, y is false: kill x's literal
                        // against ¬x?? -- use equiv_pos2 = (cl ¬T ¬x y): units x, ¬y
                        let ax = b.step(
                            vec![nt, nx, y.clone()],
                            "equiv_pos2",
                            Vec::new(),
                            Vec::new(),
                        );
                        let r = b.resolve(vec![ax, ux], vec![(x, false)])?;
                        b.resolve(vec![r, uy], vec![(y, true)])
                    }
                    (false, false, true) => {
                        // equiv_pos1 = (cl ¬T x ¬y): units ¬x, y
                        let ax = b.step(
                            vec![nt, x.clone(), ny],
                            "equiv_pos1",
                            Vec::new(),
                            Vec::new(),
                        );
                        let r = b.resolve(vec![ax, ux], vec![(x, true)])?;
                        b.resolve(vec![r, uy], vec![(y, false)])
                    }
                    _ => Err(explanation("boolean equality evaluation mismatch")),
                }
            } else if want {
                // A true numeric equality is a ring identity
                crate::checker::poly_simp_equal(b.pool, &x, &y)?;
                let clause = vec![eq(b.pool, &x, &y)];
                Ok(b.step(clause, "poly_simp", Vec::new(), Vec::new()))
            } else {
                // A false numeric equality: one la_generic step concluding the disequality
                let nt = b.not(t);
                super::recipes::la_clause(b, vec![nt])
            }
        }
        Term::Op(
            Operator::LessThan | Operator::LessEq | Operator::GreaterThan | Operator::GreaterEq,
            _,
        ) => {
            let lit = if want { t.clone() } else { b.not(t) };
            super::recipes::la_clause(b, vec![lit])
        }
        _ => Err(explanation(format!("no evaluation recipe for '{t}'"))),
    }
}
