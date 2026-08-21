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
    } else {
        crate::checker::poly_simp_equal(b.pool, term, value)?;
        unreachable!()
    }
}

/// Derives the literal `(cl t)` (for `want = true`) or `(cl ¬t)` (for `want = false`) for a
/// ground Boolean term, by structural recursion.
fn literal(b: &mut Builder, t: &Rc<Term>, want: bool) -> Res {
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
                        let r = b.resolve(vec![ax, ux], vec![(x, false)])?;
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
                        let r = b.resolve(vec![ax, ux], vec![(x, true)])?;
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
