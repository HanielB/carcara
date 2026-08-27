//! Reductions of the linear-arithmetic category: everything reduces to `la_generic` (Farkas
//! certificates) and the `la_disequality` axiom, plus clausal packaging.

use super::Builder;
use crate::{
    ast::*,
    checker::{error::CheckerError, la_generic_partial},
    elaborator::error::ElaborationError,
};
use rug::Rational;

fn real(pool: &mut PrimitivePool, n: i32) -> Rc<Term> {
    pool.add(Term::new_real(n))
}

/// `la_totality` concludes `(or (<= t1 t2) (<= t2 t1))`: a two-literal `la_generic` step with
/// coefficients `[1, 1]` derives the clause, and the `or_intro` pattern packs it into the `or`
/// term.
pub fn la_totality(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let (le_1, le_2) = match_term_err!((or l r) = &step.clause[0])?;
    let (le_1, le_2) = (le_1.clone(), le_2.clone());

    let mut b = Builder::new(pool, step);
    let args = vec![real(b.pool, 1), real(b.pool, 1)];
    let la_generic = b.step(vec![le_1, le_2], "la_generic", Vec::new(), args);
    let node = b.or_intro(la_generic)?;
    Ok(b.relabel(step, node))
}

/// `la_tautology` is `la_generic` with coefficient `[1]` (unit form) or `[1, 1]` plus `or_intro`
/// packaging (binary form) — the specification itself states the equivalence.
pub fn la_tautology(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    if let Some((phi_1, phi_2)) = match_term!((or phi_1 phi_2) = &step.clause[0]) {
        let (phi_1, phi_2) = (phi_1.clone(), phi_2.clone());
        let mut b = Builder::new(pool, step);
        let args = vec![real(b.pool, 1), real(b.pool, 1)];
        let la_generic = b.step(vec![phi_1, phi_2], "la_generic", Vec::new(), args);
        let node = b.or_intro(la_generic)?;
        Ok(b.relabel(step, node))
    } else {
        let args = vec![real(pool, 1)];
        Ok(Rc::new(ProofNode::Step(StepNode {
            rule: "la_generic".to_owned(),
            args,
            ..step.clone()
        })))
    }
}

/// `la_rw_eq` concludes `(= (= t u) (and (<= t u) (<= u t)))`. The → direction is two Farkas
/// steps under a discharge subproof; the ← direction comes from the `la_disequality` axiom
/// unpacked by `or_pos` and crossed with `and_pos`; the `equiv_intro` pattern closes.
pub fn la_rw_eq(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let (eq, conj) = match_term_err!((= eq conj) = &step.clause[0])?;
    let (eq, conj) = (eq.clone(), conj.clone());
    let (le_1, le_2) = match_term_err!((and l r) = &conj)?;
    let (le_1, le_2) = (le_1.clone(), le_2.clone());

    let mut b = Builder::new(pool, step);

    // Direction →, under a discharge subproof
    b.open();
    let assumption = b.assume(eq.clone());
    let not_eq = b.not(&eq);
    let args = vec![real(b.pool, -1), real(b.pool, 1)];
    let g1 = b.step(
        vec![not_eq.clone(), le_1.clone()],
        "la_generic",
        Vec::new(),
        args,
    );
    let args = vec![real(b.pool, 1), real(b.pool, 1)];
    let g2 = b.step(vec![not_eq, le_2.clone()], "la_generic", Vec::new(), args);
    let r1 = b.resolve(vec![g1, assumption.clone()], vec![(eq.clone(), false)])?;
    let r2 = b.resolve(vec![g2, assumption.clone()], vec![(eq.clone(), false)])?;
    let and_step = b.and_intro(vec![r1, r2])?;
    let forward = b.close_subproof(vec![assumption], and_step);

    // Direction ←, from the `la_disequality` axiom
    let (not_le_1, not_le_2) = (b.not(&le_1), b.not(&le_2));
    let axiom_term = build_term!(
        b.pool,
        (or {eq.clone()} {not_le_1.clone()} {not_le_2.clone()})
    );
    let axiom = b.step(
        vec![axiom_term.clone()],
        "la_disequality",
        Vec::new(),
        Vec::new(),
    );
    let not_axiom_term = b.not(&axiom_term);
    let or_pos = b.step(
        vec![not_axiom_term, eq.clone(), not_le_1, not_le_2],
        "or_pos",
        Vec::new(),
        Vec::new(),
    );
    let unpacked = b.resolve(vec![or_pos, axiom], vec![(axiom_term, false)])?;

    let not_conj = b.not(&conj);
    let index = b.pool.add(Term::new_int(0));
    let p1 = b.step(
        vec![not_conj.clone(), le_1.clone()],
        "and_pos",
        Vec::new(),
        vec![index],
    );
    let index = b.pool.add(Term::new_int(1));
    let p2 = b.step(
        vec![not_conj, le_2.clone()],
        "and_pos",
        Vec::new(),
        vec![index],
    );
    let r3 = b.resolve(vec![unpacked, p1], vec![(le_1, false)])?;
    let backward = b.resolve(vec![r3, p2], vec![(le_2, false)])?;

    let node = b.equiv_intro(eq, conj, forward, backward)?;
    Ok(b.relabel(step, node))
}

/// Adds an `la_generic` step with the given literals and Farkas coefficients, after checking that
/// the certificate is indeed valid. Running the rule's own checking procedure here is what makes
/// the recipes below safe: the coefficients are computed from the shape of the step, so a shape
/// the recipe did not anticipate makes the reduction fail (and the original step be kept) instead
/// of producing a derivation that does not check.
pub(super) fn farkas(
    b: &mut Builder,
    literals: Vec<Rc<Term>>,
    coefficients: Vec<Rational>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let args: Vec<_> = coefficients
        .into_iter()
        .map(|c| b.pool.add(Term::new_real(c)))
        .collect();
    la_generic_partial(b.pool, &literals, &args, &mut None)?;
    Ok(b.step(literals, "la_generic", Vec::new(), args))
}

/// The premise of a `poly_simp_rel` step, for the recipe to fall back on.
struct Premise<'a> {
    node: &'a Rc<ProofNode>,
    term: Rc<Term>,
}

/// Derives a clause of the reduction by a Farkas certificate.
///
/// The rule does not require its premise to be a polynomial *identity* — only to hold — so the
/// clause is not in general a linear-arithmetic tautology on its own. But in every instance a
/// solver has reason to emit it is one: the premise is the conclusion of a polynomial
/// normalization, and then the proportion between the two differences is already visible to
/// `la_generic`'s own normalization. So the certificate is first tried without the premise, and
/// only if that fails is the premise added as a literal and resolved away.
///
/// The premise's coefficient in that larger certificate is `±1`: it is the only weight that makes
/// `c₁` and `c₂`, which the premise's two sides carry, cancel against the `|c₁|` and `|c₂|` of the
/// relation literals. Which of the two signs it is depends on the orientation of the relation
/// (whether the literals assert the difference to be positive or negative), so both are tried.
fn certificate(
    b: &mut Builder,
    premise: &Premise,
    literals: Vec<Rc<Term>>,
    coefficients: Vec<Rational>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    if let Ok(step) = farkas(b, literals.clone(), coefficients.clone()) {
        return Ok(step);
    }

    let not_premise = b.not(&premise.term);
    let literals: Vec<_> = std::iter::once(not_premise).chain(literals).collect();
    let mut result = None;
    for gamma in [1, -1] {
        let coefficients: Vec<_> = std::iter::once(Rational::from(gamma))
            .chain(coefficients.iter().cloned())
            .collect();
        if let Ok(step) = farkas(b, literals.clone(), coefficients) {
            result = Some(step);
            break;
        }
    }
    let Some(step) = result else {
        return Err(CheckerError::Explanation(
            "no Farkas certificate for a direction of the `poly_simp_rel` equivalence".to_owned(),
        )
        .into());
    };
    b.resolve(
        vec![step, premise.node.clone()],
        vec![(premise.term.clone(), false)],
    )
}

/// Derives `(cl (not (= t1 t2)) (= u1 u2))` — one direction of the equality case of
/// `poly_simp_rel`. A positive equality literal cannot appear in an `la_generic` clause, so the
/// consequent is introduced by the `la_disequality` axiom (unpacked by `or_pos`) and its two
/// inequalities are each discharged by a Farkas step against the antecedent.
///
/// `alpha` is the coefficient of the (equality) antecedent in the first of those Farkas steps, and
/// `beta` the coefficient of its inequality literal.
fn equality_direction(
    b: &mut Builder,
    premise: &Premise,
    antecedent: &Rc<Term>,
    consequent: &Rc<Term>,
    alpha: &Rational,
    beta: &Rational,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let (u1, u2) = match_term_err!((= u1 u2) = consequent)?;
    let (u1, u2) = (u1.clone(), u2.clone());
    let le_1 = build_term!(b.pool, (<= {u1.clone()} {u2.clone()}));
    let le_2 = build_term!(b.pool, (<= {u2.clone()} {u1.clone()}));
    let not_antecedent = b.not(antecedent);

    let g1 = certificate(
        b,
        premise,
        vec![not_antecedent.clone(), le_1.clone()],
        vec![alpha.clone(), beta.clone()],
    )?;
    // When the two sides of the consequent are the same term, the two bounds are the same literal,
    // and the axiom's clause collapses to two literals: only one of them is to be resolved away
    let g2 = (le_1 != le_2)
        .then(|| {
            certificate(
                b,
                premise,
                vec![not_antecedent, le_2.clone()],
                vec![-alpha.clone(), beta.clone()],
            )
        })
        .transpose()?;

    let (not_le_1, not_le_2) = (b.not(&le_1), b.not(&le_2));
    let axiom_term = build_term!(
        b.pool,
        (or {consequent.clone()} {not_le_1.clone()} {not_le_2.clone()})
    );
    let axiom = b.step(
        vec![axiom_term.clone()],
        "la_disequality",
        Vec::new(),
        Vec::new(),
    );
    let not_axiom_term = b.not(&axiom_term);
    let or_pos = b.step(
        vec![not_axiom_term, consequent.clone(), not_le_1, not_le_2],
        "or_pos",
        Vec::new(),
        Vec::new(),
    );
    let unpacked = b.resolve(vec![or_pos, axiom], vec![(axiom_term, false)])?;
    let r1 = b.resolve(vec![unpacked, g1], vec![(le_1, false)])?;
    match g2 {
        Some(g2) => b.resolve(vec![r1, g2], vec![(le_2, false)]),
        None => Ok(r1),
    }
}

/// `poly_simp_rel` concludes `(= (x1 ⋈ x2) (y1 ⋈ y2))` from a premise
/// `(= (* c1 (- x1 x2)) (* c2 (- y1 y2)))` (either difference possibly under a `to_real`), that
/// is, it transfers a relation across two differences that are proportional. Each direction of the
/// equivalence is then a Farkas certificate: the `x` literal takes the weight `|c1|` and the `y`
/// literal the weight `|c2|`, which makes the two linear combinations cancel, and the strict one
/// of the two contributes the strengthening that closes the contradiction. `la_generic` takes the
/// absolute value of the weight of an inequality literal, which is exactly why the rule requires
/// `c1` and `c2` to have the same sign unless the relation is `=`.
///
/// For a strict or non-strict inequality, one `la_generic` step per direction suffices. For `=`,
/// a positive equality cannot be an `la_generic` literal, so each direction goes through the
/// `la_disequality` axiom (the same template as `la_rw_eq`). The `equiv_intro` pattern glues the
/// two directions.
///
/// The bitvector case of the rule (`bvmul`/`bvsub` with odd coefficients) is not covered: it is
/// modular, not ordered, arithmetic, and the core has no bitvector reasoning to reduce it to.
pub fn poly_simp_rel(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    use Operator::*;

    let [premise] = step.premises.as_slice() else {
        return Err(CheckerError::Explanation(
            "`poly_simp_rel` step does not have exactly one premise".to_owned(),
        )
        .into());
    };
    let [premise_term] = premise.clause() else {
        return Err(CheckerError::Explanation(
            "premise of `poly_simp_rel` is not a unit clause".to_owned(),
        )
        .into());
    };
    if match_term!((= (bvmul _ _) (bvmul _ _)) = premise_term).is_some() {
        return Err(CheckerError::Explanation(
            "the bitvector case of `poly_simp_rel` has no core reduction".to_owned(),
        )
        .into());
    }
    let (c1, _, c2, _) = match_term_err!((= (* c1 xs) (* c2 ys)) = premise_term)?;
    let (c1, c2) = (c1.as_fraction_err()?, c2.as_fraction_err()?);
    let premise = Premise {
        node: premise,
        term: premise_term.clone(),
    };

    let [conclusion] = step.clause.as_slice() else {
        return Err(CheckerError::Explanation(
            "`poly_simp_rel` conclusion is not a unit clause".to_owned(),
        )
        .into());
    };
    let (left, right) = match_term_err!((= l r) = conclusion)?;
    let op = match (left.as_op_err()?, right.as_op_err()?) {
        ((op @ (LessThan | LessEq | Equals | GreaterEq | GreaterThan), [_, _]), (op2, [_, _]))
            if op2 == op =>
        {
            op
        }
        ((op1, _), (op2, _)) => {
            return Err(CheckerError::Explanation(format!(
                "`poly_simp_rel` conclusion relates '{}' and '{}'",
                op1, op2
            ))
            .into())
        }
    };
    let (left, right) = (left.clone(), right.clone());

    let mut b = Builder::new(pool, step);

    // The two directions of the equivalence. In both, the literal over the `x`s takes the
    // coefficient `c1` and the literal over the `y`s the coefficient `c2`: the `x` side of the
    // premise is `c1` times the difference, so weighting the two literals this way makes the two
    // linear combinations cancel exactly. `la_generic` takes the absolute value of the coefficient
    // of an inequality literal, which is why the rule requires `c1` and `c2` to have the same sign
    // unless the relation is `=`.
    let (forward, backward) = if op == Equals {
        // For an equality literal the sign of the coefficient is significant (`la_generic` only
        // takes the absolute value of the coefficients of inequality literals), and since the
        // equality is the antecedent, it is the sign of the *other* constant that orients it.
        let (abs_1, abs_2) = (c1.clone().abs(), c2.clone().abs());
        let forward_coeff = if c2.is_positive() {
            -c1.clone()
        } else {
            c1.clone()
        };
        let backward_coeff = if c1.is_positive() {
            -c2.clone()
        } else {
            c2.clone()
        };
        (
            equality_direction(&mut b, &premise, &left, &right, &forward_coeff, &abs_2)?,
            equality_direction(&mut b, &premise, &right, &left, &backward_coeff, &abs_1)?,
        )
    } else {
        let coefficients = vec![c1.abs(), c2.abs()];
        let (not_left, not_right) = (b.not(&left), b.not(&right));
        (
            certificate(
                &mut b,
                &premise,
                vec![not_left, right.clone()],
                coefficients.clone(),
            )?,
            certificate(
                &mut b,
                &premise,
                vec![left.clone(), not_right],
                coefficients,
            )?,
        )
    };

    let node = b.equiv_intro(left, right, forward, backward)?;
    Ok(b.relabel(step, node))
}

/// The zero constant of the given term's sort.
fn zero_like(pool: &mut PrimitivePool, term: &Rc<Term>) -> Result<Rc<Term>, ElaborationError> {
    match pool.sort(term).as_sort() {
        Some(Sort::Int) => Ok(pool.add(Term::new_int(0))),
        Some(Sort::Real) => Ok(pool.add(Term::new_real(0))),
        _ => Err(CheckerError::Explanation("expected an arithmetic sort".to_owned()).into()),
    }
}

/// Adds an `la_generic` step for the given literals, searching the sign patterns of the
/// coefficient vector (all magnitudes `1`) and validating each candidate certificate.
///
/// The search is what covers equality rows: their coefficients are used *signed* (`la_generic`
/// takes the absolute value only for inequality rows), so a bridge from an equality literal to a
/// comparison needs `-1` on one side, and which side depends on the orientation of the equality.
pub(super) fn unit_farkas(
    b: &mut Builder,
    literals: Vec<Rc<Term>>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let n = literals.len();
    let mut last_err = None;
    for pattern in 0u32..(1 << n) {
        let coefficients: Vec<Rational> = (0..n)
            .map(|i| {
                if pattern & (1 << i) == 0 {
                    Rational::from(1)
                } else {
                    Rational::from(-1)
                }
            })
            .collect();
        match farkas(b, literals.clone(), coefficients) {
            Ok(node) => return Ok(node),
            Err(e) => last_err = Some(e),
        }
    }
    Err(last_err.unwrap())
}

/// Reduces `la_mult_pos` and `la_mult_neg` to the `mult_pos` axiom.
///
/// The step concludes `(=> (and M (op l r)) (op' (* m l) (* m r)))`, where `M` is `(> m 0)`
/// (`la_mult_pos`, `op' = op`) or `(< m 0)` (`la_mult_neg`, `op'` the flipped comparison). The
/// scaling fact underneath is the positive cone's closure under multiplication, which is exactly
/// one `mult_pos` instance over the positive factor `m'` (`m` itself, or `(- m)` bridged from `M`
/// by `la_generic`) and the comparison's positive difference `d`:
///
/// - strict comparisons: `¬(op l r) ∨ (> d 0)` and `¬(> E 0) ∨ (op' ml mr)` are Farkas clauses
///   (`E` the difference of the scaled sides), and `(* m d) = (- (* m l) (* m r))` is one
///   `mult_distrib` instance, which `cong`/`equiv1` transport into the comparison — the residual
///   rearrangement between that and `E` is linear, so `la_generic` closes it;
/// - non-strict comparisons additionally case-split on `la_disequality`: the strict branch is the
///   above (weakened at the final bridge), and the equality branch is `eq_congruent` — scaling an
///   equality needs no sign reasoning at all;
/// - equalities: just the `eq_congruent` branch.
///
/// Every `la_generic` certificate is validated before emission and the ring identity is checked by
/// `poly_simp_equal`, so an unanticipated shape fails the reduction (keeping the step) rather than
/// emitting a bad derivation.
pub fn la_mult(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let is_pos = step.rule == "la_mult_pos";
    let [conclusion] = step.clause.as_slice() else {
        return Err(CheckerError::WrongLengthOfClause(1.into(), step.clause.len()).into());
    };
    let (antecedent, scaled) = match_term_err!((=> a s) = conclusion)?;
    let (m_comparison, original) = match_term_err!((and m o) = antecedent)?;
    let (antecedent, scaled) = (antecedent.clone(), scaled.clone());
    let (m_comparison, original) = (m_comparison.clone(), original.clone());
    let m = if is_pos {
        match_term_err!((> m zero) = &m_comparison)?.0
    } else {
        match_term_err!((< m zero) = &m_comparison)?.0
    }
    .clone();

    let (op, args) = original.as_op_err()?;
    let [l, r] = args else {
        return Err(CheckerError::Explanation("expected a binary comparison".to_owned()).into());
    };
    let (l, r) = (l.clone(), r.clone());
    let (sl, sr) = {
        let (_, sargs) = scaled.as_op_err()?;
        (sargs[0].clone(), sargs[1].clone())
    };

    let mut b = Builder::new(pool, step);

    // The scaling factor is the multiplier the step names, in both cases: `mult_pos` covers the
    // positive one and `mult_neg` the negative one. Scaling by `(- m)` instead would take the ring
    // identity below out of `mult_distrib`'s reach
    let m_pos = m.clone();

    // The equality branch: scaling an equality is congruence. Used alone for `=`, and as the
    // second branch of the non-strict case split
    let eq_branch = |b: &mut Builder| -> Result<(Rc<ProofNode>, Rc<Term>), ElaborationError> {
        let eq_lr = build_term!(b.pool, (= {l.clone()} {r.clone()}));
        let eq_mm = build_term!(b.pool, (= {m.clone()} {m.clone()}));
        let eq_scaled = build_term!(b.pool, (= {sl.clone()} {sr.clone()}));
        let (not_mm, not_lr) = (b.not(&eq_mm), b.not(&eq_lr));
        let refl = b.step(vec![eq_mm.clone()], "refl", Vec::new(), Vec::new());
        let cong = b.step(
            vec![not_mm, not_lr, eq_scaled.clone()],
            "eq_congruent",
            Vec::new(),
            Vec::new(),
        );
        let node = b.resolve(vec![cong, refl], vec![(eq_mm, false)])?;
        Ok((node, eq_lr))
    };

    // The strict branch: `mult_pos` over the comparison's positive difference. Returns a node
    // concluding `(cl ¬(> d 0) [¬M] target)`
    let strict_branch = |b: &mut Builder,
                         target: Rc<Term>|
     -> Result<(Rc<ProofNode>, Rc<Term>), ElaborationError> {
        // The positive difference of the original comparison: "big side first"
        let flipped = matches!(op, Operator::LessThan | Operator::LessEq);
        let (dx, dy) = if flipped {
            (r.clone(), l.clone())
        } else {
            (l.clone(), r.clone())
        };
        let d = build_term!(b.pool, (- {dx.clone()} {dy.clone()}));
        let product = build_term!(b.pool, (* {m_pos.clone()} {d.clone()}));
        // What distributivity turns the product into
        let mx = build_term!(b.pool, (* {m_pos.clone()} {dx.clone()}));
        let my = build_term!(b.pool, (* {m_pos.clone()} {dy.clone()}));
        let distributed = build_term!(b.pool, (- {mx} {my}));

        let zero_d = zero_like(b.pool, &d)?;
        let zero_p = zero_like(b.pool, &product)?;
        let d_pos = build_term!(b.pool, (> {d.clone()} {zero_d.clone()}));
        // A positive multiplier keeps the product positive (`mult_pos`), a negative one makes it
        // negative (`mult_neg`)
        let (p_lit, distributed_lit) = if is_pos {
            (
                build_term!(b.pool, (> {product.clone()} {zero_p.clone()})),
                build_term!(b.pool, (> {distributed.clone()} {zero_p.clone()})),
            )
        } else {
            (
                build_term!(b.pool, (< {product.clone()} {zero_p.clone()})),
                build_term!(b.pool, (< {distributed.clone()} {zero_p.clone()})),
            )
        };

        let (not_m, not_d_pos, not_p_lit) = (b.not(&m_comparison), b.not(&d_pos), b.not(&p_lit));
        let axiom = b.step(
            vec![not_m, not_d_pos, p_lit.clone()],
            if is_pos { "mult_pos" } else { "mult_neg" },
            Vec::new(),
            Vec::new(),
        );
        // `(* m (- x y)) = (- (* m x) (* m y))`, transported into the comparison
        let distrib = {
            let clause = vec![build_term!(b.pool, (= {product.clone()} {distributed.clone()}))];
            b.step(clause, "mult_distrib", Vec::new(), Vec::new())
        };
        let cong = {
            let clause = vec![build_term!(b.pool, (= {p_lit.clone()} {distributed_lit.clone()}))];
            b.step(clause, "cong", vec![distrib], Vec::new())
        };
        let equiv1 = b.step(
            vec![not_p_lit, distributed_lit.clone()],
            "equiv1",
            vec![cong],
            Vec::new(),
        );
        // The rearrangement between the distributed difference and the step's own scaled sides is
        // linear in the products, so one Farkas step closes it
        let final_bridge = {
            let nd = b.not(&distributed_lit);
            unit_farkas(b, vec![nd, target])?
        };
        let mut node = b.resolve(vec![axiom, equiv1], vec![(p_lit, true)])?;
        node = b.resolve(vec![node, final_bridge], vec![(distributed_lit, true)])?;
        Ok((node, d_pos))
    };

    // D: `(cl … ¬(op l r) scaled)`, with `¬M` present except in the pure-equality case
    let d_node = match op {
        Operator::Equals => {
            let (eq_node, eq_lr) = eq_branch(&mut b)?;
            // `scaled` is `(= sl sr)` itself, so the branch node is D without `¬M`
            let _ = eq_lr;
            eq_node
        }
        Operator::GreaterThan | Operator::LessThan => {
            let (node, d_pos) = strict_branch(&mut b, scaled.clone())?;
            // Bridge the original comparison to its positive difference
            let not_original = b.not(&original);
            let o_bridge = unit_farkas(&mut b, vec![not_original, d_pos.clone()])?;
            b.resolve(vec![node, o_bridge], vec![(d_pos, false)])?
        }
        Operator::GreaterEq | Operator::LessEq => {
            // Case split on `la_disequality`: strictly ordered, or equal
            let (strict_node, d_pos) = strict_branch(&mut b, scaled.clone())?;
            let (eq_node, eq_lr) = eq_branch(&mut b)?;
            let eq_scaled = build_term!(b.pool, (= {sl.clone()} {sr.clone()}));
            let eq_to_s = {
                let ne = b.not(&eq_scaled);
                unit_farkas(&mut b, vec![ne, scaled.clone()])?
            };
            let eq_side = b.resolve(vec![eq_node, eq_to_s], vec![(eq_scaled, true)])?;

            let (le_lr, le_rl) = (
                build_term!(b.pool, (<= {l.clone()} {r.clone()})),
                build_term!(b.pool, (<= {r.clone()} {l.clone()})),
            );
            let disj = build_term!(b.pool, (or {eq_lr.clone()} (not {le_lr.clone()}) (not {le_rl.clone()})));
            let anti = b.step(vec![disj.clone()], "la_disequality", Vec::new(), Vec::new());
            let (not_le_lr, not_le_rl) = (b.not(&le_lr), b.not(&le_rl));
            let split = b.step(
                vec![eq_lr.clone(), not_le_lr, not_le_rl],
                "or",
                vec![anti],
                Vec::new(),
            );
            // The non-strict comparison supplies one of the two `<=` bounds; the other's negation
            // is the strict ordering the strict branch consumes
            let flipped = op == Operator::LessEq;
            let (supplied, strict_neg) = if flipped {
                (le_lr.clone(), le_rl.clone())
            } else {
                (le_rl.clone(), le_lr.clone())
            };
            let not_original = b.not(&original);
            let o_bridge = unit_farkas(&mut b, vec![not_original, supplied.clone()])?;
            let d_bridge = {
                let d_pos_lit = d_pos.clone();
                unit_farkas(&mut b, vec![strict_neg.clone(), d_pos_lit])?
            };
            let mut node = b.resolve(vec![split, o_bridge], vec![(supplied, false)])?;
            node = b.resolve(vec![node, d_bridge], vec![(strict_neg, false)])?;
            node = b.resolve(vec![node, strict_node], vec![(d_pos, true)])?;
            b.resolve(vec![node, eq_side], vec![(eq_lr, true)])?
        }
        _ => {
            return Err(CheckerError::Explanation(format!(
                "unsupported comparison operator '{op}'"
            ))
            .into())
        }
    };

    // Package `(cl … ¬(and M O) … scaled)` into the implication
    let not_antecedent = b.not(&antecedent);
    let one = b.pool.add(Term::new_int(1));
    let zero = b.pool.add(Term::new_int(0));
    let ap_m = b.step(
        vec![not_antecedent.clone(), m_comparison.clone()],
        "and_pos",
        Vec::new(),
        vec![zero],
    );
    let ap_o = b.step(
        vec![not_antecedent, original.clone()],
        "and_pos",
        Vec::new(),
        vec![one],
    );
    let mut node = d_node;
    // The equality case's D carries no `¬M` literal
    if node.clause().contains(&b.not(&m_comparison)) {
        node = b.resolve(vec![node, ap_m], vec![(m_comparison.clone(), false)])?;
    }
    node = b.resolve(vec![node, ap_o], vec![(original, false)])?;

    let neg1 = b.step(
        vec![conclusion.clone(), antecedent.clone()],
        "implies_neg1",
        Vec::new(),
        Vec::new(),
    );
    let not_scaled = b.not(&scaled);
    let neg2 = b.step(
        vec![conclusion.clone(), not_scaled],
        "implies_neg2",
        Vec::new(),
        Vec::new(),
    );
    let mut node = b.resolve(vec![node, neg1], vec![(antecedent, false)])?;
    node = b.resolve(vec![node, neg2], vec![(scaled, true)])?;
    Ok(b.relabel(step, node))
}
