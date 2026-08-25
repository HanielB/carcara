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
