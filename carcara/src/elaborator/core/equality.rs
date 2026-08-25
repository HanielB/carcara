//! Reductions of the equality category: the clausal `eq_*` rules are repackagings of the Birkhoff
//! rules (`refl`, `symm`, `trans`, `cong`) as premise-free clauses, so they reduce by deriving the
//! final literal under a discharge subproof that assumes the negated ones.

use super::Builder;
use crate::{ast::*, checker::error::CheckerError, elaborator::error::ElaborationError};

/// `eq_reflexive` is `refl` with an empty context.
///
/// The rename is only available where the context substitution does not move the conclusion.
/// `eq_reflexive` reads no context and states plain reflexivity, but `refl` — `strict_refl` at
/// elaborated granularity — checks `context.apply(left) == right`, so inside an anchor that assigns
/// a free variable of the term the renamed step would state something else and be rejected. Where
/// that happens the step is kept as it is, like every other reduction the pass cannot make.
pub fn eq_reflexive(
    pool: &mut PrimitivePool,
    context: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    if !super::context_is_safe(pool, context, &step.clause) {
        return Err(CheckerError::Explanation(
            "an anchor in scope substitutes into the conclusion, so `refl` would not mean \
             reflexivity here"
                .to_owned(),
        )
        .into());
    }
    Ok(Rc::new(ProofNode::Step(StepNode {
        rule: "refl".to_owned(),
        ..step.clone()
    })))
}

/// Finds the order in which the given premise equalities chain from `conclusion.0` to
/// `conclusion.1`, returning the indices of the used premises in chain order, paired with whether
/// each needs to be flipped.
fn find_chain(
    conclusion: (&Rc<Term>, &Rc<Term>),
    equalities: &[(&Rc<Term>, &Rc<Term>)],
) -> Result<Vec<(usize, bool)>, CheckerError> {
    let mut used = vec![false; equalities.len()];
    let mut current = conclusion.0;
    let mut chain = Vec::new();
    while current != conclusion.1 {
        let (i, flip, next) = equalities
            .iter()
            .enumerate()
            .find_map(|(i, (t, u))| {
                if used[i] {
                    None
                } else if *t == current {
                    Some((i, false, *u))
                } else if *u == current {
                    Some((i, true, *t))
                } else {
                    None
                }
            })
            .ok_or_else(|| {
                CheckerError::BrokenTransitivityChain(current.clone(), conclusion.1.clone())
            })?;
        used[i] = true;
        chain.push((i, flip));
        current = next;
    }
    Ok(chain)
}

/// `eq_transitive` becomes a discharge subproof: each negated equality is assumed, the chain is
/// derived by `trans` (with `symm` for flipped links), and the closing `subproof` step discharges
/// the assumptions. Unneeded literals become discharged-but-unused assumptions.
pub fn eq_transitive(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let n = step.clause.len();
    let conclusion = match_term_err!((= t u) = step.clause.last().unwrap())?;
    let equalities: Vec<_> = step.clause[..n - 1]
        .iter()
        .map(|term| match_term_err!((not (= t u)) = term))
        .collect::<Result<_, _>>()?;

    let chain = find_chain(conclusion, &equalities)?;

    let mut b = Builder::new(pool, step);
    b.open();
    let assumptions: Vec<_> = equalities
        .iter()
        .map(|(t, u)| {
            let term = build_term!(b.pool, (= {(*t).clone()} {(*u).clone()}));
            b.assume(term)
        })
        .collect();

    let links: Vec<_> = chain
        .iter()
        .map(|&(i, flip)| {
            if flip {
                b.symm(&assumptions[i])
            } else {
                assumptions[i].clone()
            }
        })
        .collect();

    let last = if links.len() == 1 {
        // Degenerate chains have a single link, which already concludes the conclusion, possibly
        // after the `symm` that flipped it. If the link is the assumption itself, though, the
        // subproof still needs a step to close on, since the closing `subproof` step reads its
        // conclusion off the command that immediately precedes it, which is the *last* assumption.
        // A one-premise `trans` restates the equality
        let link = links.into_iter().next().unwrap();
        if link.is_step() {
            link
        } else {
            let conclusion = step.clause[n - 1].clone();
            b.step(vec![conclusion], "trans", vec![link], Vec::new())
        }
    } else {
        let conclusion = step.clause[n - 1].clone();
        b.step(vec![conclusion], "trans", links, Vec::new())
    };

    Ok(b.close_finish(
        step,
        Vec::new(),
        "subproof",
        Vec::new(),
        Vec::new(),
        assumptions,
        last,
    ))
}

/// Matches the argument pairs of a congruence against the premise equalities, mirroring the
/// `cong` checker: each premise is consumed in order by the first argument pair it can justify,
/// and identical pairs may skip a premise. Returns, for each argument pair, the index of the
/// premise justifying it (with a flip marker), or `None` if the pair is directly equal.
fn match_cong_premises(
    premises: &[(&Rc<Term>, &Rc<Term>)],
    f_args: &[Rc<Term>],
    g_args: &[Rc<Term>],
) -> Result<Vec<Option<(usize, bool)>>, CheckerError> {
    let mut next = 0;
    let mut result = Vec::new();
    for (f_arg, g_arg) in f_args.iter().zip(g_args) {
        let expected = (f_arg, g_arg);
        if next < premises.len() && premises[next] == expected {
            result.push(Some((next, false)));
            next += 1;
        } else if next < premises.len() && (premises[next].1, premises[next].0) == expected {
            result.push(Some((next, true)));
            next += 1;
        } else if f_arg == g_arg {
            result.push(None);
        } else {
            return Err(CheckerError::Explanation(format!(
                "no premise justifies congruence of {} and {}",
                f_arg, g_arg
            )));
        }
    }
    Ok(result)
}

fn assume_equalities(b: &mut Builder, equalities: &[(&Rc<Term>, &Rc<Term>)]) -> Vec<Rc<ProofNode>> {
    equalities
        .iter()
        .map(|(t, u)| {
            let term = build_term!(b.pool, (= {(*t).clone()} {(*u).clone()}));
            b.assume(term)
        })
        .collect()
}

fn cong_from_assumptions(
    b: &mut Builder,
    assumptions: &[Rc<ProofNode>],
    matching: &[Option<(usize, bool)>],
    conclusion: Rc<Term>,
) -> Rc<ProofNode> {
    let premises: Vec<_> = matching
        .iter()
        .filter_map(|m| {
            m.map(|(i, flip)| {
                if flip {
                    b.symm(&assumptions[i])
                } else {
                    assumptions[i].clone()
                }
            })
        })
        .collect();
    b.step(vec![conclusion], "cong", premises, Vec::new())
}

/// `eq_congruent` becomes a discharge subproof assuming the argument equalities and closing with
/// one `cong` step (plus `symm` steps for flipped equalities).
pub fn eq_congruent(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let n = step.clause.len();
    let (f, g) = match_term_err!((= f g) = &step.clause[n - 1])?;
    let (f_args, g_args) = (term_args(f)?.to_vec(), term_args(g)?.to_vec());
    let equalities: Vec<_> = step.clause[..n - 1]
        .iter()
        .map(|term| match_term_err!((not (= t u)) = term))
        .collect::<Result<_, _>>()?;
    let matching = match_cong_premises(&equalities, &f_args, &g_args)?;

    let mut b = Builder::new(pool, step);
    b.open();
    let assumptions = assume_equalities(&mut b, &equalities);
    let conclusion = step.clause[n - 1].clone();
    let cong_step = cong_from_assumptions(&mut b, &assumptions, &matching, conclusion);

    Ok(b.close_finish(
        step,
        Vec::new(),
        "subproof",
        Vec::new(),
        Vec::new(),
        assumptions,
        cong_step,
    ))
}

/// `eq_congruent_pred` additionally assumes the negated application and crosses the congruence
/// with it: `cong` derives the equivalence of the two applications, and the `eq_mp` pattern
/// (`equiv_pos2` + `resolution`) concludes the positive one.
///
/// The negation may sit on either of the last two literals (veriT emits both orientations). When
/// it sits on the *last* literal, the assumed application is the last one and the derived one the
/// second-to-last — which flips the subproof's conclusion order relative to the original clause,
/// so a final `reordering` step (eliminated later by the reordering pass) restores it.
pub fn eq_congruent_pred(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let n = step.clause.len();
    // `assumed` is the negated application (which we assume positively), `derived` the positive
    // one (which the subproof derives)
    let (assumed, derived, flipped_order) = match step.clause[n - 2].remove_negation() {
        Some(inner) => (inner.clone(), step.clause[n - 1].clone(), false),
        None => (
            step.clause[n - 1].remove_negation_err()?.clone(),
            step.clause[n - 2].clone(),
            true,
        ),
    };
    let (t_args, u_args) = if flipped_order {
        // The premise equalities are stated for the argument pairs of (second-to-last, last), so
        // here they run from the *derived* application to the *assumed* one
        (term_args(&derived)?.to_vec(), term_args(&assumed)?.to_vec())
    } else {
        (term_args(&assumed)?.to_vec(), term_args(&derived)?.to_vec())
    };
    let equalities: Vec<_> = step.clause[..n - 2]
        .iter()
        .map(|term| match_term_err!((not (= t u)) = term))
        .collect::<Result<_, _>>()?;
    let mut matching = match_cong_premises(&equalities, &t_args, &u_args)?;
    if flipped_order {
        // The `cong` step goes from the assumed application to the derived one, so every premise
        // orientation flips
        for m in matching.iter_mut().flatten() {
            m.1 = !m.1;
        }
    }

    let mut b = Builder::new(pool, step);
    b.open();
    let mut assumptions = assume_equalities(&mut b, &equalities);
    let assumed_assumption = b.assume(assumed.clone());
    assumptions.push(assumed_assumption.clone());

    let equivalence = build_term!(b.pool, (= {assumed.clone()} {derived.clone()}));
    let cong_step = cong_from_assumptions(&mut b, &assumptions, &matching, equivalence.clone());

    let (not_equivalence, not_assumed) = (b.not(&equivalence), b.not(&assumed));
    let equiv_pos2 = b.step(
        vec![not_equivalence, not_assumed, derived.clone()],
        "equiv_pos2",
        Vec::new(),
        Vec::new(),
    );
    let last = b.resolve(
        vec![equiv_pos2, cong_step, assumed_assumption],
        vec![(equivalence, false), (assumed, false)],
    )?;

    if flipped_order {
        let subproof = b.close_subproof(assumptions, last);
        Ok(b.finish(step, "reordering", vec![subproof], Vec::new()))
    } else {
        Ok(b.close_finish(
            step,
            Vec::new(),
            "subproof",
            Vec::new(),
            Vec::new(),
            assumptions,
            last,
        ))
    }
}

/// `eq_symmetric` concludes an *equivalence*, so both directions are derived, each by a `symm`
/// step under a discharge subproof, and the `equiv_intro` pattern closes.
pub fn eq_symmetric(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let (lhs, rhs) = match_term_err!((= l r) = &step.clause[0])?;
    let (lhs, rhs) = (lhs.clone(), rhs.clone());

    let mut b = Builder::new(pool, step);

    let direction = |b: &mut Builder, from: &Rc<Term>| {
        b.open();
        let assumption = b.assume(from.clone());
        let symm_step = b.symm(&assumption);
        b.close_subproof(vec![assumption], symm_step)
    };
    let forward = direction(&mut b, &lhs);
    let backward = direction(&mut b, &rhs);

    let node = b.equiv_intro(lhs, rhs, forward, backward)?;
    Ok(b.relabel(step, node))
}

/// `not_symm` flips its negated premise: a `symm` step under a discharge subproof derives the
/// implication, and a resolution with the premise concludes.
pub fn not_symm(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let premise = step.premises[0].clone();
    let flipped = step.clause[0].remove_negation_err()?.clone();

    let mut b = Builder::new(pool, step);
    b.open();
    let assumption = b.assume(flipped.clone());
    let symm_step = b.symm(&assumption);
    let subproof = b.close_subproof(vec![assumption], symm_step);

    let original = premise.clause()[0].remove_negation_err()?.clone();
    let node = b.resolve(vec![subproof, premise], vec![(original, true)])?;
    Ok(b.relabel(step, node))
}

fn term_args(term: &Rc<Term>) -> Result<&[Rc<Term>], CheckerError> {
    match term.as_ref() {
        Term::App(_, args) | Term::Op(_, args) | Term::ParamOp { args, .. } => Ok(args),
        _ => Err(CheckerError::Explanation(format!(
            "expected application term, got {}",
            term
        ))),
    }
}

/// The `eq_congruent_pred` reduction for the equality-*keeping* pipeline: onto `eq_congruent`.
///
/// The predicate rule is the function rule read through an equivalence: where `eq_congruent`
/// concludes `(= p(t̄) p(ū))`, the predicate variant splits that equality into the two-literal
/// tail `¬p(t̄), p(ū)` (or `p(t̄), ¬p(ū)`). The split is exactly one `equiv_pos2` (resp.
/// `equiv_pos1`) axiom away, so even the vocabulary that keeps the clausal `eq_*` rules has no
/// need for the predicate variant: three steps, and the argument-equality literals carry over
/// verbatim, since both rules validate them with the same per-argument matching.
pub fn eq_congruent_pred_to_eq_congruent(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let n = step.clause.len();
    if n < 3 {
        return Err(CheckerError::WrongLengthOfClause((3..).into(), n).into());
    }
    let eqs = step.clause[..n - 2].to_vec();
    let (p, q, first_negated) = match step.clause[n - 2].remove_negation() {
        Some(inner) => (inner.clone(), step.clause[n - 1].clone(), true),
        None => (
            step.clause[n - 2].clone(),
            step.clause[n - 1].remove_negation_err()?.clone(),
            false,
        ),
    };

    let mut b = Builder::new(pool, step);
    let equality = build_term!(b.pool, (= {p.clone()} {q.clone()}));
    let mut cong_clause = eqs;
    cong_clause.push(equality.clone());
    let cong = b.step(cong_clause, "eq_congruent", Vec::new(), Vec::new());

    let not_equality = b.not(&equality);
    let axiom = if first_negated {
        let not_p = b.not(&p);
        b.step(
            vec![not_equality, not_p, q.clone()],
            "equiv_pos2",
            Vec::new(),
            Vec::new(),
        )
    } else {
        let not_q = b.not(&q);
        b.step(
            vec![not_equality, p.clone(), not_q],
            "equiv_pos1",
            Vec::new(),
            Vec::new(),
        )
    };
    let node = b.resolve(vec![cong, axiom], vec![(equality, true)])?;
    Ok(b.relabel(step, node))
}
