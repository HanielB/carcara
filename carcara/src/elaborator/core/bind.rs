//! The `bind` reduction: binder congruence from `sko_forall` and `forall_inst`.
//!
//! `bind` closes a subproof that derives `φ ≈ ψ` under an anchor renaming the quantifier's
//! variables, and concludes `(∀x̄.φ) ≈ (∀ȳ.ψ)`. The core derives the same equivalence without it,
//! and the cost depends entirely on what the body actually did.
//!
//! **When the two sides are α-variants** — the case `bind` exists for, where the body is a `refl`
//! chain under the renaming context — the reduction is four steps and does not look at the body
//! at all. Skolemize *both* sides at the *same* witnesses: `sko_forall` compares an anchor's
//! witnesses with its own only up to α-equivalence, so the witnesses ε̄ of `(∀x̄.φ)` serve for
//! `(∀ȳ.ψ)` as well, and both sides Skolemize to the very same term.
//!
//! ```text
//! (cl (= (∀x̄.φ) φ[ε̄]))       refl under the anchor x̄ ↦ ε̄, closed by sko_forall
//! (cl (= (∀ȳ.ψ) φ[ε̄]))       refl under the anchor ȳ ↦ ε̄, closed by sko_forall
//! (cl (= φ[ε̄] (∀ȳ.ψ)))       symm
//! (cl (= (∀x̄.φ) (∀ȳ.ψ)))     trans
//! ```
//!
//! **When the body rewrites** — the sides are not α-variants, so their Skolemizations differ and
//! the body's reasoning has to be transported — the reduction falls back on the route the
//! classification calls *admissibility of the generalized `bind`*: Skolemize the target,
//! instantiate the premise at the same witnesses, and **replay the subproof's derivation with the
//! witnesses substituted for the anchor's variables** — every core rule is schematic, so its
//! instances stay valid under a uniform substitution of closed terms.
//!
//! For one direction, with `ε̄` the sequential ε-witnesses of `(∀ȳ.ψ)`:
//!
//! ```text
//! (cl (∀ȳ.ψ) ¬ψ[ε̄])          the ∀-ε-clause: refl under the witness anchor, sko_forall, equiv2
//! (cl ¬(∀x̄.φ) φ[ε̄])          forall_inst at the witnesses, unpacked by or_pos
//! (cl (= φ[ε̄] ψ[ε̄]))         the replayed body
//! (cl ¬(∀x̄.φ) (∀ȳ.ψ))        equiv_pos2 crossing the two, then resolution
//! ```
//!
//! and symmetrically for the other, with the witnesses of `(∀x̄.φ)`; `equiv_intro` closes. The
//! price is a *copy of the body per direction* — which is why the rule is classified
//! **expensive**: the reduction is complete for the shapes below and buys no checking power, so
//! only the `core-expensive` regime applies it.
//!
//! The generalized (∀-closure) form is cheaper: there is one direction and one replay, since the
//! closure concludes a clause rather than an equivalence.
//!
//! Not covered (the step is kept): a `bind` under an enclosing anchor, whose cumulative
//! substitution the ∀-ε-clause would have to account for; bodies containing a `let` term, which
//! substitution renames independently of its surroundings; binders other than `∀` — `∃` would route through
//! `qnt_duality`, and `choice`/`lambda` congruence has no core route at all (it is the
//! classification's one binder-congruence residue) — anchors whose assignments are not renamings
//! into the declared variables, and nested anchors that bind one of the substituted variables,
//! which would shadow it. Other nested anchors are replayed with the rest: their assignments are
//! substituted and their bodies replayed one level deeper.

use super::Builder;
use crate::{ast::*, checker::error::CheckerError, elaborator::error::ElaborationError};
use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};

type Res = Result<Rc<ProofNode>, ElaborationError>;

fn explanation(msg: impl Into<String>) -> ElaborationError {
    CheckerError::Explanation(msg.into()).into()
}

fn substitute(
    pool: &mut PrimitivePool,
    term: &Rc<Term>,
    map: IndexMap<Rc<Term>, Rc<Term>>,
) -> Rc<Term> {
    if map.is_empty() {
        return term.clone();
    }
    match Substitution::new(pool, map) {
        Ok(mut s) => s.apply(pool, term),
        Err(_) => term.clone(),
    }
}

/// The sequential ε-witnesses of `(∀ v̄. χ)`, in the shape `sko_forall` checks: the `i`-th is
/// `(choice ((vᵢ Sᵢ)) (not (∀ v_{i+1}…vₙ. χ)))`, with the earlier witnesses already substituted.
/// Returns the witnesses and the successive bodies `χ[v₁↦ε₁, …, vᵢ↦εᵢ]`.
fn witnesses(
    pool: &mut PrimitivePool,
    bindings: &[SortedVar],
    body: &Rc<Term>,
) -> (Vec<Rc<Term>>, Vec<Rc<Term>>) {
    let n = bindings.len();
    let mut stages = vec![body.clone()];
    let mut result = Vec::new();
    for i in 0..n {
        let current = stages[i].clone();
        let mut inner = current.clone();
        if i < n - 1 {
            inner = pool.add(Term::Binder(
                Binder::Forall,
                BindingList(bindings[i + 1..].to_vec()),
                inner,
            ));
        }
        inner = build_term!(pool, (not { inner }));
        let witness = pool.add(Term::Binder(
            Binder::Choice,
            BindingList(vec![bindings[i].clone()]),
            inner,
        ));
        let var = pool.add(Term::from(bindings[i].clone()));
        let next = substitute(pool, &current, IndexMap::from([(var, witness.clone())]));
        stages.push(next);
        result.push(witness);
    }
    (result, stages)
}

/// Emits the ∀-ε-clause `(cl (∀ v̄. χ) ¬χ[ε̄])`: a `refl` under an anchor assigning each variable
/// its witness, closed by `sko_forall`, and unpacked by `equiv2`.
fn epsilon_clause(
    b: &mut Builder,
    quant: &Rc<Term>,
    bindings: &[SortedVar],
    body: &Rc<Term>,
    witnesses: &[Rc<Term>],
    skolemized: &Rc<Term>,
) -> Res {
    let anchor_args: Vec<AnchorArg> = bindings
        .iter()
        .zip(witnesses)
        .map(|(var, w)| AnchorArg::Assign(var.clone(), w.clone()))
        .collect();

    b.open();
    let equality = build_term!(b.pool, (= {body.clone()} {skolemized.clone()}));
    let refl = b.step(vec![equality], "refl", Vec::new(), Vec::new());
    let closing = build_term!(b.pool, (= {quant.clone()} {skolemized.clone()}));
    let sko = b.close_with(
        anchor_args,
        "sko_forall",
        vec![closing.clone()],
        Vec::new(),
        refl,
    );

    let not_skolemized = b.not(skolemized);
    Ok(b.step(
        vec![quant.clone(), not_skolemized],
        "equiv2",
        vec![sko],
        Vec::new(),
    ))
}

/// Emits `(cl ¬(∀ v̄. χ) χ[t̄])`: one `forall_inst` step (whose conclusion is a unit clause holding
/// a disjunction) unpacked by `or_pos`.
fn instantiate(b: &mut Builder, quant: &Rc<Term>, args: Vec<Rc<Term>>, instance: &Rc<Term>) -> Res {
    let not_quant = b.not(quant);
    let or_term = b.pool.add(Term::Op(
        Operator::Or,
        vec![not_quant.clone(), instance.clone()],
    ));
    let inst = b.step(vec![or_term.clone()], "forall_inst", Vec::new(), args);
    let not_or = b.not(&or_term);
    let or_pos = b.step(
        vec![not_or, not_quant, instance.clone()],
        "or_pos",
        Vec::new(),
        Vec::new(),
    );
    b.resolve(vec![or_pos, inst], vec![(or_term, false)])
}

/// Replays a derivation with a substitution applied to every step it contains.
///
/// Every core rule is schematic, so a derivation stays valid when closed terms are substituted
/// uniformly for its free variables — which is what lets the body of a `bind` subproof be reused
/// at the ε-witnesses. Premises from outside the subproof are left alone: the anchor's variables
/// cannot occur in them. Nested anchors are refused, since their own substitutions would have to
/// be composed with this one.
type ReplayCache = HashMap<(Rc<ProofNode>, usize), Rc<ProofNode>>;

/// Whether the term rebinds one of the given names anywhere inside it — or contains a `let`.
///
/// Substituting into such a term would make the substitution rename the binder to avoid capture —
/// correct, but it desynchronizes the replay: the same literal reached through a term that rebinds
/// and through one that does not would come out with different variable names, and the resolutions
/// between them would no longer find their pivots. The reduction refuses those bodies instead.
fn rebinds(term: &Rc<Term>, names: &[&str], seen: &mut HashSet<Rc<Term>>) -> bool {
    if !seen.insert(term.clone()) {
        return false;
    }
    match term.as_ref() {
        Term::Binder(_, bindings, inner) => {
            bindings.0.iter().any(|(n, _)| names.contains(&n.as_str()))
                || rebinds(inner, names, seen)
        }
        // Any `let` at all: substituting into one renames its bound variables independently of
        // the surrounding term, which desynchronizes the replay the same way a rebinding does
        Term::Let(..) => true,
        Term::Op(_, args) | Term::ParamOp { args, .. } => {
            args.iter().any(|a| rebinds(a, names, seen))
        }
        Term::App(f, args) => {
            rebinds(f, names, seen) || args.iter().any(|a| rebinds(a, names, seen))
        }
        _ => false,
    }
}

fn any_rebinds(terms: &[Rc<Term>], names: &[&str]) -> bool {
    let mut seen = HashSet::new();
    terms.iter().any(|t| rebinds(t, names, &mut seen))
}

fn replay(
    b: &mut Builder,
    node: &Rc<ProofNode>,
    map: &IndexMap<Rc<Term>, Rc<Term>>,
    inner_depth: usize,
    cache: &mut ReplayCache,
) -> Res {
    // The cache is per scope (see the nested-subproof arm), so the depth in the key only guards
    // against a node being reused across the boundary of the scope that built it
    let key = (node.clone(), b.depth());
    if let Some(done) = cache.get(&key) {
        return Ok(done.clone());
    }
    if node.depth() < inner_depth {
        // A premise from outside the subproof, which the substitution cannot touch
        return Ok(node.clone());
    }
    let result = match node.as_ref() {
        ProofNode::Assume { term, .. } => {
            let term = substitute(b.pool, term, map.clone());
            b.assume(term)
        }
        ProofNode::Subproof(sub) => {
            let Some(last) = sub.last_step.as_step() else {
                return Err(explanation("nested subproof does not end in a step"));
            };
            if !last.premises.is_empty() {
                return Err(explanation("nested closing step with premises"));
            }
            // `sko_forall` closings replay soundly because the substitution is of closed terms
            // for variables the scope does not bind (the rebinds guard ensures it), so it
            // commutes with the witness recomputation the checker performs. `let`/`onepoint`
            // closings have side conditions the replay does not track
            if last.rule != "bind" && last.rule != "subproof" && last.rule != "sko_forall" {
                return Err(explanation(format!(
                    "nested scope closed by `{}` cannot be replayed",
                    last.rule
                )));
            }
            // A nested anchor that binds a variable this substitution touches would shadow it
            let shadows = sub.args.iter().any(|arg| {
                let var = match arg {
                    AnchorArg::Variable(v) | AnchorArg::Assign(v, _) => v,
                };
                map.keys().any(|k| k.as_var() == Some(var.0.as_str()))
            });
            if shadows {
                return Err(explanation("nested anchor shadows a substituted variable"));
            }
            let args: Vec<AnchorArg> = sub
                .args
                .iter()
                .map(|arg| match arg {
                    AnchorArg::Variable(v) => AnchorArg::Variable(v.clone()),
                    AnchorArg::Assign(v, value) => {
                        AnchorArg::Assign(v.clone(), substitute(b.pool, value, map.clone()))
                    }
                })
                .collect();
            let Some(previous) = &last.previous_step else {
                return Err(explanation("nested closing step has no previous step"));
            };

            // A nested scope gets its own cache: a replayed node lives inside the scope that
            // built it, so a sibling scope needs a copy of its own
            b.open();
            let mut inner_cache = ReplayCache::new();
            let inner = replay(b, previous, map, inner_depth, &mut inner_cache)?;
            let mut discharge = Vec::new();
            for a in &last.discharge {
                discharge.push(replay(b, a, map, inner_depth, &mut inner_cache)?);
            }
            let names: Vec<&str> = map.keys().filter_map(|k| k.as_var()).collect();
            if any_rebinds(&last.clause, &names) {
                return Err(explanation(
                    "the body rebinds a variable the witnesses replace",
                ));
            }
            let clause: Vec<_> = last
                .clause
                .iter()
                .map(|t| substitute(b.pool, t, map.clone()))
                .collect();
            b.close_with(args, &last.rule, clause, discharge, inner)
        }
        ProofNode::Step(s) => {
            let names: Vec<&str> = map.keys().filter_map(|k| k.as_var()).collect();
            if any_rebinds(&s.clause, &names) || any_rebinds(&s.args, &names) {
                return Err(explanation(
                    "the body rebinds a variable the witnesses replace",
                ));
            }
            let mut premises = Vec::new();
            for p in &s.premises {
                premises.push(replay(b, p, map, inner_depth, cache)?);
            }
            let clause: Vec<_> = s
                .clause
                .iter()
                .map(|t| substitute(b.pool, t, map.clone()))
                .collect();
            let args: Vec<_> = s
                .args
                .iter()
                .map(|t| substitute(b.pool, t, map.clone()))
                .collect();
            b.step(clause, &s.rule, premises, args)
        }
    };
    cache.insert(key, result.clone());
    Ok(result)
}

/// The anchor's renaming, as the pair of binder lists it renames between.
fn anchor_renaming(args: &[AnchorArg]) -> Option<(Vec<SortedVar>, Vec<SortedVar>)> {
    let mut declared = Vec::new();
    let mut assigned = Vec::new();
    for arg in args {
        match arg {
            AnchorArg::Variable(var) => declared.push(var.clone()),
            AnchorArg::Assign(var, value) => {
                let name = value.as_var()?;
                let target = declared.iter().find(|(n, _)| n == name)?;
                assigned.push((var.clone(), target.clone()));
            }
        }
    }
    if assigned.is_empty() {
        return None;
    }
    Some((
        assigned.iter().map(|(x, _)| x.clone()).collect(),
        assigned.iter().map(|(_, y)| y.clone()).collect(),
    ))
}

/// Reduces a whole `bind` subproof. `subproof` is the [`ProofNode::Subproof`] whose last step is
/// the `bind`; the result replaces it, at the same depth.
pub fn bind(pool: &mut PrimitivePool, context: &mut ContextStack, subproof: &Rc<ProofNode>) -> Res {
    let ProofNode::Subproof(sub) = subproof.as_ref() else {
        return Err(explanation("not a subproof"));
    };

    let Some(last) = sub.last_step.as_step() else {
        return Err(explanation("subproof does not end in a step"));
    };
    let Some(previous) = &last.previous_step else {
        return Err(explanation("`bind` has no previous step"));
    };
    let inner_depth = sub.last_step.depth();
    let mut b = Builder::new(pool, last);
    // The reduction lives at the depth of the subproof, not of its body
    b.leave();

    // The vanilla form: a unit clause holding an equivalence between two quantified terms.
    // `∃` congruence routes through the duality: `(∃x̄.φ) ≈ ¬(∀x̄.¬φ)` on both sides, the `∀`
    // machinery on the negated bodies, and `cong`/`trans` to join the three equivalences
    if let [conclusion] = last.clause.as_slice() {
        if let Some((lhs, rhs)) = match_term!((= l r) = conclusion) {
            let (lhs, rhs) = (lhs.clone(), rhs.clone());
            if exists_parts(&lhs).is_some() {
                return exists_congruence(&mut b, context, sub, previous, inner_depth, &lhs, &rhs);
            }
            return congruence(&mut b, context, sub, previous, inner_depth, &lhs, &rhs);
        }
    }

    // The generalized form: a clause with one literal closed as `(∀Ȳ. l)`, the others passing
    // through
    if !context.is_empty() {
        return Err(explanation(
            "the ∀-closure reduction is only built outside an enclosing anchor",
        ));
    }
    closure(&mut b, sub, previous, inner_depth, &last.clause)
}

fn quant_parts(term: &Rc<Term>) -> Option<(Vec<SortedVar>, Rc<Term>)> {
    match term.as_ref() {
        Term::Binder(Binder::Forall, bindings, body) => Some((bindings.0.clone(), body.clone())),
        _ => None,
    }
}

fn exists_parts(term: &Rc<Term>) -> Option<(Vec<SortedVar>, Rc<Term>)> {
    match term.as_ref() {
        Term::Binder(Binder::Exists, bindings, body) => Some((bindings.0.clone(), body.clone())),
        _ => None,
    }
}

/// `∃` congruence through the duality: from the body's `φ ≈ ψ`, derive
/// `(∃x̄.φ) ≈ ¬(∀x̄.¬φ) ≈ ¬(∀ȳ.¬ψ) ≈ (∃ȳ.ψ)`. The middle link is the `∀` machinery applied to the
/// negated bodies — its α-renaming fast path applies exactly when the original bodies are
/// α-variants — lifted over the negation by `cong`; the outer links are two `qnt_duality` axioms.
#[allow(clippy::too_many_arguments)]
fn exists_congruence(
    b: &mut Builder,
    context: &mut ContextStack,
    sub: &SubproofNode,
    previous: &Rc<ProofNode>,
    inner_depth: usize,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
) -> Res {
    let (Some((x_vars, phi)), Some((y_vars, psi))) = (exists_parts(lhs), exists_parts(rhs)) else {
        return Err(explanation("`exists` congruence with a non-`exists` side"));
    };

    // The dual quantifiers, over the negated bodies
    let (not_phi, not_psi) = (b.not(&phi), b.not(&psi));
    let forall_left = b.pool.add(Term::Binder(
        Binder::Forall,
        BindingList(x_vars),
        not_phi.clone(),
    ));
    let forall_right = b.pool.add(Term::Binder(
        Binder::Forall,
        BindingList(y_vars),
        not_psi.clone(),
    ));

    // `(cl (= (∀x̄.¬φ) (∀ȳ.¬ψ)))`, by the `∀` machinery. The subproof's own body concludes
    // `φ ≈ ψ`; the negated equivalence it needs is one `cong` over it, so the replay route sees a
    // body one step longer
    let neg_previous = {
        let clause = vec![build_term!(b.pool, (= {not_phi.clone()} {not_psi.clone()}))];
        // Build at the body's depth, since it is a premise of the (replayed) body's scope
        b.open();
        let step = b.step(clause, "cong", vec![previous.clone()], Vec::new());
        b.leave_scope();
        step
    };
    let inner = congruence(
        b,
        context,
        sub,
        &neg_previous,
        inner_depth,
        &forall_left,
        &forall_right,
    )?;

    // Lift over the negation and join with the two dualities
    let not_forall_left = b.not(&forall_left);
    let not_forall_right = b.not(&forall_right);
    let lifted = {
        let clause = vec![build_term!(
            b.pool,
            (= {not_forall_left.clone()} {not_forall_right.clone()})
        )];
        b.step(clause, "cong", vec![inner], Vec::new())
    };
    let dual_left = {
        let clause = vec![build_term!(b.pool, (= {lhs.clone()} {not_forall_left}))];
        b.step(clause, "qnt_duality", Vec::new(), Vec::new())
    };
    let dual_right = {
        let clause = vec![build_term!(b.pool, (= {rhs.clone()} {not_forall_right}))];
        b.step(clause, "qnt_duality", Vec::new(), Vec::new())
    };
    let flipped = b.symm(&dual_right);
    let conclusion = build_term!(b.pool, (= {lhs.clone()} {rhs.clone()}));
    Ok(b.step(
        vec![conclusion],
        "trans",
        vec![dual_left, lifted, flipped],
        Vec::new(),
    ))
}

/// Derives `(cl (= a b))` for two α-equivalent terms, by structural recursion.
///
/// Equal terms are `refl`; an application whose children differ only α-recursively is `cong`
/// over the bridged children; a quantifier pair is [`alpha_quant`]. `choice`, `lambda` and `let`
/// differences have no core route (ε has no introduction or elimination rules — this is the
/// classification's divergence-5 residue), so those fail and the caller keeps its step.
fn alpha_bridge(b: &mut Builder, context: &mut ContextStack, a: &Rc<Term>, t: &Rc<Term>) -> Res {
    if a == t || context.apply(b.pool, a) == *t {
        // Either genuinely equal, or equal under the enclosing anchor's substitution — which is
        // exactly what a contextual `refl` states
        let clause = vec![build_term!(b.pool, (= {a.clone()} {t.clone()}))];
        return Ok(b.step(clause, "refl", Vec::new(), Vec::new()));
    }
    match (a.as_ref(), t.as_ref()) {
        // Equalities first: veriT reorients `(= a b)` after substituting, so the positional
        // bridge is tried and the crossed one (through `cong`'s four-orientation search on a
        // two-argument equality pair) backs it up
        (Term::Op(Operator::Equals, args_a), Term::Op(Operator::Equals, args_t))
            if args_a.len() == 2 && args_t.len() == 2 =>
        {
            let (a1, a2) = (args_a[0].clone(), args_a[1].clone());
            let (t1, t2) = (args_t[0].clone(), args_t[1].clone());
            let equivalence = build_term!(b.pool, (= {a.clone()} {t.clone()}));
            let positional = (|| -> Res {
                let mut premises = Vec::new();
                for (x, y) in [(&a1, &t1), (&a2, &t2)] {
                    if x != y {
                        premises.push(alpha_bridge(b, context, x, y)?);
                    }
                }
                Ok(b.step(vec![equivalence.clone()], "cong", premises, Vec::new()))
            })();
            if let Ok(node) = positional {
                return Ok(node);
            }
            let p1 = alpha_bridge(b, context, &a1, &t2)?;
            let p2 = alpha_bridge(b, context, &a2, &t1)?;
            let premise_terms: Vec<Rc<Term>> =
                [&p1, &p2].iter().map(|n| n.clause()[0].clone()).collect();
            crate::checker::cong_equal(b.pool, &premise_terms, &equivalence)?;
            Ok(b.step(vec![equivalence], "cong", vec![p1, p2], Vec::new()))
        }
        (Term::Binder(qa, _, _), Term::Binder(qt, _, _)) if qa == qt => match qa {
            Binder::Forall | Binder::Exists => alpha_quant(b, context, a, t),
            _ => Err(explanation(
                "α-difference under a `choice`/`lambda` binder has no core route",
            )),
        },
        (Term::Op(op_a, args_a), Term::Op(op_t, args_t))
            if op_a == op_t && args_a.len() == args_t.len() =>
        {
            let (args_a, args_t) = (args_a.clone(), args_t.clone());
            let mut premises = Vec::new();
            for (x, y) in args_a.iter().zip(&args_t) {
                if x != y {
                    premises.push(alpha_bridge(b, context, x, y)?);
                }
            }
            let clause = vec![build_term!(b.pool, (= {a.clone()} {t.clone()}))];
            Ok(b.step(clause, "cong", premises, Vec::new()))
        }
        (Term::App(fa, args_a), Term::App(ft, args_t))
            if fa == ft && args_a.len() == args_t.len() =>
        {
            let (args_a, args_t) = (args_a.clone(), args_t.clone());
            let mut premises = Vec::new();
            for (x, y) in args_a.iter().zip(&args_t) {
                if x != y {
                    premises.push(alpha_bridge(b, context, x, y)?);
                }
            }
            let clause = vec![build_term!(b.pool, (= {a.clone()} {t.clone()}))];
            Ok(b.step(clause, "cong", premises, Vec::new()))
        }
        _ => Err(explanation("terms differ beyond α-equivalence")),
    }
}

/// Derives `(cl (= (Qx̄.φ) (Qȳ.ψ)))` for two α-equivalent quantified terms, entirely from the
/// core: instantiate *both* sides at the target side's ε-witnesses, so that the two instances
/// differ only under φ's and ψ's own *nested* binders, and bridge those recursively.
///
/// For one direction, with ε̄ the witnesses of `(∀ȳ.ψ)`:
///
/// ```text
/// (cl (∀ȳ.ψ) ¬ψ[ε̄])          the ∀-ε-clause
/// (cl ¬(∀x̄.φ) φ[x̄↦ε̄])        forall_inst at the same witnesses, unpacked by or_pos
/// (cl (= φ[x̄↦ε̄] ψ[ȳ↦ε̄]))     the recursive bridge — nested α-differences only
/// (cl ¬(∀x̄.φ) (∀ȳ.ψ))        equiv_pos2 crossing the three
/// ```
///
/// The `∃` case routes through the duality first. Termination: each recursion strips one binder
/// layer from both sides.
fn alpha_quant(b: &mut Builder, context: &mut ContextStack, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    if exists_parts(lhs).is_some() {
        return alpha_exists(b, context, lhs, rhs);
    }
    let (Some((x_vars, phi)), Some((y_vars, psi))) = (quant_parts(lhs), quant_parts(rhs)) else {
        return Err(explanation("not a `forall` pair"));
    };
    if x_vars.len() != y_vars.len()
        || x_vars
            .iter()
            .zip(&y_vars)
            .any(|((_, sa), (_, sb))| sa != sb)
    {
        return Err(explanation("binder lists differ in length or sorts"));
    }

    let direction = |b: &mut Builder, context: &mut ContextStack, forward: bool| -> Res {
        let (from, from_vars, from_body, to, to_vars, to_body) = if forward {
            (lhs, &x_vars, &phi, rhs, &y_vars, &psi)
        } else {
            (rhs, &y_vars, &psi, lhs, &x_vars, &phi)
        };
        // `sko_forall`'s checker recomputes the witnesses over the *context-applied* body, so
        // they are built there; the ε-clause's own `refl` is contextual and reconciles the two
        let to_body_ctx = context.apply(b.pool, to_body);
        let (ws, stages) = witnesses(b.pool, to_vars, &to_body_ctx);
        let to_skolemized = stages[to_vars.len()].clone();
        let eps = epsilon_clause(b, to, to_vars, to_body, &ws, &to_skolemized)?;

        // `forall_inst` is context-free, so the instance is of the body *as written*
        let map: IndexMap<_, _> = from_vars
            .iter()
            .zip(&ws)
            .map(|(var, w)| (b.pool.add(Term::from(var.clone())), w.clone()))
            .collect();
        let from_skolemized = substitute(b.pool, from_body, map);
        let inst = instantiate(b, from, ws.clone(), &from_skolemized)?;

        // The two instances differ under nested binders, and at free variables the enclosing
        // anchor renames; bridge both recursively
        let bridged = alpha_bridge(b, context, &from_skolemized, &to_skolemized)?;
        let equality = build_term!(b.pool, (= {from_skolemized.clone()} {to_skolemized.clone()}));
        let (not_equality, not_from_sk) = (b.not(&equality), b.not(&from_skolemized));
        let axiom = b.step(
            vec![not_equality, not_from_sk, to_skolemized.clone()],
            "equiv_pos2",
            Vec::new(),
            Vec::new(),
        );
        let crossed = b.resolve(vec![axiom, bridged], vec![(equality, false)])?;
        let with_inst = b.resolve(vec![crossed, inst], vec![(from_skolemized, false)])?;
        b.resolve(vec![with_inst, eps], vec![(to_skolemized, true)])
    };
    let forward = direction(b, context, true)?;
    let backward = direction(b, context, false)?;
    b.equiv_intro(lhs.clone(), rhs.clone(), forward, backward)
}

/// The `∃` half of [`alpha_quant`]: both sides through `qnt_duality`, the `∀` case on the negated
/// bodies, `cong` over the negation, `trans` to join.
fn alpha_exists(
    b: &mut Builder,
    context: &mut ContextStack,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
) -> Res {
    let (Some((x_vars, phi)), Some((y_vars, psi))) = (exists_parts(lhs), exists_parts(rhs)) else {
        return Err(explanation("not an `exists` pair"));
    };
    let (not_phi, not_psi) = (b.not(&phi), b.not(&psi));
    let forall_left = b
        .pool
        .add(Term::Binder(Binder::Forall, BindingList(x_vars), not_phi));
    let forall_right = b
        .pool
        .add(Term::Binder(Binder::Forall, BindingList(y_vars), not_psi));
    let inner = alpha_quant(b, context, &forall_left, &forall_right)?;

    let (not_forall_left, not_forall_right) = (b.not(&forall_left), b.not(&forall_right));
    let lifted = {
        let clause = vec![build_term!(
            b.pool,
            (= {not_forall_left.clone()} {not_forall_right.clone()})
        )];
        b.step(clause, "cong", vec![inner], Vec::new())
    };
    let dual_left = {
        let clause = vec![build_term!(b.pool, (= {lhs.clone()} {not_forall_left}))];
        b.step(clause, "qnt_duality", Vec::new(), Vec::new())
    };
    let dual_right = {
        let clause = vec![build_term!(b.pool, (= {rhs.clone()} {not_forall_right}))];
        b.step(clause, "qnt_duality", Vec::new(), Vec::new())
    };
    let flipped = b.symm(&dual_right);
    let conclusion = build_term!(b.pool, (= {lhs.clone()} {rhs.clone()}));
    Ok(b.step(
        vec![conclusion],
        "trans",
        vec![dual_left, lifted, flipped],
        Vec::new(),
    ))
}

/// The vanilla case: `(∀x̄.φ) ≈ (∀ȳ.ψ)` from the body's `φ ≈ ψ`.
#[allow(clippy::too_many_arguments)]
fn congruence(
    b: &mut Builder,
    context: &mut ContextStack,
    sub: &SubproofNode,
    previous: &Rc<ProofNode>,
    inner_depth: usize,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
) -> Res {
    let (Some((x_vars, phi)), Some((y_vars, psi))) = (quant_parts(lhs), quant_parts(rhs)) else {
        let kind = lhs
            .as_binder()
            .map(|(q, _, _)| format!("{q}"))
            .unwrap_or_else(|| "non-binder".to_owned());
        return Err(explanation(format!(
            "the `bind` reduction covers `forall` congruence only, not `{kind}`"
        )));
    };
    let Some((assigned, targets)) = anchor_renaming(&sub.args) else {
        return Err(explanation("the anchor is not a renaming"));
    };
    if assigned != x_vars || targets != y_vars {
        return Err(explanation(
            "the anchor does not rename the quantifier's own variables",
        ));
    }

    // When the two sides are α-variants — which is what `bind` is *for*, and what the body then
    // proves by `refl` under the renaming context — the equivalence needs no replay at all.
    // Skolemizing both sides at the *same* witnesses gives the same term, so `sko_forall` twice,
    // one `symm` and one `trans` close it, in four steps and independently of the body's size.
    // `sko_forall` compares the anchor's witnesses with its own up to α-equivalence, which is
    // exactly the slack this uses: the witnesses of `(∀x̄.φ)` serve for `(∀ȳ.ψ)` too
    let renaming: IndexMap<_, _> = x_vars
        .iter()
        .zip(&y_vars)
        .map(|(x, y)| {
            (
                b.pool.add(Term::from(x.clone())),
                b.pool.add(Term::from(y.clone())),
            )
        })
        .collect();
    // The judgment is *contextual*: an enclosing anchor's substitution applies to the left body,
    // and `sko_forall`'s own checker applies it too when it recomputes the witnesses
    let phi_in_context = context.apply(b.pool, &phi);
    if substitute(b.pool, &phi_in_context, renaming) == psi {
        // The exact-renaming case: both sides Skolemize to the very same term, so two
        // `sko_forall` scopes and a `symm`/`trans` close it in four steps
        let (ws, stages) = witnesses(b.pool, &x_vars, &phi_in_context);
        let skolemized = stages[x_vars.len()].clone();

        let side = |b: &mut Builder, quant: &Rc<Term>, vars: &[SortedVar], body: &Rc<Term>| {
            let anchor_args: Vec<AnchorArg> = vars
                .iter()
                .zip(&ws)
                .map(|(var, w)| AnchorArg::Assign(var.clone(), w.clone()))
                .collect();
            b.open();
            let equality = build_term!(b.pool, (= {body.clone()} {skolemized.clone()}));
            let refl = b.step(vec![equality], "refl", Vec::new(), Vec::new());
            let closing = build_term!(b.pool, (= {quant.clone()} {skolemized.clone()}));
            b.close_with(anchor_args, "sko_forall", vec![closing], Vec::new(), refl)
        };
        let left = side(b, lhs, &x_vars, &phi);
        let right = side(b, rhs, &y_vars, &psi);
        let flipped = b.symm(&right);
        let conclusion = build_term!(b.pool, (= {lhs.clone()} {rhs.clone()}));
        return Ok(b.step(vec![conclusion], "trans", vec![left, flipped], Vec::new()));
    }

    // General α-equivalence — the renaming also touches *nested* bound names, or the body
    // shadows a variable: instantiate both sides at the same witnesses and bridge the residual
    // nested differences recursively. Works under an enclosing anchor too, since only the
    // ε-clause's `refl` is context-sensitive and it is built over the context-applied body
    {
        let mut time = std::time::Duration::ZERO;
        let lhs_in_context = context.apply(b.pool, lhs);
        if crate::ast::alpha_equiv(&lhs_in_context, rhs, &mut time) {
            return alpha_quant(b, context, lhs, rhs);
        }
    }

    // One direction: Skolemize `to`, instantiate `from` at the same witnesses, replay the body
    // there, and cross the two with the equivalence
    let direction = |b: &mut Builder, forward: bool| -> Res {
        let (from, from_vars, to, to_vars, to_body) = if forward {
            (lhs, &x_vars, rhs, &y_vars, &psi)
        } else {
            (rhs, &y_vars, lhs, &x_vars, &phi)
        };
        if !context.is_empty() {
            return Err(explanation(
                "a rewriting `bind` under an enclosing anchor: the replay would have to compose \
                 the two substitutions",
            ));
        }
        let (ws, stages) = witnesses(b.pool, to_vars, to_body);
        let skolemized = stages[to_vars.len()].clone();
        let eps = epsilon_clause(b, to, to_vars, to_body, &ws, &skolemized)?;

        // The replay substitutes *both* binder families by the witnesses: the body mentions the
        // left variables directly and the right ones through the anchor's renaming
        let mut map = IndexMap::new();
        for (vars, ws) in [(&x_vars, &ws), (&y_vars, &ws)] {
            for (var, w) in vars.iter().zip(ws) {
                map.insert(b.pool.add(Term::from(var.clone())), w.clone());
            }
        }
        let mut cache = ReplayCache::new();
        let replayed = replay(b, previous, &map, inner_depth, &mut cache)?;
        let [equality] = replayed.clause() else {
            return Err(explanation("the body of `bind` is not a unit equality"));
        };
        let (left_instance, right_instance) = match_term_err!((= l r) = equality)?;
        let (left_instance, right_instance) = (left_instance.clone(), right_instance.clone());

        debug_assert_eq!(from_vars.len(), ws.len());
        let from_args: Vec<_> = ws.clone();
        let instance = if forward {
            &left_instance
        } else {
            &right_instance
        };
        let inst = instantiate(b, from, from_args, instance)?;

        // `equiv_pos2`/`equiv_pos1` crosses the replayed equivalence with the instance
        let equality = equality.clone();
        let not_equality = b.not(&equality);
        let (not_left, not_right) = (b.not(&left_instance), b.not(&right_instance));
        let (axiom, pivots) = if forward {
            (
                b.step(
                    vec![not_equality, not_left, right_instance.clone()],
                    "equiv_pos2",
                    Vec::new(),
                    Vec::new(),
                ),
                (left_instance.clone(), right_instance.clone()),
            )
        } else {
            (
                b.step(
                    vec![not_equality, left_instance.clone(), not_right],
                    "equiv_pos1",
                    Vec::new(),
                    Vec::new(),
                ),
                (right_instance.clone(), left_instance.clone()),
            )
        };
        // The instance is consumed against its negation in the crossing clause, and the
        // Skolemized body against the ∀-ε-clause's negation of it
        let crossed = b.resolve(vec![axiom, replayed], vec![(equality, false)])?;
        let with_instance = b.resolve(vec![crossed, inst], vec![(pivots.0, false)])?;
        b.resolve(vec![with_instance, eps], vec![(pivots.1, true)])
    };

    let forward = direction(b, true)?;
    let backward = direction(b, false)?;
    let node = b.equiv_intro(lhs.clone(), rhs.clone(), forward, backward)?;
    Ok(node)
}

/// The generalized case: a clause whose literal `l` is closed as `(∀Ȳ. l)`.
fn closure(
    b: &mut Builder,
    sub: &SubproofNode,
    previous: &Rc<ProofNode>,
    inner_depth: usize,
    conclusion: &[Rc<Term>],
) -> Res {
    if sub.args.iter().any(|a| matches!(a, AnchorArg::Assign(..))) {
        return Err(explanation(
            "the generalized `bind` reduction covers variables-only anchors",
        ));
    }
    let inner = previous.clause();
    if inner.len() != conclusion.len() {
        return Err(explanation("clause lengths differ"));
    }
    let Some(index) = (0..inner.len()).find(|&i| inner[i] != conclusion[i]) else {
        return Err(explanation("the conclusion closes no literal"));
    };
    let Some((closure_vars, body)) = quant_parts(&conclusion[index]) else {
        return Err(explanation("the closed literal is not a `forall`"));
    };
    if body != inner[index] {
        return Err(explanation("the closure does not wrap the literal"));
    }

    let (ws, stages) = witnesses(b.pool, &closure_vars, &body);
    let skolemized = stages[closure_vars.len()].clone();
    let eps = epsilon_clause(
        b,
        &conclusion[index],
        &closure_vars,
        &body,
        &ws,
        &skolemized,
    )?;

    let mut map = IndexMap::new();
    for (var, w) in closure_vars.iter().zip(&ws) {
        map.insert(b.pool.add(Term::from(var.clone())), w.clone());
    }
    let mut cache = ReplayCache::new();
    let replayed = replay(b, previous, &map, inner_depth, &mut cache)?;
    Ok(b.resolve(vec![replayed, eps], vec![(skolemized, true)])?)
}
