//! The `bind` reduction: binder congruence from `sko_forall` and `forall_inst`.
//!
//! `bind` closes a subproof that derives `φ ≈ ψ` under an anchor renaming the quantifier's
//! variables, and concludes `(∀x̄.φ) ≈ (∀ȳ.ψ)`. The core derives the same equivalence without it,
//! by the route the classification calls *admissibility of the generalized `bind`*: Skolemize the
//! target, instantiate the premise at the same witnesses, and **replay the subproof's derivation
//! with the witnesses substituted for the anchor's variables** — every core rule is schematic, so
//! its instances stay valid under a uniform substitution of closed terms.
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
    // Under an enclosing anchor the cumulative substitution also reaches the terms this reduction
    // builds — the `refl` closing the ∀-ε-clause would have to state what that substitution makes
    // of the body, not the body as written — so a `bind` inside another scope is left alone
    if !context.is_empty() {
        return Err(explanation("`bind` under an enclosing anchor"));
    }
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

    // The vanilla form: a unit clause holding an equivalence between two quantified terms
    if let [conclusion] = last.clause.as_slice() {
        if let Some((lhs, rhs)) = match_term!((= l r) = conclusion) {
            let (lhs, rhs) = (lhs.clone(), rhs.clone());
            return congruence(&mut b, sub, previous, inner_depth, &lhs, &rhs);
        }
    }

    // The generalized form: a clause with one literal closed as `(∀Ȳ. l)`, the others passing
    // through
    closure(&mut b, sub, previous, inner_depth, &last.clause)
}

fn quant_parts(term: &Rc<Term>) -> Option<(Vec<SortedVar>, Rc<Term>)> {
    match term.as_ref() {
        Term::Binder(Binder::Forall, bindings, body) => Some((bindings.0.clone(), body.clone())),
        _ => None,
    }
}

/// The vanilla case: `(∀x̄.φ) ≈ (∀ȳ.ψ)` from the body's `φ ≈ ψ`.
fn congruence(
    b: &mut Builder,
    sub: &SubproofNode,
    previous: &Rc<ProofNode>,
    inner_depth: usize,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
) -> Res {
    let (Some((x_vars, phi)), Some((y_vars, psi))) = (quant_parts(lhs), quant_parts(rhs)) else {
        return Err(explanation(
            "the `bind` reduction covers `forall` congruence only",
        ));
    };
    let Some((assigned, targets)) = anchor_renaming(&sub.args) else {
        return Err(explanation("the anchor is not a renaming"));
    };
    if assigned != x_vars || targets != y_vars {
        return Err(explanation(
            "the anchor does not rename the quantifier's own variables",
        ));
    }

    // One direction: Skolemize `to`, instantiate `from` at the same witnesses, replay the body
    // there, and cross the two with the equivalence
    let direction = |b: &mut Builder, forward: bool| -> Res {
        let (from, from_vars, to, to_vars, to_body) = if forward {
            (lhs, &x_vars, rhs, &y_vars, &psi)
        } else {
            (rhs, &y_vars, lhs, &x_vars, &phi)
        };
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
