//! Reduction of `sko_ex` through the quantifier duality.
//!
//! `sko_forall` is the core's designated ε-introduction axiom. An existing `sko_ex` step —
//! anchor `x̄ ↦ v̄` with the progressive ∃-shaped witnesses
//! `vᵢ = (choice ((xᵢ)) (∃x_{i+1..}. φⁱ))` (`φⁱ` being `φ` with the earlier witnesses
//! substituted), subproof concluding `φ ≈ ψ`, conclusion `(= (∃x̄.φ) ψ)` with `ψ = φ[x̄↦v̄]` —
//! is re-derived from the dual, entirely inside the step's own (now vacuous) anchor. In fresh
//! variables `z̄` (the anchor's substitution would poison nested context-sensitive checks, and
//! inner anchors re-binding the variables shadow it):
//!
//! 1. an α-renaming `bind` `(= (∃x̄.φ) (∃z̄.φ_z))`, `φ_z = φ[x̄↦z̄]`;
//! 2. the ∀-ε-clause: a `sko_forall` subproof over the dual `(∀z̄.¬φ_z)`, concluding
//!    `(= (∀z̄.¬φ_z) ¬φ_z[z̄↦w̄])` with ¬∀¬-shaped witnesses
//!    `wᵢ = (choice ((zᵢ)) ¬(∀ū. ¬φ_zⁱ[z_{i+1..}↦ū]))` — each witness's quantified tail in its
//!    own fresh family `ū`, so that no substitution in the construction ever captures (the
//!    `sko_forall` checker compares witnesses modulo α);
//! 3. the `connective_def` duality `(= (∃z̄.φ_z) ¬(∀z̄.¬φ_z))`, glued by `cong`/`trans`, and a
//!    double-negation equivalence (excluded middle + `not_not` + iff-introduction), giving
//!    `(= (∃x̄.φ) φ_z[z̄↦w̄])`;
//! 4. per binding, choice congruence — a `bind` over the `choice` binder (Carcara's `bind`
//!    checker is binder-generic, so no new rule is involved) — deriving `(= wᵢ vᵢ)`: the
//!    bodies are bridged by variable-level `refl`s under the renaming context glued by deep
//!    `cong` (a single whole-body `refl` would not survive the elaborated-granularity checker,
//!    whose `strict_refl` demands syntactic equality after substitution, while substituting
//!    into a term that binds a substituted variable α-renames it), a transport over the earlier
//!    witness equalities, and either the double-negation equivalence (last binding) or an
//!    α-renaming `bind` of the quantified tail plus the `connective_def` duality (the rest);
//! 5. a deep-`cong` transport of `φ_z[z̄↦w̄]` to `ψ` over those equalities, and a final
//!    `trans`, which closes the anchor keeping the step's id and conclusion.

use super::binder::excluded_middle;
use super::onepoint::{anchor_points, eq_symmetry, relabel_dropping_previous};
use super::Builder;
use crate::{ast::*, elaborator::error::ElaborationError};
use indexmap::IndexMap;

/// Derives `(= (not (not phi)) phi)`: iff-introduction from the `not_not` axiom and an excluded
/// middle on `¬φ`.
fn not_not_equivalence(b: &mut Builder, phi: &Rc<Term>) -> Result<Rc<ProofNode>, ElaborationError> {
    let not_phi = b.not(phi);
    let nn_phi = b.not(&not_phi);
    let nnn_phi = b.not(&nn_phi);
    let em = excluded_middle(b, &not_phi)?;
    let not_not = b.step(
        vec![nnn_phi, phi.clone()],
        "not_not",
        Vec::new(),
        Vec::new(),
    );
    b.equiv_intro(nn_phi, phi.clone(), not_not, em)
}

/// Wraps the body in a binder over the variables, or returns it unchanged if there are none.
fn wrap(pool: &mut PrimitivePool, binder: Binder, vars: &[SortedVar], body: &Rc<Term>) -> Rc<Term> {
    if vars.is_empty() {
        body.clone()
    } else {
        pool.add(Term::Binder(
            binder,
            BindingList(vars.to_vec()),
            body.clone(),
        ))
    }
}

fn substitute(
    pool: &mut PrimitivePool,
    term: &Rc<Term>,
    map: IndexMap<Rc<Term>, Rc<Term>>,
) -> Option<Rc<Term>> {
    if map.is_empty() {
        return Some(term.clone());
    }
    Substitution::new(pool, map)
        .ok()
        .map(|mut s| s.apply(pool, term))
}

/// Emits per-variable `refl` facts (checkable under the enclosing renaming context) for the
/// given pairs, keyed by the source variable. Facts that end up unused are simply never
/// referenced, so they do not appear in the output.
fn variable_facts(
    b: &mut Builder,
    pairs: &[(Rc<Term>, Rc<Term>)],
) -> IndexMap<Rc<Term>, Rc<ProofNode>> {
    pairs
        .iter()
        .map(|(from, to)| {
            let clause = vec![build_term!(b.pool, (= {from.clone()} {to.clone()}))];
            (from.clone(), b.step(clause, "refl", Vec::new(), Vec::new()))
        })
        .collect()
}

/// Derives `(= from to)` by a deep `cong` descent: positions covered by a fact use the fact's
/// node, and equality subterms that veriT wrote in the flipped orientation are bridged by
/// [`eq_symmetry`] (crossed descent + `cong` + `trans`). Returns `None` when the terms are
/// identical; `Err(())` when they differ in any other way (e.g. below a binder).
fn bridge(
    b: &mut Builder,
    facts: &IndexMap<Rc<Term>, Rc<ProofNode>>,
    from: &Rc<Term>,
    to: &Rc<Term>,
) -> Result<Option<Rc<ProofNode>>, ()> {
    if from == to {
        return Ok(None);
    }
    if let Some(node) = facts.get(from) {
        if node.clause()[0] == build_term!(b.pool, (= {from.clone()} {to.clone()})) {
            return Ok(Some(node.clone()));
        }
    }
    let descend = |b: &mut Builder| -> Result<Option<Rc<ProofNode>>, ()> {
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
            if let Some(node) = bridge(b, facts, u, v)? {
                premises.push(node);
            }
        }
        let clause = vec![build_term!(b.pool, (= {from.clone()} {to.clone()}))];
        Ok(Some(b.step(clause, "cong", premises, Vec::new())))
    };
    // Note: the direct descent may emit dead steps before failing; they are never referenced,
    // so they do not appear in the output
    if let Ok(node) = descend(b) {
        return Ok(node);
    }
    // A flipped equality: bridge the children pairwise to the *swapped* sides, then apply
    // equality symmetry
    if let (Some((a, bb)), Some((c, d))) = (match_term!((= a b) = from), match_term!((= a b) = to))
    {
        let (a, bb, c, d) = (a.clone(), bb.clone(), c.clone(), d.clone());
        let left = bridge(b, facts, &a, &d)?;
        let right = bridge(b, facts, &bb, &c)?;
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
    Err(())
}

/// Derives `(= from to)` by [`bridge`], or by a plain `refl` when the terms are already equal.
fn bridge_or_refl(
    b: &mut Builder,
    facts: &IndexMap<Rc<Term>, Rc<ProofNode>>,
    from: &Rc<Term>,
    to: &Rc<Term>,
) -> Result<Rc<ProofNode>, ()> {
    match bridge(b, facts, from, to)? {
        Some(node) => Ok(node),
        None => {
            let clause = vec![build_term!(b.pool, (= {from.clone()} {to.clone()}))];
            Ok(b.step(clause, "refl", Vec::new(), Vec::new()))
        }
    }
}

/// The `sko_ex` rule. Covers the instances whose anchor carries exactly the progressive
/// ∃-shaped witnesses and whose right-hand side is exactly the substituted body — the shape
/// veriT emits. Anything else (including bodies whose bound variables occur under further
/// binders, which the transports cannot reach) is kept unchanged.
#[allow(clippy::too_many_lines)]
pub fn sko_ex(
    pool: &mut PrimitivePool,
    context: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let keep = || Ok(Rc::new(ProofNode::Step(step.clone())));

    let Some((exists, psi)) = match_term!((= l r) = &step.clause[0]) else {
        return keep();
    };
    let (exists, psi) = (exists.clone(), psi.clone());
    let Some((Binder::Exists, bindings, phi)) = exists
        .as_binder()
        .map(|(q, bs, t)| (q, bs.0.clone(), t.clone()))
    else {
        return keep();
    };
    let Some((points, kept)) = anchor_points(context) else {
        return keep();
    };
    let n = bindings.len();
    if n == 0 || points.len() != n || !kept.is_empty() {
        return keep();
    }
    if (0..n).any(|i| points[i].0 != bindings[i]) {
        return keep();
    }
    let x_terms: Vec<Rc<Term>> = bindings
        .iter()
        .map(|var| pool.add(Term::from(var.clone())))
        .collect();

    // The step's own progressive ∃-shaped witnesses, as written in the anchor (the original
    // checker already validated them, modulo α and equality reordering — veriT reorients
    // equality subterms after substituting, so they need not match a recomputation exactly);
    // `v_stages[i]` is `φ` with the first `i` witnesses substituted, and `v_bodies[i]` the body
    // of the `i`-th `choice`, whose quantified tail must be exactly the remaining bindings
    let mut v_stages = vec![phi.clone()];
    let mut v_bodies = Vec::new();
    let mut vs = Vec::new();
    for i in 0..n {
        let witness = points[i].1.clone();
        let Some((Binder::Choice, choice_vars, choice_body)) = witness
            .as_binder()
            .map(|(q, bs, t)| (q, bs.0.clone(), t.clone()))
        else {
            return keep();
        };
        if choice_vars.as_slice() != &bindings[i..=i] {
            return keep();
        }
        if i < n - 1 {
            let Some((Binder::Exists, tail_vars, _)) = choice_body
                .as_binder()
                .map(|(q, bs, t)| (q, bs.0.clone(), t.clone()))
            else {
                return keep();
            };
            if tail_vars.as_slice() != &bindings[i + 1..] {
                return keep();
            }
        }
        let body = choice_body;
        let map = IndexMap::from([(x_terms[i].clone(), witness.clone())]);
        let current = v_stages[i].clone();
        let Some(next) = substitute(pool, &current, map) else {
            return keep();
        };
        v_stages.push(next);
        v_bodies.push(body);
        vs.push(witness);
    }
    // The right-hand side must be exactly the fully substituted body (the inner derivation is a
    // pure transport in the covered shape)
    if v_stages[n] != psi {
        return keep();
    }

    // The fresh variables: the renamed bindings `z̄`, and one tail family `ūⁱ` per witness
    let free_names: Vec<String> = pool
        .free_vars(&phi)
        .iter()
        .filter_map(|t| t.as_var().map(ToOwned::to_owned))
        .collect();
    let mut used_names: Vec<String> = Vec::new();
    let mut fresh = |base: &str, tag: String| -> String {
        let mut name = format!("{base}!{tag}");
        while free_names.contains(&name) || used_names.contains(&name) {
            name.push('\'');
        }
        used_names.push(name.clone());
        name
    };
    let z_vars: Vec<SortedVar> = bindings
        .iter()
        .map(|(name, sort)| (fresh(name, "sko".to_owned()), sort.clone()))
        .collect();
    let u_vars: Vec<Vec<SortedVar>> = (0..n)
        .map(|i| {
            bindings[i + 1..]
                .iter()
                .map(|(name, sort)| (fresh(name, format!("sko{i}")), sort.clone()))
                .collect()
        })
        .collect();
    let z_terms: Vec<Rc<Term>> = z_vars
        .iter()
        .map(|var| pool.add(Term::from(var.clone())))
        .collect();

    let rename: IndexMap<_, _> = x_terms
        .iter()
        .cloned()
        .zip(z_terms.iter().cloned())
        .collect();
    let Some(phi_z) = substitute(pool, &phi, rename) else {
        return keep();
    };
    let exists_z = wrap(pool, Binder::Exists, &z_vars, &phi_z);
    let not_phi_z = build_term!(pool, (not {phi_z.clone()}));
    let forall_z = wrap(pool, Binder::Forall, &z_vars, &not_phi_z);

    // The progressive ¬∀¬-shaped witnesses of the dual `sko_forall`; `w_stages[i]` is `φ_z`
    // with the first `i` witnesses substituted, and each witness's quantified tail lives in its
    // own `ūⁱ` family (the checker compares them modulo α), so that none of these substitutions
    // ever renames a binder — the whole construction stays syntactically aligned
    let mut w_stages = vec![phi_z.clone()];
    let mut w_bodies = Vec::new();
    let mut ws = Vec::new();
    for i in 0..n {
        let current = w_stages[i].clone();
        let tail_rename: IndexMap<_, _> = z_terms[i + 1..]
            .iter()
            .cloned()
            .zip(
                u_vars[i]
                    .iter()
                    .map(|var| pool.add(Term::from(var.clone()))),
            )
            .collect();
        let Some(renamed) = substitute(pool, &current, tail_rename) else {
            return keep();
        };
        let negated = build_term!(pool, (not { renamed }));
        let inner = wrap(pool, Binder::Forall, &u_vars[i], &negated);
        let body = build_term!(pool, (not { inner }));
        let witness = wrap(pool, Binder::Choice, &z_vars[i..=i], &body);
        let map = IndexMap::from([(z_terms[i].clone(), witness.clone())]);
        let Some(next) = substitute(pool, &current, map) else {
            return keep();
        };
        w_stages.push(next);
        w_bodies.push(body);
        ws.push(witness);
    }
    let psi_w = w_stages[n].clone();

    let mut b = Builder::new(pool, step);

    // (1) The α-renaming bind `(= (∃x̄.φ) (∃z̄.φ_z))`
    b.open();
    let pairs: Vec<_> = x_terms
        .iter()
        .cloned()
        .zip(z_terms.iter().cloned())
        .collect();
    let facts = variable_facts(&mut b, &pairs);
    let Ok(refl) = bridge_or_refl(&mut b, &facts, &phi, &phi_z) else {
        return keep();
    };
    let clause = vec![build_term!(b.pool, (= {exists.clone()} {exists_z.clone()}))];
    let mut anchor: Vec<AnchorArg> = z_vars.iter().cloned().map(AnchorArg::Variable).collect();
    anchor.extend(
        bindings
            .iter()
            .zip(&z_terms)
            .map(|(x, z)| AnchorArg::Assign(x.clone(), z.clone())),
    );
    let alpha = b.close_with(anchor, "bind", clause, Vec::new(), refl);

    // (2) The ∀-ε-clause for the dual quantifier
    let not_psi_w = b.not(&psi_w);
    b.open();
    let pairs: Vec<_> = z_terms.iter().cloned().zip(ws.iter().cloned()).collect();
    let facts = variable_facts(&mut b, &pairs);
    let Ok(refl) = bridge_or_refl(&mut b, &facts, &not_phi_z, &not_psi_w) else {
        return keep();
    };
    let clause = vec![build_term!(b.pool, (= {forall_z.clone()} {not_psi_w.clone()}))];
    let anchor = z_vars
        .iter()
        .zip(&ws)
        .map(|(z, w)| AnchorArg::Assign(z.clone(), w.clone()))
        .collect();
    let epsilon = b.close_with(anchor, "sko_forall", clause, Vec::new(), refl);

    // (3) Duality, then eliminate the double negation
    let not_forall_z = b.not(&forall_z);
    let clause = vec![build_term!(b.pool, (= {exists_z.clone()} {not_forall_z.clone()}))];
    let duality = b.step(clause, "connective_def", Vec::new(), Vec::new());
    let nn_psi_w = b.not(&not_psi_w);
    let clause = vec![build_term!(b.pool, (= {not_forall_z} {nn_psi_w.clone()}))];
    let cong = b.step(clause, "cong", vec![epsilon], Vec::new());
    let nn_equiv = not_not_equivalence(&mut b, &psi_w)?;
    let clause = vec![build_term!(b.pool, (= {exists.clone()} {psi_w.clone()}))];
    let mut current = b.step(
        clause,
        "trans",
        vec![alpha, duality, cong, nn_equiv],
        Vec::new(),
    );

    // (4) + (5) Bridge the ¬∀¬-shaped witnesses to the step's ∃-shaped ones, unless no
    // variable occurs in `φ` (in which case the two substituted bodies coincide)
    if psi_w != psi {
        // `wv_facts` maps each `wᵢ` to the derived `(= wᵢ vᵢ)`
        let mut wv_facts: IndexMap<Rc<Term>, Rc<ProofNode>> = IndexMap::new();
        for i in 0..n {
            b.open();
            let inner = if i == n - 1 {
                // Last binding: bodies are `¬¬φ_zⁱ` and the as-written `φⁱ`
                let target = v_bodies[i].clone();
                let pairs = vec![(z_terms[i].clone(), x_terms[i].clone())];
                let mut facts = variable_facts(&mut b, &pairs);
                facts.extend(wv_facts.clone());
                let nn_target = {
                    let not = b.not(&target);
                    b.not(&not)
                };
                let Ok(renamed) = bridge_or_refl(&mut b, &facts, &w_bodies[i], &nn_target) else {
                    return keep();
                };
                let nn_equiv = not_not_equivalence(&mut b, &target)?;
                let clause = vec![build_term!(b.pool, (= {w_bodies[i].clone()} {target.clone()}))];
                b.step(clause, "trans", vec![renamed, nn_equiv], Vec::new())
            } else {
                // Other bindings: bodies are `¬(∀ūⁱ.¬φ_zⁱ[ū])` and the as-written
                // `(∃x_tail.φⁱ)`; α-rename the quantified tail, then cross the duality
                let Some((_, _, target)) = v_bodies[i].as_binder() else {
                    return keep();
                };
                let target = target.clone();
                let not_target = b.not(&target);
                let u_terms: Vec<Rc<Term>> = u_vars[i]
                    .iter()
                    .map(|var| b.pool.add(Term::from(var.clone())))
                    .collect();
                let tail_rename: IndexMap<_, _> = z_terms[i + 1..]
                    .iter()
                    .cloned()
                    .zip(u_terms.iter().cloned())
                    .collect();
                let Some(renamed_stage) = substitute(b.pool, &w_stages[i], tail_rename) else {
                    return keep();
                };
                let not_renamed_stage = b.not(&renamed_stage);

                b.open();
                let mut pairs = vec![(z_terms[i].clone(), x_terms[i].clone())];
                pairs.extend(
                    u_terms
                        .iter()
                        .cloned()
                        .zip(x_terms[i + 1..].iter().cloned()),
                );
                let mut facts = variable_facts(&mut b, &pairs);
                facts.extend(wv_facts.clone());
                let Ok(tail_inner) =
                    bridge_or_refl(&mut b, &facts, &not_renamed_stage, &not_target)
                else {
                    return keep();
                };
                let forall_tail_u = wrap(b.pool, Binder::Forall, &u_vars[i], &not_renamed_stage);
                let forall_tail_x = wrap(b.pool, Binder::Forall, &bindings[i + 1..], &not_target);
                let clause = vec![build_term!(
                    b.pool,
                    (= {forall_tail_u.clone()} {forall_tail_x.clone()})
                )];
                let mut anchor: Vec<AnchorArg> = bindings[i + 1..]
                    .iter()
                    .cloned()
                    .map(AnchorArg::Variable)
                    .collect();
                anchor.extend(
                    u_vars[i]
                        .iter()
                        .zip(&x_terms[i + 1..])
                        .map(|(u, x)| AnchorArg::Assign(u.clone(), x.clone())),
                );
                let tail_bind = b.close_with(anchor, "bind", clause, Vec::new(), tail_inner);

                let not_forall_tail_x = b.not(&forall_tail_x);
                let clause = vec![build_term!(
                    b.pool,
                    (= {w_bodies[i].clone()} {not_forall_tail_x.clone()})
                )];
                let cong = b.step(clause, "cong", vec![tail_bind], Vec::new());
                let clause = vec![build_term!(
                    b.pool,
                    (= {v_bodies[i].clone()} {not_forall_tail_x})
                )];
                let duality = b.step(clause, "connective_def", Vec::new(), Vec::new());
                let flipped = b.symm(&duality);
                let clause =
                    vec![build_term!(b.pool, (= {w_bodies[i].clone()} {v_bodies[i].clone()}))];
                b.step(clause, "trans", vec![cong, flipped], Vec::new())
            };
            let clause = vec![build_term!(b.pool, (= {ws[i].clone()} {vs[i].clone()}))];
            let anchor = vec![
                AnchorArg::Variable(bindings[i].clone()),
                AnchorArg::Assign(z_vars[i].clone(), x_terms[i].clone()),
            ];
            let witness_eq = b.close_with(anchor, "bind", clause, Vec::new(), inner);
            wv_facts.insert(ws[i].clone(), witness_eq);
        }

        let Ok(Some(final_bridge)) = bridge(&mut b, &wv_facts, &psi_w, &psi) else {
            // An occurrence of a variable below a binder in `φ`: the bridge cannot reach it
            return keep();
        };
        let clause = vec![build_term!(b.pool, (= {exists.clone()} {psi.clone()}))];
        current = b.step(clause, "trans", vec![current, final_bridge], Vec::new());
    }

    Ok(relabel_dropping_previous(step, &current))
}
