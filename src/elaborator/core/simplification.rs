//! Reductions that target `aci_simp`, the designated ACI-normalization primitive: `shuffle` and
//! `nary_elim` are renames (their checks are subsumed by ACI normalization), and the legacy
//! `ac_simp` decomposes into one `aci_simp` step per connective layer, glued by `cong` and
//! `trans`.

use super::Builder;
use crate::{ast::*, elaborator::error::ElaborationError};
use indexmap::IndexMap;

/// The operators whose `aci_simp` check flattens and compares argument multisets — renaming a
/// step to `aci_simp` is only complete for these.
fn is_aci_op(op: Operator) -> bool {
    matches!(
        op,
        Operator::And
            | Operator::Or
            | Operator::Add
            | Operator::Mult
            | Operator::BvAdd
            | Operator::BvOr
            | Operator::BvMul
            | Operator::BvAnd
            | Operator::BvXor
    )
}

/// `shuffle` is a rename to `aci_simp`: a multiset comparison of the arguments is subsumed by ACI
/// normalization.
pub fn shuffle(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    if !aci_checkable(pool, &step.clause[0]) {
        log::warn!(
            "shuffle '{}': not an aci_simp instance, keeping step",
            step.id
        );
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    Ok(Rc::new(ProofNode::Step(StepNode {
        rule: "aci_simp".to_owned(),
        ..step.clone()
    })))
}

/// Whether the `aci_simp` checker accepts the given equality — guards the renames and the
/// `ac_simp` decomposition against edge cases of the ACI normalization (e.g. an identity-only
/// layer collapsing to a zero-argument operation).
fn aci_checkable(pool: &mut PrimitivePool, equality: &Rc<Term>) -> bool {
    match_term!((= t1 t2) = equality)
        .is_some_and(|(t1, t2)| crate::checker::aci_simp_equal(pool, t1, t2).is_ok())
}

/// `nary_elim` is a rename to `aci_simp` for the associative-commutative operators: both the
/// n-ary application and its binary nested form flatten to the same argument multiset. The
/// chainable (`=`) and non-commutative (`=>`, `-`, …) cases are left untouched.
pub fn nary_elim(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let renameable = match_term!((= l r) = &step.clause[0])
        .and_then(|(l, _)| l.as_op())
        .is_some_and(|(op, _)| is_aci_op(op))
        && aci_checkable(pool, &step.clause[0]);
    if !renameable {
        // The chainable and non-commutative cases are deliberately left; only an
        // aci-compatible instance that fails the check is worth a warning
        if match_term!((= l r) = &step.clause[0])
            .and_then(|(l, _)| l.as_op())
            .is_some_and(|(op, _)| is_aci_op(op))
        {
            log::warn!(
                "nary_elim '{}': aci-headed but not an aci_simp instance, keeping step",
                step.id
            );
        }
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    Ok(Rc::new(ProofNode::Step(StepNode {
        rule: "aci_simp".to_owned(),
        ..step.clone()
    })))
}

/// The sub-rewrites given by an `ac_simp` step's premises: maps each premise's left-hand side to
/// its right-hand side, the premise node, and whether the premise equality is flipped relative to
/// that orientation.
type PremiseRewrites = IndexMap<Rc<Term>, (Rc<Term>, Rc<ProofNode>, bool)>;

/// How premise rewrites are applied while computing the normal form.
#[derive(Clone, Copy, PartialEq)]
enum RewriteMode {
    /// Both orientations of every premise, and normalization *stops* at a premise's replacement
    /// --- the historical behavior, which reaches the conclusion whenever its right-hand side is
    /// literally built from the premises' replacement terms.
    Legacy,
    /// Forward orientation only, and normalization *continues* past a premise's replacement.
    /// Used by the meet-in-the-middle route, which normalizes both sides of the conclusion to a
    /// common form --- this is what the checker's structural reading accepts, so it covers the
    /// instances where a `Legacy` orientation would have to run a premise backwards (and, being
    /// undirected, could rewrite an already-normal subterm back into a nested one).
    Forward,
}

/// Computes the `ac_simp` normal form of a term, mirroring the checker for the binder-free
/// fragment: `and`/`or` layers are flattened and consecutive duplicates are removed, recursively
/// through all applications. Subterms rewritten by a premise of the step (veriT's
/// premise-carrying form of the rule — congruence over previously derived flattenings, notably
/// the under-binder ones packaged as `bind` subproofs) are replaced by the premise's right-hand
/// side. Beyond the premises this does *not* descend into binders or `let`s, so a premise-free
/// instance rewriting under a binder computes a normal form that differs from the conclusion's
/// right-hand side, and `ac_simp` keeps the original step for it.
fn ac_normal_form(
    pool: &mut PrimitivePool,
    cache: &mut IndexMap<Rc<Term>, Rc<Term>>,
    rewrites: &PremiseRewrites,
    term: &Rc<Term>,
    mode: RewriteMode,
    skip_root: bool,
) -> Rc<Term> {
    use crate::utils::DedupIterator;
    // `skip_root` (only used in `Forward` mode) computes the *structural* normal form of a
    // premise's replacement term: the premise map is not consulted for the term itself ---
    // which is what lets a converse pair of premises terminate --- and the cache is bypassed,
    // since its entries are the full normal forms.
    if !skip_root {
        if let Some(t) = cache.get(term) {
            return t.clone();
        }
        if let Some((rhs, _, _)) = rewrites.get(term) {
            let result = match mode {
                RewriteMode::Legacy => rhs.clone(),
                RewriteMode::Forward => {
                    let rhs = rhs.clone();
                    ac_normal_form(pool, cache, rewrites, &rhs, mode, true)
                }
            };
            cache.insert(term.clone(), result.clone());
            return result;
        }
    }
    let result = match term.as_ref() {
        Term::Op(op @ (Operator::And | Operator::Or), args) => {
            let args: Vec<_> = args
                .iter()
                .flat_map(|arg| {
                    let arg = ac_normal_form(pool, cache, rewrites, arg, mode, false);
                    match arg.as_ref() {
                        Term::Op(inner_op, inner_args) if inner_op == op => inner_args.clone(),
                        _ => vec![arg.clone()],
                    }
                })
                .dedup()
                .collect();
            if args.len() == 1 {
                args[0].clone()
            } else {
                pool.add(Term::Op(*op, args))
            }
        }
        Term::Op(op, args) => {
            let args = args
                .iter()
                .map(|arg| ac_normal_form(pool, cache, rewrites, arg, mode, false))
                .collect();
            pool.add(Term::Op(*op, args))
        }
        Term::App(func, args) => {
            let args = args
                .iter()
                .map(|arg| ac_normal_form(pool, cache, rewrites, arg, mode, false))
                .collect();
            pool.add(Term::App(func.clone(), args))
        }
        _ => term.clone(),
    };
    if !skip_root {
        cache.insert(term.clone(), result.clone());
    }
    result
}

/// Recursively derives `(= term N(term))`, where `N` is the `ac_simp` normal form: children are
/// normalized first (glued by `cong`), and each `and`/`or` layer is closed by one `aci_simp` step
/// (glued by `trans`). Returns `None` if the term is already normal.
fn derive_normalization(
    b: &mut Builder,
    cache: &mut IndexMap<Rc<Term>, Rc<Term>>,
    proofs: &mut IndexMap<Rc<Term>, Option<Rc<ProofNode>>>,
    rewrites: &PremiseRewrites,
    term: &Rc<Term>,
    mode: RewriteMode,
    skip_root: bool,
) -> Option<Rc<ProofNode>> {
    enum Head {
        Op(Operator),
        App(Rc<Term>),
    }

    if !skip_root {
        // Terms are DAGs with heavy sharing, so each distinct subterm is derived only once
        if let Some(hit) = proofs.get(term) {
            return hit.clone();
        }

        // A subterm rewritten by one of the step's premises is derived by the premise itself;
        // in `Forward` mode, the replacement's own normalization is derived too and glued on
        if let Some((rhs, node, flipped)) = rewrites.get(term) {
            let (rhs, node, flipped) = (rhs.clone(), node.clone(), *flipped);
            let mut node = if flipped { b.symm(&node) } else { node };
            if mode == RewriteMode::Forward {
                if let Some(rest) = derive_normalization(b, cache, proofs, rewrites, &rhs, mode, true)
                {
                    let last = normal_of(&rest);
                    let clause = vec![build_term!(b.pool, (= {term.clone()} {last}))];
                    node = b.step(clause, "trans", vec![node, rest], Vec::new());
                }
            }
            proofs.insert(term.clone(), Some(node.clone()));
            return Some(node);
        }
    }

    let normal = ac_normal_form(b.pool, cache, rewrites, term, mode, skip_root);
    if *term == normal {
        if !skip_root {
            proofs.insert(term.clone(), None);
        }
        return None;
    }

    let (head, children) = match term.as_ref() {
        Term::Op(op, args) => (Head::Op(*op), args.clone()),
        Term::App(func, args) => (Head::App(func.clone()), args.clone()),
        _ => {
            if !skip_root {
                proofs.insert(term.clone(), None);
            }
            return None;
        }
    };

    // First, normalize the children, gluing with a `cong` step if any of them changed
    let mut cong_premises = Vec::new();
    let new_children: Vec<_> = children
        .iter()
        .map(|child| {
            if let Some(proof) = derive_normalization(b, cache, proofs, rewrites, child, mode, false) {
                let normal_child = match_term!((= a b) = proof.clause()[0]).unwrap().1.clone();
                cong_premises.push(proof);
                normal_child
            } else {
                child.clone()
            }
        })
        .collect();
    let intermediate = match head {
        Head::Op(op) => b.pool.add(Term::Op(op, new_children)),
        Head::App(func) => b.pool.add(Term::App(func, new_children)),
    };

    let cong_step = if cong_premises.is_empty() {
        None
    } else {
        let clause = vec![build_term!(b.pool, (= {term.clone()} {intermediate.clone()}))];
        Some(b.step(clause, "cong", cong_premises, Vec::new()))
    };

    // Then, flatten this layer with one `aci_simp` step, if the layer is not already flat
    let aci_step = if intermediate == normal {
        None
    } else {
        let equality = build_term!(b.pool, (= {intermediate} {normal}));
        if !aci_checkable(b.pool, &equality) {
            if !skip_root {
                proofs.insert(term.clone(), None);
            }
            return None;
        }
        Some(b.step(vec![equality], "aci_simp", Vec::new(), Vec::new()))
    };

    let result = match (cong_step, aci_step) {
        (Some(c), Some(a)) => {
            let clause = vec![build_term!(b.pool, (= {term.clone()} {normal_of(&a)}))];
            Some(b.step(clause, "trans", vec![c, a], Vec::new()))
        }
        (Some(c), None) => Some(c),
        (None, Some(a)) => Some(a),
        (None, None) => unreachable!("term differs from its normal form"),
    };
    if !skip_root {
        proofs.insert(term.clone(), result.clone());
    }
    result
}

fn normal_of(node: &Rc<ProofNode>) -> Rc<Term> {
    match_term!((= a b) = node.clause()[0]).unwrap().1.clone()
}

/// The legacy `ac_simp` decomposes into per-layer `aci_simp` steps glued by `cong`/`trans`.
///
/// veriT emits the rule in two forms: premise-free (a pure flattening) and premise-carrying —
/// congruence over previously derived flattenings of subterms, which is how rewrites under a
/// binder reach the conclusion (as `bind` subproofs among the premises). The decomposition
/// consumes the premises as ready-made equalities for those subterms, so no binder congruence
/// needs to be derived here.
pub fn ac_simp(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let (original, flattened) = match_term_err!((= psi phis) = &step.clause[0])?;
    let (original, flattened) = (original.clone(), flattened.clone());

    // The premises' equalities, indexed by their left-hand side: forward-only for the
    // meet-in-the-middle route, both orientations for the historical one
    let mut forward = PremiseRewrites::new();
    let mut legacy = PremiseRewrites::new();
    for premise in &step.premises {
        let [equality] = premise.clause() else {
            log::warn!("ac_simp '{}': premise is not a unit clause, keeping step", step.id);
            return Ok(Rc::new(ProofNode::Step(step.clone())));
        };
        let Some((lhs, rhs)) = match_term!((= l r) = equality) else {
            log::warn!("ac_simp '{}': premise is not an equality, keeping step", step.id);
            return Ok(Rc::new(ProofNode::Step(step.clone())));
        };
        forward
            .entry(lhs.clone())
            .or_insert_with(|| (rhs.clone(), premise.clone(), false));
        legacy
            .entry(lhs.clone())
            .or_insert_with(|| (rhs.clone(), premise.clone(), false));
        legacy
            .entry(rhs.clone())
            .or_insert_with(|| (lhs.clone(), premise.clone(), true));
    }

    // Route 1, the historical single-direction decomposition: derive the left-hand side's
    // normal form and reach the conclusion's right-hand side directly. Kept first so that
    // every instance it covers is decomposed exactly as before.
    {
        let mut b = Builder::new(pool, step);
        let mut cache = IndexMap::new();
        let mode = RewriteMode::Legacy;
        if ac_normal_form(b.pool, &mut cache, &legacy, &original, mode, false) == flattened {
            let mut proofs = IndexMap::new();
            match derive_normalization(&mut b, &mut cache, &mut proofs, &legacy, &original, mode, false)
            {
                Some(node) => return close(b, step, node),
                // Degenerate instance concluding `(= t t)`
                None if original == flattened => {
                    return Ok(b.finish(step, "refl", Vec::new(), Vec::new()));
                }
                // A derived layer would not check; the meet route will not do better, since it
                // emits the same layers
                None => {
                    log::warn!(
                        "ac_simp '{}': a derived layer would not check, keeping step",
                        step.id
                    );
                    return Ok(Rc::new(ProofNode::Step(step.clone())));
                }
            }
        }
    }

    // Route 2, meet in the middle: normalize *both* sides of the conclusion — forward premise
    // rewrites only, normalization continuing past each replacement — and glue the two
    // derivations with `symm`/`trans`. This is the checker's structural reading, and covers the
    // instances where the right-hand side is not itself the normal form (e.g. a premise whose
    // replacement term is less normal than what the conclusion writes at that position).
    let mut b = Builder::new(pool, step);
    let mut cache = IndexMap::new();
    let mode = RewriteMode::Forward;
    let nl = ac_normal_form(b.pool, &mut cache, &forward, &original, mode, false);
    let nr = ac_normal_form(b.pool, &mut cache, &forward, &flattened, mode, false);
    if nl != nr {
        log::warn!(
            "ac_simp '{}': the two sides have different normal forms, keeping step",
            step.id
        );
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    let mut proofs = IndexMap::new();
    let dl = derive_normalization(&mut b, &mut cache, &mut proofs, &forward, &original, mode, false);
    if dl.is_none() && original != nl {
        log::warn!(
            "ac_simp '{}': a derived layer would not check, keeping step",
            step.id
        );
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    let dr = derive_normalization(&mut b, &mut cache, &mut proofs, &forward, &flattened, mode, false);
    if dr.is_none() && flattened != nr {
        log::warn!(
            "ac_simp '{}': a derived layer would not check, keeping step",
            step.id
        );
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    let node = match (dl, dr) {
        // Both sides are already normal: the conclusion is `(= t t)`
        (None, None) => return Ok(b.finish(step, "refl", Vec::new(), Vec::new())),
        // The right-hand side is the normal form: the left derivation concludes the step
        (Some(d), None) => d,
        // The left-hand side is: flip the right derivation
        (None, Some(d)) => b.symm(&d),
        (Some(dl), Some(dr)) => {
            let flipped = b.symm(&dr);
            let clause = vec![build_term!(b.pool, (= {original.clone()} {flattened.clone()}))];
            b.step(clause, "trans", vec![dl, flipped], Vec::new())
        }
    };
    close(b, step, node)
}

/// Gives the derived node the step's identity. If the whole derivation is one of the premises
/// (the step merely repeats it), that node cannot take the step's identity; a double `symm`
/// re-derives the equality as a fresh step instead.
fn close(
    mut b: Builder,
    step: &StepNode,
    node: Rc<ProofNode>,
) -> Result<Rc<ProofNode>, ElaborationError> {
    if step.premises.contains(&node) {
        let once = b.symm(&node);
        let twice = b.symm(&once);
        return Ok(b.relabel(step, twice));
    }
    Ok(b.relabel(step, node))
}