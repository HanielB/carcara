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
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    Ok(Rc::new(ProofNode::Step(StepNode {
        rule: "aci_simp".to_owned(),
        ..step.clone()
    })))
}

/// Computes the `ac_simp` normal form of a term, mirroring the checker: `and`/`or` layers are
/// flattened and consecutive duplicates are removed, recursively through all subterms.
fn ac_normal_form(
    pool: &mut PrimitivePool,
    cache: &mut IndexMap<Rc<Term>, Rc<Term>>,
    term: &Rc<Term>,
) -> Rc<Term> {
    use crate::utils::DedupIterator;
    if let Some(t) = cache.get(term) {
        return t.clone();
    }
    let result = match term.as_ref() {
        Term::Op(op @ (Operator::And | Operator::Or), args) => {
            let args: Vec<_> = args
                .iter()
                .flat_map(|arg| {
                    let arg = ac_normal_form(pool, cache, arg);
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
                .map(|arg| ac_normal_form(pool, cache, arg))
                .collect();
            pool.add(Term::Op(*op, args))
        }
        Term::App(func, args) => {
            let args = args
                .iter()
                .map(|arg| ac_normal_form(pool, cache, arg))
                .collect();
            pool.add(Term::App(func.clone(), args))
        }
        _ => term.clone(),
    };
    cache.insert(term.clone(), result.clone());
    result
}

/// Recursively derives `(= term N(term))`, where `N` is the `ac_simp` normal form: children are
/// normalized first (glued by `cong`), and each `and`/`or` layer is closed by one `aci_simp` step
/// (glued by `trans`). Returns `None` if the term is already normal.
fn derive_normalization(
    b: &mut Builder,
    cache: &mut IndexMap<Rc<Term>, Rc<Term>>,
    proofs: &mut IndexMap<Rc<Term>, Option<Rc<ProofNode>>>,
    term: &Rc<Term>,
) -> Option<Rc<ProofNode>> {
    enum Head {
        Op(Operator),
        App(Rc<Term>),
    }

    // Terms are DAGs with heavy sharing, so each distinct subterm is derived only once
    if let Some(hit) = proofs.get(term) {
        return hit.clone();
    }

    let normal = ac_normal_form(b.pool, cache, term);
    if *term == normal {
        proofs.insert(term.clone(), None);
        return None;
    }

    let (head, children) = match term.as_ref() {
        Term::Op(op, args) => (Head::Op(*op), args.clone()),
        Term::App(func, args) => (Head::App(func.clone()), args.clone()),
        _ => {
            proofs.insert(term.clone(), None);
            return None;
        }
    };

    // First, normalize the children, gluing with a `cong` step if any of them changed
    let mut cong_premises = Vec::new();
    let new_children: Vec<_> = children
        .iter()
        .map(|child| {
            if let Some(proof) = derive_normalization(b, cache, proofs, child) {
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
            proofs.insert(term.clone(), None);
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
    proofs.insert(term.clone(), result.clone());
    result
}

fn normal_of(node: &Rc<ProofNode>) -> Rc<Term> {
    match_term!((= a b) = node.clause()[0]).unwrap().1.clone()
}

/// The legacy `ac_simp` decomposes into per-layer `aci_simp` steps glued by `cong`/`trans`.
pub fn ac_simp(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    let (original, flattened) = match_term_err!((= psi phis) = &step.clause[0])?;
    let (original, flattened) = (original.clone(), flattened.clone());

    let mut b = Builder::new(pool, step);
    let mut cache = IndexMap::new();

    // The conclusion's right-hand side must be the normal form for the decomposition to reach it
    if ac_normal_form(b.pool, &mut cache, &original) != flattened {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }
    let mut proofs = IndexMap::new();
    match derive_normalization(&mut b, &mut cache, &mut proofs, &original) {
        Some(node) => Ok(b.relabel(step, node)),
        // Degenerate instance concluding `(= t t)`
        None if original == flattened => Ok(b.finish(step, "refl", Vec::new(), Vec::new())),
        // The decomposition bailed out (an emitted `aci_simp` layer would not check)
        None => Ok(Rc::new(ProofNode::Step(step.clone()))),
    }
}
