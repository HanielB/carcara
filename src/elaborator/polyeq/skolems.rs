//! Canonical skolem terms for `sko_forall`/`sko_ex` anchors.
//!
//! The skolemization rules accept a witness that is only alpha-equivalent modulo the reordering of
//! equalities to the `choice` term they expect (veriT, for one, writes some equalities of the
//! quantifier body flipped inside the witness). A consumer that checks the elaborated proof
//! without that leniency then sees two different terms. This pass replaces every such witness by
//! the expected `choice` term, everywhere in the proof: the witness is a closed term, so a uniform
//! substitution keeps every step valid, and the anchors then bind exactly what the rules recompute.

use super::*;
use crate::ast::*;
use indexmap::IndexMap;
use std::{collections::HashMap, convert::Infallible, time::Duration};

/// Replaces closed terms by closed terms, everywhere in a term. (`Substitution` maps variables
/// only; the witnesses are `choice` terms, and closed, so no binder can capture anything.)
struct Replacer {
    map: IndexMap<Rc<Term>, Rc<Term>>,
    cache: HashMap<Rc<Term>, Rc<Term>>,
}

impl Replacer {
    fn new(map: IndexMap<Rc<Term>, Rc<Term>>) -> Self {
        Self { map, cache: HashMap::new() }
    }

    fn apply(&mut self, pool: &mut PrimitivePool, term: &Rc<Term>) -> Rc<Term> {
        if let Some(t) = self.cache.get(term) {
            return t.clone();
        }
        if let Some(t) = self.map.get(term) {
            return t.clone();
        }
        let result = match term.as_ref() {
            Term::App(func, args) => {
                let func = self.apply(pool, func);
                let args = self.apply_all(pool, args);
                pool.add(Term::App(func, args))
            }
            Term::Op(op, args) => {
                let args = self.apply_all(pool, args);
                pool.add(Term::Op(*op, args))
            }
            Term::Binder(binder, bindings, inner) => {
                let inner = self.apply(pool, inner);
                pool.add(Term::Binder(*binder, bindings.clone(), inner))
            }
            Term::Let(bindings, inner) => {
                let bindings = bindings
                    .iter()
                    .map(|(name, value)| (name.clone(), self.apply(pool, value)))
                    .collect();
                let inner = self.apply(pool, inner);
                pool.add(Term::Let(BindingList(bindings), inner))
            }
            Term::Match(scrutinee, cases) => {
                let scrutinee = self.apply(pool, scrutinee);
                let cases = cases
                    .iter()
                    .map(|c| MatchCase { pattern: c.pattern.clone(), body: self.apply(pool, &c.body) })
                    .collect();
                pool.add(Term::Match(scrutinee, cases))
            }
            Term::ParamOp { op, op_args, args } => {
                let op_args = self.apply_all(pool, op_args);
                let args = self.apply_all(pool, args);
                pool.add(Term::ParamOp { op: op.clone(), op_args, args })
            }
            Term::AsOp(op, sort, args) => {
                let args = self.apply_all(pool, args);
                pool.add(Term::AsOp(op.clone(), sort.clone(), args))
            }
            Term::Const(_) | Term::Var(..) => term.clone(),
        };
        self.cache.insert(term.clone(), result.clone());
        result
    }

    fn apply_all(&mut self, pool: &mut PrimitivePool, terms: &[Rc<Term>]) -> Vec<Rc<Term>> {
        terms.iter().map(|t| self.apply(pool, t)).collect()
    }
}

/// Rewrites the non-canonical skolem terms of the proof to the `choice` terms the skolemization
/// rules expect.
pub fn canonicalize_skolems(pool: &mut PrimitivePool, proof: ProofNodeForest) -> ProofNodeForest {
    // Phase 1: the witnesses to rewrite, in terms of the original proof
    let mut map: IndexMap<Rc<Term>, Rc<Term>> = IndexMap::new();
    let proof = proof
        .mutate::<_, Infallible>(|context, node, _| {
            if let ProofNode::Subproof(sub) = node.as_ref() {
                if let ProofNode::Step(last) = sub.last_step.as_ref() {
                    let quant = match last.rule.as_str() {
                        "sko_forall" => Some(Binder::Forall),
                        "sko_ex" => Some(Binder::Exists),
                        _ => None,
                    };
                    if let Some(quant) = quant {
                        collect(pool, context, sub, last, quant, &mut map);
                    }
                }
            }
            Ok(node.clone())
        })
        .unwrap_or_else(|e| match e {});
    if map.is_empty() {
        return proof;
    }

    // A witness may contain the witness of an enclosing anchor, in either form: close the
    // replacements under the map, so that they mention canonical witnesses only
    for _ in 0..map.len() {
        let mut replacer = Replacer::new(map.clone());
        let mut changed = false;
        for i in 0..map.len() {
            let value = map[i].clone();
            let new_value = replacer.apply(pool, &value);
            if new_value != value {
                map[i] = new_value;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut subst = Replacer::new(map);

    // Phase 2: apply the substitution to every term of the proof
    proof
        .mutate::<_, Infallible>(|_, node, _| {
            Ok(match node.as_ref() {
                ProofNode::Assume { id, depth, term } => {
                    let new_term = subst.apply(pool, term);
                    if new_term == *term {
                        node.clone()
                    } else {
                        Rc::new(ProofNode::Assume { id: id.clone(), depth: *depth, term: new_term })
                    }
                }
                ProofNode::Step(s) => {
                    let clause: Vec<_> = s.clause.iter().map(|t| subst.apply(pool, t)).collect();
                    let args: Vec<_> = s.args.iter().map(|t| subst.apply(pool, t)).collect();
                    if clause == s.clause && args == s.args {
                        node.clone()
                    } else {
                        Rc::new(ProofNode::Step(StepNode { clause, args, ..s.clone() }))
                    }
                }
                ProofNode::Subproof(sub) => {
                    let args: Vec<_> = sub
                        .args
                        .iter()
                        .map(|arg| match arg {
                            AnchorArg::Assign(var, value) => {
                                AnchorArg::Assign(var.clone(), subst.apply(pool, value))
                            }
                            other => other.clone(),
                        })
                        .collect();
                    if args == sub.args {
                        node.clone()
                    } else {
                        Rc::new(ProofNode::Subproof(SubproofNode { args, ..sub.clone() }))
                    }
                }
            })
        })
        .unwrap_or_else(|e| match e {})
}

/// The witnesses of one skolemization anchor that differ from the expected `choice` terms, which
/// are built exactly as the checker builds them (the enclosing context applied to the body, then
/// the earlier bindings replaced by their canonical witnesses).
fn collect(
    pool: &mut PrimitivePool,
    context: &mut ContextStack,
    sub: &SubproofNode,
    last: &StepNode,
    quant: Binder,
    map: &mut IndexMap<Rc<Term>, Rc<Term>>,
) {
    let [conclusion] = last.clause.as_slice() else { return };
    let Some((left, _)) = match_term!((= l r) = conclusion) else { return };
    let Some((q, bindings, phi)) = left.as_quant() else { return };
    if q != quant {
        return;
    }
    let apply_map = |pool: &mut PrimitivePool, map: &IndexMap<Rc<Term>, Rc<Term>>, t: &Rc<Term>| {
        if map.is_empty() {
            return t.clone();
        }
        Replacer::new(map.clone()).apply(pool, t)
    };
    let mut current_phi = context.apply(pool, phi);
    current_phi = apply_map(pool, map, &current_phi);

    let assignments: Vec<(Rc<Term>, Rc<Term>)> = sub
        .args
        .iter()
        .filter_map(AnchorArg::as_assign)
        .map(|(k, v)| {
            let var = Term::new_var(k, pool.sort(v));
            (pool.add(var), v.clone())
        })
        .collect();

    let mut time = Duration::ZERO;
    for (i, x) in bindings.iter().enumerate() {
        let x_term = pool.add(Term::from(x.clone()));
        let witness = if assignments.len() == bindings.len() && assignments[i].0 == x_term {
            &assignments[i].1
        } else {
            match assignments.iter().find(|(var, _)| *var == x_term) {
                Some((_, t)) => t,
                None => return,
            }
        };
        let expected = {
            let mut inner = current_phi.clone();
            if i < bindings.len() - 1 {
                inner = pool.add(Term::Binder(
                    quant,
                    BindingList(bindings.0[i + 1..].to_vec()),
                    inner,
                ));
            }
            if quant == Binder::Forall {
                inner = build_term!(pool, (not { inner }));
            }
            pool.add(Term::Binder(Binder::Choice, BindingList(vec![x.clone()]), inner))
        };
        let current = apply_map(pool, map, witness);
        if current != expected {
            if !alpha_equiv(&current, &expected, &mut time) {
                // not a reordering: the checker rejects this anchor, nothing to canonicalize
                return;
            }
            map.insert(witness.clone(), expected.clone());
            if current != *witness {
                map.insert(current, expected.clone());
            }
        }
        let Ok(mut s) = Substitution::single(pool, x_term, expected) else { return };
        current_phi = s.apply(pool, &current_phi);
    }
}
