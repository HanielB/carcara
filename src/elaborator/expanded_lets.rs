//! `let` steps under `--expand-let-bindings`.
//!
//! When the parser expands `let` bindings, a `let` step's conclusion `(= (let ((x t)) u) u')`
//! arrives as `(= u[t/x] u')`, and the steps of its subproof — which spell out the substitution
//! of the bound names, in terms of the anchor's context variables — no longer match the terms
//! the parser produced, because every name they mention that was defined under the `let` (a
//! `:named` term, say) already denotes its expansion. The subproof is pointless once `let`s are
//! expanded: the conclusion holds by reflexivity, modulo the context of the enclosing anchors.
//!
//! This pass replaces every subproof closed by a `let` step whose conclusion is reflexive in that
//! sense by a `refl` step with the same id and conclusion, so that neither the checker nor the
//! elaborator sees a `let` step (or has to produce a `bind_let` step). A `let` step whose two
//! sides genuinely differ is left alone.

use crate::ast::*;
use std::time::Duration;

/// Replaces the `let` subproofs of `proof` whose conclusion is reflexive (modulo the enclosing
/// context) by `refl` steps. Returns the number of subproofs replaced and the number of `let`
/// steps left as they were.
pub fn trivialize_let_steps(pool: &mut dyn TermPool, proof: &mut Proof) -> (usize, usize) {
    let mut context = ContextStack::new();
    let mut counts = (0, 0);
    trivialize_commands(pool, &mut context, &mut proof.commands, &mut counts);
    counts
}

fn trivialize_commands(
    pool: &mut dyn TermPool,
    context: &mut ContextStack,
    commands: &mut [ProofCommand],
    counts: &mut (usize, usize),
) {
    for command in commands.iter_mut() {
        let ProofCommand::Subproof(sub) = command else { continue };
        if let Some(ProofCommand::Step(last)) = sub.commands.last() {
            if last.rule == "let" {
                if let [conclusion] = last.clause.as_slice() {
                    if let Some((a, b)) = match_term!((= a b) = conclusion) {
                        if refl_holds(pool, context, a, b) {
                            *command = ProofCommand::Step(ProofStep {
                                id: last.id.clone(),
                                clause: last.clause.clone(),
                                rule: "refl".to_owned(),
                                premises: Vec::new(),
                                args: Vec::new(),
                                discharge: Vec::new(),
                            });
                            counts.0 += 1;
                            continue;
                        }
                    }
                }
                counts.1 += 1;
            }
        }
        context.push(&sub.args);
        trivialize_commands(pool, context, &mut sub.commands, counts);
        context.pop();
    }
}

/// Whether `(= a b)` is accepted by the `refl` rule in the given context.
fn refl_holds(pool: &mut dyn TermPool, context: &mut ContextStack, a: &Rc<Term>, b: &Rc<Term>) -> bool {
    let mut time = Duration::ZERO;
    if alpha_equiv(a, b, &mut time) {
        return true;
    }
    if context.is_empty() {
        return false;
    }
    let new_a = context.apply(pool, a);
    alpha_equiv(&new_a, b, &mut time) || {
        let new_b = context.apply(pool, b);
        alpha_equiv(a, &new_b, &mut time) || alpha_equiv(&new_a, &new_b, &mut time)
    }
}
