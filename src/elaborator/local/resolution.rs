use crate::{
    ast::{
        ContextStack, ProofNode, Rc, StepNode, Term, build_term, match_term,
        pool::{PrimitivePool, TermPool},
    },
    elaborator::{ElaborationError, IdHelper},
    resolution::{
        ResolutionError, ResolutionTrace, greedy_resolution, rup_chain, set_replay_valid,
    },
    utils::DedupIterator,
};

pub fn resolution(
    pool: &mut PrimitivePool,
    _: &mut ContextStack,
    step: &StepNode,
) -> Result<Rc<ProofNode>, ElaborationError> {
    if !step.args.is_empty() {
        return Ok(Rc::new(ProofNode::Step(step.clone())));
    }

    let mut ids = IdHelper::new(&step.id);

    // In the cases where the rule is used to get an empty clause from `(not true)`, we add a `true`
    // step to get an actual resolution step
    if step.clause.is_empty()
        && step.premises.len() == 1
        && let [t] = step.premises[0].clause()
        && match_term!((not true) = t).is_some()
    {
        let true_step = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![pool.bool_true()],
            rule: "true".to_owned(),
            ..Default::default()
        }));

        return Ok(Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: Vec::new(),
            rule: "resolution".to_owned(),
            premises: vec![step.premises[0].clone(), true_step],
            args: [true, false].map(|a| pool.bool_constant(a)).to_vec(),
            ..Default::default()
        })));
    }

    // In some cases, due to a bug in veriT, a resolution step will conclude the empty clause, and
    // will have multiple premises, of which one has an empty clause as its conclusion. The checker
    // can already deal with this case safely, but not the elaborator, so if we detect it we skip
    // elaborating this step. Either way, since this step has a premise which concludes the empty
    // clause, it is not actually necessary, and will be pruned during post-processing.
    if step.clause.is_empty() {
        for p in &step.premises {
            if p.clause().is_empty() {
                return Ok(Rc::new(ProofNode::Step(step.clone())));
            }
        }
    }

    let mut premises: Vec<_> = step.premises.iter().dedup().cloned().collect();

    // The greedy algorithm can accept configurations that are not valid ordered chains (e.g. a
    // premise re-introducing a literal after its eliminator), so we validate its trace by
    // replaying it, and fall back to reconstructing a chain from the RUP certificate when the
    // trace does not replay
    let verified_greedy = |premises: &[Rc<ProofNode>], pool: &mut PrimitivePool| {
        let premise_clauses: Vec<_> = premises.iter().map(|p| p.clause()).collect();
        let trace = greedy_resolution(&step.clause, &premise_clauses, pool, true)?;
        if trace.not_not_added
            || set_replay_valid(&step.clause, &premise_clauses, &trace.pivot_trace)
        {
            Ok(trace)
        } else {
            Err(ResolutionError::RupFailed)
        }
    };

    let greedy = verified_greedy(&premises, pool).or_else(|first_error| {
        premises.reverse();
        let result = verified_greedy(&premises, pool);
        if result.is_err() {
            premises.reverse();
        }
        result.map_err(|_| first_error) // we prefer returning the first error
    });

    let (premises, ResolutionTrace { not_not_added, pivot_trace }) = match greedy {
        Ok(trace) => (premises, trace),
        Err(first_error) => {
            let premise_clauses: Vec<_> = premises.iter().map(|p| p.clause()).collect();
            if let Some(chain) = rup_chain(&step.clause, &premise_clauses, pool) {
                return Ok(build_rup_chain_step(pool, step, &premises, chain, &mut ids));
            }

            // The chain may exist only modulo double negation: reduce the stacked negations
            // and infer it over the reduced premises, by the same two routes
            if let Some(reduced) = reduce_stacked_negations(pool, step, &premises, &mut ids) {
                match verified_greedy(&reduced, pool) {
                    Ok(trace) => (reduced, trace),
                    Err(_) => {
                        let reduced_clauses: Vec<_> = reduced.iter().map(|p| p.clause()).collect();
                        let Some(chain) = rup_chain(&step.clause, &reduced_clauses, pool) else {
                            log::warn!(
                                "resolution '{}': could not infer pivots ({}), keeping step",
                                step.id,
                                first_error
                            );
                            return Ok(Rc::new(ProofNode::Step(step.clone())));
                        };
                        return Ok(build_rup_chain_step(pool, step, &reduced, chain, &mut ids));
                    }
                }
            } else {
                // Neither the greedy inference nor a RUP certificate yields a chain for this
                // step. Keeping it is much better than failing the whole elaboration, which
                // would throw away an otherwise perfectly checkable proof: the `resolution`
                // checker itself falls back to RUP, so the step still checks, and a consumer
                // that wants the pivots can search for them per link as it always could. The
                // steps this happens on are the ones whose chain the greedy algorithm cannot
                // order --- typically a premise that is a tautology `(cl p (not p))`, whose two
                // literals both become pivots and leave the wrong one un-eliminated.
                log::warn!(
                    "resolution '{}': could not infer pivots ({}), keeping step",
                    step.id,
                    first_error
                );
                return Ok(Rc::new(ProofNode::Step(step.clone())));
            }
        }
    };

    let pivots = pivot_trace
        .into_iter()
        .flat_map(|(pivot, polarity)| [pivot, pool.bool_constant(polarity)])
        .collect();

    let mut resolution_step = StepNode {
        id: step.id.clone(),
        depth: step.depth,
        clause: step.clause.clone(),
        rule: "resolution".to_owned(),
        premises,
        args: pivots,
        ..Default::default()
    };

    if not_not_added {
        // In this case, where the solver added a double negation implicitly to the concluded term,
        // we remove it from the resolution conclusion, and then add a series of steps to
        // reconstruct it again. More precisely, if the conclusion of the resolution step should
        // have been `c`, but was instead `(not (not c))`, we will have:
        //
        // ```
        // (step t1 (cl (not (not c))) :rule resolution :premises ...)
        // ```
        //
        // which will become:
        //
        // ```
        // (step t1 (cl c) :rule resolution :premises ...)
        // (step t1.t2 (cl (not (not (not (not c)))) (not c)) :rule not_not)
        // (step t1.t3 (cl (not (not (not (not (not c))))) (not (not c))) :rule not_not)
        // (step t1.t4 (cl (not (not c))) :rule resolution :premises (t1 t1.t2 t1.t3)
        //     :args (c true (not (not (not (not c)))) true))
        // ```

        assert!(resolution_step.clause.len() == 1);
        let original_conclusion = resolution_step.clause;
        let double_not_c = original_conclusion[0].clone();
        let single_not_c = double_not_c.remove_negation().unwrap().clone();
        let c = single_not_c.remove_negation().unwrap().clone();
        let quadruple_not_c = build_term!(pool, (not (not {double_not_c.clone()})));
        let quintuple_not_c = build_term!(pool, (not {quadruple_not_c.clone()}));

        // First, we change the conclusion of the resolution step
        resolution_step.clause = vec![c.clone()];
        let resolution_step = Rc::new(ProofNode::Step(resolution_step));

        // Then we add the two `not_not` steps
        let first_not_not_step = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![quadruple_not_c.clone(), single_not_c],
            rule: "not_not".to_owned(),
            ..Default::default()
        }));

        let second_not_not_step = Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![quintuple_not_c, double_not_c.clone()],
            rule: "not_not".to_owned(),
            ..Default::default()
        }));

        // Finally, we add a new resolution step, referring to the previous three, and concluding
        // the original resolution step's conclusion
        let args = [c, pool.bool_true(), quadruple_not_c, pool.bool_true()]
            .into_iter()
            .collect();

        Ok(Rc::new(ProofNode::Step(StepNode {
            id: ids.next_id(),
            depth: step.depth,
            clause: vec![double_not_c],
            rule: "resolution".to_owned(),
            premises: vec![resolution_step, first_not_not_step, second_not_not_step],
            args,
            ..Default::default()
        })))
    } else {
        Ok(Rc::new(ProofNode::Step(resolution_step)))
    }
}

/// Builds the replacement for a resolution step from a chain reconstructed by [`rup_chain`]: the
/// premises are reordered (and possibly pruned) to the chain order, and, when the chain concludes
/// a proper subset of the target clause, `weakening` and `reordering` steps restore it.
fn build_rup_chain_step(
    pool: &mut PrimitivePool,
    step: &StepNode,
    premises: &[Rc<ProofNode>],
    chain: crate::resolution::RupChain,
    ids: &mut IdHelper,
) -> Rc<ProofNode> {
    use std::collections::HashSet;

    let chain_premises: Vec<_> = chain.order.iter().map(|&i| premises[i].clone()).collect();
    let args: Vec<_> = chain
        .pivots
        .iter()
        .flat_map(|(pivot, polarity)| [pivot.clone(), pool.bool_constant(*polarity)])
        .collect();

    // A chain of one premise resolves nothing: the conclusion is that premise, or a weakening of
    // it. If it is the premise verbatim, the step goes and its consumers use the premise, as
    // `remove_reorderings` does with a reordering; otherwise the weakening is written directly
    // over the premise, and no resolution step at all.
    if let [i] = chain.order[..] {
        let premise = premises[i].clone();
        let clause = premise.clause().to_vec();
        if clause == step.clause {
            return premise;
        }
        return restore_clause(step, premise, clause, ids);
    }

    let final_set: HashSet<_> = chain.final_clause.iter().cloned().collect();
    let target_set: HashSet<_> = step.clause.iter().cloned().collect();

    if final_set == target_set {
        return Rc::new(ProofNode::Step(StepNode {
            id: step.id.clone(),
            depth: step.depth,
            clause: step.clause.clone(),
            rule: "resolution".to_owned(),
            premises: chain_premises,
            args,
            ..Default::default()
        }));
    }

    // The chain concludes a proper subset of the target: weaken, then restore the original order
    let resolution_step = Rc::new(ProofNode::Step(StepNode {
        id: ids.next_id(),
        depth: step.depth,
        clause: chain.final_clause.clone(),
        rule: "resolution".to_owned(),
        premises: chain_premises,
        args,
        ..Default::default()
    }));
    restore_clause(step, resolution_step, chain.final_clause, ids)
}

/// The target clause of `step` from `base`, which concludes `base_clause`, a subset of the target
/// as a set: a `weakening` for the literals the base lacks, and a `reordering` when the order
/// still differs. Whichever step concludes the target carries the original id.
fn restore_clause(
    step: &StepNode,
    base: Rc<ProofNode>,
    base_clause: Vec<Rc<Term>>,
    ids: &mut IdHelper,
) -> Rc<ProofNode> {
    use std::collections::HashSet;

    let base_set: HashSet<_> = base_clause.iter().cloned().collect();
    let missing: Vec<_> = step
        .clause
        .iter()
        .filter(|t| !base_set.contains(t))
        .cloned()
        .collect();

    let (node, clause) = if missing.is_empty() {
        (base, base_clause)
    } else {
        let mut weakened = base_clause;
        weakened.extend(missing);
        let id = if weakened == step.clause {
            step.id.clone()
        } else {
            ids.next_id()
        };
        let weakening_step = Rc::new(ProofNode::Step(StepNode {
            id,
            depth: step.depth,
            clause: weakened.clone(),
            rule: "weakening".to_owned(),
            premises: vec![base],
            ..Default::default()
        }));
        (weakening_step, weakened)
    };

    if clause == step.clause {
        return node;
    }
    Rc::new(ProofNode::Step(StepNode {
        id: step.id.clone(),
        depth: step.depth,
        clause: step.clause.clone(),
        rule: "reordering".to_owned(),
        premises: vec![node],
        ..Default::default()
    }))
}

/// A solver whose SAT-level literals identify `(not (not p))` with `p` writes chains in which one
/// `(not p)` eliminates both, or in which a premise carries the pivot under two more negations
/// than the literal that eliminates it. cvc5 does this on the QF_UF hardware benchmarks. Neither
/// is a chain over Alethe's syntactic literals, so pivot inference fails, though the step is
/// valid: the gap is exactly a double negation. This reduces every premise literal carrying two
/// or more negations that the conclusion does not keep, by a `not_not` step and a binary
/// resolution on that literal, so that the chain can be inferred over the reduced premises.
/// Returns `None` when there was nothing to reduce.
fn reduce_stacked_negations(
    pool: &mut PrimitivePool,
    step: &StepNode,
    premises: &[Rc<ProofNode>],
    ids: &mut IdHelper,
) -> Option<Vec<Rc<ProofNode>>> {
    let mut reduced = Vec::with_capacity(premises.len());
    let mut changed = false;
    for premise in premises {
        let mut node = premise.clone();
        loop {
            let clause = node.clause();
            let Some(i) = clause
                .iter()
                .position(|l| l.remove_all_negations().0 >= 2 && !step.clause.contains(l))
            else {
                break;
            };
            let lit = clause[i].clone();
            let inner = lit
                .remove_negation()
                .unwrap()
                .remove_negation()
                .unwrap()
                .clone();
            let not_lit = build_term!(pool, (not { lit.clone() }));

            // `(cl (not (not (not t))) t)`, which resolved against the premise on the literal
            // `(not (not t))` replaces that literal by `t`
            let not_not_step = Rc::new(ProofNode::Step(StepNode {
                id: ids.next_id(),
                depth: step.depth,
                clause: vec![not_lit, inner.clone()],
                rule: "not_not".to_owned(),
                ..Default::default()
            }));
            let mut new_clause: Vec<_> = clause.to_vec();
            if new_clause.contains(&inner) {
                new_clause.remove(i);
            } else {
                new_clause[i] = inner;
            }
            node = Rc::new(ProofNode::Step(StepNode {
                id: ids.next_id(),
                depth: step.depth,
                clause: new_clause,
                rule: "resolution".to_owned(),
                premises: vec![node, not_not_step],
                args: vec![lit, pool.bool_true()],
                ..Default::default()
            }));
            changed = true;
        }
        reduced.push(node);
    }
    changed.then_some(reduced)
}
