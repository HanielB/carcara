use crate::ast::*;
use indexmap::{map::Entry, IndexMap, IndexSet};
use std::collections::{hash_map, HashMap};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ResolutionError {
    #[error("couldn't find tautology in clause")]
    TautologyFailed,

    #[error("pivot was not eliminated: '{0}'")]
    RemainingPivot(Rc<Term>),

    #[error("term in conclusion was not produced by resolution: '{0}'")]
    ExtraTermInConclusion(Rc<Term>),

    #[error("term produced by resolution is missing in conclusion: '{0}'")]
    MissingTermInConclusion(Rc<Term>),

    #[error("pivot was not found in clause: '{0}'")]
    PivotNotFound(Rc<Term>),

    #[error("RUP resolution failed")]
    RupFailed,
}

pub type Literal<'a> = (u32, &'a Rc<Term>);

/// A collection that can be used as a clause during resolution.
pub trait ClauseCollection<'a>: FromIterator<Literal<'a>> {
    fn insert_term(&mut self, item: Literal<'a>);

    fn remove_term(&mut self, item: &Literal<'a>) -> bool;
}

impl<'a> ClauseCollection<'a> for Vec<Literal<'a>> {
    fn insert_term(&mut self, item: Literal<'a>) {
        self.push(item);
    }

    fn remove_term(&mut self, item: &Literal<'a>) -> bool {
        if let Some(pos) = self.iter().position(|x| x == item) {
            self.remove(pos);
            true
        } else {
            false
        }
    }
}

impl<'a> ClauseCollection<'a> for IndexSet<Literal<'a>> {
    fn insert_term(&mut self, item: Literal<'a>) {
        self.insert(item);
    }

    fn remove_term(&mut self, item: &Literal<'a>) -> bool {
        self.swap_remove(item)
    }
}

/// Transformas a `Literal` into an `Rc<Term>`, by undoing the transformation done by
/// `Rc<Term>::remove_all_negations`.
pub fn literal_to_term(pool: &mut dyn TermPool, (n, term): Literal) -> Rc<Term> {
    let mut term = term.clone();
    for _ in 0..n {
        term = build_term!(pool, (not { term }));
    }
    term
}

pub struct ResolutionTrace {
    pub not_not_added: bool,
    pub pivot_trace: Vec<(Rc<Term>, bool)>,
}

pub fn greedy_resolution(
    conclusion: &[Rc<Term>],
    premises: &[&[Rc<Term>]],
    pool: &mut dyn TermPool,
    tracing: bool,
) -> Result<ResolutionTrace, ResolutionError> {
    // If we are elaborating, we record which pivot was found for each binary resolution step, so we
    // can add them all as arguments later
    let mut pivot_trace = Vec::new();

    // When checking this rule, we must look at what the conclusion clause looks like in order to
    // determine the pivots. The reason for that is because there is no other way to know which
    // terms should be removed in a given binary resolution step. Consider the following example,
    // adapted from an actual generated proof:
    //
    //     (step t1 (cl (not q) (not (not p)) (not p)) :rule irrelevant)
    //     (step t2 (cl (not (not (not p))) p) :rule irrelevant)
    //     (step t3 (cl (not q) p (not p)) :rule resolution :premises (t1 t2))
    //
    // Without looking at the conclusion, it is unclear if the (not p) term should be removed by the
    // p term, or if the (not (not p)) should be removed by the (not (not (not p))). We can only
    // determine this by looking at the conclusion and using it to derive the pivots.
    let conclusion: IndexSet<_> = conclusion
        .iter()
        .map(Rc::remove_all_negations)
        .map(|(n, t)| (n as i32, t))
        .collect();

    // The working clause contains the terms from the conclusion clause that we already encountered
    let mut working_clause = IndexSet::new();

    // The pivots are the encountered terms that are not present in the conclusion clause, and so
    // should be removed. After being used to eliminate a term, a pivot can still be used to
    // eliminate other terms. Because of that, we represent the pivots as a hash map to a boolean,
    // which represents if the pivot was already eliminated or not. At the end, this boolean should
    // be true for all pivots
    let mut pivots = IndexMap::new();

    for &premise in premises {
        // Only one pivot may be eliminated per clause. This restriction is required so logically
        // unsound proofs like this one are not considered valid:
        //
        //     (step t1 (cl (= false true) (not false) (not true)) :rule equiv_neg1)
        //     (step t2 (cl (= false true) false true) :rule equiv_neg2)
        //     (step t3 (cl (= false true)) :rule resolution :premises (t1 t2))
        let mut eliminated_clause_pivot = false;

        // Pivots introduced by the current premise are buffered and only merged into the pivots
        // set after the premise is fully processed. This prevents a literal from being eliminated
        // against a pivot that came from the same premise, which is never a valid chain move: in a
        // resolution chain, each premise is resolved against the accumulated clause on a single
        // pivot, and the premise's literals never cancel each other. This matters when a clause
        // contains the same atom under different numbers of negations, e.g.
        //
        //     (step t1 (cl (not (not p)) (not (not (not p))) false) :rule hole)
        //     (step t2 (cl q (not p)) :rule hole)
        //     (step t3 (cl q (not (not p))) :rule hole)
        //     (step t4 (cl false q) :rule resolution :premises (t1 t2 t3))
        //
        // Without the buffer, the two stacked-negation literals in t1 would cancel each other,
        // deriving a bogus trace instead of the valid chain with pivots (not p) and (not (not p)).
        let mut new_pivots = Vec::new();
        for term in premise {
            let (n, inner) = term.remove_all_negations();
            let n = n as i32;

            // There are two possible negations of a term, with one leading negation added, or with
            // one leading negation removed (if the term had any in the first place)
            let below = (n - 1, inner);
            let above = (n + 1, inner);

            // First, if the encountered term should be in the conclusion, but is not yet in the
            // working clause, we insert it and don't try to remove it with a pivot
            if conclusion.contains(&(n, inner)) && !working_clause.contains(&(n, inner)) {
                working_clause.insert((n, inner));
                continue;
            }

            // If the negation of the encountered term is present in the pivots set, we simply
            // eliminate it. Otherwise, we insert the encountered term in the working clause or the
            // pivots set, depending on whether it is present in the conclusion clause or not
            let mut try_eliminate = |pivot| match pivots.entry(pivot) {
                Entry::Occupied(mut e) => {
                    e.insert(true);
                    true
                }
                Entry::Vacant(_) => false,
            };

            // Only one pivot may be eliminated per clause, so if we already found this clauses'
            // pivot, we don't try to eliminate the term. If we are elaborating, we add the pivot
            // found to the pivot trace.
            let eliminated = if eliminated_clause_pivot {
                false
            } else if try_eliminate(below) {
                if tracing {
                    pivot_trace.push((literal_to_term(pool, (n as u32 - 1, inner)), true));
                }
                true
            } else if try_eliminate(above) {
                if tracing {
                    pivot_trace.push((term.clone(), false));
                }
                true
            } else {
                false
            };

            if eliminated {
                eliminated_clause_pivot = true;
            } else if conclusion.contains(&(n, inner)) {
                working_clause.insert((n, inner));
            } else {
                // If the term is not in the conclusion clause, it must be a pivot. If it was
                // not already in the pivots set, we insert `false`, to indicate that it was
                // not yet eliminated. The insertion is deferred to the end of the premise so
                // this pivot cannot eliminate a literal of the same premise
                new_pivots.push((n, inner));
            }
        }
        for pivot in new_pivots {
            pivots.entry(pivot).or_insert(false);
        }
    }

    // There are some special cases in the resolution rules that are valid, but leave a pivot
    // remaining
    let mut remaining_pivots = pivots.iter().filter(|&(_, eliminated)| !eliminated);

    if let Some(((i, pivot), _)) = remaining_pivots.next() {
        if remaining_pivots.next().is_none() {
            // There is a special case in the resolution rules that is valid, but leaves a pivot
            // remaining: when the result of the resolution is just the boolean constant `false`, it
            // may be implicitly eliminated. For example:
            //     (step t1 (cl p q false) :rule hole)
            //     (step t2 (cl (not p)) :rule hole)
            //     (step t3 (cl (not q)) :rule hole)
            //     (step t4 (cl) :rule resolution :premises (t1 t2 t3))
            if conclusion.is_empty() && *i == 0 && pivot.is_bool_false() {
                return Ok(ResolutionTrace { not_not_added: false, pivot_trace });
            }

            // There is another, similar, special case: when the result of the resolution is just
            // one term, it may appear in the conclusion clause with an even number of leading
            // negations added to it. The following is an example of this, adapted from a generated
            // proof:
            //     (step t1 (cl (not e)) :rule hole)
            //     (step t2 (cl (= (not e) (not (not f)))) :rule hole)
            //     (step t3 (cl (not (= (not e) (not (not f)))) e f) :rule hole)
            //     (step t4 (cl (not (not f))) :rule resolution :premises (t1 t2 t3))
            // Usually, we would expect the clause in the t4 step to be (cl f). This behavior may
            // be a bug in veriT, but it is still logically sound and happens often enough that it
            // is useful to support it here.
            if conclusion.len() == 1 {
                let (j, conclusion) = conclusion.into_iter().next().unwrap();
                if conclusion == *pivot && (i % 2) == (j % 2) {
                    return Ok(ResolutionTrace { not_not_added: true, pivot_trace });
                }
            }
        }
        let pivot = literal_to_term(pool, (*i as u32, pivot));
        Err(ResolutionError::RemainingPivot(pivot))
    } else {
        // This is the general case, where all pivots have been eliminated. In this case, the
        // working clause should be equal to the conclusion clause
        for (i, t) in conclusion {
            // By construction, the working clause is a subset of the conclusion. Therefore, we
            // only need to check that all terms in the conclusion are also in the working clause
            if !working_clause.contains(&(i, t)) {
                let t = literal_to_term(pool, (i as u32, t));
                return Err(ResolutionError::ExtraTermInConclusion(t));
            }
        }
        Ok(ResolutionTrace { not_not_added: false, pivot_trace })
    }
}

/// Checks that a pivot trace produced by pivot inference actually replays as a left-to-right
/// resolution chain (under the set semantics of `resolution_with_args`) concluding exactly the
/// given conclusion.
///
/// This catches the configurations that `greedy_resolution` accepts but that are not valid
/// ordered chains — e.g. a premise re-introducing a literal *after* the premise that eliminated
/// it, which the greedy algorithm absorbs by marking the pivot as still eliminated.
pub fn set_replay_valid(
    conclusion: &[Rc<Term>],
    premises: &[&[Rc<Term>]],
    pivot_trace: &[(Rc<Term>, bool)],
) -> bool {
    if premises.len() != pivot_trace.len() + 1 {
        return false;
    }
    let mut current: IndexSet<Literal> = premises[0].iter().map(Rc::remove_all_negations).collect();
    for (premise, (pivot, polarity)) in premises[1..].iter().zip(pivot_trace) {
        let pivot = pivot.remove_all_negations();
        let negated_pivot = (pivot.0 + 1, pivot.1);
        let (pivot_in_current, pivot_in_next) = if *polarity {
            (pivot, negated_pivot)
        } else {
            (negated_pivot, pivot)
        };
        if !current.swap_remove(&pivot_in_current) {
            return false;
        }
        let mut found = false;
        for t in *premise {
            let t = t.remove_all_negations();
            if !found && t == pivot_in_next {
                found = true;
            } else {
                current.insert(t);
            }
        }
        if !found {
            return false;
        }
    }
    let conclusion: IndexSet<Literal> = conclusion.iter().map(Rc::remove_all_negations).collect();
    current == conclusion
}

/// A valid ordered resolution chain reconstructed from a RUP certificate.
pub struct RupChain {
    /// Indices into the original premise list, in chain order. May be a subset of the premises,
    /// and is never empty when the reconstruction succeeds.
    pub order: Vec<usize>,

    /// The pivot arguments for the chain, aligned with `order[1..]`, in the convention of
    /// elaborated `resolution` steps.
    pub pivots: Vec<(Rc<Term>, bool)>,

    /// The clause the chain concludes: a subset of the target conclusion (as a set).
    pub final_clause: Vec<Rc<Term>>,
}

/// Reconstructs a valid ordered resolution chain for a step that is RUP-valid but has no valid
/// chain in its given premise order.
///
/// Unit propagation runs over the premises starting from the negated conclusion, recording the
/// reason clause of each propagation; conflict analysis then resolves the conflict clause with
/// the reasons in reverse propagation order. By construction each pivot, once eliminated, cannot
/// be re-introduced by a later premise of the chain, so the result replays both under set and
/// (after uncrowding) multiset semantics. Only proofs whose literals carry at most one negation
/// are handled — stacked negations make chain adjacency ambiguous, and don't occur in the
/// proofs this fallback targets.
pub fn rup_chain(
    conclusion: &[Rc<Term>],
    premises: &[&[Rc<Term>]],
    pool: &mut dyn TermPool,
) -> Option<RupChain> {
    type Lit<'a> = (bool, &'a Rc<Term>); // (positive?, atom)

    fn lit(t: &Rc<Term>) -> Option<(bool, &Rc<Term>)> {
        let (n, inner) = t.remove_all_negations();
        match n {
            0 => Some((true, inner)),
            1 => Some((false, inner)),
            _ => None,
        }
    }

    let clauses: Vec<Vec<Lit>> = premises
        .iter()
        .map(|clause| clause.iter().map(lit).collect::<Option<Vec<_>>>())
        .collect::<Option<Vec<_>>>()?;
    let conclusion_lits: Vec<Lit> = conclusion.iter().map(lit).collect::<Option<Vec<_>>>()?;

    // Assign the negation of every conclusion literal. If the conclusion is a tautology, this
    // fallback does not apply.
    let mut assignment: HashMap<&Rc<Term>, bool> = HashMap::new();
    for (positive, atom) in &conclusion_lits {
        match assignment.entry(atom) {
            hash_map::Entry::Occupied(e) if *e.get() == *positive => return None,
            hash_map::Entry::Occupied(_) => (),
            hash_map::Entry::Vacant(e) => {
                e.insert(!positive);
            }
        }
    }

    // Unit propagation, recording the trail of (atom, reason clause index)
    let mut trail: Vec<(&Rc<Term>, usize)> = Vec::new();
    let mut used_as_reason = vec![false; clauses.len()];
    let conflict = 'propagation: loop {
        let mut progressed = false;
        for (i, clause) in clauses.iter().enumerate() {
            if used_as_reason[i] {
                continue;
            }
            let mut unassigned = None;
            let mut satisfied = false;
            let mut num_unassigned = 0;
            for &(positive, atom) in clause {
                match assignment.get(atom) {
                    Some(&value) if value == positive => {
                        satisfied = true;
                        break;
                    }
                    Some(_) => (),
                    None => {
                        num_unassigned += 1;
                        unassigned = Some((positive, atom));
                    }
                }
            }
            if satisfied {
                continue;
            }
            match num_unassigned {
                0 => break 'propagation i, // conflict
                1 => {
                    let (positive, atom) = unassigned.unwrap();
                    assignment.insert(atom, positive);
                    trail.push((atom, i));
                    used_as_reason[i] = true;
                    progressed = true;
                }
                _ => (),
            }
        }
        if !progressed {
            return None; // no conflict reachable: the step is not RUP-valid
        }
    };

    // Conflict analysis: resolve the conflict clause with the reasons, in reverse propagation
    // order, eliminating each propagated literal present in the current clause
    let mut order = vec![conflict];
    let mut pivots = Vec::new();
    let mut current: IndexSet<Lit> = clauses[conflict].iter().copied().collect();
    for &(atom, reason) in trail.iter().rev() {
        if reason == conflict {
            continue;
        }
        // The current clause contains the *negation* of the propagated literal, if anything
        let value = assignment[atom];
        let falsified = (!value, atom);
        if !current.swap_remove(&falsified) {
            continue;
        }
        let propagated = (value, atom);
        for &l in &clauses[reason] {
            if l != propagated {
                current.insert(l);
            }
        }
        order.push(reason);
        // In the convention of elaborated resolution steps, the pivot argument is the literal as
        // it occurs in the accumulated clause when its polarity flag is `true`
        let (pivot, polarity) = if value {
            // `atom` occurs positively in the reason (the next premise), negatively in current
            (atom.clone(), false)
        } else {
            (atom.clone(), true)
        };
        pivots.push((pivot, polarity));
    }

    if order.len() < 2 {
        return None;
    }

    // The remaining literals are all falsified by the initial assumptions, so they form a subset
    // of the conclusion
    let final_clause = current
        .into_iter()
        .map(|(positive, atom)| {
            if positive {
                atom.clone()
            } else {
                build_term!(pool, (not { atom.clone() }))
            }
        })
        .collect();

    Some(RupChain { order, pivots, final_clause })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::pool::PrimitivePool;
    use crate::parser::tests::parse_terms;

    /// A pattern produced by cvc5 when it refutes the contradictory conjunction `(and (not p)
    /// (not (not p)))` via a subproof: the same atom occurs under one, two, and three negations.
    /// The step is a valid left-to-right chain with pivots `(not p)` and `(not (not p))`, but a
    /// greedy algorithm that allows a pivot to eliminate a literal of its own premise instead
    /// cancels the two stacked-negation literals of the first premise against each other,
    /// producing a trace that does not replay as a chain.
    #[test]
    fn stacked_negations_within_a_premise() {
        let mut pool = PrimitivePool::new();
        let definitions = "(declare-fun p () Bool)";
        let [nnp, nnnp, false_, na, np] = parse_terms(
            &mut pool,
            definitions,
            [
                "(not (not p))",
                "(not (not (not p)))",
                "false",
                "(not (and (not p) (not (not p))))",
                "(not p)",
            ],
        );

        let premises: [&[Rc<Term>]; 3] = [
            &[nnp.clone(), nnnp, false_.clone()],
            &[na.clone(), np],
            &[na.clone(), nnp],
        ];
        let conclusion = [false_, na.clone(), na];

        let trace = greedy_resolution(&conclusion, &premises, &mut pool, true)
            .expect("greedy resolution failed");
        assert!(!trace.not_not_added);
        assert!(
            set_replay_valid(&conclusion, &premises, &trace.pivot_trace),
            "greedy trace does not replay as a valid chain"
        );
    }
}
