//! Cross-step sharing of the derivations that the `core` pass emits.
//!
//! Reduction recipes are local: each one turns a single step into a derivation, and two steps with
//! the same conclusion get two copies of the same derivation. On solver output this is expensive —
//! on cvc5's arithmetic proofs, 72% of the `poly_simp_rel` instances are literal duplicates of an
//! earlier one — and the duplication is almost entirely *across* subproofs, so it cannot be removed
//! by anything that stays inside one scope.
//!
//! This module memoizes derivations by their conclusion and emits each distinct one once, at depth
//! 0, where every use can see it. A step whose derivation was already emitted is simply replaced by
//! the node that was emitted for it; since premises are pointers in a [`ProofNodeForest`], the
//! steps that referred to the replaced step now refer to the shared derivation, and a use from
//! inside a subproof becomes an ordinary outbound premise.
//!
//! Hoisting a derivation out of its subproof is only sound if the derivation does not depend on
//! anything that subproof provides, so [`Sharing`] only shares a derivation that is
//!
//! - *self-contained*: every node reachable from its conclusion is a step at the depth of the step
//!   being elaborated, with no `:discharge` and no implicit premise, so its leaves are premise-free
//!   steps and no assumption, no step of an enclosing scope, and no subproof is involved;
//! - *context-free*: no term it mentions has a free variable bound by an anchor in scope, so that
//!   checking it outside those anchors is the same problem as checking it inside them.
//!
//! A self-contained derivation proves its conclusion on its own, which is what makes the conclusion
//! a complete key: two self-contained derivations of the same clause are interchangeable, whatever
//! the steps they were built from. Note that self-containedness is a property of the *derivation*,
//! not of the rule: when a recipe uses the premises of the step it is reducing (as
//! `poly_simp_rel`'s does when no premise-free Farkas certificate exists), the premise shows up as
//! a reachable node and, if it is a premise-free step of the same depth, it is copied into the
//! shared derivation like any other node. If it is an assumption, a step of an enclosing scope, or
//! a subproof, the derivation is not shared at all.
//!
//! Copying a step that was already in the proof is the one case where hoisting costs something, so
//! it is only done once a second step asks for the same derivation, and sharing never makes a proof
//! larger than the unshared pass would have.

use crate::ast::*;
use std::collections::{HashMap, HashSet};

/// What the memo holds for a conclusion that has been derived at least once.
enum Entry {
    /// A derivation that is available for reuse, because it is at depth 0.
    Shared(Rc<ProofNode>),

    /// A derivation that was emitted inside a subproof, and that hoisting would have to copy a step
    /// of the proof into: it is kept aside, and only hoisted if a second step needs it.
    Pending(Vec<Rc<ProofNode>>),
}

/// A memo of the derivations emitted by the `core` pass, keyed by their conclusion.
pub struct Sharing {
    /// The derivations emitted so far, keyed by their conclusion clause.
    cache: HashMap<Vec<Rc<Term>>, Entry>,

    /// The prefix of the ids given to hoisted steps. It is chosen so that it is not a prefix of any
    /// id already in the proof, which makes the hoisted ids unique, and also keeps the ids that
    /// later passes derive from them (by appending to them) unique.
    prefix: String,

    /// The number of hoisted steps emitted so far, which is also the next id to use.
    emitted: usize,

    /// The ids of the steps that are the implicit premise of a subproof's last step. Those steps
    /// are referred to by their position in the subproof, so they cannot be hoisted out of it.
    implicit_premises: HashSet<String>,

    /// The number of steps that sharing removed, for logging.
    saved: usize,
}

impl Sharing {
    /// Prepares to share derivations in the given proof: picks an id namespace that is free in it,
    /// and collects the steps that cannot be moved out of their subproof.
    pub fn new(proof: &ProofNodeForest) -> Self {
        let mut ids: Vec<&str> = Vec::new();
        let mut implicit_premises = HashSet::new();
        for node in visit_all(proof) {
            ids.push(node.id());
            if let ProofNode::Step(s) = node.as_ref() {
                if let Some(previous) = &s.previous_step {
                    implicit_premises.insert(previous.id().to_owned());
                }
            }
        }

        let mut prefix = String::from("sh");
        while ids.iter().any(|id| id.starts_with(&prefix)) {
            prefix.push('_');
        }

        Self {
            cache: HashMap::new(),
            prefix,
            emitted: 0,
            implicit_premises,
            saved: 0,
        }
    }

    /// The number of steps that sharing removed from the proof.
    pub fn saved(&self) -> usize {
        self.saved
    }

    /// Given the derivation a recipe emitted for `step`, returns the derivation to actually use:
    /// either the one already emitted for an earlier step with the same conclusion, or `node`
    /// itself, hoisted to depth 0 and recorded for later steps.
    ///
    /// If the derivation cannot be shared, `node` is returned unchanged, and the pass behaves
    /// exactly as it did before.
    pub fn share(
        &mut self,
        pool: &mut PrimitivePool,
        context: &ContextStack,
        step: &StepNode,
        node: Rc<ProofNode>,
    ) -> Rc<ProofNode> {
        // A step with a `:discharge` or an implicit premise closes a subproof, and one that is the
        // implicit premise of such a step is referred to by its position inside it: neither can
        // leave its scope
        if !step.discharge.is_empty()
            || step.previous_step.is_some()
            || self.implicit_premises.contains(&step.id)
        {
            return node;
        }

        let Some(derivation) = self_contained(&node, step.depth) else {
            return node;
        };
        if !context_free(pool, context, &derivation) {
            return node;
        }

        match self.cache.get(&step.clause) {
            Some(Entry::Shared(shared)) => {
                let shared = shared.clone();
                self.saved += derivation.len();
                return shared;
            }
            Some(Entry::Pending(pending)) => {
                // The second step to need this derivation makes hoisting it worthwhile: from here
                // on there is one copy at depth 0 instead of one copy per step
                let pending = pending.clone();
                let shared = self.hoist(&pending);
                self.cache
                    .insert(step.clause.clone(), Entry::Shared(shared.clone()));
                return shared;
            }
            None => (),
        }

        // A derivation already at depth 0 is reused as it is: it is visible from everywhere, and
        // keeping it avoids renumbering the steps of proofs that have no subproofs at all. One
        // inside a subproof has to be copied out, which is free only if the copy does not duplicate
        // a step that was already in the proof — that is, if the recipe did not use the premises of
        // the step it reduced. When it did, the derivation is only hoisted once a second step needs
        // it, so that sharing never makes a proof larger than it would have been
        let entry = if step.depth == 0 {
            Entry::Shared(node.clone())
        } else if step.premises.iter().any(|p| derivation.contains(p)) {
            Entry::Pending(derivation)
        } else {
            Entry::Shared(self.hoist(&derivation))
        };
        let node = match &entry {
            Entry::Shared(shared) => shared.clone(),
            Entry::Pending(_) => node,
        };
        self.cache.insert(step.clause.clone(), entry);
        node
    }

    fn next_id(&mut self) -> String {
        self.emitted += 1;
        format!("{}{}", self.prefix, self.emitted)
    }

    /// Rebuilds a derivation at depth 0, with fresh ids. The derivation is given in postorder, so
    /// every premise of a step has already been rebuilt when the step is reached.
    fn hoist(&mut self, derivation: &[Rc<ProofNode>]) -> Rc<ProofNode> {
        let mut hoisted: HashMap<&Rc<ProofNode>, Rc<ProofNode>> = HashMap::new();
        for node in derivation {
            let s = node.as_step().expect("derivation node must be a step");
            let premises = s.premises.iter().map(|p| hoisted[p].clone()).collect();
            let id = self.next_id();
            let new_node = Rc::new(ProofNode::Step(StepNode {
                id,
                depth: 0,
                clause: s.clause.clone(),
                rule: s.rule.clone(),
                premises,
                args: s.args.clone(),
                discharge: Vec::new(),
                previous_step: None,
            }));
            hoisted.insert(node, new_node);
        }
        hoisted[derivation.last().unwrap()].clone()
    }
}

/// Returns the nodes of `root`'s derivation in postorder, if it is self-contained: if every node
/// reachable from it is a step at depth `depth` with no `:discharge` and no implicit premise.
///
/// Such a derivation refers to nothing outside itself — its leaves are premise-free steps — so it
/// can be rebuilt anywhere.
fn self_contained(root: &Rc<ProofNode>, depth: usize) -> Option<Vec<Rc<ProofNode>>> {
    let mut order = Vec::new();
    let mut done: HashSet<Rc<ProofNode>> = HashSet::new();
    let mut todo = vec![(root.clone(), false)];
    while let Some((node, is_done)) = todo.pop() {
        if done.contains(&node) {
            continue;
        }
        let s = node.as_step()?;
        if s.depth != depth || !s.discharge.is_empty() || s.previous_step.is_some() {
            return None;
        }
        if is_done {
            done.insert(node.clone());
            order.push(node);
        } else {
            let premises: Vec<_> = s.premises.iter().map(|p| (p.clone(), false)).collect();
            todo.push((node, true));
            todo.extend(premises);
        }
    }
    Some(order)
}

/// Returns `true` if no term in the derivation has a free variable that an anchor in scope binds.
///
/// When that holds, the anchors' substitution is the identity on every term of the derivation, and
/// the variables they declare are not among the derivation's, so checking the derivation outside
/// the anchors is the same problem as checking it inside them.
fn context_free(
    pool: &mut PrimitivePool,
    context: &ContextStack,
    derivation: &[Rc<ProofNode>],
) -> bool {
    let bound = context.bound_variables();
    if bound.is_empty() {
        return true;
    }
    let bound: HashSet<Rc<Term>> = bound
        .into_iter()
        .map(|(name, sort)| pool.add(Term::new_var(name, sort)))
        .collect();
    !derivation.iter().any(|node| {
        let s = node.as_step().unwrap();
        s.clause
            .iter()
            .chain(&s.args)
            .any(|t| pool.free_vars(t).iter().any(|v| bound.contains(v)))
    })
}

/// Visits every node of a proof forest, including the ones that [`Rc<ProofNode>::traverse`] skips
/// because nothing depends on them.
fn visit_all(proof: &ProofNodeForest) -> Vec<&Rc<ProofNode>> {
    let mut result = Vec::new();
    let mut seen: HashSet<&Rc<ProofNode>> = HashSet::new();
    let mut todo: Vec<&Rc<ProofNode>> = proof.0.iter().collect();
    while let Some(node) = todo.pop() {
        if !seen.insert(node) {
            continue;
        }
        result.push(node);
        match node.as_ref() {
            ProofNode::Assume { .. } => (),
            ProofNode::Step(s) => {
                todo.extend(
                    s.premises
                        .iter()
                        .chain(&s.discharge)
                        .chain(&s.previous_step),
                );
            }
            ProofNode::Subproof(s) => {
                todo.push(&s.last_step);
                todo.extend(s.extra_steps.iter().chain(&s.outbound_premises));
            }
        }
    }
    result
}
