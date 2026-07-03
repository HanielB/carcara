//! A proof-producing congruence closure module, used to check and elaborate the `g_eunif` rule.
//!
//! The design follows veriT's congruence closure (`src/congruence/congruence.c`), which operates
//! directly on n-ary term nodes (no currying), stripped down to its algorithmic core: a flat
//! representative map updated eagerly on merge, per-class parent ("use") lists, a signature table
//! driving congruence detection, and a separate proof forest from which explanations are extracted
//! (in the spirit of Nieuwenhuis & Oliveras, "Proof-Producing Congruence Closure", RTA 2005).
//!
//! The state is split in two layers so that a single instance can be reused for many `g_eunif`
//! steps of the same proof: a persistent term index, which is built once (from all terms in the
//! term pool) and only grows, and the equality-derived state, which is cleared by [`reset`] between
//! invocations. The equality-derived state is kept in hash maps where an absent key means "default
//! value", so resetting costs time proportional to the terms touched by the previous invocation's
//! equalities, and not to the total number of indexed terms.
//!
//! [`reset`]: CongruenceClosure::reset

use crate::ast::*;
use std::collections::{HashMap, HashSet};

type NodeId = usize;

/// A reference-counted [`EqProof`]. Sub-proofs are shared, so an explanation is a DAG, not a tree.
pub type EqProofRc = std::sync::Arc<EqProof>;

/// A proof that `conclusion.0` and `conclusion.1` are equal, entailed by a set of premise
/// equalities.
#[derive(Debug)]
pub struct EqProof {
    pub conclusion: (Rc<Term>, Rc<Term>),
    pub rule: EqProofRule,
}

/// The rule concluding an [`EqProof`], mirroring the Alethe rules `symm`, `refl`, `trans` and
/// `cong`, with premise equalities as leaves.
#[derive(Debug)]
pub enum EqProofRule {
    /// The `index`-th premise equality, exactly as it was given to `add_equality`.
    Premise(usize),

    /// Symmetry: the sub-proof concludes the flipped conclusion.
    Symm(EqProofRc),

    /// Reflexivity: the two terms in the conclusion are syntactically equal.
    Refl,

    /// Transitivity chain: each sub-proof concludes one link, and the links connect the two terms
    /// in the conclusion.
    Trans(Vec<EqProofRc>),

    /// Congruence: the conclusion terms are applications of the same head symbol, and each
    /// sub-proof concludes the equality of the corresponding pair of arguments. `None` means the
    /// pair is syntactically equal and needs no justification.
    Cong(Vec<Option<EqProofRc>>),
}

/// The head symbol of an application node.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Head {
    App(Rc<Term>),
    Op(Operator),
    ParamOp(ParamOperator, Vec<Rc<Term>>),
}

/// A signature: the head symbol of an application together with one node per argument. In the
/// persistent `static_sigs` table the arguments are the argument nodes themselves; in lookups and
/// in the `delta_sigs` table they are the arguments' current class representatives.
type Signature = (Head, Vec<NodeId>);

/// The justification recorded on a proof forest edge.
#[derive(Debug, Clone, Copy)]
enum Reason {
    /// The `index`-th premise equality.
    Premise(usize),

    /// The edge's endpoints are applications of the same head symbol whose arguments were pairwise
    /// congruent when the edge was created.
    Congruence,
}

/// A proof forest edge from a node to its parent.
#[derive(Debug, Clone, Copy)]
struct Edge {
    parent: NodeId,
    reason: Reason,
    /// Whether `reason` justifies the equality in the direction child-to-parent (as opposed to
    /// parent-to-child). Merging and path inversion can flip edges relative to the equality that
    /// created them, so this must be tracked to orient premises correctly in explanations.
    child_eq_parent: bool,
}

#[derive(Debug, Default)]
pub struct CongruenceClosure {
    // Persistent term index: built once, grows monotonically as new terms are interned.
    /// The term of each node.
    nodes: Vec<Rc<Term>>,
    /// The node of each term.
    ids: HashMap<Rc<Term>, NodeId>,
    /// For application nodes, the head symbol and argument nodes.
    app_view: Vec<Option<(Head, Vec<NodeId>)>>,
    /// For each node, the application nodes that have it as a direct argument.
    static_parents: Vec<Vec<NodeId>>,
    /// Signature table under the identity mapping of classes. Since terms are hash-consed, this
    /// is injective, and it doubles as the initial signature table of every invocation: an entry
    /// matched by a lookup key made of current class representatives is never stale, because its
    /// arguments being representatives implies its signature is current.
    static_sigs: HashMap<Signature, NodeId>,

    // Equality-derived state: cleared by `reset`. An absent key always means "default".
    /// The class representative of a node (default: the node itself). Updated eagerly for every
    /// member of the absorbed class on merge, so lookups need no traversal.
    repr: HashMap<NodeId, NodeId>,
    /// The members of a touched class, keyed by representative (default: just the node itself).
    class_members: HashMap<NodeId, Vec<NodeId>>,
    /// The parent application nodes of all members of a touched class, keyed by representative
    /// (default: the node's `static_parents`).
    class_parents: HashMap<NodeId, Vec<NodeId>>,
    /// Signatures recomputed after merges. Lookups check this table first and `static_sigs`
    /// second, and insertions only happen when neither table has the key, so there is at most one
    /// live entry per signature.
    delta_sigs: HashMap<Signature, NodeId>,
    /// The proof forest: each merge adds one edge between the two nodes of the merged equality.
    forest: HashMap<NodeId, Edge>,
    /// Cache of already-computed explanations.
    explanations: HashMap<(NodeId, NodeId), EqProofRc>,
}

impl CongruenceClosure {
    /// Constructs a new congruence closure whose term index is seeded with the given terms,
    /// typically all terms in the term pool (see `TermPool::stored_terms`).
    pub fn new<T: IntoIterator<Item = Rc<Term>>>(initial_terms: T) -> Self {
        let mut cc = Self::default();
        for term in initial_terms {
            if !matches!(term.as_ref(), Term::Sort(_)) {
                cc.intern(&term);
            }
        }
        cc
    }

    /// Clears all equality-derived state, keeping the term index. Takes time proportional to the
    /// number of terms touched by the equalities added since the last reset.
    pub fn reset(&mut self) {
        self.repr.clear();
        self.class_members.clear();
        self.class_parents.clear();
        self.delta_sigs.clear();
        self.forest.clear();
        self.explanations.clear();
    }

    /// Asserts the `index`-th premise equality, `lhs = rhs`. New terms are interned.
    pub fn add_equality(&mut self, lhs: &Rc<Term>, rhs: &Rc<Term>, index: usize) {
        let (l, r) = (self.intern(lhs), self.intern(rhs));
        self.merge(l, r, Reason::Premise(index));
    }

    /// Returns whether the two terms are in the same congruence class. New terms are interned.
    pub fn are_congruent(&mut self, a: &Rc<Term>, b: &Rc<Term>) -> bool {
        let (a, b) = (self.intern(a), self.intern(b));
        self.find(a) == self.find(b)
    }

    /// Returns a proof that the two terms are equal, whose leaves are the added premise
    /// equalities, or `None` if they are not in the same congruence class.
    pub fn explain(&mut self, a: &Rc<Term>, b: &Rc<Term>) -> Option<EqProofRc> {
        if !self.are_congruent(a, b) {
            return None;
        }
        let (a, b) = (self.ids[a], self.ids[b]);
        Some(self.explain_nodes(a, b))
    }

    fn find(&self, node: NodeId) -> NodeId {
        self.repr.get(&node).copied().unwrap_or(node)
    }

    /// Interns a term and all its subterms, returning its node. If the term is a new application
    /// and equalities were already added, it may join an existing congruence class (veriT's "late
    /// term addition", which is simple here because state only grows within an invocation).
    fn intern(&mut self, term: &Rc<Term>) -> NodeId {
        if let Some(&id) = self.ids.get(term) {
            return id;
        }
        let view = match term.as_ref() {
            Term::App(f, args) => Some((Head::App(f.clone()), args.clone())),
            Term::Op(op, args) if !args.is_empty() => Some((Head::Op(*op), args.clone())),
            Term::ParamOp { op, op_args, args } if !args.is_empty() => {
                Some((Head::ParamOp(*op, op_args.clone()), args.clone()))
            }
            // Everything else (constants, variables, binders, etc.) is an atomic leaf, compared
            // by reference
            _ => None,
        };
        let view = view.map(|(head, args)| {
            let children: Vec<_> = args.iter().map(|arg| self.intern(arg)).collect();
            (head, children)
        });

        let id = self.nodes.len();
        self.nodes.push(term.clone());
        self.ids.insert(term.clone(), id);
        self.static_parents.push(Vec::new());
        self.app_view.push(view.clone());

        if let Some((head, children)) = view {
            for &child in &children {
                self.static_parents[child].push(id);
                // If the child's class was already touched by a merge, its parent list was
                // materialized from `static_parents` before this term existed, so it must be
                // updated as well
                if let Some(parents) = self.class_parents.get_mut(&self.find(child)) {
                    parents.push(id);
                }
            }
            self.static_sigs.insert((head, children), id);
            if !self.repr.is_empty() {
                // If merges already happened, the new node's signature under current
                // representatives may coincide with that of an existing node
                let sig = self.signature(id);
                match self.lookup_sig(&sig) {
                    Some(other) if other != id => self.merge(id, other, Reason::Congruence),
                    Some(_) => (),
                    None => {
                        if self.static_sigs.get(&sig) != Some(&id) {
                            self.delta_sigs.insert(sig, id);
                        }
                    }
                }
            }
        }
        id
    }

    /// The signature of an application node under the current class representatives.
    fn signature(&self, node: NodeId) -> Signature {
        let (head, children) = self.app_view[node].as_ref().unwrap();
        let children = children.iter().map(|&c| self.find(c)).collect();
        (head.clone(), children)
    }

    fn lookup_sig(&self, sig: &Signature) -> Option<NodeId> {
        self.delta_sigs
            .get(sig)
            .or_else(|| self.static_sigs.get(sig))
            .copied()
    }

    /// Merges the classes of `a` and `b`, justified by `reason` (which proves `a = b`, in that
    /// order), and propagates all congruences this entails (veriT's `CC_merge`/`CC_union`).
    fn merge(&mut self, a: NodeId, b: NodeId, reason: Reason) {
        let mut pending = vec![(a, b, reason)];
        while let Some((a, b, reason)) = pending.pop() {
            let (ra, rb) = (self.find(a), self.find(b));
            if ra == rb {
                continue;
            }

            // Union by size: the smaller class, henceforth `b`'s, is absorbed into the larger
            let size = |cc: &Self, r: NodeId| cc.class_members.get(&r).map_or(1, Vec::len);
            let (a, b, ra, rb, child_eq_parent) = if size(self, ra) < size(self, rb) {
                (b, a, rb, ra, true)
            } else {
                (a, b, ra, rb, false)
            };

            // Add the proof forest edge between the two nodes of the merged equality (not their
            // representatives), making `b` a root of its tree first by inverting the path from it
            self.invert_forest_path(b);
            self.forest
                .insert(b, Edge { parent: a, reason, child_eq_parent });

            // Remove the current signatures of the absorbed class's parents, which are about to
            // change. Only `delta_sigs` entries can match: a `static_sigs` entry matching a
            // signature under current representatives is never stale, so it can stay
            let b_parents = self
                .class_parents
                .remove(&rb)
                .unwrap_or_else(|| self.static_parents[rb].clone());
            for &parent in &b_parents {
                let sig = self.signature(parent);
                if self.delta_sigs.get(&sig) == Some(&parent) {
                    self.delta_sigs.remove(&sig);
                }
            }

            // Update the representative of every member of the absorbed class
            let mut b_members = self.class_members.remove(&rb).unwrap_or_else(|| vec![rb]);
            for &member in &b_members {
                self.repr.insert(member, ra);
            }
            self.class_members
                .entry(ra)
                .or_insert_with(|| vec![ra])
                .append(&mut b_members);

            // Re-enter the parents' new signatures. A collision with a node of a different class
            // is a newly detected congruence
            for &parent in &b_parents {
                let sig = self.signature(parent);
                match self.lookup_sig(&sig) {
                    Some(other) if self.find(other) != self.find(parent) => {
                        pending.push((parent, other, Reason::Congruence));
                    }
                    Some(_) => (),
                    None => {
                        self.delta_sigs.insert(sig, parent);
                    }
                }
            }
            self.class_parents
                .entry(ra)
                .or_insert_with(|| self.static_parents[ra].clone())
                .extend(b_parents);
        }
    }

    /// Inverts the proof forest path from `node` to the root of its tree, making `node` a root.
    fn invert_forest_path(&mut self, node: NodeId) {
        let mut cur = node;
        let mut inverted: Option<Edge> = None;
        loop {
            let old = self.forest.get(&cur).copied();
            match inverted {
                Some(edge) => {
                    self.forest.insert(cur, edge);
                }
                None => {
                    self.forest.remove(&cur);
                }
            }
            match old {
                Some(edge) => {
                    inverted = Some(Edge {
                        parent: cur,
                        reason: edge.reason,
                        child_eq_parent: !edge.child_eq_parent,
                    });
                    cur = edge.parent;
                }
                None => break,
            }
        }
    }

    /// Builds a proof that `a = b`, which must be in the same class: finds their nearest common
    /// ancestor in the proof forest and concatenates the explanations of the edges along both
    /// paths (veriT's `explain_eq`).
    fn explain_nodes(&mut self, a: NodeId, b: NodeId) -> EqProofRc {
        if a == b {
            return EqProofRc::new(EqProof {
                conclusion: (self.nodes[a].clone(), self.nodes[b].clone()),
                rule: EqProofRule::Refl,
            });
        }
        if let Some(proof) = self.explanations.get(&(a, b)) {
            return proof.clone();
        }

        let ancestor = self.nearest_common_ancestor(a, b);
        let path_edges = |cc: &Self, mut cur: NodeId| {
            let mut edges = Vec::new();
            while cur != ancestor {
                let edge = cc.forest[&cur];
                edges.push((cur, edge));
                cur = edge.parent;
            }
            edges
        };
        // The chain is: a = ... = ancestor (following edges upwards), then ancestor = ... = b
        // (following the edges from `b` upwards, reversed and flipped)
        let mut chain = Vec::new();
        for (child, edge) in path_edges(self, a) {
            chain.push(self.explain_edge(child, edge, true));
        }
        for (child, edge) in path_edges(self, b).into_iter().rev() {
            chain.push(self.explain_edge(child, edge, false));
        }

        let proof = if chain.len() == 1 {
            chain.pop().unwrap()
        } else {
            EqProofRc::new(EqProof {
                conclusion: (self.nodes[a].clone(), self.nodes[b].clone()),
                rule: EqProofRule::Trans(chain),
            })
        };
        self.explanations.insert((a, b), proof.clone());
        proof
    }

    /// Builds a proof for a proof forest edge: `child = parent` if `child_to_parent`, and
    /// `parent = child` otherwise.
    fn explain_edge(&mut self, child: NodeId, edge: Edge, child_to_parent: bool) -> EqProofRc {
        let (from, to) = if child_to_parent {
            (child, edge.parent)
        } else {
            (edge.parent, child)
        };
        match edge.reason {
            Reason::Premise(index) => {
                // The premise proves `child = parent` or `parent = child`, according to the
                // edge's orientation; if that is not the direction we need, flip it with `Symm`
                let premise = if edge.child_eq_parent {
                    (child, edge.parent)
                } else {
                    (edge.parent, child)
                };
                let proof = EqProofRc::new(EqProof {
                    conclusion: (self.nodes[premise.0].clone(), self.nodes[premise.1].clone()),
                    rule: EqProofRule::Premise(index),
                });
                if premise == (from, to) {
                    proof
                } else {
                    EqProofRc::new(EqProof {
                        conclusion: (self.nodes[from].clone(), self.nodes[to].clone()),
                        rule: EqProofRule::Symm(proof),
                    })
                }
            }
            Reason::Congruence => {
                // Both endpoints are applications of the same head symbol whose arguments were
                // pairwise congruent when the edge was created (and thus still are); recursively
                // explain each pair, directly in the needed orientation
                let from_args = self.app_view[from].as_ref().unwrap().1.clone();
                let to_args = self.app_view[to].as_ref().unwrap().1.clone();
                let args = from_args
                    .into_iter()
                    .zip(to_args)
                    .map(|(x, y)| (x != y).then(|| self.explain_nodes(x, y)))
                    .collect();
                EqProofRc::new(EqProof {
                    conclusion: (self.nodes[from].clone(), self.nodes[to].clone()),
                    rule: EqProofRule::Cong(args),
                })
            }
        }
    }

    /// Finds the nearest common ancestor of two nodes of the same class in the proof forest.
    fn nearest_common_ancestor(&self, a: NodeId, b: NodeId) -> NodeId {
        let mut seen = HashSet::new();
        let mut cur = a;
        loop {
            seen.insert(cur);
            match self.forest.get(&cur) {
                Some(edge) => cur = edge.parent,
                None => break,
            }
        }
        let mut cur = b;
        while !seen.contains(&cur) {
            cur = self.forest[&cur].parent;
        }
        cur
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast::pool::PrimitivePool, parser::tests::parse_terms};

    const DEFINITIONS: &str = "
        (declare-sort T 0)
        (declare-fun a () T)
        (declare-fun b () T)
        (declare-fun c () T)
        (declare-fun d () T)
        (declare-fun e () T)
        (declare-fun f (T) T)
        (declare-fun g (T) T)
        (declare-fun h (T T) T)
        (declare-fun p (T) Bool)
    ";

    /// Parses the premise equalities and the goal equality, adds the premises to a fresh
    /// congruence closure, and returns whether the goal terms become congruent.
    fn check(premises: &[(&str, &str)], goal: (&str, &str)) -> bool {
        let mut pool = PrimitivePool::new();
        run(&mut pool, &mut CongruenceClosure::new([]), premises, goal)
    }

    fn run(
        pool: &mut PrimitivePool,
        cc: &mut CongruenceClosure,
        premises: &[(&str, &str)],
        goal: (&str, &str),
    ) -> bool {
        for (i, (lhs, rhs)) in premises.iter().enumerate() {
            let [lhs, rhs] = parse_terms(pool, DEFINITIONS, [lhs, rhs]);
            cc.add_equality(&lhs, &rhs, i);
        }
        let [lhs, rhs] = parse_terms(pool, DEFINITIONS, [goal.0, goal.1]);
        let result = cc.are_congruent(&lhs, &rhs);
        if result {
            // Whenever the goal is congruent, also exercise proof production and check that the
            // explanation is well-formed
            let proof = cc.explain(&lhs, &rhs).unwrap();
            assert_eq!(proof.conclusion, (lhs, rhs));
            check_proof(&proof, premises, pool);
        }
        result
    }

    /// Checks that an explanation is well-formed: sub-proof conclusions line up, and every leaf
    /// is one of the supplied premises.
    fn check_proof(proof: &EqProof, premises: &[(&str, &str)], pool: &mut PrimitivePool) {
        let (lhs, rhs) = &proof.conclusion;
        match &proof.rule {
            EqProofRule::Premise(i) => {
                let [l, r] = parse_terms(pool, DEFINITIONS, [premises[*i].0, premises[*i].1]);
                assert_eq!((l, r), (lhs.clone(), rhs.clone()));
            }
            EqProofRule::Symm(inner) => {
                assert_eq!(inner.conclusion, (rhs.clone(), lhs.clone()));
                check_proof(inner, premises, pool);
            }
            EqProofRule::Refl => assert_eq!(lhs, rhs),
            EqProofRule::Trans(links) => {
                assert!(links.len() >= 2);
                let mut cur = lhs.clone();
                for link in links {
                    assert_eq!(link.conclusion.0, cur);
                    cur = link.conclusion.1.clone();
                    check_proof(link, premises, pool);
                }
                assert_eq!(cur, *rhs);
            }
            EqProofRule::Cong(args) => {
                let (l_args, r_args) = match (lhs.as_ref(), rhs.as_ref()) {
                    (Term::App(f, l_args), Term::App(g, r_args)) => {
                        assert_eq!(f, g);
                        (l_args, r_args)
                    }
                    (Term::Op(f, l_args), Term::Op(g, r_args)) => {
                        assert_eq!(f, g);
                        (l_args, r_args)
                    }
                    _ => panic!("congruence between non-applications"),
                };
                assert_eq!(l_args.len(), args.len());
                for ((l, r), arg) in l_args.iter().zip(r_args).zip(args) {
                    match arg {
                        None => assert_eq!(l, r),
                        Some(inner) => {
                            assert_eq!(inner.conclusion, (l.clone(), r.clone()));
                            check_proof(inner, premises, pool);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn direct_and_symm() {
        assert!(check(&[("a", "b")], ("a", "b")));
        assert!(check(&[("a", "b")], ("b", "a")));
        assert!(check(&[], ("a", "a")));
        assert!(!check(&[("a", "b")], ("a", "c")));
        assert!(!check(&[], ("a", "b")));
    }

    #[test]
    fn transitivity() {
        assert!(check(&[("a", "b"), ("b", "c")], ("a", "c")));
        assert!(check(&[("b", "a"), ("c", "b"), ("c", "d")], ("a", "d")));
        assert!(check(&[("c", "d"), ("a", "b"), ("b", "c")], ("d", "a")));
        assert!(!check(&[("a", "b"), ("c", "d")], ("a", "d")));
    }

    #[test]
    fn congruence() {
        assert!(check(&[("a", "b")], ("(f a)", "(f b)")));
        assert!(check(&[("a", "b")], ("(h (g a) c)", "(h (g b) c)")));
        assert!(check(&[("a", "b"), ("c", "d")], ("(h a c)", "(h b d)")));
        assert!(check(&[("a", "b")], ("(p a)", "(p b)")));
        assert!(check(&[], ("(f a)", "(f a)")));
        assert!(!check(&[("a", "b")], ("(f a)", "(g b)")));
        // Congruence is not injectivity
        assert!(!check(&[("(f a)", "(f b)")], ("a", "b")));
    }

    #[test]
    fn congruence_and_transitivity() {
        assert!(check(
            &[("a", "b"), ("(f b)", "c"), ("c", "d")],
            ("(f a)", "d")
        ));
        assert!(check(
            &[("a", "b"), ("b", "c"), ("(g c)", "d")],
            ("(f (g a))", "(f d)")
        ));
        // The equality of `(f a)` and `(f c)` requires transitivity through the argument
        // equalities, and then congruence
        assert!(check(&[("a", "b"), ("b", "c")], ("(f a)", "(f c)")));
        // Deep congruence chains
        assert!(check(
            &[("a", "b"), ("(h a a)", "c"), ("(h b b)", "d")],
            ("c", "d")
        ));
    }

    #[test]
    fn late_term_addition() {
        let mut pool = PrimitivePool::new();
        let mut cc = CongruenceClosure::new([]);
        // `(g a)` and `(g b)` are only interned by the goal query, after the merges already
        // happened, so they must join the existing classes upon interning
        assert!(run(&mut pool, &mut cc, &[("a", "b")], ("(g a)", "(g b)")));
    }

    #[test]
    fn reset_and_reuse() {
        let mut pool = PrimitivePool::new();
        let mut cc = CongruenceClosure::new([]);
        assert!(run(&mut pool, &mut cc, &[("a", "b")], ("(f a)", "(f b)")));

        // After a reset, the previous equalities are gone but the terms are still interned
        cc.reset();
        assert!(!run(&mut pool, &mut cc, &[], ("(f a)", "(f b)")));
        assert!(!run(&mut pool, &mut cc, &[("c", "d")], ("a", "b")));

        cc.reset();
        assert!(run(
            &mut pool,
            &mut cc,
            &[("a", "d"), ("d", "b")],
            ("(f a)", "(f b)")
        ));
    }

    #[test]
    fn seeded_with_pool_terms() {
        let mut pool = PrimitivePool::new();
        // Pre-parse some terms so they are in the pool, then seed the congruence closure with
        // every pool term, like the `g_eunif` rule does
        let _ = parse_terms(&mut pool, DEFINITIONS, ["(f (g a))", "(g b)", "(h a b)"]);
        let mut cc = CongruenceClosure::new(pool.stored_terms());
        assert!(run(
            &mut pool,
            &mut cc,
            &[("a", "b")],
            ("(f (g a))", "(f (g b))")
        ));
        cc.reset();
        assert!(run(
            &mut pool,
            &mut cc,
            &[("(g a)", "b")],
            ("(h a (g a))", "(h a b)")
        ));
    }
}
