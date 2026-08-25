//! Collapsing lemma scopes into the clausal steps they are equivalent to.
//!
//! A solver that proves a lemma by *scoping* assumes the lemma's hypotheses, derives its conclusion
//! under them, and discharges the whole block into one clause. cvc5 does this everywhere: 190 375
//! of the subproofs in the evaluation corpus come from it, against 3 149 from veriT.
//!
//! ```text
//! (anchor :step t7)
//! (assume t7.a0 (= a b))
//! (assume t7.a1 (= b c))
//! (step t7.t0 (cl (= a c)) :rule trans :premises (t7.a0 t7.a1))
//! (step t7 (cl (not (= a b)) (not (= b c)) (= a c)) :rule subproof :discharge (t7.a0 t7.a1))
//! ```
//!
//! The hypotheses are re-introduced inside the scope only so that a *context-sensitive* rule —
//! `trans` here — can consume them as premises. But they are already spelled out, negated, in the
//! clause the scope discharges, and Alethe has a *clausal* rule that concludes exactly that clause
//! from nothing: `eq_transitive`. Four commands become one:
//!
//! ```text
//! (step t7 (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)
//! ```
//!
//! So this pass never looks at what a scope contains. It takes the clause the scope discharges and
//! offers it to a battery of premise-free rules; if one accepts, the whole subproof is replaced by
//! a single step with that rule. The checker itself decides, which is what makes the replacement
//! sound whatever the scope was doing internally: the emitted step is accepted by the same function
//! that will check it, with no premises, no context and no discharge, so it proves its clause
//! outright.
//!
//! Two rules take arguments that the clause determines, and are tried with those arguments
//! synthesized: `and_pos` and `or_neg` need the index of the conjunct or disjunct, and `la_generic`
//! needs a Farkas coefficient per literal — which the checker can *infer* from the clause for every
//! literal but the first (this is what the `bounded_farkas` elaboration does).
//!
//! The battery is filtered by `--allowed-rules` for the same reason [`super::hoist`] filters its
//! candidates: a rule the checker was told to accept as a hole must not become the justification of
//! something that had a real derivation.

use crate::ast::*;
use crate::checker::{check_premise_free_rule, la_generic_partial};

/// The premise-free rules a discharged clause is offered to, in the order they are tried.
///
/// The order is by how often each fires on the corpus, so the common cases are decided in one or
/// two calls. Every rule here reads only its conclusion: no premises, no arguments, no context. A
/// rule that needs any of those cannot be validated this way and is handled separately, below.
const CLAUSAL_RULES: &[&str] = &[
    // Congruence-closure lemmas, which are what almost every small cvc5 scope proves
    "eq_transitive",
    "eq_congruent",
    "eq_congruent_pred",
    // CNF-shaped lemmas
    "equiv_pos1",
    "equiv_pos2",
    "equiv_neg1",
    "equiv_neg2",
    "implies_pos",
    "implies_neg1",
    "implies_neg2",
    "and_neg",
    "or_pos",
    "not_not",
    "xor_pos1",
    "xor_pos2",
    "xor_neg1",
    "xor_neg2",
    "ite_pos1",
    "ite_pos2",
    "ite_neg1",
    "ite_neg2",
    // Unit lemmas: a scope with no assumptions, or one whose assumptions are all unused
    "la_disequality",
    "la_totality",
    "la_tautology",
    "la_rw_eq",
    "refl",
    "distinct_elim",
    "connective_def",
    "nary_elim",
    "aci_simp",
    "poly_simp",
    "evaluate",
];

/// The replacement a scope's discharged clause was found to have.
pub(super) struct Collapse {
    pub rule: String,
    pub args: Vec<Rc<Term>>,

    /// The clause the rule concludes, when it is a strict prefix of what the scope discharges and a
    /// `weakening` step has to add the rest. This is the `false`-tailed shape: a solver that proves
    /// a lemma by deriving `false` under its hypotheses discharges `(cl ¬A … ¬Z false)`, and the
    /// clause without that literal is the one a rule can prove.
    pub weaken_from: Option<Vec<Rc<Term>>>,
}

/// Returns the single clausal step that proves what this subproof discharges, if there is one.
///
/// `is_hole` tells whether the checker would treat a rule as a hole, so that a scope with a real
/// derivation is never replaced by one.
pub(super) fn collapse(
    pool: &mut PrimitivePool,
    subproof: &SubproofNode,
    is_hole: &impl Fn(&str) -> bool,
) -> Option<Collapse> {
    // An anchor with arguments changes the context, so its last step is a `bind`, `onepoint`,
    // `sko_ex`, `sko_forall` or `let` — a rule about the substitution the anchor carries, not a
    // lemma with dischargeable hypotheses
    if !subproof.args.is_empty() {
        return None;
    }
    let last = subproof.last_step.as_step()?;
    if last.rule != "subproof" {
        return None;
    }
    let clause = &last.clause;

    if let Some(found) = try_clause(pool, clause, is_hole) {
        return Some(found);
    }
    // A lemma proved by deriving `false` under its hypotheses discharges that `false` along with
    // the negated hypotheses. The literal is redundant — the clause without it is stronger — and
    // the rules below can prove that one, so the collapse becomes two steps instead of one: the
    // rule, and a `weakening` that puts the literal back so the consumers are unaffected
    let [head @ .., last] = clause.as_slice() else {
        return None;
    };
    if !last.is_bool_false() || head.len() < 2 || is_hole("weakening") {
        return None;
    }
    let head = head.to_vec();
    let mut found = try_clause(pool, &head, is_hole)?;
    found.weaken_from = Some(head);
    Some(found)
}

/// Offers a clause to the battery, then to the two argument-synthesizing rules.
fn try_clause(
    pool: &mut PrimitivePool,
    clause: &[Rc<Term>],
    is_hole: &impl Fn(&str) -> bool,
) -> Option<Collapse> {
    for rule in CLAUSAL_RULES {
        if is_hole(rule) {
            continue;
        }
        // `refl` here means plain reflexivity (the scope has no context), but at elaborated
        // granularity it is checked syntactically, so only the syntactic case is taken
        if *rule == "refl" {
            let syntactic = matches!(clause, [t] if match_term!((= a b) = t).is_some_and(|(a, b)| a == b));
            if !syntactic {
                continue;
            }
        }
        if check_premise_free_rule(pool, rule, clause, &[]).is_ok() {
            return Some(Collapse {
                rule: (*rule).to_owned(),
                args: Vec::new(),
                weaken_from: None,
            });
        }
    }
    index_rule(pool, clause, is_hole).or_else(|| farkas(pool, clause, is_hole))
}

/// Tries `and_pos` and `or_neg`, whose single argument is the position of the literal in the
/// conjunction or disjunction, and is therefore determined by the clause.
///
/// The index is *searched for* rather than read off, and the rule is then run with it, so a clause
/// that happens to match the shape but not the rule is still rejected by the checker.
fn index_rule(
    pool: &mut PrimitivePool,
    clause: &[Rc<Term>],
    is_hole: &impl Fn(&str) -> bool,
) -> Option<Collapse> {
    if clause.len() != 2 {
        return None;
    }
    let (rule, contents) = match (
        match_term!((not (and ...)) = &clause[0]),
        match_term!((or ...) = &clause[0]),
    ) {
        (Some(args), _) => ("and_pos", args),
        (None, Some(args)) => ("or_neg", args),
        _ => return None,
    };
    if is_hole(rule) {
        return None;
    }
    // The literal the rule selects, whose position is the argument
    let selected = match rule {
        "and_pos" => clause[1].clone(),
        _ => clause[1].remove_negation()?.clone(),
    };
    let index = contents.iter().position(|t| *t == selected)?;
    let args = vec![pool.add(Term::new_int(index))];
    check_premise_free_rule(pool, rule, clause, &args)
        .is_ok()
        .then(|| Collapse { rule: rule.to_owned(), args, weaken_from: None })
}

/// Tries `la_generic`, whose arguments are one Farkas coefficient per literal.
///
/// The coefficients are not searched for: the checker derives all but the first from the clause, by
/// requiring each literal's linear combination to cancel against the accumulated one. Only the
/// leading coefficient has to be chosen, and for a clause the solver derived by scaling and adding
/// its hypotheses it is 1 — the same assumption the `bounded_farkas` elaboration makes.
fn farkas(
    pool: &mut PrimitivePool,
    clause: &[Rc<Term>],
    is_hole: &impl Fn(&str) -> bool,
) -> Option<Collapse> {
    if clause.len() < 2 || is_hole("la_generic") {
        return None;
    }
    let one = pool.add(Term::new_real(1));
    let given = [one.clone()];
    let mut trace = Some(Vec::new());
    la_generic_partial(pool, clause, &given, &mut trace).ok()?;
    let inferred = trace.unwrap();
    if inferred.len() + 1 != clause.len() {
        return None;
    }
    let args: Vec<_> = std::iter::once(one)
        .chain(inferred.into_iter().map(|a| pool.add(Term::new_real(a))))
        .collect();
    check_premise_free_rule(pool, "la_generic", clause, &args)
        .is_ok()
        .then(|| Collapse {
            rule: "la_generic".to_owned(),
            args,
            weaken_from: None,
        })
}

// ---------------------------------------------------------------------------------------------
// Clausal replay: turning a scope inside-out
// ---------------------------------------------------------------------------------------------
//
// The battery above only sees scopes whose discharged clause one rule proves outright. Most lemma
// scopes are not like that: cvc5's congruence scopes skip the identical argument pairs, so the
// discharged clause has fewer equality literals than `eq_congruent` demands, and its rewriting
// scopes interleave context-sensitive steps (`cong`, `trans` from the assumptions) with closed
// rewriting lemmas. The replay handles those by *translating the body*, step by step, into the
// premise-free clausal vocabulary:
//
// - an `assume` of the scope becomes a *hypothesis literal*: its negation is threaded through the
//   clauses of every step that used it, which is exactly where the `subproof` discharge would have
//   put it;
// - `cong` becomes `eq_congruent`, with `eq_reflexive` supplying the equalities of the argument
//   pairs the implicit-premise convention skipped;
// - `trans` becomes `eq_transitive`, `symm` an `eq_transitive`/`eq_reflexive` pair;
// - a premise-carrying clausification step (`equiv1`, `and`, `implies`, …) becomes its
//   premise-free axiom counterpart (`equiv_pos2`, `and_pos`, `implies_pos`, …) resolved against
//   the translated premise;
// - `resolution` stays `resolution` over the translated premises, an `assume` premise turning
//   into the hypothesis literal its unit clause would have resolved away;
// - a *closed* step (premise-free reasoning: `refl`, `evaluate`, `poly_simp`, `rare_rewrite`
//   chains, …) is rebuilt outside the scope as it is.
//
// Every `eq_congruent`/`eq_transitive` instance is validated by the checker before emission, and a
// rule the replay does not know makes the whole scope bail out (kept unchanged), so the pass stays
// best-effort and verdict-preserving.

use std::collections::{HashMap, HashSet};

/// What a body node translates to.
#[derive(Clone)]
enum Replayed {
    /// An `assume` of the scope being replayed: consumers thread `¬term` as a literal.
    Hyp(Rc<Term>),

    /// A node at the enclosing depth whose clause is the original node's clause plus the negations
    /// of the hypotheses its derivation used.
    Node {
        node: Rc<ProofNode>,
        hyps: Vec<Rc<Term>>,
    },
}

/// The id supply and target depth for the steps a replay emits.
pub(super) struct Emitter<'a> {
    pub next_id: &'a mut dyn FnMut() -> String,
    pub depth: usize,
    pub emitted: usize,
}

impl Emitter<'_> {
    fn step(
        &mut self,
        clause: Vec<Rc<Term>>,
        rule: &str,
        premises: Vec<Rc<ProofNode>>,
        args: Vec<Rc<Term>>,
    ) -> Rc<ProofNode> {
        self.emitted += 1;
        Rc::new(ProofNode::Step(StepNode {
            id: (self.next_id)(),
            depth: self.depth,
            clause,
            rule: rule.to_owned(),
            premises,
            args,
            discharge: Vec::new(),
            previous_step: None,
        }))
    }
}

/// Merges hypothesis lists, preserving first-use order.
fn merge_hyps(into: &mut Vec<Rc<Term>>, from: &[Rc<Term>]) {
    for h in from {
        if !into.contains(h) {
            into.push(h.clone());
        }
    }
}

/// Replays the body of a lemma scope outside of it, returning the node that takes the subproof's
/// place. `None` means the scope has a shape the replay does not cover, and is kept.
pub(super) fn replay(
    pool: &mut PrimitivePool,
    subproof: &SubproofNode,
    emitter: &mut Emitter,
    is_hole: &impl Fn(&str) -> bool,
) -> Option<Rc<ProofNode>> {
    if !subproof.args.is_empty() {
        return None;
    }
    let last = subproof.last_step.as_step()?;
    if last.rule != "subproof" {
        return None;
    }
    let body_root = last.previous_step.as_ref()?;
    let scope_depth = last.depth;

    // The scope's assumptions, in discharge order
    let mut assumes: Vec<(Rc<ProofNode>, Rc<Term>)> = Vec::new();
    for d in &last.discharge {
        let ProofNode::Assume { term, .. } = d.as_ref() else {
            return None;
        };
        assumes.push((d.clone(), term.clone()));
    }

    let mut replay = ReplayState {
        pool,
        emitter,
        is_hole,
        scope_depth,
        assumes,
        memo: HashMap::new(),
    };
    // Translate the body bottom-up, so that every premise is memoized before its consumer asks
    // for it: `translate` would otherwise recurse through the body, and solver bodies run
    // thousands of steps deep
    let mut order: Vec<Rc<ProofNode>> = Vec::new();
    {
        let mut seen: HashSet<Rc<ProofNode>> = HashSet::new();
        let mut todo: Vec<(Rc<ProofNode>, bool)> = vec![(body_root.clone(), false)];
        while let Some((node, done)) = todo.pop() {
            if done {
                order.push(node);
                continue;
            }
            if node.depth() < scope_depth || !seen.insert(node.clone()) {
                continue;
            }
            todo.push((node.clone(), true));
            if let ProofNode::Step(step) = node.as_ref() {
                todo.extend(step.premises.iter().map(|p| (p.clone(), false)));
            }
        }
    }
    for node in &order {
        let _ = replay.node(node);
    }
    let fin = replay.node(body_root)?;
    let Replayed::Node { node: fin, hyps } = fin else {
        // A body that is literally one of the assumptions has nothing to replay
        return None;
    };

    // A negated hypothesis `h = ¬φ` used as a resolution unit leaves the residual `φ` in the
    // replayed clause where the discharged clause states `¬¬φ`; excluded middle on `h` —
    // `(cl ¬h h)`, from `refl` and `equiv_pos2` — bridges the two
    let mut fin = fin;
    let target = last.clause.clone();
    for h in &hyps {
        let Some(inner) = h.remove_negation() else {
            continue;
        };
        let inner = inner.clone();
        let nh = build_term!(replay.pool, (not {h.clone()}));
        if !fin.clause().contains(&inner) || !target.contains(&nh) || target.contains(&inner) {
            continue;
        }
        let em = {
            let eq = build_term!(replay.pool, (= {h.clone()} {h.clone()}));
            let refl = replay.emitter.step(vec![eq.clone()], "refl", Vec::new(), Vec::new());
            let not_eq = build_term!(replay.pool, (not {eq.clone()}));
            let pos2 = replay.emitter.step(
                vec![not_eq, nh.clone(), h.clone()],
                "equiv_pos2",
                Vec::new(),
                Vec::new(),
            );
            let clause = vec![nh.clone(), h.clone()];
            replay
                .emitter
                .step(clause, "resolution", vec![pos2, refl], Vec::new())
        };
        let mut clause: Vec<Rc<Term>> = fin
            .clause()
            .iter()
            .filter(|l| **l != inner)
            .cloned()
            .collect();
        if !clause.contains(&nh) {
            clause.push(nh);
        }
        fin = replay
            .emitter
            .step(clause, "resolution", vec![fin, em], Vec::new());
    }

    // Adjust the final clause to exactly what the scope discharged: `weakening` appends the unused
    // hypotheses (and any literal-count difference), `reordering` puts everything in place
    let current = fin.clause().to_vec();
    if current == target {
        return Some(fin);
    }
    let mut missing = target.clone();
    for lit in &current {
        match missing.iter().position(|t| t == lit) {
            Some(i) => {
                missing.remove(i);
            }
            // A literal the replay produced that the discharged clause lacks: give up
            None => return None,
        }
    }
    let _ = hyps;
    let node = if missing.is_empty() {
        fin
    } else {
        let mut clause = current;
        clause.extend(missing);
        replay.emitter.step(clause, "weakening", vec![fin], Vec::new())
    };
    if node.clause() == target.as_slice() {
        return Some(node);
    }
    Some(
        replay
            .emitter
            .step(target, "reordering", vec![node], Vec::new()),
    )
}

struct ReplayState<'a, 'b, H: Fn(&str) -> bool> {
    pool: &'a mut PrimitivePool,
    emitter: &'a mut Emitter<'b>,
    is_hole: &'a H,
    scope_depth: usize,
    assumes: Vec<(Rc<ProofNode>, Rc<Term>)>,
    memo: HashMap<Rc<ProofNode>, Replayed>,
}

impl<H: Fn(&str) -> bool> ReplayState<'_, '_, H> {
    /// Emits a step, unless its rule is one the checker treats as a hole: the replay must not
    /// justify anything with a rule from `--allowed-rules`, for the same reason the battery and
    /// the hoist refuse to.
    fn emit(
        &mut self,
        clause: Vec<Rc<Term>>,
        rule: &str,
        premises: Vec<Rc<ProofNode>>,
        args: Vec<Rc<Term>>,
    ) -> Option<Rc<ProofNode>> {
        if (self.is_hole)(rule) {
            return None;
        }
        Some(self.emitter.step(clause, rule, premises, args))
    }

    fn node(&mut self, node: &Rc<ProofNode>) -> Option<Replayed> {
        if let Some(r) = self.memo.get(node) {
            return Some(r.clone());
        }
        let result = self.translate(node)?;
        self.memo.insert(node.clone(), result.clone());
        Some(result)
    }

    fn translate(&mut self, node: &Rc<ProofNode>) -> Option<Replayed> {
        // Anything already visible outside the scope is used where it is
        if node.depth() < self.scope_depth {
            return Some(Replayed::Node { node: node.clone(), hyps: Vec::new() });
        }
        if let Some((_, term)) = self.assumes.iter().find(|(a, _)| a == node) {
            return Some(Replayed::Hyp(term.clone()));
        }
        let ProofNode::Step(s) = node.as_ref() else {
            // An assume that is not in the discharge list, or a nested subproof: out of scope
            return None;
        };
        // A closed derivation proves its clause outright: rebuild it at the enclosing depth
        if let Some(rebuilt) = self.rebuild_closed(node) {
            return Some(Replayed::Node { node: rebuilt, hyps: Vec::new() });
        }
        match s.rule.as_str() {
            "cong" => self.congruence(s),
            "trans" => self.transitivity(s),
            "symm" => self.symmetry(s),
            "refl" => None, // a non-closed refl would need the context; does not happen here
            "resolution" | "th_resolution" => self.resolution(s),
            "contraction" | "reordering" | "weakening" => self.bookkeeping(s),
            "and_intro" => self.and_intro(s),
            // Premise-carrying clausification: the paired premise-free axiom
            "equiv1" => self.clausification(s, "equiv_pos2"),
            "equiv2" => self.clausification(s, "equiv_pos1"),
            "not_equiv1" => self.clausification(s, "equiv_neg2"),
            "not_equiv2" => self.clausification(s, "equiv_neg1"),
            "and" => self.indexed_clausification(s, "and_pos"),
            "not_or" => self.indexed_clausification(s, "or_neg"),
            "or" => self.clausification(s, "or_pos"),
            "not_and" => self.clausification(s, "and_neg"),
            "implies" => self.clausification(s, "implies_pos"),
            "not_implies1" => self.clausification(s, "implies_neg1"),
            "not_implies2" => self.clausification(s, "implies_neg2"),
            _ => None,
        }
    }

    /// Rebuilds a derivation that is closed relative to the scope — every reachable node at the
    /// scope's depth is a hole-free step with no discharge and no implicit premise, bottoming out
    /// in premise-free steps or in nodes already visible outside — at the enclosing depth.
    fn rebuild_closed(&mut self, root: &Rc<ProofNode>) -> Option<Rc<ProofNode>> {
        let depth = self.scope_depth;
        // Collect the local nodes in postorder, failing fast on anything not closed
        let mut order: Vec<Rc<ProofNode>> = Vec::new();
        let mut seen: HashSet<Rc<ProofNode>> = HashSet::new();
        let mut todo = vec![(root.clone(), false)];
        while let Some((node, done)) = todo.pop() {
            if done {
                order.push(node);
                continue;
            }
            if node.depth() < depth {
                continue;
            }
            if seen.contains(&node) {
                continue;
            }
            seen.insert(node.clone());
            let s = node.as_step()?;
            if s.depth != depth
                || !s.discharge.is_empty()
                || s.previous_step.is_some()
                || (self.is_hole)(&s.rule)
            {
                return None;
            }
            todo.push((node.clone(), true));
            todo.extend(s.premises.iter().map(|p| (p.clone(), false)));
        }
        let mut rebuilt: HashMap<Rc<ProofNode>, Rc<ProofNode>> = HashMap::new();
        for node in &order {
            let s = node.as_step().unwrap();
            let premises = s
                .premises
                .iter()
                .map(|p| rebuilt.get(p).unwrap_or(p).clone())
                .collect();
            let new = self.emit(s.clause.clone(), &s.rule, premises, s.args.clone())?;
            rebuilt.insert(node.clone(), new);
        }
        Some(rebuilt[root].clone())
    }

    /// The unit conclusion of a premise, together with how to consume it: a hypothesis contributes
    /// its literal directly, a node is resolved in afterwards.
    ///
    /// The conclusion is read off the *original* premise node — a replayed node's clause holds the
    /// same literal at whatever position its construction put it (an `eq_congruent` instance ends
    /// with it, a rebuilt closed step starts with it), plus the hypothesis literals.
    fn premise_parts(&mut self, p: &Rc<ProofNode>) -> Option<(Rc<Term>, Replayed)> {
        let r = self.node(p)?;
        let term = match &r {
            Replayed::Hyp(t) => t.clone(),
            Replayed::Node { .. } => p.clause().first()?.clone(),
        };
        Some((term, r))
    }

    /// Resolves the non-hypothesis premises into an instance clause, merging their hypotheses.
    /// Each part is a premise whose conclusion `term` cancels the instance's `¬term` literal.
    fn close_over(
        &mut self,
        instance: Rc<ProofNode>,
        parts: Vec<(Rc<Term>, Replayed)>,
    ) -> Option<Replayed> {
        let parts = parts
            .into_iter()
            .map(|(term, r)| {
                let nt = build_term!(self.pool, (not {term.clone()}));
                (nt, term, r)
            })
            .collect();
        self.close_over_lits(instance, parts)
    }

    /// The general form: each part names the literal of the instance clause it discharges and the
    /// (complementary) literal of the premise's clause that discharges it.
    fn close_over_lits(
        &mut self,
        instance: Rc<ProofNode>,
        parts: Vec<(Rc<Term>, Rc<Term>, Replayed)>,
    ) -> Option<Replayed> {
        let mut node = instance;
        let mut hyps: Vec<Rc<Term>> = Vec::new();
        for (instance_lit, premise_lit, r) in parts {
            match r {
                Replayed::Hyp(h) => merge_hyps(&mut hyps, std::slice::from_ref(&h)),
                Replayed::Node { node: p, hyps: ph } => {
                    merge_hyps(&mut hyps, &ph);
                    let mut clause: Vec<Rc<Term>> = node
                        .clause()
                        .iter()
                        .filter(|l| **l != instance_lit)
                        .cloned()
                        .collect();
                    for l in p.clause() {
                        if *l != premise_lit && !clause.contains(l) {
                            clause.push(l.clone());
                        }
                    }
                    node = self.emit(clause, "resolution", vec![node, p], Vec::new())?;
                }
            }
        }
        Some(Replayed::Node { node, hyps })
    }

    fn congruence(&mut self, s: &StepNode) -> Option<Replayed> {
        let (f, g) = match_term!((= f g) = s.clause.first()?)?;
        let (f_args, g_args) = match (f.as_ref(), g.as_ref()) {
            (Term::App(ff, fa), Term::App(gf, ga)) if ff == gf => (fa.clone(), ga.clone()),
            (Term::Op(fo, fa), Term::Op(go, ga)) if fo == go => (fa.clone(), ga.clone()),
            _ => return None,
        };
        if f_args.len() != g_args.len() {
            return None;
        }
        // One equality literal per argument pair: from the next premise if it justifies the pair,
        // from reflexivity if the pair is identical
        let mut parts: Vec<(Rc<Term>, Replayed)> = Vec::new();
        for p in &s.premises {
            parts.push(self.premise_parts(p)?);
        }
        let mut eqs: Vec<Rc<Term>> = Vec::new();
        let mut used: Vec<(Rc<Term>, Replayed)> = Vec::new();
        let mut next = parts.into_iter().peekable();
        for (fa, ga) in f_args.iter().zip(&g_args) {
            let justified = next.peek().is_some_and(|(t, _)| {
                match_term!((= a b) = t)
                    .is_some_and(|(a, b)| (a, b) == (fa, ga) || (a, b) == (ga, fa))
            });
            if justified {
                let (t, r) = next.next().unwrap();
                eqs.push(t.clone());
                used.push((t, r));
            } else if fa == ga {
                let eq = build_term!(self.pool, (= {fa.clone()} {fa.clone()}));
                let refl = self.emit(vec![eq.clone()], "refl", Vec::new(), Vec::new())?;
                eqs.push(eq.clone());
                used.push((eq, Replayed::Node { node: refl, hyps: Vec::new() }));
            } else {
                return None;
            }
        }
        if next.next().is_some() {
            return None;
        }
        // The validated eq_congruent instance
        let mut clause: Vec<Rc<Term>> = eqs
            .iter()
            .map(|e| build_term!(self.pool, (not {e.clone()})))
            .collect();
        clause.push(s.clause[0].clone());
        check_premise_free_rule(self.pool, "eq_congruent", &clause, &[]).ok()?;
        let instance = self.emit(clause, "eq_congruent", Vec::new(), Vec::new())?;
        self.close_over(instance, used)
    }

    fn transitivity(&mut self, s: &StepNode) -> Option<Replayed> {
        let mut parts: Vec<(Rc<Term>, Replayed)> = Vec::new();
        for p in &s.premises {
            parts.push(self.premise_parts(p)?);
        }
        let mut clause: Vec<Rc<Term>> = parts
            .iter()
            .map(|(t, _)| build_term!(self.pool, (not {t.clone()})))
            .collect();
        clause.push(s.clause.first()?.clone());
        check_premise_free_rule(self.pool, "eq_transitive", &clause, &[]).ok()?;
        let instance = self.emit(clause, "eq_transitive", Vec::new(), Vec::new())?;
        self.close_over(instance, parts)
    }

    fn symmetry(&mut self, s: &StepNode) -> Option<Replayed> {
        let [p] = s.premises.as_slice() else {
            return None;
        };
        let (term, r) = self.premise_parts(p)?;
        let (_, b) = match_term!((= a b) = &term)?;
        let refl_eq = build_term!(self.pool, (= {b.clone()} {b.clone()}));
        let (not_term, not_refl) = (
            build_term!(self.pool, (not {term.clone()})),
            build_term!(self.pool, (not {refl_eq.clone()})),
        );
        let clause = vec![not_term, not_refl, s.clause.first()?.clone()];
        check_premise_free_rule(self.pool, "eq_transitive", &clause, &[]).ok()?;
        let instance = self.emit(clause, "eq_transitive", Vec::new(), Vec::new())?;
        let refl = self.emit(vec![refl_eq.clone()], "refl", Vec::new(), Vec::new())?;
        self.close_over(
            instance,
            vec![
                (term, r),
                (refl_eq, Replayed::Node { node: refl, hyps: Vec::new() }),
            ],
        )
    }

    fn resolution(&mut self, s: &StepNode) -> Option<Replayed> {
        let mut nodes: Vec<Rc<ProofNode>> = Vec::new();
        let mut hyps: Vec<Rc<Term>> = Vec::new();
        let mut dropped: Vec<Rc<Term>> = Vec::new();
        for p in &s.premises {
            match self.node(p)? {
                Replayed::Hyp(h) => {
                    merge_hyps(&mut hyps, std::slice::from_ref(&h));
                    dropped.push(h);
                }
                Replayed::Node { node, hyps: ph } => {
                    merge_hyps(&mut hyps, &ph);
                    nodes.push(node);
                }
            }
        }
        if nodes.is_empty() {
            return None;
        }
        // The conclusion is the original one plus whatever the translated premises carry beyond
        // their originals (hypothesis literals or their residuals — a premise resolved against a
        // negated hypothesis `h = ¬φ` carries the residual `φ` rather than `¬h`; the final fix-up
        // in `replay` bridges the two where the discharged clause demands it), plus the residual
        // of each dropped assume unit: `¬h` if some premise still carries it to cancel, the
        // stripped `φ` where the pivot ran the other way
        let mut clause: Vec<Rc<Term>> = s.clause.to_vec();
        for (orig, translated) in s
            .premises
            .iter()
            .filter(|p| !matches!(self.memo.get(*p), Some(Replayed::Hyp(_))))
            .zip(&nodes)
        {
            for l in translated.clause() {
                if !orig.clause().contains(l) && !clause.contains(l) {
                    clause.push(l.clone());
                }
            }
        }
        for h in &dropped {
            let nh = build_term!(self.pool, (not {h.clone()}));
            let residual = match h.remove_negation() {
                Some(inner)
                    if !nodes.iter().any(|n| n.clause().contains(&nh))
                        && nodes.iter().any(|n| n.clause().contains(inner)) =>
                {
                    inner.clone()
                }
                _ => nh,
            };
            if !clause.contains(&residual) {
                clause.push(residual);
            }
        }
        if nodes.len() == 1 {
            // A single remaining premise: nothing to resolve, its clause already covers the set
            return Some(Replayed::Node { node: nodes.remove(0), hyps });
        }
        let node = self.emit(clause, &s.rule, nodes, Vec::new())?;
        Some(Replayed::Node { node, hyps })
    }

    fn bookkeeping(&mut self, s: &StepNode) -> Option<Replayed> {
        let [p] = s.premises.as_slice() else {
            return None;
        };
        let Replayed::Node { node, hyps } = self.node(p)? else {
            return None;
        };
        // The premise's clause gained extra literals (hypotheses or their residuals), so the
        // conclusion is recomputed: for contraction and reordering, the original conclusion plus
        // exactly those extras keeps the required multiset relation to the translated premise;
        // weakening instead extends the translated premise with whatever the original step
        // appended, since its conclusion must keep the premise as a prefix
        let clause = if s.rule == "weakening" {
            let appended = s.clause.get(p.clause().len()..).unwrap_or(&[]);
            let mut clause = node.clause().to_vec();
            clause.extend(appended.iter().cloned());
            clause
        } else {
            let mut clause = s.clause.to_vec();
            for l in node.clause() {
                if !p.clause().contains(l) && !clause.contains(l) {
                    clause.push(l.clone());
                }
            }
            clause
        };
        let node = self.emit(clause, &s.rule, vec![node], Vec::new())?;
        Some(Replayed::Node { node, hyps })
    }

    fn and_intro(&mut self, s: &StepNode) -> Option<Replayed> {
        let conj = s.clause.first()?.clone();
        let conjuncts = match_term!((and ...) = &conj)?.to_vec();
        let mut parts: Vec<(Rc<Term>, Replayed)> = Vec::new();
        for p in &s.premises {
            parts.push(self.premise_parts(p)?);
        }
        if parts.len() != conjuncts.len() {
            return None;
        }
        let mut clause = vec![conj.clone()];
        for c in &conjuncts {
            clause.push(build_term!(self.pool, (not {c.clone()})));
        }
        check_premise_free_rule(self.pool, "and_neg", &clause, &[]).ok()?;
        let instance = self.emit(clause, "and_neg", Vec::new(), Vec::new())?;
        self.close_over(instance, parts)
    }

    /// A premise-carrying clausification step, replayed as its premise-free axiom counterpart:
    /// the axiom's clause is `¬premise-term` followed by the step's own conclusion.
    fn clausification(&mut self, s: &StepNode, axiom: &str) -> Option<Replayed> {
        let [p] = s.premises.as_slice() else {
            return None;
        };
        let (term, r) = self.premise_parts(p)?;
        // The `_neg` axioms serve the `not_*` rules, whose premise is a *negated* connective term;
        // the axiom itself carries the connective term positively, so the premise's negation is
        // stripped. The premise then discharges that literal by resolution (a derived premise
        // concluding `¬φ` against the axiom's `φ`); a hypothesis premise leaves it in place, and
        // the final fix-up bridges `φ` to the `¬¬φ` the discharged clause states
        let negated_premise = matches!(
            axiom,
            "equiv_neg1" | "equiv_neg2" | "implies_neg1" | "implies_neg2" | "and_neg" | "or_neg"
        );
        let (instance_lit, premise_lit) = if negated_premise {
            (term.remove_negation()?.clone(), term.clone())
        } else {
            (build_term!(self.pool, (not {term.clone()})), term.clone())
        };
        let mut clause = vec![instance_lit.clone()];
        clause.extend(s.clause.iter().cloned());
        check_premise_free_rule(self.pool, axiom, &clause, &[]).ok()?;
        let instance = self.emit(clause, axiom, Vec::new(), Vec::new())?;
        self.close_over_lits(instance, vec![(instance_lit, premise_lit, r)])
    }

    /// Like [`Self::clausification`], for the axioms that take the selected index as an argument.
    fn indexed_clausification(&mut self, s: &StepNode, axiom: &str) -> Option<Replayed> {
        let [p] = s.premises.as_slice() else {
            return None;
        };
        let (term, r) = self.premise_parts(p)?;
        let inner = term.remove_negation().unwrap_or(&term);
        let (_, args) = inner.as_op().map(|(op, a)| (op, a))?;
        let selected = match axiom {
            "and_pos" => s.clause.first()?.clone(),
            _ => s.clause.first()?.remove_negation()?.clone(),
        };
        let index = args.iter().position(|t| *t == selected)?;
        let negated_premise = axiom == "or_neg";
        let (instance_lit, premise_lit) = if negated_premise {
            (term.remove_negation()?.clone(), term.clone())
        } else {
            (build_term!(self.pool, (not {term.clone()})), term.clone())
        };
        let mut clause = vec![instance_lit.clone()];
        clause.extend(s.clause.iter().cloned());
        let index_arg = vec![self.pool.add(Term::new_int(index))];
        check_premise_free_rule(self.pool, axiom, &clause, &index_arg).ok()?;
        let instance = self.emit(clause, axiom, Vec::new(), index_arg.clone())?;
        self.close_over_lits(instance, vec![(instance_lit, premise_lit, r)])
    }
}
