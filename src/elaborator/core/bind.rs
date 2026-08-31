//! The `bind` reduction: binder congruence from `sko_forall` and `forall_inst`.
//!
//! `bind` closes a subproof that derives `φ ≈ ψ` under an anchor renaming the quantifier's
//! variables, and concludes `(∀x̄.φ) ≈ (∀ȳ.ψ)`. The core derives the same equivalence without it,
//! and the cost depends entirely on what the body actually did.
//!
//! **When the two sides are α-variants** — the case `bind` exists for, where the body is a `refl`
//! chain under the renaming context — the reduction is four steps and does not look at the body
//! at all. Skolemize *both* sides at the *same* witnesses: `sko_forall` compares an anchor's
//! witnesses with its own only up to α-equivalence, so the witnesses ε̄ of `(∀x̄.φ)` serve for
//! `(∀ȳ.ψ)` as well, and both sides Skolemize to the very same term.
//!
//! ```text
//! (cl (= (∀x̄.φ) φ[ε̄]))       refl under the anchor x̄ ↦ ε̄, closed by sko_forall
//! (cl (= (∀ȳ.ψ) φ[ε̄]))       refl under the anchor ȳ ↦ ε̄, closed by sko_forall
//! (cl (= φ[ε̄] (∀ȳ.ψ)))       symm
//! (cl (= (∀x̄.φ) (∀ȳ.ψ)))     trans
//! ```
//!
//! **When the body rewrites** — the sides are not α-variants, so their Skolemizations differ and
//! the body's reasoning has to be transported — the reduction falls back on the route the
//! classification calls *admissibility of the generalized `bind`*: Skolemize the target,
//! instantiate the premise at the same witnesses, and **replay the subproof's derivation with the
//! witnesses substituted for the anchor's variables** — every core rule is schematic, so its
//! instances stay valid under a uniform substitution of closed terms.
//!
//! For one direction, with `ε̄` the sequential ε-witnesses of `(∀ȳ.ψ)`:
//!
//! ```text
//! (cl (∀ȳ.ψ) ¬ψ[ε̄])          the ∀-ε-clause: refl under the witness anchor, sko_forall, equiv2
//! (cl ¬(∀x̄.φ) φ[ε̄])          forall_inst at the witnesses, unpacked by or_pos
//! (cl (= φ[ε̄] ψ[ε̄]))         the replayed body
//! (cl ¬(∀x̄.φ) (∀ȳ.ψ))        equiv_pos2 crossing the two, then resolution
//! ```
//!
//! and symmetrically for the other, with the witnesses of `(∀x̄.φ)`; `equiv_intro` closes. The
//! price is a *copy of the body per direction* — which is why the rule is classified
//! **expensive**: the reduction is complete for the shapes below and buys no checking power, so
//! only the `core-expensive` regime applies it.
//!
//! The generalized (∀-closure) form is cheaper: there is one direction and one replay, since the
//! closure concludes a clause rather than an equivalence.
//!
//! Not covered (the step is kept): a `bind` under an enclosing anchor, whose cumulative
//! substitution the ∀-ε-clause would have to account for; bodies containing a `let` term, which
//! substitution renames independently of its surroundings; binders other than `∀` — `∃` would route through
//! `qnt_duality`, and `choice`/`lambda` congruence has no core route at all (it is the
//! classification's one binder-congruence residue) — anchors whose assignments are not renamings
//! into the declared variables, and nested anchors that bind one of the substituted variables,
//! which would shadow it. Other nested anchors are replayed with the rest: their assignments are
//! substituted and their bodies replayed one level deeper.

use super::Builder;
use crate::{ast::*, checker::error::CheckerError, elaborator::error::ElaborationError};
use indexmap::IndexMap;
use std::collections::HashMap;

type Res = Result<Rc<ProofNode>, ElaborationError>;

fn explanation(msg: impl Into<String>) -> ElaborationError {
    CheckerError::Explanation(msg.into()).into()
}

fn substitute(
    pool: &mut PrimitivePool,
    term: &Rc<Term>,
    map: IndexMap<Rc<Term>, Rc<Term>>,
) -> Rc<Term> {
    if map.is_empty() {
        return term.clone();
    }
    match Substitution::new(pool, map) {
        Ok(mut s) => s.apply(pool, term),
        Err(_) => term.clone(),
    }
}

/// A substitution for the replay, which differs from [`Substitution`] in one respect that the
/// replay cannot do without: it never renames a binder gratuitously.
///
/// Carcara's substitution renames a bound variable `y` when `y` is one of the substituted
/// variables or occurs free in what they are replaced by — the second is genuinely needed to
/// avoid capture, the first is not. Under a binder that binds `x`, the occurrences of `x` are
/// that binder's, so the substitution simply does not reach them; renaming `x` to `x_renamed`
/// gives an α-variant of the right answer, which is fine for a checker comparing terms it built
/// itself, and fatal for a replay, where the renamed term has to keep matching the *same* term
/// reached through a premise from outside the subproof, which nothing renamed.
///
/// So shadowed variables are dropped from the map instead of renamed, and a subterm with nothing
/// free to substitute is returned as it stands, at every level rather than only at the top.
struct Replacement {
    map: IndexMap<Rc<Term>, Rc<Term>>,
    /// The names occurring free in the range, which a binder *does* have to avoid
    captured: Vec<String>,
    cache: HashMap<Rc<Term>, Rc<Term>>,
}

impl Replacement {
    fn new(pool: &mut PrimitivePool, map: IndexMap<Rc<Term>, Rc<Term>>) -> Self {
        let mut captured = Vec::new();
        for value in map.values() {
            for var in pool.free_vars(value).iter() {
                if let Some(name) = var.as_var() {
                    captured.push(name.to_owned());
                }
            }
        }
        captured.sort();
        captured.dedup();
        Self {
            map,
            captured,
            cache: HashMap::new(),
        }
    }

    /// The same substitution with the given names removed — what holds under a binder that binds
    /// them. It gets its own cache, since the same subterm can come out differently there.
    fn shadowing(&self, names: &[String]) -> Self {
        let map = self
            .map
            .iter()
            .filter(|(k, _)| !k.as_var().is_some_and(|n| names.iter().any(|s| s == n)))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        Self {
            map,
            captured: self.captured.clone(),
            cache: HashMap::new(),
        }
    }

    /// This substitution with a `let`'s bindings folded in: the bound names map to their
    /// (already substituted) values, replacing whatever the outer substitution said about them.
    fn extended(
        &self,
        pool: &mut PrimitivePool,
        bindings: &BindingList<Rc<Term>>,
        substituted: &BindingList<Rc<Term>>,
    ) -> Self {
        let names: Vec<String> = bindings.0.iter().map(|(n, _)| n.clone()).collect();
        let mut map: IndexMap<Rc<Term>, Rc<Term>> = self
            .map
            .iter()
            .filter(|(k, _)| !k.as_var().is_some_and(|n| names.contains(&n.to_owned())))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        for (name, value) in &substituted.0 {
            let sort = pool.sort(value);
            let var = pool.add(Term::new_var(name.clone(), sort));
            map.insert(var, value.clone());
        }
        Self::new(pool, map)
    }

    /// Whether the name is one of the variables being replaced.
    fn binds(&self, name: &str) -> bool {
        self.map.keys().any(|k| k.as_var() == Some(name))
    }

    fn apply(&mut self, pool: &mut PrimitivePool, term: &Rc<Term>) -> Rc<Term> {
        if self.map.is_empty() {
            return term.clone();
        }
        if let Some(hit) = self.cache.get(term) {
            return hit.clone();
        }
        let free = pool.free_vars(term);
        if !self.map.keys().any(|k| free.contains(k)) {
            return term.clone();
        }
        let result = match term.as_ref() {
            Term::Var(..) => self.map.get(term).cloned().unwrap_or_else(|| term.clone()),
            Term::Op(op, args) => {
                let (op, args) = (*op, args.clone());
                let args = args.iter().map(|a| self.apply(pool, a)).collect();
                pool.add(Term::Op(op, args))
            }
            Term::App(f, args) => {
                let (f, args) = (f.clone(), args.clone());
                let f = self.apply(pool, &f);
                let args = args.iter().map(|a| self.apply(pool, a)).collect();
                pool.add(Term::App(f, args))
            }
            Term::Binder(q, bindings, body) => {
                let (q, bindings, body) = (*q, bindings.clone(), body.clone());
                let names: Vec<String> = bindings.0.iter().map(|(n, _)| n.clone()).collect();
                if names.iter().any(|n| self.captured.contains(n)) {
                    // A real capture: fall back to the renaming substitution, whose result is
                    // still deterministic in the map, and which the caller's guard covers
                    return substitute(pool, term, self.map.clone());
                }
                let mut under = self.shadowing(&names);
                let body = under.apply(pool, &body);
                pool.add(Term::Binder(q, bindings, body))
            }
            Term::Let(bindings, body) => {
                let (bindings, body) = (bindings.clone(), body.clone());
                let names: Vec<String> = bindings.0.iter().map(|(n, _)| n.clone()).collect();
                if names.iter().any(|n| self.captured.contains(n)) {
                    return substitute(pool, term, self.map.clone());
                }
                let values: Vec<(String, Rc<Term>)> = bindings
                    .0
                    .iter()
                    .map(|(n, v)| (n.clone(), self.apply(pool, v)))
                    .collect();
                let mut under = self.shadowing(&names);
                let body = under.apply(pool, &body);
                pool.add(Term::Let(BindingList(values), body))
            }
            _ => substitute(pool, term, self.map.clone()),
        };
        self.cache.insert(term.clone(), result.clone());
        result
    }
}

/// The sequential ε-witnesses of `(∀ v̄. χ)`, in the shape `sko_forall` checks: the `i`-th is
/// `(choice ((vᵢ Sᵢ)) (not (∀ v_{i+1}…vₙ. χ)))`, with the earlier witnesses already substituted.
/// Returns the witnesses and the successive bodies `χ[v₁↦ε₁, …, vᵢ↦εᵢ]`.
fn witnesses(
    pool: &mut PrimitivePool,
    bindings: &[SortedVar],
    body: &Rc<Term>,
) -> (Vec<Rc<Term>>, Vec<Rc<Term>>) {
    let n = bindings.len();
    let mut stages = vec![body.clone()];
    let mut result = Vec::new();
    for i in 0..n {
        let current = stages[i].clone();
        let mut inner = current.clone();
        if i < n - 1 {
            inner = pool.add(Term::Binder(
                Binder::Forall,
                BindingList(bindings[i + 1..].to_vec()),
                inner,
            ));
        }
        inner = build_term!(pool, (not { inner }));
        let witness = pool.add(Term::Binder(
            Binder::Choice,
            BindingList(vec![bindings[i].clone()]),
            inner,
        ));
        let var = pool.add(Term::from(bindings[i].clone()));
        let next = substitute(pool, &current, IndexMap::from([(var, witness.clone())]));
        stages.push(next);
        result.push(witness);
    }
    (result, stages)
}

/// The substitution an anchor assigning these witnesses actually stands for.
///
/// A context builds its substitution one assignment at a time, applying what it has so far to
/// each new value (see `ContextStack::catch_up_cumulative`). That matters when a binder list
/// repeats a name — veriT writes `(∀ x y y x. φ)` for what binds each of them once — since the
/// later assignment's value is then rewritten by the earlier ones.
fn anchor_map(
    pool: &mut PrimitivePool,
    vars: &[SortedVar],
    ws: &[Rc<Term>],
) -> IndexMap<Rc<Term>, Rc<Term>> {
    let mut map: IndexMap<Rc<Term>, Rc<Term>> = IndexMap::new();
    for (var, w) in vars.iter().zip(ws) {
        let value = substitute(pool, w, map.clone());
        let var_term = pool.add(Term::from(var.clone()));
        map.insert(var_term, value);
    }
    map
}

/// Whether a contextual `refl` can carry `have` to `want` — that is, whether the enclosing
/// substitution is the whole of the difference between them. It usually is, since the one side
/// is the body as written and the other the body as the ε-clause skolemizes it; when it is not,
/// there is no step to state, and the reduction says so instead of writing one that fails.
fn bridgeable(
    b: &mut Builder,
    context: &mut ContextStack,
    have: &Rc<Term>,
    want: &Rc<Term>,
) -> Result<(), ElaborationError> {
    let applied = context.apply(b.pool, have);
    let mut time = std::time::Duration::ZERO;
    if applied == *want || crate::ast::alpha_equiv(&applied, want, &mut time) {
        return Ok(());
    }
    Err(explanation(
        "the replayed body and the ε-clause differ by more than the enclosing substitution",
    ))
}

/// Emits the ∀-ε-clause `(cl (∀ v̄. χ) ¬χ[ε̄])`: a `refl` under an anchor assigning each variable
/// its witness, closed by `sko_forall`, and unpacked by `equiv2`.
fn epsilon_clause(
    b: &mut Builder,
    context: &mut ContextStack,
    quant: &Rc<Term>,
    bindings: &[SortedVar],
    body: &Rc<Term>,
    witnesses: &[Rc<Term>],
) -> Result<(Rc<ProofNode>, Rc<Term>), ElaborationError> {
    let anchor_args: Vec<AnchorArg> = bindings
        .iter()
        .zip(witnesses)
        .map(|(var, w)| AnchorArg::Assign(var.clone(), w.clone()))
        .collect();

    // `sko_forall` recomputes the witnesses for *this* quantifier, from the body as the enclosing
    // substitution leaves it, and compares them with the anchor's up to α-equivalence. Checking
    // that here keeps a caller from handing over witnesses that belong to another quantifier
    {
        // The quantifier and the body must be each other's: `sko_forall` reads the body off the
        // conclusion, so a caller that passes a body from elsewhere gets witnesses for it
        match quant.as_ref() {
            Term::Binder(Binder::Forall, bs, inner) if bs.0 == bindings && inner == body => (),
            _ => {
                return Err(explanation(
                    "the ε-clause's quantifier and body do not match",
                ))
            }
        }
        let body_in_context = context.apply(b.pool, body);
        let (expected, _) =
            crate::elaborator::core::bind::witnesses(b.pool, bindings, &body_in_context);
        let mut time = std::time::Duration::ZERO;
        let matches = expected.len() == witnesses.len()
            && expected
                .iter()
                .zip(witnesses)
                .all(|(e, w)| crate::ast::alpha_equiv(e, w, &mut time));
        if !matches {
            return Err(explanation(
                "the ε-clause's witnesses are not the ones `sko_forall` recomputes",
            ));
        }
    }

    // The Skolemized body is read off the context stack with the anchor pushed, which is what the
    // `refl` inside the scope will be checked against — the enclosing substitution reaches the
    // witnesses there, and composing the two by hand gets that wrong whenever it is not
    // idempotent
    context.push(&anchor_args);
    let skolemized = context.apply(b.pool, body);
    context.pop();
    let skolemized = &skolemized;

    b.open();
    let equality = build_term!(b.pool, (= {body.clone()} {skolemized.clone()}));
    let refl = b.step(vec![equality], "refl", Vec::new(), Vec::new());
    let closing = build_term!(b.pool, (= {quant.clone()} {skolemized.clone()}));
    let sko = b.close_with(
        anchor_args,
        "sko_forall",
        vec![closing.clone()],
        Vec::new(),
        refl,
    );

    // `(cl (∀v̄.χ) ¬χ[ε̄])` from the equivalence — what `equiv2` states, in the core: the CNF
    // axiom `equiv_pos1` resolved against it. The reduction emits only core rules, since nothing
    // runs after the expensive pass to reduce what it leaves
    let not_skolemized = b.not(skolemized);
    let equivalence = closing;
    let not_equivalence = b.not(&equivalence);
    let axiom = b.step(
        vec![not_equivalence, quant.clone(), not_skolemized.clone()],
        "equiv_pos1",
        Vec::new(),
        Vec::new(),
    );
    let clause = b.resolve(vec![axiom, sko], vec![(equivalence, false)])?;
    Ok((clause, skolemized.clone()))
}

/// Emits `(cl ¬(∀ v̄. χ) χ[t̄])`: one `forall_inst` step (whose conclusion is a unit clause holding
/// a disjunction) unpacked by `or_pos`.
fn instantiate(b: &mut Builder, quant: &Rc<Term>, args: Vec<Rc<Term>>, instance: &Rc<Term>) -> Res {
    let not_quant = b.not(quant);
    let or_term = b.pool.add(Term::Op(
        Operator::Or,
        vec![not_quant.clone(), instance.clone()],
    ));
    let inst = b.step(vec![or_term.clone()], "forall_inst", Vec::new(), args);
    let not_or = b.not(&or_term);
    let or_pos = b.step(
        vec![not_or, not_quant, instance.clone()],
        "or_pos",
        Vec::new(),
        Vec::new(),
    );
    b.resolve(vec![or_pos, inst], vec![(or_term, false)])
}

/// Replays a derivation with a substitution applied to every step it contains.
///
/// Every core rule is schematic, so a derivation stays valid when closed terms are substituted
/// uniformly for its free variables — which is what lets the body of a `bind` subproof be reused
/// at the ε-witnesses. Premises from outside the subproof are left alone: the anchor's variables
/// cannot occur in them. Nested anchors are refused, since their own substitutions would have to
/// be composed with this one.
type ReplayCache = HashMap<(Rc<ProofNode>, usize), Rc<ProofNode>>;

/// Transports one of the body's terms into the replay: the witness substitution, and nothing
/// else.
///
/// The enclosing anchors' substitution is deliberately *not* applied. The replayed derivation
/// sits at the same depth as the `bind` step it replaces, so its `refl` leaves are checked
/// against the same cumulative context the originals were; every other rule compares terms
/// syntactically, and premises reached from *outside* the subproof keep the shape they have
/// there, which they would not if the replay rewrote its terms.
///
/// What makes this hold under an enclosing anchor is that the witnesses are built over the
/// context-applied body: being closed under the enclosing substitution, they commute with it, so
/// a `refl` leaf that held as `Γ(ρ(a)) ≡ b` still holds as `Γ(σ(a)) ≡ σ(b)`.
fn transport(
    b: &mut Builder,
    _context: &mut ContextStack,
    replacement: &mut Replacement,
    term: &Rc<Term>,
) -> Rc<Term> {
    replacement.apply(b.pool, term)
}

/// `levels` maps a scope's depth in the original proof to the depth the replay has put it at.
/// The two differ by the `bind` anchor being eliminated, by every nested `let` scope dissolved
/// along the way, and by nothing else — but not uniformly, so the correspondence is recorded as
/// the replay descends rather than computed from a difference. It is what places an assumption:
/// a step in a deeper scope is often the first to reach one, and the node's depth is what decides
/// which subproof prints it.
#[allow(clippy::too_many_arguments)]
fn replay(
    b: &mut Builder,
    context: &mut ContextStack,
    node: &Rc<ProofNode>,
    replacement: &mut Replacement,
    inner_depth: usize,
    levels: &mut Vec<(usize, usize)>,
    cache: &mut ReplayCache,
    assumes: &mut ReplayCache,
) -> Res {
    // The cache is per scope (see the nested-subproof arm), so the depth in the key only guards
    // against a node being reused across the boundary of the scope that built it
    let key = (node.clone(), b.depth());
    if let Some(done) = cache.get(&key) {
        return Ok(done.clone());
    }
    if node.depth() < inner_depth {
        // A premise from outside the subproof, which the substitution cannot touch
        return Ok(node.clone());
    }
    let result = match node.as_ref() {
        ProofNode::Assume { term, depth, .. } => {
            // The replay drops levels — the `bind` anchor, and every `let` scope it dissolves —
            // so an assumption belongs at the depth its own scope has landed at, which is not
            // necessarily the one being built: a step in a deeper scope can be the first to need
            // it. The node's depth is what decides which subproof prints it
            let Some(&(_, at)) = levels.iter().rev().find(|(orig, _)| orig == depth) else {
                return Err(explanation(
                    "an assumption of a scope the replay has not entered",
                ));
            };
            // Assumptions are shared across the scopes of one replay, not cached per scope like
            // everything else: the scope that discharges an assumption and the one that uses it
            // are different scopes, and two copies would leave one of them undischarged
            let key = (node.clone(), at);
            if let Some(done) = assumes.get(&key) {
                return Ok(done.clone());
            }
            let term = transport(b, context, replacement, term);
            let assumption = b.assume_at(at, term);
            assumes.insert(key, assumption.clone());
            assumption
        }
        ProofNode::Subproof(sub) => {
            let Some(last) = sub.last_step.as_step() else {
                return Err(explanation("nested subproof does not end in a step"));
            };

            // These closings replay soundly because the substitution is of terms the scope does
            // not bind (the rebinds guard ensures it), so it commutes with whatever the closing
            // rule recomputes — `sko_forall`'s witnesses, `let`'s anchor-to-binding match.
            // `onepoint` has a side condition the replay does not track
            // A nested `let` scope is dissolved rather than replayed: keeping its anchor would
            // mean keeping the checker's composition of two substitutions in step with ours
            if last.rule == "let" {
                let Some(inner) = &last.previous_step else {
                    return Err(explanation("a `let` step with no previous step"));
                };
                let inner = inner.clone();
                return replay_let(
                    b,
                    context,
                    last,
                    &inner,
                    replacement,
                    inner_depth,
                    levels,
                    cache,
                    assumes,
                );
            }
            // `onepoint` is the one closing whose side condition the replay does not track: it
            // reads the points off the body, and the substituted body can offer different ones
            if last.rule == "onepoint" {
                return Err(explanation("nested scope closed by `onepoint`"));
            }
            // A nested anchor that binds a variable this substitution touches would shadow it.
            // Unlike a binder inside a term, an anchor's variable cannot be renamed away here —
            // the scope's own steps name it
            let shadows = sub.args.iter().any(|arg| {
                let var = match arg {
                    AnchorArg::Variable(v) | AnchorArg::Assign(v, _) => v,
                };
                replacement.binds(var.0.as_str())
            });
            if shadows {
                return Err(explanation("nested anchor shadows a substituted variable"));
            }
            let args: Vec<AnchorArg> = sub
                .args
                .iter()
                .map(|arg| match arg {
                    AnchorArg::Variable(v) => AnchorArg::Variable(v.clone()),
                    AnchorArg::Assign(v, value) => {
                        AnchorArg::Assign(v.clone(), transport(b, context, replacement, value))
                    }
                })
                .collect();
            let Some(previous) = &last.previous_step else {
                return Err(explanation("nested closing step has no previous step"));
            };

            // A nested scope gets its own cache: a replayed node lives inside the scope that
            // built it, so a sibling scope needs a copy of its own
            b.open();
            // The scope's anchor joins the context too, so that anything built inside it — an
            // expansion read off the context stack, a contextual `refl` — is written against the
            // same cumulative substitution the checker will apply there
            context.push(&args);
            levels.push((last.depth, b.depth()));
            let mut inner_cache = ReplayCache::new();
            type Scoped =
                Result<(Rc<ProofNode>, Vec<Rc<ProofNode>>, Vec<Rc<ProofNode>>), ElaborationError>;
            let mut scoped = |b: &mut Builder, context: &mut ContextStack| -> Scoped {
                // Every assumption of the scope comes first, discharged or not: a subproof's
                // `assume` commands have to precede its steps, while the replay emits nodes in
                // the order it builds them, which follows the premises
                let mut discharge = Vec::new();
                for a in &last.discharge {
                    discharge.push(replay(
                        b,
                        context,
                        a,
                        replacement,
                        inner_depth,
                        levels,
                        &mut inner_cache,
                        assumes,
                    )?);
                }
                let inner = replay(
                    b,
                    context,
                    previous,
                    replacement,
                    inner_depth,
                    levels,
                    &mut inner_cache,
                    assumes,
                )?;
                let mut premises = Vec::new();
                for p in &last.premises {
                    premises.push(replay(
                        b,
                        context,
                        p,
                        replacement,
                        inner_depth,
                        levels,
                        &mut inner_cache,
                        assumes,
                    )?);
                }
                Ok((inner, discharge, premises))
            };
            let scoped = scoped(b, context);
            context.pop();
            levels.pop();
            let (inner, discharge, premises) = scoped?;
            let clause: Vec<_> = last
                .clause
                .iter()
                .map(|t| transport(b, context, replacement, t))
                .collect();
            b.close_with_premises(args, &last.rule, clause, premises, discharge, inner)
        }
        ProofNode::Step(s) => {
            let mut premises = Vec::new();
            for p in &s.premises {
                premises.push(replay(
                    b,
                    context,
                    p,
                    replacement,
                    inner_depth,
                    levels,
                    cache,
                    assumes,
                )?);
            }
            let clause: Vec<_> = s
                .clause
                .iter()
                .map(|t| transport(b, context, replacement, t))
                .collect();
            let args: Vec<_> = s
                .args
                .iter()
                .map(|t| transport(b, context, replacement, t))
                .collect();
            b.step(clause, &s.rule, premises, args)
        }
    };
    cache.insert(key, result.clone());
    Ok(result)
}

/// Replays a nested `let` scope by *dissolving* it: its bindings join the witness substitution,
/// so the body is replayed one level out, and the `let` step it closed is rebuilt as what it
/// always was — a definitional expansion.
///
/// Replaying the scope as it stands would keep its anchor, and the checker composes an anchor's
/// assignment with the enclosing substitution; keeping that composition in step with the witness
/// one is exactly the difficulty the replay exists to avoid. Expanding instead leaves nothing to
/// compose: one `let` scope whose body is the `refl` that states the expansion, and a `trans`.
#[allow(clippy::too_many_arguments)]
#[allow(clippy::too_many_arguments)]
fn replay_let(
    b: &mut Builder,
    context: &mut ContextStack,
    last: &StepNode,
    previous: &Rc<ProofNode>,
    replacement: &mut Replacement,
    inner_depth: usize,
    levels: &mut Vec<(usize, usize)>,
    _cache: &mut ReplayCache,
    assumes: &mut ReplayCache,
) -> Res {
    let [conclusion] = last.clause.as_slice() else {
        return Err(explanation("a `let` step with a non-unit clause"));
    };
    let (let_term, rewritten) = match_term_err!((= l r) = conclusion)?;
    let (let_term, rewritten) = (let_term.clone(), rewritten.clone());
    let Some((bindings, _)) = let_term.as_let() else {
        return Err(explanation(
            "a `let` step whose conclusion is not about a `let`",
        ));
    };
    let bindings = bindings.clone();

    // The whole `let` term under the witness substitution — which leaves the bound names alone,
    // since `Replacement` drops what a binder shadows
    let new_let = replacement.apply(b.pool, &let_term);
    let new_rewritten = replacement.apply(b.pool, &rewritten);
    let Some((new_bindings, new_body)) = new_let.as_let() else {
        return Err(explanation("the substituted term is no longer a `let`"));
    };
    let (new_bindings, new_body) = (new_bindings.clone(), new_body.clone());

    // The expansion, read off the context stack with the anchor pushed, so that it agrees with
    // what the `let` rule recomputes
    let anchor: Vec<AnchorArg> = new_bindings
        .0
        .iter()
        .map(|(name, value)| {
            let sort = b.pool.sort(value);
            AnchorArg::Assign((name.clone(), sort), value.clone())
        })
        .collect();
    context.push(&anchor);
    let expanded = context.apply(b.pool, &new_body);
    context.pop();

    let expansion = {
        b.open();
        let equality = build_term!(b.pool, (= {new_body.clone()} {expanded.clone()}));
        let refl = b.step(vec![equality], "refl", Vec::new(), Vec::new());
        let closing = build_term!(b.pool, (= {new_let.clone()} {expanded.clone()}));
        b.close_with(anchor, "let", vec![closing], Vec::new(), refl)
    };

    // The body, replayed with the bindings folded into the substitution: what it proved under the
    // scope's context, it now proves about the expansion
    let mut extended = replacement.extended(b.pool, &bindings, &new_bindings);
    let mut cache = ReplayCache::new();
    // The scope is dissolved: its contents land at the depth the replay is already at
    levels.push((last.depth, b.depth()));
    let body = replay(
        b,
        context,
        previous,
        &mut extended,
        inner_depth,
        levels,
        &mut cache,
        assumes,
    );
    levels.pop();
    let body = body?;
    let [equality] = body.clause() else {
        return Err(explanation(
            "the body of a `let` scope is not a unit equality",
        ));
    };
    let (left, right) = match_term_err!((= l r) = equality)?;
    let (left, right) = (left.clone(), right.clone());

    // The expansion is read off the context stack, so it carries the enclosing substitution,
    // while the replayed body is written as the body writes it. Contextual `refl`s bridge the
    // difference, in the one direction that has content
    let mut premises = vec![expansion];
    if left != expanded {
        let clause = vec![build_term!(b.pool, (= {left.clone()} {expanded.clone()}))];
        let bridge = b.step(clause, "refl", Vec::new(), Vec::new());
        premises.push(b.symm(&bridge));
    }
    premises.push(body);
    if right != new_rewritten {
        let clause = vec![build_term!(b.pool, (= {right.clone()} {new_rewritten.clone()}))];
        premises.push(b.step(clause, "refl", Vec::new(), Vec::new()));
    }

    let clause = vec![build_term!(b.pool, (= {new_let} {new_rewritten}))];
    Ok(b.step(clause, "trans", premises, Vec::new()))
}

/// The anchor's renaming, as the pair of binder lists it renames between.
fn anchor_renaming(args: &[AnchorArg]) -> Option<(Vec<SortedVar>, Vec<SortedVar>)> {
    let mut declared = Vec::new();
    let mut assigned = Vec::new();
    for arg in args {
        match arg {
            AnchorArg::Variable(var) => declared.push(var.clone()),
            AnchorArg::Assign(var, value) => {
                let name = value.as_var()?;
                let target = declared.iter().find(|(n, _)| n == name)?;
                assigned.push((var.clone(), target.clone()));
            }
        }
    }

    // An anchor that only declares variables renames nothing: both sides bind the same names, and
    // the identity is the renaming between them
    if assigned.is_empty() {
        return Some((declared.clone(), declared));
    }
    Some((
        assigned.iter().map(|(x, _)| x.clone()).collect(),
        assigned.iter().map(|(_, y)| y.clone()).collect(),
    ))
}

/// Reduces a whole `bind` subproof. `subproof` is the [`ProofNode::Subproof`] whose last step is
/// the `bind`; the result replaces it, at the same depth.
pub fn bind(pool: &mut PrimitivePool, context: &mut ContextStack, subproof: &Rc<ProofNode>) -> Res {
    let ProofNode::Subproof(sub) = subproof.as_ref() else {
        return Err(explanation("not a subproof"));
    };

    let Some(last) = sub.last_step.as_step() else {
        return Err(explanation("subproof does not end in a step"));
    };
    let Some(previous) = &last.previous_step else {
        return Err(explanation("`bind` has no previous step"));
    };
    let inner_depth = sub.last_step.depth();
    let mut b = Builder::new(pool, last);
    // The reduction lives at the depth of the subproof, not of its body
    b.leave();

    // The vanilla form: a unit clause holding an equivalence between two quantified terms.
    // `∃` congruence routes through the duality: `(∃x̄.φ) ≈ ¬(∀x̄.¬φ)` on both sides, the `∀`
    // machinery on the negated bodies, and `cong`/`trans` to join the three equivalences
    if let [conclusion] = last.clause.as_slice() {
        if let Some((lhs, rhs)) = match_term!((= l r) = conclusion) {
            let (lhs, rhs) = (lhs.clone(), rhs.clone());
            if exists_parts(&lhs).is_some() {
                return exists_congruence(&mut b, context, sub, previous, inner_depth, &lhs, &rhs);
            }
            return congruence(&mut b, context, sub, previous, inner_depth, &lhs, &rhs);
        }
    }

    // The generalized form: a clause with one literal closed as `(∀Ȳ. l)`, the others passing
    // through
    closure(&mut b, context, sub, previous, inner_depth, &last.clause)
}

fn quant_parts(term: &Rc<Term>) -> Option<(Vec<SortedVar>, Rc<Term>)> {
    match term.as_ref() {
        Term::Binder(Binder::Forall, bindings, body) => Some((bindings.0.clone(), body.clone())),
        _ => None,
    }
}

fn exists_parts(term: &Rc<Term>) -> Option<(Vec<SortedVar>, Rc<Term>)> {
    match term.as_ref() {
        Term::Binder(Binder::Exists, bindings, body) => Some((bindings.0.clone(), body.clone())),
        _ => None,
    }
}

/// `∃` congruence through the duality: from the body's `φ ≈ ψ`, derive
/// `(∃x̄.φ) ≈ ¬(∀x̄.¬φ) ≈ ¬(∀ȳ.¬ψ) ≈ (∃ȳ.ψ)`. The middle link is the `∀` machinery applied to the
/// negated bodies — its α-renaming fast path applies exactly when the original bodies are
/// α-variants — lifted over the negation by `cong`; the outer links are two `qnt_duality` axioms.
#[allow(clippy::too_many_arguments)]
fn exists_congruence(
    b: &mut Builder,
    context: &mut ContextStack,
    sub: &SubproofNode,
    previous: &Rc<ProofNode>,
    inner_depth: usize,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
) -> Res {
    let (Some((x_vars, phi)), Some((y_vars, psi))) = (exists_parts(lhs), exists_parts(rhs)) else {
        return Err(explanation("`exists` congruence with a non-`exists` side"));
    };

    // The dual quantifiers, over the negated bodies
    let (not_phi, not_psi) = (b.not(&phi), b.not(&psi));
    let forall_left = b.pool.add(Term::Binder(
        Binder::Forall,
        BindingList(x_vars),
        not_phi.clone(),
    ));
    let forall_right = b.pool.add(Term::Binder(
        Binder::Forall,
        BindingList(y_vars),
        not_psi.clone(),
    ));

    // `(cl (= (∀x̄.¬φ) (∀ȳ.¬ψ)))`, by the `∀` machinery. The subproof's own body concludes
    // `φ ≈ ψ`; the negated equivalence it needs is one `cong` over it, so the replay route sees a
    // body one step longer
    let neg_previous = {
        let clause = vec![build_term!(b.pool, (= {not_phi.clone()} {not_psi.clone()}))];
        // Build at the body's depth, since it is a premise of the (replayed) body's scope
        b.open();
        let step = b.step(clause, "cong", vec![previous.clone()], Vec::new());
        b.leave_scope();
        step
    };
    let inner = congruence(
        b,
        context,
        sub,
        &neg_previous,
        inner_depth,
        &forall_left,
        &forall_right,
    )?;

    // Lift over the negation and join with the two dualities
    let not_forall_left = b.not(&forall_left);
    let not_forall_right = b.not(&forall_right);
    let lifted = {
        let clause = vec![build_term!(
            b.pool,
            (= {not_forall_left.clone()} {not_forall_right.clone()})
        )];
        b.step(clause, "cong", vec![inner], Vec::new())
    };
    let dual_left = {
        let clause = vec![build_term!(b.pool, (= {lhs.clone()} {not_forall_left}))];
        b.step(clause, "qnt_duality", Vec::new(), Vec::new())
    };
    let dual_right = {
        let clause = vec![build_term!(b.pool, (= {rhs.clone()} {not_forall_right}))];
        b.step(clause, "qnt_duality", Vec::new(), Vec::new())
    };
    let flipped = b.symm(&dual_right);
    let conclusion = build_term!(b.pool, (= {lhs.clone()} {rhs.clone()}));
    Ok(b.step(
        vec![conclusion],
        "trans",
        vec![dual_left, lifted, flipped],
        Vec::new(),
    ))
}

/// The shape of a term, for diagnostics — naming it does not print it, which the printer's sort
/// lookup would need and cannot always do for a term built mid-elaboration.
fn kind(term: &Rc<Term>) -> String {
    match term.as_ref() {
        Term::Const(_) => "const".to_owned(),
        Term::Var(..) => "var".to_owned(),
        Term::App(..) => "app".to_owned(),
        Term::Op(op, _) => format!("op {op}"),
        Term::Binder(q, ..) => format!("binder {q}"),
        Term::Let(..) => "let".to_owned(),
        Term::ParamOp { op, .. } => format!("paramop {op}"),
        Term::Match(..) => "match".to_owned(),
        Term::AsOp(..) => "asop".to_owned(),
    }
}

/// Derives `(cl (= a b))` for two α-equivalent terms, by structural recursion.
///
/// Equal terms are `refl`; an application whose children differ only α-recursively is `cong`
/// over the bridged children; a quantifier pair is [`alpha_quant`]. `choice`, `lambda` and `let`
/// differences have no core route (ε has no introduction or elimination rules — this is the
/// classification's divergence-5 residue), so those fail and the caller keeps its step.
fn alpha_bridge(b: &mut Builder, context: &mut ContextStack, a: &Rc<Term>, t: &Rc<Term>) -> Res {
    let mut time = std::time::Duration::ZERO;
    if a == t
        || context.apply(b.pool, a) == *t
        || crate::ast::alpha_equiv(&context.apply(b.pool, a), t, &mut time)
    {
        // Equal outright, equal under the enclosing anchor's substitution — which is what a
        // contextual `refl` states — or equal up to the names of bound variables, which is what
        // `refl` means in the specification, and the only way to relate two terms that differ by
        // a capture-avoiding renaming
        let clause = vec![build_term!(b.pool, (= {a.clone()} {t.clone()}))];
        return Ok(b.step(clause, "refl", Vec::new(), Vec::new()));
    }
    match (a.as_ref(), t.as_ref()) {
        // Equalities first: veriT reorients `(= a b)` after substituting, so the positional
        // bridge is tried and the crossed one (through `cong`'s four-orientation search on a
        // two-argument equality pair) backs it up
        (Term::Op(Operator::Equals, args_a), Term::Op(Operator::Equals, args_t))
            if args_a.len() == 2 && args_t.len() == 2 =>
        {
            let (a1, a2) = (args_a[0].clone(), args_a[1].clone());
            let (t1, t2) = (args_t[0].clone(), args_t[1].clone());
            let equivalence = build_term!(b.pool, (= {a.clone()} {t.clone()}));
            let positional = (|| -> Res {
                let mut premises = Vec::new();
                for (x, y) in [(&a1, &t1), (&a2, &t2)] {
                    if x != y {
                        premises.push(alpha_bridge(b, context, x, y)?);
                    }
                }
                Ok(b.step(vec![equivalence.clone()], "cong", premises, Vec::new()))
            })();
            if let Ok(node) = positional {
                return Ok(node);
            }
            let p1 = alpha_bridge(b, context, &a1, &t2)?;
            let p2 = alpha_bridge(b, context, &a2, &t1)?;
            let premise_terms: Vec<Rc<Term>> =
                [&p1, &p2].iter().map(|n| n.clause()[0].clone()).collect();
            crate::checker::cong_equal(b.pool, &premise_terms, &equivalence)?;
            Ok(b.step(vec![equivalence], "cong", vec![p1, p2], Vec::new()))
        }
        (Term::Binder(qa, _, _), Term::Binder(qt, _, _)) if qa == qt => match qa {
            Binder::Forall | Binder::Exists => alpha_quant(b, context, a, t),
            _ => Err(explanation(
                "α-difference under a `choice`/`lambda` binder has no core route",
            )),
        },
        (Term::Let(..), Term::Let(..)) => alpha_let(b, context, a, t),
        (Term::Op(op_a, args_a), Term::Op(op_t, args_t))
            if op_a == op_t && args_a.len() == args_t.len() =>
        {
            let (args_a, args_t) = (args_a.clone(), args_t.clone());
            let mut premises = Vec::new();
            for (x, y) in args_a.iter().zip(&args_t) {
                if x != y {
                    premises.push(alpha_bridge(b, context, x, y)?);
                }
            }
            let clause = vec![build_term!(b.pool, (= {a.clone()} {t.clone()}))];
            Ok(b.step(clause, "cong", premises, Vec::new()))
        }
        (Term::App(fa, args_a), Term::App(ft, args_t))
            if fa == ft && args_a.len() == args_t.len() =>
        {
            let (args_a, args_t) = (args_a.clone(), args_t.clone());
            let mut premises = Vec::new();
            for (x, y) in args_a.iter().zip(&args_t) {
                if x != y {
                    premises.push(alpha_bridge(b, context, x, y)?);
                }
            }
            let clause = vec![build_term!(b.pool, (= {a.clone()} {t.clone()}))];
            Ok(b.step(clause, "cong", premises, Vec::new()))
        }
        _ => Err(explanation(format!(
            "terms differ beyond α-equivalence ({} vs {})",
            kind(a),
            kind(t)
        ))),
    }
}

/// Derives `(cl (= (Qx̄.φ) (Qȳ.ψ)))` for two α-equivalent quantified terms, entirely from the
/// core: instantiate *both* sides at the target side's ε-witnesses, so that the two instances
/// differ only under φ's and ψ's own *nested* binders, and bridge those recursively.
///
/// For one direction, with ε̄ the witnesses of `(∀ȳ.ψ)`:
///
/// ```text
/// (cl (∀ȳ.ψ) ¬ψ[ε̄])          the ∀-ε-clause
/// (cl ¬(∀x̄.φ) φ[x̄↦ε̄])        forall_inst at the same witnesses, unpacked by or_pos
/// (cl (= φ[x̄↦ε̄] ψ[ȳ↦ε̄]))     the recursive bridge — nested α-differences only
/// (cl ¬(∀x̄.φ) (∀ȳ.ψ))        equiv_pos2 crossing the three
/// ```
///
/// The `∃` case routes through the duality first. Termination: each recursion strips one binder
/// layer from both sides.
fn alpha_quant(b: &mut Builder, context: &mut ContextStack, lhs: &Rc<Term>, rhs: &Rc<Term>) -> Res {
    if exists_parts(lhs).is_some() {
        return alpha_exists(b, context, lhs, rhs);
    }
    let (Some((x_vars, phi)), Some((y_vars, psi))) = (quant_parts(lhs), quant_parts(rhs)) else {
        return Err(explanation("not a `forall` pair"));
    };
    if x_vars.len() != y_vars.len()
        || x_vars
            .iter()
            .zip(&y_vars)
            .any(|((_, sa), (_, sb))| sa != sb)
    {
        return Err(explanation("binder lists differ in length or sorts"));
    }

    let direction = |b: &mut Builder, context: &mut ContextStack, forward: bool| -> Res {
        let (from, from_vars, from_body, to, to_vars, to_body) = if forward {
            (lhs, &x_vars, &phi, rhs, &y_vars, &psi)
        } else {
            (rhs, &y_vars, &psi, lhs, &x_vars, &phi)
        };
        // `sko_forall`'s checker recomputes the witnesses over the *context-applied* body, so
        // they are built there; the ε-clause's own `refl` is contextual and reconciles the two
        let to_body_ctx = context.apply(b.pool, to_body);
        let (ws, _) = witnesses(b.pool, to_vars, &to_body_ctx);
        let (eps, to_skolemized) = epsilon_clause(b, context, to, to_vars, to_body, &ws)?;

        // `forall_inst` is context-free, so the instance is of the body *as written*
        let map: IndexMap<_, _> = from_vars
            .iter()
            .zip(&ws)
            .map(|(var, w)| (b.pool.add(Term::from(var.clone())), w.clone()))
            .collect();
        let from_skolemized = substitute(b.pool, from_body, map);
        let inst = instantiate(b, from, ws.clone(), &from_skolemized)?;

        // The two instances differ under nested binders, and at free variables the enclosing
        // anchor renames; bridge both recursively
        let bridged = alpha_bridge(b, context, &from_skolemized, &to_skolemized)?;
        let equality = build_term!(b.pool, (= {from_skolemized.clone()} {to_skolemized.clone()}));
        let (not_equality, not_from_sk) = (b.not(&equality), b.not(&from_skolemized));
        let axiom = b.step(
            vec![not_equality, not_from_sk, to_skolemized.clone()],
            "equiv_pos2",
            Vec::new(),
            Vec::new(),
        );
        let crossed = b.resolve(vec![axiom, bridged], vec![(equality, false)])?;
        let with_inst = b.resolve(vec![crossed, inst], vec![(from_skolemized, false)])?;
        b.resolve(vec![with_inst, eps], vec![(to_skolemized, true)])
    };
    let forward = direction(b, context, true)?;
    let backward = direction(b, context, false)?;
    b.equiv_intro(lhs.clone(), rhs.clone(), forward, backward)
}

/// Two α-equivalent `let` terms, expanded and rejoined — the `let` analogue of [`alpha_quant`],
/// and the same shape: each side reduces to its own expansion by one `let` scope (whose body is
/// the contextual `refl` that states the expansion), the expansions are bridged recursively, and
/// `symm`/`trans` close the equivalence.
///
/// `bind_let` cannot do this: its checker requires the two binding lists to carry the *same*
/// names, which is exactly what an α-difference violates. Expanding sidesteps the question — a
/// `let` is a definition, and two definitions that differ only in the defined name have the same
/// expansion.
fn alpha_let(b: &mut Builder, context: &mut ContextStack, a: &Rc<Term>, t: &Rc<Term>) -> Res {
    let (Some((a_bindings, a_body)), Some((t_bindings, t_body))) = (a.as_let(), t.as_let()) else {
        return Err(explanation("not a `let` pair"));
    };
    if a_bindings.len() != t_bindings.len() {
        return Err(explanation("`let` binding lists differ in length"));
    }
    let (a_bindings, a_body) = (a_bindings.clone(), a_body.clone());
    let (t_bindings, t_body) = (t_bindings.clone(), t_body.clone());

    let side = |b: &mut Builder,
                context: &mut ContextStack,
                term: &Rc<Term>,
                bindings: &BindingList<Rc<Term>>,
                body: &Rc<Term>|
     -> (Rc<ProofNode>, Rc<Term>) {
        // The expansion is taken from the context stack itself, with the anchor pushed: the
        // checker computes it by one cumulative substitution, and computing it here in two
        // (enclosing first, then the bindings) can rename a shadowing binder differently
        let anchor: Vec<AnchorArg> = bindings
            .0
            .iter()
            .map(|(name, value)| {
                let sort = b.pool.sort(value);
                AnchorArg::Assign((name.clone(), sort), value.clone())
            })
            .collect();
        context.push(&anchor);
        let expanded = context.apply(b.pool, body);
        context.pop();

        b.open();
        let equality = build_term!(b.pool, (= {body.clone()} {expanded.clone()}));
        let refl = b.step(vec![equality], "refl", Vec::new(), Vec::new());
        let closing = build_term!(b.pool, (= {term.clone()} {expanded.clone()}));
        let node = b.close_with(anchor, "let", vec![closing], Vec::new(), refl);
        (node, expanded)
    };

    let (left, a_expanded) = side(b, context, a, &a_bindings, &a_body);
    let (right, t_expanded) = side(b, context, t, &t_bindings, &t_body);
    let flipped = b.symm(&right);
    let conclusion = build_term!(b.pool, (= {a.clone()} {t.clone()}));
    if a_expanded == t_expanded {
        return Ok(b.step(vec![conclusion], "trans", vec![left, flipped], Vec::new()));
    }
    let middle = alpha_bridge(b, context, &a_expanded, &t_expanded)?;
    Ok(b.step(
        vec![conclusion],
        "trans",
        vec![left, middle, flipped],
        Vec::new(),
    ))
}

/// The `∃` half of [`alpha_quant`]: both sides through `qnt_duality`, the `∀` case on the negated
/// bodies, `cong` over the negation, `trans` to join.
fn alpha_exists(
    b: &mut Builder,
    context: &mut ContextStack,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
) -> Res {
    let (Some((x_vars, phi)), Some((y_vars, psi))) = (exists_parts(lhs), exists_parts(rhs)) else {
        return Err(explanation("not an `exists` pair"));
    };
    let (not_phi, not_psi) = (b.not(&phi), b.not(&psi));
    let forall_left = b
        .pool
        .add(Term::Binder(Binder::Forall, BindingList(x_vars), not_phi));
    let forall_right = b
        .pool
        .add(Term::Binder(Binder::Forall, BindingList(y_vars), not_psi));
    let inner = alpha_quant(b, context, &forall_left, &forall_right)?;

    let (not_forall_left, not_forall_right) = (b.not(&forall_left), b.not(&forall_right));
    let lifted = {
        let clause = vec![build_term!(
            b.pool,
            (= {not_forall_left.clone()} {not_forall_right.clone()})
        )];
        b.step(clause, "cong", vec![inner], Vec::new())
    };
    let dual_left = {
        let clause = vec![build_term!(b.pool, (= {lhs.clone()} {not_forall_left}))];
        b.step(clause, "qnt_duality", Vec::new(), Vec::new())
    };
    let dual_right = {
        let clause = vec![build_term!(b.pool, (= {rhs.clone()} {not_forall_right}))];
        b.step(clause, "qnt_duality", Vec::new(), Vec::new())
    };
    let flipped = b.symm(&dual_right);
    let conclusion = build_term!(b.pool, (= {lhs.clone()} {rhs.clone()}));
    Ok(b.step(
        vec![conclusion],
        "trans",
        vec![dual_left, lifted, flipped],
        Vec::new(),
    ))
}

/// The vanilla case: `(∀x̄.φ) ≈ (∀ȳ.ψ)` from the body's `φ ≈ ψ`.
///
/// Under an enclosing anchor the judgment is contextual — what it asserts is `Γ(∀x̄.φ) ≈ (∀ȳ.ψ)`
/// — while most of the rules the reduction is built from are not. The seam is handled where it
/// appears: the ε-clause is about the context-applied body, since that is what `sko_forall`'s
/// checker recomputes its witnesses from, and one contextual `refl` step joins it to the replayed
/// body, which stays as written.
#[allow(clippy::too_many_arguments)]
fn congruence(
    b: &mut Builder,
    context: &mut ContextStack,
    sub: &SubproofNode,
    previous: &Rc<ProofNode>,
    inner_depth: usize,
    lhs: &Rc<Term>,
    rhs: &Rc<Term>,
) -> Res {
    let (Some((x_vars, phi)), Some((y_vars, psi))) = (quant_parts(lhs), quant_parts(rhs)) else {
        let kind = lhs
            .as_binder()
            .map(|(q, _, _)| format!("{q}"))
            .unwrap_or_else(|| "non-binder".to_owned());
        return Err(explanation(format!(
            "the `bind` reduction covers `forall` congruence only, not `{kind}`"
        )));
    };

    // An anchor that only declares variables renames nothing — both sides bind the same names —
    // so the renaming is the identity on the quantifier's own variables
    let declares_only = sub
        .args
        .iter()
        .all(|arg| matches!(arg, AnchorArg::Variable(_)));
    if declares_only {
        // The lists may differ in a repeated binder — `(∀ x y y x. φ)` binds each of x and y
        // once — so what has to agree is which variables they bind, not how often
        let names = |vars: &[SortedVar]| {
            let mut names: Vec<String> = vars.iter().map(|(n, _)| n.clone()).collect();
            names.sort();
            names.dedup();
            names
        };
        if names(&x_vars) != names(&y_vars) {
            return Err(explanation(format!(
                "an anchor that renames nothing, between quantifiers binding [{}] and [{}]",
                x_vars
                    .iter()
                    .map(|(n, _)| n.clone())
                    .collect::<Vec<_>>()
                    .join(" "),
                y_vars
                    .iter()
                    .map(|(n, _)| n.clone())
                    .collect::<Vec<_>>()
                    .join(" ")
            )));
        }
    } else {
        let Some((assigned, targets)) = anchor_renaming(&sub.args) else {
            return Err(explanation("the anchor is not a renaming"));
        };
        if assigned != x_vars || targets != y_vars {
            return Err(explanation(
                "the anchor does not rename the quantifier's own variables",
            ));
        }
    }

    // When the two sides are α-variants — which is what `bind` is *for*, and what the body then
    // proves by `refl` under the renaming context — the equivalence needs no replay at all.
    // Skolemizing both sides at the *same* witnesses gives the same term, so `sko_forall` twice,
    // one `symm` and one `trans` close it, in four steps and independently of the body's size.
    // `sko_forall` compares the anchor's witnesses with its own up to α-equivalence, which is
    // exactly the slack this uses: the witnesses of `(∀x̄.φ)` serve for `(∀ȳ.ψ)` too
    // The four-step and α routes pair the binders position by position, so they need lists of
    // the same length; the replay route below reads the witnesses by name and does not
    let same_arity = x_vars.len() == y_vars.len();
    let renaming: IndexMap<_, _> = x_vars
        .iter()
        .zip(&y_vars)
        .map(|(x, y)| {
            (
                b.pool.add(Term::from(x.clone())),
                b.pool.add(Term::from(y.clone())),
            )
        })
        .collect();
    // The judgment is *contextual*: an enclosing anchor's substitution applies to the left body,
    // and `sko_forall`'s own checker applies it too when it recomputes the witnesses
    let phi_in_context = context.apply(b.pool, &phi);
    if same_arity && substitute(b.pool, &phi_in_context, renaming) == psi {
        // The exact-renaming case: both sides Skolemize to the very same term, so two
        // `sko_forall` scopes and a `symm`/`trans` close it in four steps
        let (ws, _) = witnesses(b.pool, &x_vars, &phi_in_context);

        // `sko_forall` compares an anchor's witnesses with the ones it recomputes for *that*
        // side, up to α-equivalence. Sharing the left side's witnesses with the right is what
        // makes this route work, and it is a claim about the two bodies, so it is checked rather
        // than assumed: a vacuous binder, for one, has a witness that mentions nothing of the
        // other side
        let psi_in_context = context.apply(b.pool, &psi);
        let (right_ws, _) = witnesses(b.pool, &y_vars, &psi_in_context);
        let mut time = std::time::Duration::ZERO;
        let interchangeable = ws
            .iter()
            .zip(&right_ws)
            .all(|(l, r)| crate::ast::alpha_equiv(l, r, &mut time));

        // Each side is its own ε-clause's Skolemization; they agree because the witnesses are the
        // same and the bodies are α-variants, which is what put us on this path
        let side = |b: &mut Builder,
                    context: &mut ContextStack,
                    quant: &Rc<Term>,
                    vars: &[SortedVar],
                    body: &Rc<Term>| {
            let anchor_args: Vec<AnchorArg> = vars
                .iter()
                .zip(&ws)
                .map(|(var, w)| AnchorArg::Assign(var.clone(), w.clone()))
                .collect();
            context.push(&anchor_args);
            let skolemized = context.apply(b.pool, body);
            context.pop();
            b.open();
            let equality = build_term!(b.pool, (= {body.clone()} {skolemized.clone()}));
            let refl = b.step(vec![equality], "refl", Vec::new(), Vec::new());
            let closing = build_term!(b.pool, (= {quant.clone()} {skolemized.clone()}));
            (
                b.close_with(anchor_args, "sko_forall", vec![closing], Vec::new(), refl),
                skolemized,
            )
        };
        if interchangeable {
            let (left, left_sk) = side(b, context, lhs, &x_vars, &phi);
            let (right, right_sk) = side(b, context, rhs, &y_vars, &psi);
            if left_sk == right_sk {
                let flipped = b.symm(&right);
                let conclusion = build_term!(b.pool, (= {lhs.clone()} {rhs.clone()}));
                return Ok(b.step(vec![conclusion], "trans", vec![left, flipped], Vec::new()));
            }
        }
    }

    // General α-equivalence — the renaming also touches *nested* bound names, or the body
    // shadows a variable: instantiate both sides at the same witnesses and bridge the residual
    // nested differences recursively. Works under an enclosing anchor too, since only the
    // ε-clause's `refl` is context-sensitive and it is built over the context-applied body
    {
        let mut time = std::time::Duration::ZERO;
        let lhs_in_context = context.apply(b.pool, lhs);
        if same_arity && crate::ast::alpha_equiv(&lhs_in_context, rhs, &mut time) {
            return alpha_quant(b, context, lhs, rhs);
        }
    }

    // One direction: Skolemize `to`, instantiate `from` at the same witnesses, replay the body
    // there, and cross the two with the equivalence
    let direction = |b: &mut Builder, context: &mut ContextStack, forward: bool| -> Res {
        let (from, from_vars, from_body, to, to_vars, to_body) = if forward {
            (lhs, &x_vars, &phi, rhs, &y_vars, &psi)
        } else {
            (rhs, &y_vars, &psi, lhs, &x_vars, &phi)
        };
        // `sko_forall`'s checker recomputes the witnesses over the context-applied body, so they
        // are built there; the ε-clause's own `refl` is contextual and reconciles the two
        let to_body_ctx = context.apply(b.pool, to_body);
        let (ws, _) = witnesses(b.pool, to_vars, &to_body_ctx);
        let (eps, skolemized) = epsilon_clause(b, context, to, to_vars, to_body, &ws)?;

        // Which witness stands for which variable. A binder list may repeat a name — veriT
        // writes `(∀ x y y x. φ)` for what binds each of them once — and then only the last
        // occurrence is the live one, so the later entry wins, exactly as the binder does
        let to_map = anchor_map(b.pool, to_vars, &ws);
        let mut by_name: IndexMap<&str, Rc<Term>> = IndexMap::new();
        for (var, w) in to_vars.iter().zip(to_map.values()) {
            by_name.insert(var.0.as_str(), w.clone());
        }

        // The instance `forall_inst` will state, which must be the literal one: the rule is
        // context-insensitive and knows nothing of the replay's renamings. Its arguments follow
        // `from`'s binder list, position by position, whatever names that list repeats
        let from_args: Vec<Rc<Term>> = if from_vars.len() == to_vars.len() {
            // The usual case: the two binder lists match position by position, and the anchor
            // says how their names correspond
            to_map.values().cloned().collect()
        } else {
            // Only a repeated binder can make the lists differ in length, and a list that
            // repeats a name is one the anchor renames nothing in, so the names coincide
            from_vars
                .iter()
                .map(|var| by_name.get(var.0.as_str()).cloned())
                .collect::<Option<_>>()
                .ok_or_else(|| explanation("the two sides bind different variables"))?
        };
        let mut from_map = IndexMap::new();
        for (var, w) in from_vars.iter().zip(&from_args) {
            let var_term = b.pool.add(Term::from(var.clone()));
            from_map.insert(var_term, w.clone());
        }
        let from_skolemized = substitute(b.pool, from_body, from_map);

        // The replay substitutes *both* binder families by the witnesses: the body mentions the
        // left variables directly and the right ones through the anchor's renaming
        let values: Vec<Rc<Term>> = to_map.values().cloned().collect();
        let mut map = IndexMap::new();
        for vars in [&x_vars, &y_vars] {
            for (var, w) in vars.iter().zip(&values) {
                map.insert(b.pool.add(Term::from(var.clone())), w.clone());
            }
        }
        let mut replacement = Replacement::new(b.pool, map);
        let mut cache = ReplayCache::new();
        let mut assumes = ReplayCache::new();
        let mut levels = vec![(inner_depth, b.depth())];
        let mut replayed = replay(
            b,
            context,
            previous,
            &mut replacement,
            inner_depth,
            &mut levels,
            &mut cache,
            &mut assumes,
        )?;

        // What the replay ends at and what the surrounding steps need can differ in two harmless
        // ways: the ε-clause skolemizes the *context-applied* body, and the replay renames a
        // binder the witnesses would otherwise capture. Both are settled by `refl` — contextual
        // in the first case, α-identifying in the second — and one `trans`
        let (want_left, want_right) = if forward {
            (from_skolemized.clone(), skolemized.clone())
        } else {
            (skolemized.clone(), from_skolemized.clone())
        };
        let [equality] = replayed.clause() else {
            return Err(explanation("the body of `bind` is not a unit equality"));
        };
        let (have_left, have_right) = match_term_err!((= l r) = equality)?;
        let (have_left, have_right) = (have_left.clone(), have_right.clone());
        if have_left != want_left || have_right != want_right {
            // The bridging steps are contextual `refl`s, so each is stated in the one direction
            // that has content — from the term as the body writes it to what the enclosing
            // substitution makes of it — and the left one is turned around by `symm`
            let mut premises = Vec::new();
            if have_left != want_left {
                bridgeable(b, context, &have_left, &want_left)?;
                let clause = vec![build_term!(
                    b.pool,
                    (= {have_left.clone()} {want_left.clone()})
                )];
                let bridge = b.step(clause, "refl", Vec::new(), Vec::new());
                premises.push(b.symm(&bridge));
            }
            premises.push(replayed);
            if have_right != want_right {
                bridgeable(b, context, &have_right, &want_right)?;
                let clause = vec![build_term!(
                    b.pool,
                    (= {have_right.clone()} {want_right.clone()})
                )];
                premises.push(b.step(clause, "refl", Vec::new(), Vec::new()));
            }
            let clause = vec![build_term!(
                b.pool,
                (= {want_left.clone()} {want_right.clone()})
            )];
            replayed = b.step(clause, "trans", premises, Vec::new());
        }
        let [equality] = replayed.clause() else {
            return Err(explanation("the body of `bind` is not a unit equality"));
        };
        let (left_instance, right_instance) = match_term_err!((= l r) = equality)?;
        let (left_instance, right_instance) = (left_instance.clone(), right_instance.clone());

        let instance = if forward {
            &left_instance
        } else {
            &right_instance
        };
        let inst = instantiate(b, from, from_args, instance)?;

        // `equiv_pos2`/`equiv_pos1` crosses the replayed equivalence with the instance
        let equality = equality.clone();
        let not_equality = b.not(&equality);
        let (not_left, not_right) = (b.not(&left_instance), b.not(&right_instance));
        let (axiom, pivots) = if forward {
            (
                b.step(
                    vec![not_equality, not_left, right_instance.clone()],
                    "equiv_pos2",
                    Vec::new(),
                    Vec::new(),
                ),
                (left_instance.clone(), right_instance.clone()),
            )
        } else {
            (
                b.step(
                    vec![not_equality, left_instance.clone(), not_right],
                    "equiv_pos1",
                    Vec::new(),
                    Vec::new(),
                ),
                (right_instance.clone(), left_instance.clone()),
            )
        };
        // The instance is consumed against its negation in the crossing clause, and the
        // Skolemized body against the ∀-ε-clause's negation of it
        let crossed = b.resolve(vec![axiom, replayed], vec![(equality, false)])?;
        let with_instance = b.resolve(vec![crossed, inst], vec![(pivots.0, false)])?;
        b.resolve(vec![with_instance, eps], vec![(pivots.1, true)])
    };

    let forward = direction(b, context, true)?;
    let backward = direction(b, context, false)?;
    let node = b.equiv_intro(lhs.clone(), rhs.clone(), forward, backward)?;
    Ok(node)
}

/// The generalized case: a clause whose literal `l` is closed as `(∀Ȳ. l)`.
fn closure(
    b: &mut Builder,
    context: &mut ContextStack,
    sub: &SubproofNode,
    previous: &Rc<ProofNode>,
    inner_depth: usize,
    conclusion: &[Rc<Term>],
) -> Res {
    if sub.args.iter().any(|a| matches!(a, AnchorArg::Assign(..))) {
        return Err(explanation(
            "the generalized `bind` reduction covers variables-only anchors",
        ));
    }
    let inner = previous.clause();
    if inner.len() != conclusion.len() {
        return Err(explanation("clause lengths differ"));
    }
    let Some(index) = (0..inner.len()).find(|&i| inner[i] != conclusion[i]) else {
        return Err(explanation("the conclusion closes no literal"));
    };
    let Some((closure_vars, body)) = quant_parts(&conclusion[index]) else {
        return Err(explanation("the closed literal is not a `forall`"));
    };
    if body != inner[index] {
        return Err(explanation("the closure does not wrap the literal"));
    }

    let body_in_context = context.apply(b.pool, &body);
    let (ws, _) = witnesses(b.pool, &closure_vars, &body_in_context);
    let (eps, skolemized) =
        epsilon_clause(b, context, &conclusion[index], &closure_vars, &body, &ws)?;

    let mut map = anchor_map(b.pool, &closure_vars, &ws);
    // The anchor may bind more variables than the closed literal quantifies. The checker reads
    // those as universally irrelevant — the closing clause cannot mention them — but the *body*
    // may, e.g. a `forall_inst` instantiating an anchor variable at itself. Once the anchor is
    // gone such a reference would be unbound, so the replay substitutes each of them by a closed
    // term of its sort; any term works, since nothing in the conclusion depends on the value
    for arg in &sub.args {
        let AnchorArg::Variable(var) = arg else {
            unreachable!("assign anchors are rejected above");
        };
        let var_term = b.pool.add(Term::from(var.clone()));
        if !map.contains_key(&var_term) {
            let body = b.pool.bool_true();
            let dummy = b.pool.add(Term::Binder(
                Binder::Choice,
                BindingList(vec![var.clone()]),
                body,
            ));
            map.insert(var_term, dummy);
        }
    }
    let mut replacement = Replacement::new(b.pool, map.clone());
    let mut cache = ReplayCache::new();
    let mut assumes = ReplayCache::new();
    let mut levels = vec![(inner_depth, b.depth())];
    let mut replayed = replay(
        b,
        context,
        previous,
        &mut replacement,
        inner_depth,
        &mut levels,
        &mut cache,
        &mut assumes,
    )?;

    // The ε-clause skolemizes the body as `sko_forall` recomputes it — through the enclosing
    // substitution — while the replay states it as written. A contextual `refl`, read as an
    // implication by `equiv1`, carries the replayed literal to the one the ε-clause offers
    let written = substitute(b.pool, &body, map);
    if written != skolemized {
        bridgeable(b, context, &written, &skolemized)?;
        let equality = build_term!(b.pool, (= {written.clone()} {skolemized.clone()}));
        let bridge = b.step(vec![equality.clone()], "refl", Vec::new(), Vec::new());
        let not_written = b.not(&written);
        let not_equality = b.not(&equality);
        let axiom = b.step(
            vec![not_equality, not_written, skolemized.clone()],
            "equiv_pos2",
            Vec::new(),
            Vec::new(),
        );
        let implied = b.resolve(vec![axiom, bridge], vec![(equality, false)])?;
        replayed = b.resolve(vec![replayed, implied], vec![(written, true)])?;
    }

    Ok(b.resolve(vec![replayed, eps], vec![(skolemized, true)])?)
}
