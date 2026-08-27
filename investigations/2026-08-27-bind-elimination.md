# Eliminating `bind`: what is admissible, what is mechanical, and what is neither

*2026-08-27*

`bind` is Alethe's congruence-under-a-binder rule: from a subproof proving `Γ, x̄ ↦ ȳ ▷ φ ≈ ψ`
it concludes `Γ ▷ (Qx̄. φ) ≈ (Qȳ. ψ)`. The [classification](../docs/src/core/classification.md)
calls it *expensive* — reducible, but at a price the default regimes decline to pay. This note
records what the reduction actually needs, after the round of work that took corpus coverage from
57% to 89%.

## The question that started it: is `bind` beyond the other rules?

No, over the quantifiers. `sko_forall` is ∀-introduction at the canonical ε-witness and
`forall_inst` is ∀-elimination at an arbitrary term; between them the quantifier fragment is
complete, and every `bind` instance over `∀`/`∃` is derivable. The implementation now does so in
three tiers, tried in order.

**1. Exact renaming.** Skolemize *both* sides at the *same* witnesses. `sko_forall`'s checker
compares an anchor's witnesses with the ones it recomputes only up to α-equivalence, so the
witnesses of `(∀x̄.φ)` serve for `(∀ȳ.ψ)` too, and both sides Skolemize to the identical term.
Two `sko_forall` scopes, a `symm` and a `trans`: **four steps, and the body is never read**.

**2. General α-equivalence** — nested bound names differ, veriT reoriented an equality, the body
shadows a variable. Instantiate *both* sides at the target's ε-witnesses, so the two instances
differ only under nested binders and at variables the enclosing anchor renames, and bridge those
residues recursively:

- a nested quantifier pair recurses through the same construction (`∃` first through
  `qnt_duality`, the `∀` machinery on the negated bodies, `cong` back over the negation);
- a renamed free variable is a contextual `refl`;
- a reoriented equality goes through `cong`'s four-orientation search on a two-argument pair;
- two α-variant `let` terms are expanded and rejoined. `bind_let` cannot do this — its checker
  requires the two binding lists to carry the *same* names, which is exactly what an α-difference
  violates — but a `let` is a definition, and two definitions differing only in the defined name
  have the same expansion, so each side reduces to its own expansion by one `let` scope and
  `symm`/`trans` close it.

**3. Rewriting bodies.** The ∀-ε-clause of one side, `forall_inst` of the other at the same
witnesses, a replay of the body with the witnesses substituted for the anchor's variables (every
core rule is schematic, so its instances survive a uniform substitution), both directions closed
by iff-introduction.

## The contextual seam

A `bind` under an enclosing anchor asserts `Γ(∀x̄.φ) ≈ (∀ȳ.ψ)`, while nearly every rule the
reduction is built from is context-insensitive: `forall_inst` instantiates the quantifier it is
handed, `resolution` matches pivots syntactically. Three facts settle where the enclosing
substitution may and may not appear.

- **The witnesses are built over the context-applied body**, because that is what `sko_forall`'s
  checker recomputes them from. Being closed under the enclosing substitution, they then commute
  with it.
- **The replayed body is written as-is.** The replayed derivation sits at the same depth as the
  step it replaces, so its `refl` leaves are checked against the same cumulative context the
  originals were; rewriting its terms would also break the match with premises reached from
  *outside* the subproof, which keep the shape they have there.
- **One contextual `refl` joins the two** where the ε-clause and the replay meet — its entire
  content being that the enclosing substitution is what it is.

Composing the substitutions everywhere instead (the first attempt) is what breaks the
outside-premise match; the residual bind count went *up*, from 46 to 78 on the sample.

## What it took to get from 89% to all of them

The residue at 89% was two clusters, and both came down to the same thing: a term built during a
reduction is written against the substitution in force where it is built, and everything that
moves it afterwards has to agree about what that substitution was.

**Substitution renaming.** Carcara renames a bound variable when it is one of the substituted
variables or occurs free in what they are replaced by. The second is capture-avoidance; the first
is not — under a binder that binds `x`, the substitution does not reach the occurrences it binds,
and renaming `x` gives an α-variant of the right answer. Harmless for a checker comparing terms
it built itself, fatal for a replay, whose terms must keep matching the ones nothing renamed.
Carcara already did the right thing for single-mapping substitutions, with a comment saying that
removing the mapping is what the renaming stands in for; the general case needed a child
substitution with its own cache. A term with nothing free to substitute is now returned as it
stands, for the same reason — the substitution tests said as much in a comment, and now say it as
an assertion.

**Order.** A `bind` inside another `bind` waits for a later round: reducing the enclosing one
afterwards would carry the inner reduction's terms out of the anchor they were written against.
The nesting is read off the proof rather than the context stack, which cannot tell a `bind_let`
anchor from a ∀-closure `bind` — and keyed by the closing step's *id*, since a pass is handed a
rebuilt node whenever one of its premises moved.

**Reading the context rather than reconstructing it.** The ε-clause takes its Skolemized body
from the context stack with its own anchor pushed, instead of composing the enclosing
substitution with the witnesses by hand. A scope's cumulative substitution puts each anchor value
through the enclosing one, and that composition is not idempotent — a `let` whose values name an
outer `let`'s variables is enough — so the hand-composed term was not what the `refl` inside the
scope gets checked against. Where the replay and the ε-clause still differ, a contextual `refl`
joins them, in the vanilla form through the equivalence and in the ∀-closure form as an
implication (`equiv1`) resolved against the clause; the bridge is emitted only when it will
check.

**Nested `let` scopes are dissolved, not replayed.** Their bindings join the witness substitution
and the `let` step becomes the definitional expansion it always was, so there is no second
composition to keep in step.

**A checker fix.** `sko_forall` read its anchor's assignments as a map from variable to witness,
which cannot hold a binder list that repeats a name — and veriT writes `(∀ x y y x. φ)` for what
binds each of them once. Read in order, one assignment per binding, each position is skolemized
by a witness of its own.

Also: assumptions are placed at the depth of their own scope and shared across the scopes of one
replay (the scope that discharges one and the scope that uses it are different scopes), and
`proof_nodes_to_list` emits a subproof's assumptions before its steps, which a premise-following
traversal does not.

## Choice congruence is not the blocker

Carcara's `bind` is binder-generic, and congruence under `choice` has no core route: ε has no
introduction or elimination rules of its own. That is [divergence 5](../docs/src/core.md), and it
turns out to be conditional on one thing only — the `sko_ex` reduction.

- No solver emits a `bind` over a `choice` binder: **0 of the corpus's 12 893 `bind` steps** (the
  9 whose text mentions `choice` are `forall` binds whose *bodies* contain witnesses).
- The only construction that emits one is the `sko_ex` reduction's own witness bridge
  (`core/skolem.rs`), relating veriT's `∃`-shaped witness `εx.ψ` to the duality-shaped
  `εx.¬(∀tail.¬ψ)`.

So the trade is: *derive `sko_ex` from `sko_forall` and pay for it with binder-generic `bind`, or
keep both Skolemization rules and pay nothing.* Keeping `sko_ex` core is exactly what having both
∃-introduction and ∃-elimination primitive means — which is how RESOLUTE's four quantifier axioms
are arranged, and why RESOLUTE never needs a choice rule either. Its other reason is structural:
being refutational and clausal, RESOLUTE has no binder-equivalence judgment at all, so two
α-variant ε-terms never meet as an equality to be proved.

A corollary measured here: with `sko_ex` core, nothing in the corpus asks `strict_refl` to
identify α-variants. The relaxation was implemented (`cf18ba59`) and reverted (`6b342b52`) when an
A/B left the residual count unchanged at 80 either way.

**The final measurement.** Of 1053 `bind` steps in the `bind`-heavy sample, 1052 reduce with the
`sko_ex` reduction enabled — the one that does not is the `choice` bind that reduction emits —
and **all 1053 reduce with `sko_ex` kept core**. Every proof re-checks at elaborated granularity.
So the answer to "is `bind` admissible?" is not "in principle": it is, in this corpus, entirely.
