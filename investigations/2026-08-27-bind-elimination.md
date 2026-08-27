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

## What blocks the last 11%

Both remaining categories are mechanical consequences of capture-avoiding substitution, not gaps
in the core:

| residue | count (sample) | why |
| --- | --- | --- |
| nested scope closed by `let` | 10 | replaying it means substituting into the anchor *and* keeping the contextual steps under it in step with the new assignment; the two drift |
| body rebinds a substituted variable | 9 | Carcara renames a binder that shadows a substituted variable **whether or not anything is replaced under it** (`compute_should_be_renamed` renames `y` when `y = x` or `y` is free in `t`), and the renamed term no longer matches the same term reached from outside |

Two routes out were tried and rejected:

- **α-renaming the shadowing binders before the replay** (`freshen`). Coverage jumps to 5
  residual, but the freshened terms no longer match the unfreshened ones at every seam, and 7 of
  12 proofs stop checking. Normalizing the seams with α-`refl` steps requires `strict_refl` to
  identify α-variants, and even then a resolution against an outside premise fails.
- **`--expand-let-bindings`**, which would remove the `let` terms at parse time. It breaks these
  veriT proofs on its own, before the core passes run at all (611 steps out of 10 781 survive
  elaboration), so it is not a route for veriT output.

Leaving the terms with nothing to substitute *verbatim* — the fix that did land — removes the
gratuitous renaming, but the genuinely-substituted shadowing terms still rename.

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
