# Binder recipes rebuilt against their checkers

**Branch:** `inv/cvc5-binder-shapes` (commit `47e68a24`) — **merged into `coreAlethe`**.
**Verdict:** the residue was a recipe limitation, not a semantic one. Rebuilding both recipes
against the checkers removed it entirely: 61 `onepoint` and 32 `qnt_rm_unused` leftovers → 0
corpus-wide, with the veriT corpus elaborated byte-identically.

## Symptom

Elaborating cvc5 proofs left a residue of binder steps that the `core` pass kept and warned
about, while the same rules were fully reduced in veriT proofs. Instrumenting every bail-out site
over the cvc5 UF/UFLIA corpus showed two kinds, each hitting a single site:

| kind | steps | bail site | what it is |
|---|---|---|---|
| `qnt_rm_unused` | 32 | `has_duplicate_names(left)` | the binder list repeats names, e.g. `(forall ((x L) (y L) (y L) (x L)) φ)`. In all 32, the two lists have the same *set* of variables, the right one is repetition-free, and it is often reordered relative to the left |
| `onepoint` | 61 | `orientation_bridge(σφ, φ')` | the right-hand side is the substituted body with a *repeated disjunct dropped*: 51 order-preserving dedup, 9 dedup with reordering, 1 where `(or A A)` collapses to `A` |

Spread over 18 files. Both were symptoms of writing the recipes against veriT's output rather
than against what the rules accept.

## What the checkers actually accept

- **`onepoint`** (`checker/rules/subproof.rs`): the anchor's assignments must be *points* of the
  body according to `extract_points`, a polarity-driven traversal — strip negations flipping
  polarity, descend through any quantifier, and then at positive polarity read `(= a b)` as a
  point for whichever side is a variable (**both** orientations, and both sides when both are
  variables) and recurse into every conjunct of `and`; at negative polarity recurse positively
  into `p` and negatively into `q` of `(=> p q)` and negatively into every disjunct of `or`. The
  starting polarity is `quant == Exists`. Beyond that, the rule only requires the subproof's
  previous step to conclude `(= φ φ')` — φ' need merely be *provably* equal to the substituted
  body.
- **`qnt_rm_unused`** (`checker/rules/quantifier.rs`): both binder lists are read as `IndexSet`s,
  the bodies must be equal, the right list may not introduce new variables, and the removed
  variables must not be free in the body. Repetitions and reordering are therefore *inside* the
  rule.

## The rebuild

**`onepoint`.** `extract_points` is now `pub` and returns an `IndexMap` from each point to the
equality term it was read off (the checker only ever used the keys). The recipe calls it instead
of the old two-template body classifier, and a new `guard_escape` mirrors the traversal
production by production, returning `(cl (not term) guard)` at positive polarity and
`(cl term guard)` at negative: `and_pos` for a conjunct, `or_neg` for a disjunct,
`implies_neg1`/`implies_neg2` for the two sides of `=>`, an excluded middle for the negation
flip, and — for a quantifier crossed on the way — instantiation at dummy `choice` witnesses
(positive) or a generalized-`bind` closure (negative), with the `connective_def` duality and
`not_not` for the `exists` variants. Both directions became uniform: assume all guards, transport
σφ back to φ, and discharge each guard's failure through its escape. `transport` gained the
matching binder case (a `bind` subproof over the unchanged binder list, capture-checked). The old
special cases — the `refl`-refutation of trivialized guards, the negated-consequent inner
subproof — are gone.

**`qnt_rm_unused`.** Repetitions are normalized away by a `bind` step on each side (a `bind`
compares its binder lists as sets too, so this is exactly the normalization it licenses), and the
removal proper runs between the normalized quantifiers, with the anchor ordered so the surviving
list is a subsequence of it. The `exists` case routes through the `connective_def` duality (plus
a double-negation equivalence for the all-removed case), so the removal itself always happens on
a `forall`.

## Coverage, stated against the checkers

`qnt_rm_unused` is **fully covered**. `onepoint` covers every *body* the rule accepts — every
production of `extract_points`, both quantifiers, with or without a kept prefix. What remains is
the rule's other degree of freedom: since φ' need only be *provably* equal to σφ, and the
subproof's proof of that equality is checked under the anchor's substitution and cannot be
replayed outside it, the recipe has to bridge φ' to σφ itself. It does so up to equality
orientation and `or`-disjunct multiplicity, and keeps the step otherwise. Lifting that limit
means instantiating the whole subproof — a context-elimination pass — not a local recipe.

The boundary was verified with 16 hand-written proofs (all `valid` as inputs, i.e. inside the
checkers' space): `exists`/`forall` `qnt_rm_unused` with duplicates on either side and the
all-removed case; `onepoint` with `and`/`=>`/`or`/negated-`and` bodies, flipped guards, two
points, kept prefixes, `exists`, and guards under an inner `forall`/`exists` at both polarities.
All reduce completely and re-check; only the "φ' is a rewrite of σφ" case stays, as expected.

## Validation

- **cvc5, UF+UFLIA (187 proofs):** `onepoint` 61 → **0**, `qnt_rm_unused` 32 → **0**. Verdicts
  unchanged: 186 valid, 1 pre-existing elaboration failure (a polyeq panic on
  `sledgehammer__Hoare__smtlib.849485`).
- **cvc5, all six logics (494 proofs):** 450 valid, 35 holey (QF_UF, from `hole` steps in the
  input), 9 elaboration failures — all pre-existing and unrelated. **0 binder leftovers
  corpus-wide.**
- **veriT, UF+UFLIA (175 proofs):** byte-identical outcome against a baseline binary — 175 valid,
  0 leftovers, no diff in any field.
- `cargo test --release` passes; `cargo fmt` and `cargo clippy --release --all-targets` clean.
