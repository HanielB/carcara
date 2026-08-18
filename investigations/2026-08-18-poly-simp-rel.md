# Reducing `poly_simp_rel`, cvc5's largest non-core residue

**Branch:** `inv/poly-simp-rel` (commit `07f11057`) — **merged into `coreAlethe`**.
**Verdict:** the arithmetic case is **reducible** at 8 steps (inequalities) or 20 (equalities);
all 114 015 corpus instances reduce and re-check. The bitvector case is **not** reducible over
the core's arithmetic vocabulary and is kept.

## The rule

Checker: `carcara/src/checker/rules/polynomial.rs::poly_simp_rel`. From a premise
`(= (* c₁ (- x₁ x₂)) (* c₂ (- y₁ y₂)))` — optionally with `to_real` wrappers — with non-zero
rational `c₁`, `c₂` of equal sign (unless the relation is `=`), it concludes
`(= (x₁ ⋈ x₂) (y₁ ⋈ y₂))` for `⋈ ∈ {<, ≤, =, ≥, >}`. There is also a bitvector case over
`bvmul`/`bvsub` with odd coefficients.

It is the second-largest non-core rule in cvc5's output: 129 589 steps, 1.2% of the cvc5 corpus.

## The reduction

Each direction of the equivalence is a **single `la_generic` step**. For
`(cl ¬(x₁ ⋈ x₂) (y₁ ⋈ y₂))`, weight the x-literal by `|c₁|` and the y-literal by `|c₂|`: writing
the differences as linear combinations, the premise identity `c₁Λx = c₂Λy` makes the two
combinations cancel exactly, because `|c₂|·c₁/c₂ = |c₁|` precisely when the signs agree.
Whatever `⋈` is, exactly one of the two literals is strict after negation, and its strengthening
bump is what makes the accumulated constant positive — the contradiction. The same weights work
in both directions, and the absolute values are exactly *why* the checker demands equal signs
except for `=`.

For `=`, a positive equality cannot be an `la_generic` literal, so each direction goes through
the `la_disequality` axiom by the `la_rw_eq` template, with the two bounds discharged by one
Farkas step each. `equiv_intro` glues the directions.

**Cost: 8 steps for an inequality, 20 for an equality** (10 and 24 in the general case below).
Measured average over the corpus: +12.2 steps per instance.

## Two things the first analysis got wrong

**The premise is not always dispensable.** The checker only checks the premise's *shape*; it
never verifies that `c₁(x₁−x₂)` and `c₂(y₁−y₂)` are the same polynomial. The rule is sound
because the premise *holds*, not because it is an identity — so a premise-free certificate is
not valid over the checker's whole accepted space. The recipe therefore tries the premise-free
certificate first and, if `la_generic` rejects it, carries `(not premise)` as a literal with
weight `±1` (the only weight that cancels the `c₁`/`c₂` its sides carry; both signs are tried)
and resolves the premise away. On the corpus the fallback never fires — every real premise is a
`poly_simp` conclusion — but it is covered by tests.

**`to_real` was a hard blocker in the *checker*.** `la_generic`'s `LinearComb::add_term` had no
`ToReal` case, although `Polynomial::add_term` (used by `poly_simp` itself) did, so `(to_real t)`
was an atom distinct from `t`. cvc5 emits many `poly_simp_rel` steps relating an integer term
with its real embedding, and none of them normalized. The missing case was added
(`carcara/src/checker/rules/linear_arithmetic.rs`): `to_real` is the identity on values, so it is
transparent to linear normalization. **Without it, 67% of the QF_LIA instances (32 292/48 407)
do not reduce.** This is a completeness fix to the checker, not only to the elaboration.

## Corpus results

Pipeline `polyeq core local core reordering`; every elaborated proof re-checked at elaborated
granularity.

| logic | `poly_simp_rel` before → after | steps before → after | premise fallbacks |
|---|---|---|---|
| QF_LIA (48 proofs) | 48 602 → **0** | 1 889 451 → 2 316 620 (+22.6%) | 0 |
| QF_LRA (66) | 26 174 → **0** | 1 027 385 → 1 254 667 (+22.1%) | 0 |
| QF_UFLIA (95) | 39 239 → **0** | 2 661 608 → 3 392 721 (+27.5%) | 0 |
| **total** | **114 015 → 0** | 5 578 444 → 6 964 008 (**+24.8%**) | 0 |

QF_UFLIA is almost all equality instances (+18.6 steps each); QF_LIA and QF_LRA almost all
inequalities (+8.8, +8.7). Checking time on the heaviest files grows 14–28%:

| file | `poly_simp_rel` steps | checking before → after |
|---|---|---|
| `rings_…_2exp6` | 16 780 | 2.18 s → 2.48 s |
| `clocksynchro_7clocks` | 6 089 | 0.82 s → 0.97 s |
| `EufLaArithmetic hard20` | 3 819 | 0.91 s → 1.12 s |
| `wisas__xs_15_25` | 3 806 | 0.87 s → 1.11 s |

Six files fail identically before and after (pre-existing: one stack overflow, five that do not
conclude the empty clause).

## Robustness

Every emitted `la_generic` is validated by calling `la_generic_partial` *before* the step is
built, so an unanticipated shape fails the reduction — keeping the step and logging a warning —
rather than producing a derivation that does not check. Two shapes are rejected explicitly: the
bitvector premise, and conclusions whose sides use different relations. The degenerate case where
the consequent's two sides are the same term (the two bounds collapse into one literal) is
handled.

Carcara's `la_generic` downgrades the accumulated operator to `≥` when any literal is
non-strict, so the contradiction relies on the strengthening bump; under a strictness-tracking
`la_generic` the same certificates still close (at `0 > 0`), so the recipe does not depend on
that quirk.

## The bitvector case: not reducible

It justifies itself by odd coefficients being units modulo `2ⁿ`, so multiplying a difference by
one is injective. That is modular arithmetic, and the core's arithmetic vocabulary — Farkas
certificates over an ordered field, plus `la_disequality`'s antisymmetry — cannot express it; no
bitvector core rule states that an odd constant is invertible. The pass detects the shape and
keeps the step. It awaits a solver-side removal or a dedicated bitvector core rule.

## Validation

- `cargo test --release` passes (252 tests, including a new integration file
  `carcara/tests/test_core_elaboration.rs`: 15 arithmetic cases covering all five relations,
  both-negative and fractional coefficients, opposite signs in the `=` case, reals, `to_real`
  around the premise's difference and inside the conclusion's terms, the degenerate same-term
  case, three non-identity premises forcing the premise-using certificate, plus a bitvector case
  asserted to be *kept*).
- `cargo fmt` and `cargo clippy --release --all-targets` clean.
