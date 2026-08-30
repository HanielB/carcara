# Non-RUP resolution steps in cvc5 proofs

**Branch:** `inv/nonrup-resolution` (commit `df2887dc`) — **merged into `coreAlethe`** as
`84047532`.
**Verdict:** Carcara completeness gap, *not* a cvc5 defect. Nothing to report upstream.

## Symptom

Two UFLIA sledgehammer proofs produced by cvc5 (`--proof-format-mode=alethe
--proof-granularity=dsl-rewrite`) failed to elaborate, defeating both mechanisms Carcara has
for inferring explicit resolution pivots:

- `sledgehammer__Fundamental_Theorem_Algebra__smtlib.921784`, step `t20`:
  *"could not infer pivots for resolution step: RUP resolution failed"*
- `sledgehammer__TwoSquares__smtlib.678375`, step `t264`:
  *"could not infer pivots for resolution step: pivot was not eliminated"*

## The failing steps

Both have the same shape. cvc5 refutes a contradictory conjunction via a subproof, which
stacks negations on one atom. For FTA `t20`, with `L` the equality
`(= (f13 @p_16 @p_5) (f13 (f14 f17 @p_5) @p_15))` and `A := (and (not L) (not (not L)))`:

```
t17 (subproof, discharges ¬L and ¬¬L):  (cl ¬¬L  ¬¬¬L  false)
t18 (and_pos 0):                        (cl ¬A   ¬L)
t19 (and_pos 1):                        (cl ¬A   ¬¬L)
t20 (resolution t17 t18 t19):           (cl false ¬A ¬A)
```

TwoSquares `t264` is isomorphic, with `M` an arithmetic equality.

The step **is** a valid left-to-right chain exactly as written: resolve `t17` with `t18` on
pivot `¬L` (the `¬¬L` of `t17` against the `¬L` of `t18`), then with `t19` on pivot `¬¬L` (the
`¬¬¬L` against the `¬¬L`), leaving `{false, ¬A}`. cvc5's output is correct.

## Root cause

Two independent Carcara limitations conspired:

1. **`greedy_resolution`** (`carcara/src/resolution.rs`) inserted a pivot into the working set
   *as soon as it was seen*, while still scanning the premise that introduced it. So the two
   stacked-negation literals *of the same premise* (`¬¬L` and `¬¬¬L` in `t17`) cancelled each
   other. That is never a legal chain move — in a resolution chain each premise is resolved
   against the accumulated clause on a single pivot, and a premise's own literals never cancel
   — and it produced a trace that fails `set_replay_valid` (FTA) or leaves a literal stranded
   and reports "pivot was not eliminated" (TwoSquares).
2. **`rup_chain`**, the fallback, explicitly bails on literals with two or more negations (a
   documented limitation), so it could not rescue the step.

## Fix

Buffer the pivots discovered while processing a premise and merge them into the pivot set only
after that premise is fully scanned, so a pivot can only eliminate literals of *later*
premises:

```rust
let mut new_pivots = Vec::new();
for term in premise {
    ...
    // not in the conclusion ⇒ it is a pivot; defer the insertion
    new_pivots.push((n, inner));
}
for pivot in new_pivots {
    pivots.entry(pivot).or_insert(false);
}
```

Greedy then finds the correct traces — elaborated `t20` gets `:args (¬L false ¬¬L false)`,
`t264` gets `:args (¬M false M false)` — and both survive set-replay, so the RUP fallback is
never reached. A unit test `resolution::tests::stacked_negations_within_a_premise` reproduces
the pattern; it fails on the unfixed code.

## Why plain `carcara check` accepted these proofs all along

The default-granularity `resolution` checker falls back to a RUP test that abstracts literals
with `remove_all_negations_with_polarity`, i.e. it collapses `¬¬` entirely. Since `¬¬φ ≡ φ`
that is a sound satisfiability-preservation test, and it is strictly more permissive than what
the *elaborator* must produce — an explicit ordered chain with named pivots. The gap was
therefore invisible until elaboration was attempted.

## Validation

- Both proofs elaborate (`polyeq core local core reordering`) and re-check **valid** in
  elaborated granularity with the RARE rule file. cvc5 coverage in the evaluation: 483/494 →
  **485/494**.
- `cargo test --release` passes (250 tests, including the new one); `cargo fmt` and
  `cargo clippy --release --all-targets` clean.
- Regression sweep over all 94 UFLIA/cvc5 and 98 QF_UF/cvc5 proofs, fixed binary vs baseline:
  the only two changed outcomes are the two target proofs flipping from elaboration failure to
  valid. Everything else is byte-identical, including pre-existing unrelated failures.
