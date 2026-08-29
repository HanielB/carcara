# Running `core` after the regular elaboration, and the two-arm comparison regime

*2026-08-29 — validated on a 41-proof cross-logic sample; corpus sweep in flight*

The elaboration pipeline had always been `hoist polyeq core local core reordering prune`: the
reductions first, the canonicalization passes after. That order confounds every measurement of
what the reductions cost, because the baseline they are compared against carries no resolution
pivots and cannot be checked at the elaborated granularity — the pivot and granularity effects
land on one side of the ratio. This note records that the order can be swapped, what the swap
revealed about why the pipeline is shaped the way it is, and the two-arm regime the evaluation
uses from here on.

## The swap is sound and free

`hoist polyeq local core core reordering prune` produces, on the sample, proofs that are
**identical in non-core residue** (971 veriT / 5,372 cvc5 steps), identical in size on veriT and
+0.03% on cvc5, all checking at the elaborated granularity, at −2% elaboration time. Nothing in
`core` ever depended on running first: its recipes are schematic in the conclusion, and `local`
preserves conclusions.

Two structural facts surfaced on the way:

- **`core` runs twice because reductions emit second-generation reducible steps** — with a
  single `core` after `local`, cvc5 keeps ~5k extra `equiv1`/`or` steps that the second pass
  removes. `local`'s position between the two passes was incidental; `core core` back to back
  behaves identically.
- **`reordering` requires `local` before it.** Its conclusion-recompute fires for any
  order-sensitive step whose premises were rebuilt, and for resolutions it reads the pivot
  arguments only `local` writes; on a pipeline without `local` it fails with "expected N
  arguments, got 0". This is why the no-elaboration arm below drops the pass entirely.

## The two arms

- **Arm A — `regular elab + core`.** Baseline `hoist polyeq local reordering prune` (config
  `*-elab`), rungs `hoist polyeq local <rung> <rung> reordering prune` for `core`, `core-taut`
  and `core-taut core-expensive`. Baseline and rungs all carry pivots and are all checked at the
  **elaborated** granularity: a rung ratio against the baseline is pure reduction cost, no pivot
  or granularity term in it.
- **Arm B — `no reg. elab + core`.** The same rungs with nothing in front: `core core prune`,
  `core-taut core-taut prune`, `core-taut core-taut core-expensive prune` (configs `*-bcore`,
  `*-btaut`, `*-bfull`). `polyeq` turns out not to be needed — the recipes match the solver's
  terms as written. No pivots exist, so these are checked at the **default** granularity, against
  the original proof at the same granularity.

Sample numbers (41 proofs, ~109 MB): arm B elaborates ~33% cheaper than either full pipeline
(4.3 s vs 6.4/6.5 s veriT, 6.4 s vs 9.3/9.4 s cvc5) and its output checks slightly slower
(2.64 vs 2.48 s, 0.82 vs 0.64 s at default granularity). Its residue is the point of the
comparison: on veriT the reductions *alone* reach the same non-core residue as the full pipeline
(972 vs 971 steps) in fewer steps; on cvc5 they leave +23k extra non-core steps — 21k
`reordering` bridges from the core pass's own sharing that only the (unavailable) `reordering`
pass removes, and simplify-tier duplicates that `hoist` would have merged. What the regular
elaboration contributes is exactly that difference.

## Bookkeeping

`run-eval.sh` carries both arms (and per-config granularity); `ladder-run.sh` drives all
fourteen configs; `core-isolated.sh`'s separate measurement is subsumed by arm A's baseline
config but kept. The `prune`-closes-every-stage convention (2026-08-29) applies to all of it.
