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

## Corpus results (sweep of 2026-08-29, 14 configs × 6 logics)

Aggregates over the proofs completing every stage of an arm; ×prev per rung.

**Arm A — vs the regular elaboration, all at elaborated granularity** (459 veriT / 484 cvc5):

| rung | veriT steps | veriT check | cvc5 steps | cvc5 check |
| --- | --- | --- | --- | --- |
| core (− reducible) | 1.172 | **1.157** | 1.278 | **1.268** |
| core-taut (− rw+simp) | 1.014 | 0.974 | 1.161 | 1.088 |
| core-full (− expensive) | 8.926 | 2.855 | 1.727 | 1.438 |

The first rung's checking column is the number the old regime could never produce: the pure
cost of reducing the reducible tier, measured against a pivot-carrying baseline at the same
granularity — +16% (veriT) and +27% (cvc5), no pivot or granularity term in it.

**Arm B — vs the original proof, all at default granularity** (444 veriT / 487 cvc5):

| rung | veriT steps | veriT check | cvc5 steps | cvc5 check |
| --- | --- | --- | --- | --- |
| core | 1.419 | 1.179 | 1.137 | 1.106 |
| core-taut | 1.016 | 0.970 | 1.138 | 0.992 |
| core-full | 9.504 | 2.092 | 1.622 | 1.216 |

Readings across the arms:

- **The rw+simp rung is free or better in checking, in every arm and solver** (0.97–1.09) —
  removing the rewrite vocabulary costs 1.4–16% in steps and *saves* checking time as often
  as not.
- **The reductions need the regular elaboration for checkability, not for correctness.**
  Arm B's outputs are all valid at default granularity, and *smaller* than arm A's (no `local`
  scaffolding: 4.7M vs 5.5M steps at veriT's core rung) — but nothing carries pivots, so they
  cannot be checked strictly, and their absolute checking time is ~55% higher (18.1 s vs
  11.6 s at that rung).
- **Arm B's residue names what the regular elaboration removes**: on cvc5, 301,698
  `reordering` scaffolding steps (1.45% of the proof — only the `reordering` pass, which needs
  `local`'s pivots, removes them); on veriT, 4 `ite_intro` steps whose fallback needs `polyeq`.
  Plus the usual `lia_generic` 2,993.
- **The expensive rung is insensitive to what runs before it**: same shape (×8.9–9.5 veriT,
  ×1.6–1.7 cvc5), and the same three QF_LIA/veriT timeout files, in both arms.
- Elaboration cost: arm B is ~33% cheaper than arm A end to end (sample measurement above),
  and its cheap pipelines fit the 300 s budget on every file arm A's full pipelines time out
  on, except the three QF_LIA aci_simp blowups, which are the reductions' own.

## Addendum: pruning stopped being a pass (2026-08-29, commits `113ac8d2`, `5d620f40`)

Prune cost anything only because the conversion to nodes was faithful: the premise graph is
rooted at the conclusion already, and a dead step survives solely through the root list and the
subproofs' `extra_steps` — which every pass then carried, and which a trailing pass paid four
whole-forest walks to remove. Both ends now handle it in walks they were doing anyway:
`check_and_elaborate` restricts the forest to the conclusion's derivation right after
`from_commands`, and the printer computes the reachable set once and guards its four
membership-driven push sites. `--keep-unused` opts out of both. Outputs are identical on veriT
and up to 0.2% *smaller* on cvc5 (the print filter also drops the moved-out extras the pass
kept defensively), all strictly checkable; one corpus proof turns out to be 98% dead steps
(pb2010: 28,957 kept under `--keep-unused`, 489 live). Elaboration on the sample: 6.5→5.4 s
(veriT) and 9.4→6.7 s (cvc5) against the original trailing-prune pipelines, −17%/−29%. The
`prune` pass remains available but no evaluation pipeline uses it.
