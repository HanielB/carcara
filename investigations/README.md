# Investigation notes

Written-up results of focused performance/correctness investigations, one file per
investigation. Each note records the reproduction, the measured root cause, the change (or the
argument that no change is warranted), before/after numbers, and validation status — so that a
result can be reviewed without re-running the experiment.

| date | note | branch | status |
|---|---|---|---|
| 2026-08-18 | [Non-RUP resolution steps in cvc5 proofs](./2026-08-18-nonrup-resolution.md) | `inv/nonrup-resolution` | **merged** |
| 2026-08-18 | [The 2.3 s `refl` step: eager cache invalidation](./2026-08-18-refl-context-cache.md) | `inv/refl-outlier` | **merged** |
| 2026-08-18 | [`rare_rewrite` timing outliers: deferred allocator work](./2026-08-18-rare-rewrite-timing-artifact.md) | `inv/rare-rewrite-outlier` | `OnceLock` **merged**; bench drain not taken |
| 2026-08-18 | [`aci_simp` timing outliers: the same artifact, and mimalloc](./2026-08-18-aci-simp-timing-artifact.md) | `inv/aci-simp-outlier` | **declined** (no new dependency) |
| 2026-08-18 | [What the `sko_ex` reduction costs](./2026-08-18-sko-ex-cost.md) | `inv/sko-ex-cost` | measurement; rule moved to *expensive* |
| 2026-08-18 | [Reducing `poly_simp_rel`](./2026-08-18-poly-simp-rel.md) | `inv/poly-simp-rel` | **merged** |
| 2026-08-18 | [Binder recipes rebuilt against their checkers](./2026-08-18-cvc5-binder-shapes.md) | `inv/cvc5-binder-shapes` | **merged** |
| 2026-08-18 | [Global normalization of arithmetic atoms: a negative result](./2026-08-18-poly-normalization.md) | `inv/poly-normalization` | negative; found hoist-and-share instead |
| 2026-08-18 | [Sharing the core pass's derivations](./2026-08-18-share-derivations.md) | `inv/share-derivations` | **merged** |
| 2026-08-18 | [Orientation normalization: feasible and not worth building](./2026-08-18-orientation-normalization.md) | `inv/orientation-normalization` | negative; found a round-trip to fix at its source |
| 2026-08-18 | [`symm` round trips in elaboration](./2026-08-18-symm-round-trip.md) | `inv/symm-round-trip` | **merged** |
| 2026-08-20 | [`rare_rewrite`: skipping the meta-rewriting sweep](./2026-08-20-rare-meta-skip.md) | `inv/rare-meta-skip` | **merged** |
| 2026-08-21 | [Lifting repeated closed steps](./2026-08-21-hoist-pass.md) | `inv/hoist-pass` | **merged** |
| 2026-08-21 | [The rewrite-reduction regimes](./2026-08-21-rewrite-reduction-regimes.md) | `coreAlethe` | **merged** |
| 2026-08-24 | [veriT emits singleton applications of `and`/`or`](./2026-08-24-verit-singleton-applications.md) | `coreAlethe` | solver-side, reported |
| 2026-08-25 | [An algebraic hierarchy for `aci_simp` and `poly_simp`](./2026-08-25-aci-poly-algebraic-hierarchy.md) | `coreAlethe` | analysis; kept as two primitives |
| 2026-08-25 | [`la_generic` integer strengthening: two unsoundnesses](./2026-08-25-la-generic-strengthening.md) | `coreAlethe` | **merged** |
| 2026-08-25 | [Taking `rare_rewrite` to zero](./2026-08-25-rare-rewrite-to-zero.md) | `coreAlethe` | **merged** |
| 2026-08-25 | [Collapsing lemma scopes clausally: `deep-hoist`](./2026-08-25-deep-hoist.md) | `coreAlethe` | **merged** |
| 2026-08-25 | [What each rewrite recipe costs](./2026-08-25-recipe-cost-per-rewrite.md) | `coreAlethe` | measurement; no rewrite earns a rule |
| 2026-08-26 | [Per-rule elaboration growth over the corpus](./2026-08-26-per-rule-growth.md) | `coreAlethe` | measurement; drives the SMT-LIB run |
| 2026-08-26 | [Splitting the rewrite-removal cost: `rare_rewrite` vs `evaluate`](./2026-08-26-rare-vs-evaluate.md) | `coreAlethe` | **merged** (new `core-no-rare` regime) |
| 2026-08-27 | [Should `evaluate` be a core primitive?](./2026-08-27-evaluate-core-or-reducible.md) | `coreAlethe` | measurement; premise refuted, `aci_simp`-as-expensive supported |
| 2026-08-27 | [Eliminating `bind`](./2026-08-27-bind-elimination.md) | `coreAlethe` | every corpus `bind` step reduces; the last residue is the `choice` bind the `sko_ex` reduction itself emits |
| 2026-08-28 | [Splitting `la_generic` into Farkas + tightening](./2026-08-28-la-generic-split.md) | `coreAlethe` | exploration: +3.5% steps, +3.4% checking, in exchange for removing all integrality reasoning from the arithmetic checker |

Most were prompted by the core-elaboration evaluation in `~/benchmarks/alethecore-eval` (see its
`report.md`): three by extreme per-step checking-time outliers in the Fig. 5a box plots, one by
proofs that failed to elaborate, one by a classification question. The last entries are
*exploratory*: they look for proof-compression opportunities rather than fixing a defect.
