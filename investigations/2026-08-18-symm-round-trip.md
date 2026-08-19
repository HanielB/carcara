# `symm` round trips in elaboration

**Branch:** `inv/symm-round-trip` (`061f7026`, `cba00ca2`, `1d72f9a8`) — **merged into
`coreAlethe`**.
**Verdict:** the actionable half of the
[orientation investigation](./2026-08-18-orientation-normalization.md). Removes **107 100 steps**
from the elaborated veriT corpus — 1.49% of all steps, 11.97% of its `symm` steps — with identical
verdicts on all 682 files elaborated. Two incidental fixes rode along, one of them a 17 000×
speedup of forest-wide analyses.

## The round trip

`strict_refl` applies the context substitution to the **left-hand term only**, so
`polyeq/reflexivity.rs` reaches the right-substituting orientation by emitting a flipped `refl`
plus a `symm`. Later, `flip_needed_premises` (`local/congruence.rs`), `trans`
(`local/transitivity.rs`) and the `core` recipes need the original orientation back, and stacked a
*second* `symm` whose conclusion restates the `refl` verbatim:

```
(step … (cl (= ?v_0 @p_1)) :rule refl)                    ; polyeq/reflexivity.rs
(step … (cl (= @p_1 ?v_0)) :rule symm :premises (…))      ; polyeq/reflexivity.rs
(step … (cl (= ?v_0 @p_1)) :rule symm :premises (…))      ; local/congruence.rs — restates the refl
(step … (cl (= (= e0 ?v_0) (= e0 @p_1))) :rule cong :premises (…))
```

## The fix

`add_symm_step` and `Builder::symm` now return the premise of a `symm` step rather than wrapping
it in another one, guarded by a check that the premise really concludes the wanted clause
(`unwrap_symm_step` in `elaborator/mod.rs`). Sound by inspection — `symm(symm(X))` and `X`
conclude the same clause — and no pruning was needed: the bypassed steps are freshly created
nodes, unreachable from any root once bypassed, and `proof_nodes_to_list` drops them (verified:
symm-over-symm goes 169 → 0 in a sample file, with the step count dropping by exactly 169).

Making `polyeq/reflexivity.rs` keep both orientations instead was considered and rejected: the
flipped step's id and conclusion are fixed, so the `refl`+`symm` pair there is already minimal.

## Results

veriT, six logics, 462 elaborated files, pipeline `polyeq core local core reordering`:

| config | steps before → after | removed | `symm` before → after |
|---|---|---|---|
| QF_UF | 4 174 551 → 4 092 489 | 82 062 (1.97%) | 742 961 → 660 899 |
| QF_UFLIA | 493 987 → 480 405 | 13 582 (2.75%) | 79 328 → 65 746 |
| QF_LIA | 1 232 941 → 1 227 050 | 5 891 (0.48%) | 19 116 → 13 225 |
| QF_LRA | 1 125 229 → 1 120 473 | 4 756 (0.42%) | 38 600 → 33 844 |
| UFLIA | 139 236 → 138 493 | 743 (0.53%) | 13 357 → 12 614 |
| UF | 34 991 → 34 925 | 66 (0.19%) | 1 725 → 1 659 |
| **total** | **7 200 935 → 7 093 835** | **107 100 (1.49%)** | **895 087 → 787 987 (−11.97%)** |

Every removed step is a `symm`; the rule falls from 12.43% to 11.11% of all steps. cvc5 proofs are
untouched by design — their elaborations contain no `symm`-over-`symm` at all (0 instances in a
281 689-step QF_UFLIA proof; their `symm` steps sit over `rare_rewrite`, `contraction` and
assumptions).

**Why this is 61% of the 175 016 estimate, not 100%.** Each round trip is *two* `symm` steps and
only the outer one can go. The inner one is the elaborated form of the *original* `refl` step — its
id and conclusion are fixed — and the elaborator preserves every original command, since all
top-level commands are forest roots and `SubproofNode::extra_steps` keeps every inner command. So
it survives in the output, unreferenced. Measured exactly: on UFLIA + QF_UFLIA the new outputs
contain 14 325 unreferenced `symm`-over-`refl` steps, precisely matching the 14 325 steps removed
there. Recovering the second half — worth about another 107 000 steps — means pruning original
steps that elaboration itself made unreachable, which is a distinct change with implications well
beyond `symm`: Carcara deliberately keeps unused steps so that they are still checked.

## Two incidental fixes

**Shared traversal state** (`cba00ca2`). `Rc<ProofNode>::traverse` allocated a fresh visited set
per call, and since *every* command is a root of its `ProofNodeForest`, a root-by-root analysis is
quadratic in the shared subgraph. On a 25 MB proof (74 117 roots, 78 675 nodes) that is
**1 686 786 866 visits in 580 s, against 78 675 visits in 33 ms** with the visited set shared —
now available as `VisitedNodes`, `traverse_with` and `ProofNodeForest::traverse`.

**Degenerate `eq_transitive`** (`061f7026`). The one-link chain was materialized by applying `symm`
twice. A step is genuinely needed there — the closing `subproof` step reads its conclusion off the
command preceding it, which is the last assumption rather than the link — so it now emits a
one-premise `trans`, and when the single link is the `symm` that flipped the assumption, that step
closes the subproof directly. No instance of the shape occurs in the evaluation corpus (the step
and `symm` deltas above coincide exactly, which pins the count at zero), so it is covered by a unit
test rather than by the sweep.

## Validation

- **682 files** elaborated with both a baseline binary from the branch point and the new one, each
  output re-checked at elaborated granularity: **0 verdict mismatches**, with identical
  valid/holey/failure breakdowns and all failures pre-existing.
- `cargo test --release` green, `cargo fmt --all --check` clean, `cargo clippy --release
  --all-targets` zero warnings. Tests added: `cong_does_not_stack_symm_steps`,
  `degenerate_eq_transitive`, `test_forest_traversal_visits_shared_nodes_once`.
- Timing is inside the noise, as expected: a 1.5% cut in the cheapest rule there is buys size, not
  time.
