# Sharing the core pass's derivations

**Branch:** `inv/share-derivations` (commit on `inv/share-derivations`) — **merged into
`coreAlethe`**.
**Verdict:** the largest compression win found so far. The `core` pass's growth on cvc5's
arithmetic proofs falls from **+34.7% to +9.7%**; end to end those proofs now grow **8.6%** over
the input instead of 36.8%, and elaboration and checking of the heaviest proofs get 20–35%
faster. Every proof still elaborates and re-checks with the same verdict.

## The observation

The pass reduces each step independently, so duplicate conclusions get duplicate derivations. The
measurement in the [normalization note](./2026-08-18-poly-normalization.md) found that 72% of the
114 015 `poly_simp_rel` instances on the cvc5 corpus are literal duplicates — 31 866 distinct
conclusions — and that the duplication is entirely *cross-subproof*, so exploiting it requires
hoisting rather than local caching.

## The mechanism

`elaborate_core` owns a `Sharing` memo (`carcara/src/elaborator/core/share.rs`). After a recipe
produces a derivation, `Sharing::share` either hoists it to depth 0 and records it, or hands back
a derivation recorded earlier for the same conclusion.

Hoisting exploits machinery the forest already has: premises are `Rc` pointers, so replacing a
step's node with the shared one redirects every consumer; a use from inside a subproof then
becomes an ordinary *outbound premise*, which `mutate` accumulates and propagates up nested
`SubproofNode`s and which `proof_nodes_to_list` already emits into the top-level frame. No changes
to the forest machinery were needed.

**The key is the conclusion clause alone**, which is sound *because* of the guards: a
self-contained derivation proves its clause on its own, so two of them with the same clause are
interchangeable whatever they were built from. When a recipe actually used the premise of the step
it reduced (`poly_simp_rel`'s fallback for a premise that is not a polynomial identity), that
premise is a reachable node and is copied *into* the shared derivation — it becomes part of the
derivation rather than part of the key.

**Guards**, all conservative, falling back to the previous per-instance behaviour:

- *self-contained* — every node reachable from the conclusion is a `Step` at the elaborated step's
  own depth, with empty `:discharge` and no `previous_step`. One predicate rules out assumptions,
  enclosing-scope steps and subproofs, and guarantees the leaves are premise-free;
- *context-free* — no free variable of any clause or argument term is bound by an anchor in scope.
  A new `ContextStack::bound_variables()` fast-paths this: it is empty for the `subproof` anchors
  that dominate these proofs, so free variables are only computed under a real binder;
- *not positionally referenced* — a step that closes a subproof, or that is the implicit premise of
  such a step, is referred to by position rather than by id, so it is never hoisted. This needs a
  pre-scan of the forest (including `extra_steps`, which `traverse` skips), because at the point
  the recipe runs the consumer has not been visited yet.

**Ids** live in a namespace whose prefix is the shortest of `sh`, `sh_`, `sh__`, … that is not a
prefix of *any* id in the proof. Not being a prefix — rather than merely distinct — is what keeps
the ids that `local`/`uncrowd` later derive by appending (`sh1.t1`) collision-free too.

**Never a regression.** Hoisting is free when the derivation contains only recipe-created nodes,
but costs a few steps when it must copy a premise-free step that was already in the proof. Such a
derivation is therefore stored as *pending* and hoisted only once a second step asks for it. This
was not cosmetic: without the deferral, veriT UF/UFLIA grew by 6 and 48 steps; with it, those
outputs are byte-identical to the baseline.

## Results

`poly_simp_rel`'s share of the pass's growth, measured against the same baseline as the
projection:

| logic | baseline | projected | achieved |
|---|---|---|---|
| QF_LIA | +22.6% | +6.9% | **+7.2%** |
| QF_LRA | +22.1% | +9.3% | **+8.1%** |
| QF_UFLIA | +27.5% | +4.3% | **+3.9%** |
| total added steps | 1 432 679 | 338 891 | **328 223** |

The mechanism is rule-agnostic — it sits in `elaborate_core`, not in any recipe — so the whole
pass benefits:

| logic | pass growth, baseline → shared |
|---|---|
| QF_LIA | +32.9% → **+7.3%** |
| QF_LRA | +35.3% → **+14.9%** |
| QF_UFLIA | +35.7% → **+9.7%** |
| QF_UF (no arithmetic recipe fires at all) | +18.9% → **+13.3%** |
| the three arithmetic logics together | +34.7% → **+9.7%** |

End to end, with the full pipeline against the original proofs: 5 089 254 → 6 964 008 (+36.8%)
becomes 5 528 867 (**+8.6%**). Time on the heaviest files (elaborate / re-check, seconds):

| file | steps | elaborate | check |
|---|---|---|---|
| `rings_preprocessed__ring_2exp6_4vars_2ite` | 927 360 → 700 003 | 14.35 → 8.64 | 3.70 → 2.49 |
| `mathsat__EufLaArithmetic__hard__hard20` | 386 998 → 302 844 | 6.64 → 4.52 | 1.55 → 1.11 |
| `wisas__xs_15_25` | 383 228 → 311 290 | 6.48 → 4.74 | 1.51 → 1.13 |
| `Averest__parallel_prefix_sum` | 204 073 → 204 073 | 46.41 → 30.70 | 37.22 → 27.45 |

(`Averest` shares nothing; its speedup is `mutate` doing less work, not fewer steps.)

## Validation

- Every cvc5 proof in QF_LIA/QF_LRA/QF_UFLIA elaborated and re-checked at elaborated granularity:
  **verdicts identical to the baseline on every file**, including which ones fail (all
  pre-existing).
- veriT UF and UFLIA: identical verdicts, identical step counts, byte-identical outputs but for
  two files of identical size. QF_UF cvc5/veriT and veriT QF_LIA/QF_LRA/QF_UFLIA also checked —
  no regression anywhere.
- `cargo test --release`, `cargo fmt --check`, `cargo clippy --release --all-targets` clean. New
  test `sharing_across_subproofs`: two identical `poly_simp_rel` steps in two different subproof
  scopes yield 2 `la_generic` steps rather than 4, at the top level, and the result checks —
  verified to fail (4 vs 2) with sharing disabled.

## Two obstacles, recorded

They constrained the design rather than blocking it:

1. A step that is the implicit premise of a subproof's last step is referenced *positionally*, so
   hoisting it silently corrupts the subproof — and this is invisible where `mutate` calls the
   recipe, since traversal is postorder and the consumer has not been visited. Hence the pre-scan.
2. Derivations containing subproofs are excluded: a depth-0 `SubproofNode` reached from inside
   another subproof trips the "all outbound premises should have already been dealt with"
   assertion unless the enclosing subproof lists it as an outbound premise, which `mutate` only
   arranges through consumers. Requiring step-only derivations sidesteps this at no cost for
   `poly_simp_rel`, but it does mean `la_rw_eq` and the binder recipes are never shared — the
   obvious next increment.

Beyond that: 50% of *all* premise-free steps in these proofs are exact duplicates, so sharing
steps the pass did not itself create would be a separate and larger win.
