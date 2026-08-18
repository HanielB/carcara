# The 2.3 s `refl` step: inherited context substitution caches

**Branch:** `inv/refl-outlier` (commit `15e48628`). Not merged yet.
**Verdict:** genuine algorithmic cost, quadratic in anchor nesting depth. Fixed; recommended
for merge.

## Symptom

In the evaluation's per-rule box plots, single `refl` steps reached **2.3 s** — a rule whose
check should be a syntactic comparison. The worst file is
`QF_LIA/verit/Averest__parallel_prefix_sum__ParallelPrefixSum_safe_blmc004` (734 MB original
proof, 1.7 GB elaborated); the same file shows a 1.9 s `refl` *before* elaboration, so the
cost was not introduced by the `core` pass.

## Where the step sits

The proof is essentially one enormous `assume` that is a tower of nested `let`s with `:named`
sharing. Elaborating that assume (the `polyeq` pass) emits **one `bind_let` subproof per `let`
level**: 2226 anchors, nested up to **1338 levels deep**, each anchor carrying one assignment
`(:= (?v_k Bool) @p_N)`. The outlier `refl` steps are the ones at the bottom of these chains
(worst: `t2.t3.t3.t4...t3199.t1`, anchor depth ~1330). 13 `refl` steps exceeded 100 ms, all at
depths 569–1338. The slow step is always the *first* one that forces
`ContextStack::catch_up_cumulative` to materialize the cumulative substitutions of a deep
chain.

## Root cause: cache invalidation, not term traversal

Each context level's *cumulative* substitution is built by cloning the parent's and inserting
the level's own mapping. `Substitution` carries an application cache (`term → substituted
term`) — a pure memoization of `apply`. Two things followed from cloning it:

- `Substitution::insert` must **invalidate** the inherited entries that the new mapping
  invalidates: it runs `cache.retain(|k, _| !pool.free_vars(k).contains(&x))` over the *whole*
  inherited cache, and `PrimitivePool::free_vars` **clones** the free-variable `IndexSet` on
  every lookup (~3.5 µs per entry).
- The clone itself copies up to ~4300 entries per level (5.7 M entries copied over the file).

With depth `d` and inherited cache size `c`, building the chain is `O(d · c)` with a heavy
constant — quadratic in nesting depth in practice. Per-phase instrumentation over the
elaborated run (12.96 s of total `refl` time):

| phase | time |
|---|---|
| `Substitution::insert` (cache-invalidation `retain`) | **19.97 s** |
| clone of the parent's cumulative substitution | 0.56 s |
| applying the substitution to anchor values | 41 ms |
| applying the substitution to `refl` conclusions | 23 ms |

The suspected culprits — `Substitution::apply` over huge terms, polyeq, alpha-equivalence —
are together under 0.1 s. Essentially all the time is spent maintaining a cache.

## Fix, and why *not* inheriting the cache is the right call

```rust
// carcara/src/ast/substitution.rs
pub(crate) fn clone_without_cache(&self) -> Self {
    Self { map: self.map.clone(), avoid_capture: self.avoid_capture,
           should_be_renamed: self.should_be_renamed.clone(), cache: IndexMap::new() }
}
```

used by `catch_up_cumulative` in place of `.clone()`.

The cache is *pure memoization*: dropping an entry can only cost a recomputation, never change
a result, so the change is semantics-preserving by construction. The question is purely
economic, and three facts decide it:

1. **The inherited entries are mostly worthless to the child.** An entry is a memo of "term `t`
   under substitution σ". The child's substitution is σ extended with `?v_k ↦ value`, a
   *different function*: every entry whose key mentions `?v_k` free is stale and must be
   dropped. In a `let`-tower that is precisely the interesting part of the cache — each level's
   terms are built from the level below — so the inherited entries are either invalidated
   immediately or never queried again, because each context applies the substitution to its own
   small set of terms (its anchor value and its `refl` conclusion).
2. **Keeping the cache is charged per level, whether or not it is used.** The `retain` scan is
   paid on *every* insertion at *every* level, and its per-entry predicate allocates. So the
   cost grows with the product of depth and cache size while the benefit stays flat.
3. **The measurements confirm the trade.** What the inherited cache could save is bounded by
   the total application time — 64 ms across the whole file. What it cost was 20 s of
   invalidation plus 0.6 s of copying. Starting each level's cache empty gives up at most the
   former to eliminate the latter.

Within a single context the cache still does its job: repeated applications inside one level
hit it as before. Only the *inheritance across levels* is dropped.

## Before/after (clean, uncontended, `-j 1`)

| measurement | baseline | fixed | speedup |
|---|---|---|---|
| elaborated `blmc004`, worst `refl` step | 2.19 s | **189 ms** | ~11× |
| elaborated `blmc004`, total `refl` (53 424 steps) | 12.96 s | 0.79 s | 16× |
| elaborated `blmc004`, total checking | 8.11 s | 1.29 s | 6.3× |
| original `blmc004`, worst `refl` step | 1.80 s | **113 ms** | 16× |
| original `blmc004`, total checking | 7.29 s | 1.28 s | 5.7× |
| elaborated `bgmc005`, worst step | 95.8 ms (`refl`) | 24.1 ms (an anchor; no `refl` outlier) | 4× |

The residual 189 ms is the one-time, now *linear* catch-up over 1338 levels (dominated by the
`O(depth)` map clones and the free-variable computation of the substituted values). Removing
that too would need persistent/shared map structures — a much larger change, and not worth it
at these numbers.

## Validation

- `cargo test --release` passes; `cargo fmt` applied; `cargo clippy --release` clean.
- Full-directory sweeps, baseline vs fixed, identical flags: `elab/QF_LIA/verit` → identical
  verdict and the same two pre-existing error files in both (wall 48.9 s → 35.5 s);
  `proofs/QF_LIA/verit` → identical verdict, 0 errors in both, per-file mean checking
  234 ms → 60 ms.
