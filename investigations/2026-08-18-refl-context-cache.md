# The 2.3 s `refl` step: eager invalidation of context substitution caches

**Branch:** `inv/refl-outlier` (commit `63f9e344`) — **merged into `coreAlethe`**.
**Verdict:** genuine algorithmic cost, quadratic in anchor nesting depth. Fixed by deferring cache
invalidation, which preserves every cache hit the eager scheme served.

## Symptom

In the evaluation's per-rule box plots, single `refl` steps reached **2.3 s** — a rule whose
check should be a syntactic comparison. The worst file is
`QF_LIA/verit/Averest__parallel_prefix_sum__ParallelPrefixSum_safe_blmc004` (734 MB original
proof, 1.7 GB elaborated); the same file shows a 2.1 s `refl` *before* elaboration, so the
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
term`) — a pure memoization of `apply`. `Substitution::insert` used to **invalidate** the
inherited entries eagerly:

```rust
self.cache.retain(|k, _| !pool.free_vars(k).contains(&x));
```

This scans the *whole* cache on every insertion, and `PrimitivePool::free_vars` **clones** the
free-variable `IndexSet` on every lookup (~3.5 µs per entry). With depth `d` and inherited
cache size `c`, building the chain is `O(d · c)` — quadratic in nesting depth in practice.

Per-phase instrumentation over the elaborated run (12.96 s of total `refl` time at the time):

| phase | time |
|---|---|
| `Substitution::insert` (cache-invalidation `retain`) | **19.97 s** |
| clone of the parent's cumulative substitution | 0.56 s |
| applying the substitution to anchor values | 41 ms |
| applying the substitution to `refl` conclusions | 23 ms |

The suspected culprits — `Substitution::apply` over huge terms, polyeq, alpha-equivalence — are
together under 0.1 s. Essentially all the time was spent maintaining a cache.

The decisive measurement is how much of that scanning did any work. Counting the entries the
eager `retain` visited, and how many it actually dropped:

| benchmark | entries scanned by `retain` | entries actually dropped |
|---|---|---|
| elaborated `blmc004` | **45 175 369** | **0** |
| `elab/QF_LRA/verit` (whole dir) | 7 003 714 | 0 |
| `elab/UFLIA/verit` (whole dir) | 70 777 | 1 399 |
| `elab/UF/verit` (whole dir) | 7 737 | 1 034 |

On the pathological file, 45 million free-variable computations dropped *nothing*.

## Fix: defer the invalidation instead of dropping the cache

The first attempt was to simply not inherit the cache when composing cumulative substitutions
(`clone_without_cache`). That works, but it throws away memoization that pays off elsewhere:
`blmc004` is a pathological case, not the general one. The better answer is to keep every entry
and make invalidation **lazy**, so that invalidation work is only ever done for entries that are
actually consulted.

Each cache entry is tagged with the *generation* at which it was stored:

```rust
cache: IndexMap<Rc<Term>, (Rc<Term>, u32)>,
generation: u32,                          // bumped by every `insert`
invalidated_at: IndexMap<Rc<Term>, u32>,  // x ↦ generation of its latest insertion
```

- `insert` no longer touches the cache. It bumps `generation` and records
  `invalidated_at[x] = generation`. Everything else (sort check, `should_be_renamed` update,
  `map.insert`) is unchanged.
- `get_cached` validates on lookup:
  - **fast path** — the entry's generation is `>= self.generation`, so it was stored after every
    insertion and cannot be stale: `O(1)`, no `free_vars` call;
  - **slow path** — the entry is older than the latest insertion, so it is valid iff no variable
    `w` with `invalidated_at[w] > entry_generation` occurs free in the key. This computes
    `pool.free_vars(key)` once and scans whichever of the two sets is smaller. A valid entry is
    **promoted** to the current generation, so it is validated at most once per version of the
    substitution; an invalid one is dropped and recomputed.

### Correctness

The scheme is observationally equivalent to the eager one. The eager predicate for dropping an
entry at an insertion of `x` was exactly "`x` occurs free in the key". So an entry survived all
the eager `retain`s iff no inserted variable occurs free in its key — and an entry stored at
generation `g` is used by the lazy scheme iff no variable inserted after `g` occurs free in its
key. The two conditions coincide, entry by entry: the lazy scheme uses exactly the entries the
eager scheme would have kept, and recomputes exactly the ones it would have dropped. Promotion is
sound because it only happens after the check has established the entry is valid at the current
generation. This is confirmed empirically below: the hit counts are *identical*, not merely
similar.

Note that `remove()` still does not invalidate the cache. That was true before this change too,
and it is preserved deliberately — the lazy scheme keeps `x` in `invalidated_at` after a
`remove`, which is exactly the (conservative) behavior of the eager scheme, where the entries had
already been dropped. If `remove` should invalidate, that is a separate, pre-existing question.

### Cost model

Building a chain of `d` contexts costs `O(d)` map/cache clones per level instead of
`O(#inserts · cache_size · free_vars_cost)`; lookups are `O(1)` except for one validation per
stale entry that is actually consulted.

## Memoization is genuinely preserved

Instrumented cache counters, eager baseline vs deferred (identical runs):

| benchmark | scheme | hits (fast + slow) | lookups | stale entries hit | entries scanned by `insert` |
|---|---|---|---|---|---|
| elaborated `blmc004` | eager | 23 832 | 87 206 | 0 | 45 175 369 |
| elaborated `blmc004` | deferred | 3 985 + 19 847 = **23 832** | 87 206 | 0 | **0** |
| `elab/QF_LRA/verit` | eager | 28 575 | 99 485 | 0 | 7 003 714 |
| `elab/QF_LRA/verit` | deferred | 5 205 + 23 370 = **28 575** | 99 485 | 0 | **0** |
| `elab/UFLIA/verit` | eager | 5 679 | 42 023 | — | 70 777 |
| `elab/UFLIA/verit` | deferred | 3 847 + 1 832 = **5 679** | 42 023 | 256 | **0** |
| `elab/UF/verit` | eager | 3 740 | 25 684 | — | 7 737 |
| `elab/UF/verit` | deferred | 3 307 + 433 = **3 740** | 25 684 | 169 | **0** |

Every hit the eager scheme served, the deferred scheme serves too — same totals on every
benchmark, quantified logics included, so no memoization is lost. The slow path is not rare (in
these workloads a context applies its substitution and *then* extends it, so entries are
frequently older than the last insertion), but it is bounded by the number of *lookups*: 19 847
validations on `blmc004` against 45 million entry scans under the eager scheme, a ~2300×
reduction in invalidation work. Where inherited entries are reused across insertions — the
`hit_slow` column — they are reused, rather than being recomputed as they would be if the cache
were simply not inherited.

## Before/after (clean, uncontended, `-j 1`)

Three-way, all on the current `coreAlethe` base: `baseline` = eager invalidation, `no-cache` =
the rejected `clone_without_cache`, `deferred` = this change.

| measurement | baseline | no-cache | deferred |
|---|---|---|---|
| elaborated `blmc004`, worst `refl` step | 2 358 ms | 201 ms | **3.4 ms** |
| elaborated `blmc004`, total `refl` (53 424 steps) | 7.71 s | 0.48 s | **0.34 s** |
| elaborated `blmc004`, total checking | 8.47 s | 1.57 s | **1.36 s** |
| original `blmc004`, worst `refl` step | 2 097 ms | 131 ms | **3.5 ms** |
| original `blmc004`, total `refl` (47 112 steps) | 7.22 s | 0.41 s | **0.35 s** |
| original `blmc004`, total checking | 9.17 s | 1.48 s | **1.54 s** |
| elaborated `bgmc005`, worst step | 106 ms (`refl`) | 24 ms (an anchor) | **24 ms** (an anchor) |
| elaborated `bgmc005`, total checking | 996 ms | 437 ms | **399 ms** |

These three columns were measured with all three binaries built from the same base. Re-measured
after rebasing onto the `coreAlethe` commit that charges the deferred allocator work to parsing
time, the elaborated `blmc004` numbers are 2 347 ms → **4.4 ms** for the worst `refl` step and
8.48 s → **1.61 s** for total checking; the shift in the totals is that reattribution, not the
cache.

The deferred scheme is an order of magnitude better than dropping the cache on the outlier step
itself (3.4 ms vs 201 ms), because the inherited entries are still there: the deep chain reuses
the parent's memoized applications instead of re-traversing the terms. After the fix there is no
`refl` outlier left in either proof — the worst step of the original `blmc004` is an `ac_simp`
(117 ms).

## No regression outside the pathological case

Whole-directory mean checking time per file, `-j 4`, baseline vs deferred:

| directory | baseline | deferred |
|---|---|---|
| `elab/QF_UF/verit` (820 MB) | 70.5 ms | 66.7 ms |
| `elab/QF_LRA/verit` (694 MB) | 33.1 ms | 21.0 ms |
| `elab/QF_LIA/verit` (2.6 GB) | 255.5 ms | 94.0 ms |
| `proofs/QF_LIA/verit` (1.0 GB) | 204.5 ms | 59.8 ms |

## Validation

- `cargo test --release` passes (54 + 194 + doc tests); `cargo fmt --check` and
  `cargo clippy --release --all-targets` clean.
- Full-directory sweeps, baseline vs deferred, identical flags: `elab/QF_LIA/verit` → same
  verdict and the same two error files (wall 44.6 s → 37.9 s); `proofs/QF_LIA/verit` → same
  verdict, 0 errors in both (wall 11.7 s → 5.4 s); `elab/QF_UF/verit` → same verdict, same 1
  error file; `elab/QF_LRA/verit` → same verdict, same 35 error files.
