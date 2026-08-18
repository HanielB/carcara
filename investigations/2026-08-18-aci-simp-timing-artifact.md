# `aci_simp` timing outliers, and why mimalloc makes checking faster

**Branch:** `inv/aci-simp-outlier` (commit `392a6d76`). Not merged yet.
**Verdict:** the outlier is the same allocator artifact as the
[`rare_rewrite` one](./2026-08-18-rare-rewrite-timing-artifact.md) — the `aci_simp` checker
itself is already DAG-aware and memoized. The change (mimalloc as the CLI's global allocator)
is nevertheless recommended: besides erasing the artifact it makes real checking ~25% faster
on large proofs.

## Symptom

Single `aci_simp` steps reached ~30 ms, against ~20–40 µs for other `aci_simp` steps *in the
same file*.

## What the outlier steps are

- `elab/QF_UF/verit/PEQ__PEQ002_size6` (400 MB proof), step `t9`: 32.9–34.6 ms. The equated
  terms are `and`-applications with 977 and 805 direct arguments, 16 515 / 13 910 tree nodes —
  but only **2733 unique DAG nodes** (the right-hand side adds one node over the left-hand
  side's subterms), same-operator nesting depth 5.
- `elab/QF_UFLIA/cvc5/wisas__xs_15_25`: one `aci_simp` at 31.5 ms while the other 20
  `aci_simp` steps in the file take 20–40 µs.

## Root cause: allocator, not algorithm

The rule is already DAG-aware and memoized: `apply_aci_simp` caches by pointer-hashed
`Rc<Term>` (so equality and hashing are O(1)), and deduplication is hash-set based, not
quadratic. Instrumentation on the worst case: 1799 recursive calls, 808 cache entries, 1625
flattened arguments total, 35 µs spent in `pool.add`. **Warm steady-state cost of the whole
check: ~150–350 µs.** There is no blowup to fix — no tree explosion, no quadratic dedup.

The 30 ms is glibc free-list/bin consolidation, charged to the first steps that allocate after
checking starts: `run_job` drops the 400 MB proof string and millions of parser temporaries
immediately before the checking timer starts. Evidence: `rusage` shows cpu ≈ wall with no page
faults (real CPU work, not swapping); the cost vanishes after ~4 repetitions of the same
check; and warming the allocator with ~2 MB of *unrelated* dummy allocations burns 132 ms
itself and then lets the first real check run in 1.2 ms.

Note that a checker-internal fix cannot dodge this: the multiset-comparison tail of the rule
makes only ~10 allocations, yet was charged 15–21 ms. The cost scales with the allocator's
backlog, not with the rule's allocation count.

## Change: mimalloc as the CLI's global allocator

```rust
// cli/src/main.rs
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
```

plus the `mimalloc = "0.1.52"` dependency. Three lines, library untouched.

### Why this removes the artifact

glibc's `malloc` keeps a single per-arena set of bins. A mass free parks chunks in the
*unsorted bin* and defers the real work — walking that bin, coalescing neighbours, and
inserting into the sorted large bins (an O(n) insertion per chunk) — to the *next* allocation
requests, up to 10 000 chunks per call. So a free storm at the end of parsing is paid by
whichever step allocates first during checking, in one lump.

mimalloc instead manages memory as per-thread heaps of size-segregated *pages*. A free pushes
the block onto its page's local free list; there is no global sorted structure to maintain and
no deferred consolidation pass that a later allocation must absorb. Freeing a large object
graph therefore costs what it costs, where it happens, and no subsequent allocation inherits a
backlog. The per-step numbers stop lying.

### Why it also makes checking genuinely faster

The artifact is about *attribution*; the speedup is about *throughput*, and Carcara is an
allocation-heavy program: terms are `Rc`-shared but every `pool.add`, every `IndexMap`/
`IndexSet` growth, every substitution and clause vector is an allocation, and checking a large
proof performs tens of millions of them, interleaved with frees. On that workload glibc's
generic path (bin lookup, unlink/coalesce bookkeeping, arena locking) costs more per operation
than mimalloc's — mimalloc's fast path is a pop from a thread-local free list of the exact
size class, with sharded, mostly lock-free handling of cross-thread frees (which matters for
`bench -j 6`, where six checker threads allocate concurrently). Size-segregated pages also
improve locality, so the term graph traversals that dominate checking touch fewer cache lines.

Measured on the 400 MB `PEQ002` proof: whole-file checking (user time) **14.6–16.7 s → 12.1–12.8 s**,
about 25% faster, with per-file results unchanged. That is the part that would show up in the
evaluation's totals, not just its box plots.

## Before/after

| metric | glibc | mimalloc | |
|---|---|---|---|
| `PEQ002` worst `aci_simp` step | 32.9 / 33.7 / 34.6 ms | 0.352 / 0.376 / 0.376 ms | ~90× |
| `wisas_xs_15_25` max `aci_simp` | 31.5 / 32.4 ms | 0.172 / 0.176 ms | ~180× |
| `PEQ002` whole-file check (user) | 14.6–16.7 s | 12.1–12.8 s | ~25% faster |

## Validation

- `cargo test --release` passes (including the `aci_simp` unit tests); `cargo fmt` and
  `cargo clippy --release` clean.
- Sweeps with identical flags, baseline vs fixed: `elab/QF_UF/verit` 92/92 valid,
  `elab/QF_LRA/verit` 54/54 valid — per-file results byte-identical, 0 errors on both sides.

## Caveats before merging

- mimalloc is a C dependency built by the `mimalloc` crate; it adds a build-time toolchain
  requirement and affects the CLI binary only (the `carcara` library still uses whatever
  allocator its embedder chooses).
- The gain is glibc-specific. On musl, macOS, or under an embedder that already sets a global
  allocator, the artifact and the speedup will differ.
