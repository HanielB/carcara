# `rare_rewrite` timing outliers: deferred allocator work

**Branch:** `inv/rare-rewrite-outlier` (commit `b9e533ee`). The `OnceLock` half is **merged**
into `coreAlethe` as `61c65719`; the bench-only allocator drain was not taken.
**Verdict:** measurement artifact, not checking cost. Of the two changes, the `OnceLock` is a
real improvement and was taken; the allocator drain is bench-only cosmetics and was not. See
the [`aci_simp` note](./2026-08-18-aci-simp-timing-artifact.md) for the same artifact seen from
the other rule.

## Symptom

Single `rare_rewrite` steps reached 20–40 ms in the evaluation's per-step timings, against a
median of ~30 µs for the same rule. Worst files: `QF_UFLIA/cvc5/mathsat__EufLaArithmetic__hard19`
and `hard20`, in both the elaborated and the original proofs.

## What the outlier steps actually are

Always **the first `rare_rewrite` step checked in the file** — in `hard19` that is step `t27`,
rule `bool-double-not-elim`, whose instantiated conclusion is 159 tree nodes / 32 DAG nodes.
The second-slowest `rare_rewrite` in the same file takes ~50 µs. Term size, `:list` splicing
(n-ary rules) and premises are all irrelevant: the "expensive" step is trivial.

## Root cause

Instrumentation (`/proc/thread-self/schedstat` and `stat`) shows the step burns ~48–50 ms of
*userspace CPU* (utime 5 ticks, stime 0, no page faults, no runqueue wait) — it is real work,
just not proof checking. It is deferred **glibc malloc** bookkeeping:

when `parse_instance` returns, the parser state and the proof source text (29 MB for `hard19`;
333 K steps, 45 K named terms) are dropped at once. glibc parks the freed chunks in its
*unsorted bin* and defers the binning work — walking the unsorted bin, coalescing, and
inserting into the sorted large bins — to whichever allocation comes next. The first
allocation-heavy consumer after parsing is the first `rare_rewrite` step, because `check_rare`
rebuilt the entire meta-rule set (hundreds of small allocations) on *every* call.

Proof by absorption: inserting an unrelated 100 K-allocation churn just before the step made
that churn take 82–91 ms (normally <2 ms) and dropped the step to **60 µs**. `malloc_trim(0)`
does *not* drain the unsorted bin (the step stayed at 30–49 ms); a loop of large-bin-sized
(64 KB) requests does. Pool/sort-cache hash resizes were ruled out (≤4 ms, and they land in
the parsing phase).

## Changes

### 1. `get_rules()` behind a `OnceLock` — what is cached, and why it matters

`get_rules()` (`carcara/src/rare/mod.rs`) returns the **meta-rewrite rule set**: a fixed,
program-constant list of ~40 rewrite pairs used to normalize RARE rule instantiations (n-ary
list splicing `(Op (RareList ..x..)) ~> (Op x)`, singleton collapse, and so on). It is not a
cache of proof-checking *results* — it is constant data that was being **rebuilt from scratch
on every call**, and `check_rare` calls it once for the conclusion plus once per premise, i.e.
at least once per `rare_rewrite` step.

The change makes it build once per process and hand out `&'static [(RewriteTerm, RewriteTerm)]`
thereafter. So the reuse is across every `rare_rewrite` step of every proof handled by that
process — in a `bench` run over hundreds of files, one construction instead of hundreds of
thousands. Nothing is retained between *runs* of the binary; there is no on-disk cache and no
staleness concern, since the data is compiled-in constants.

This is a genuine (if modest) win independent of the timing artifact: it removes hundreds of
allocations per rare-rewrite step. It did **not**, on its own, fix the outlier — the deferred
glibc backlog simply moved to the step's remaining allocations.

### 2. `drain_allocator_backlog()` in `bench` — measurement hygiene only

A loop of 1000 × 64 KB `Vec::with_capacity` between the parsing and checking timers in
`run_job`, forcing glibc to process the free-list backlog *before* per-step timing starts, so
the cost is not misattributed to one step. It costs <1 ms on a clean heap or under a
non-glibc allocator. This affects only what `bench` reports, never what checking costs. It was
**not merged**: it is a hack in the measurement path, and the artifact is now documented
instead. It remains on the branch should future measurements need it.

## Before/after (maximum `rare_rewrite` step, ns)

| file | baseline | fixed |
|---|---|---|
| elab `hard19` | 29,820,379 | 1,909,126 |
| elab `hard20` | 25,101,539 | 903,738 |
| elab `hard16` | 29,731,974 | 508,545 |
| elab `hard13` | 28,005,880 | 163,537 |
| orig `hard19` | 37,845,031 | 346,027 |
| orig `hard20` | 36,402,735 | 1,374,532 |

Residual sub-2 ms maxima are scheduler noise from a concurrent sweep on the same machine
(1 ms CPU + 3 ms runqueue wait = one CFS timeslice); on-CPU time for the former outlier is
~0. Medians are unchanged (~30–40 µs).

## Validation

- `cargo test --release` passes; `cargo fmt` applied; `cargo clippy --release --all-targets`
  clean.
- Re-check of all 94 `elab/QF_UFLIA/cvc5` and 95 `proofs/QF_UFLIA/cvc5` proofs, baseline vs
  fixed: byte-identical results.

## Consequence for the evaluation

The `rare_rewrite` whiskers in the Fig. 5a box plots overstate the rule's cost by three orders
of magnitude at the maximum. Total checking times are unaffected — the work was always
happening, it was merely charged to one step instead of spread over the run.
