# all-alethe3: the hoisting printer at corpus scale (and what it exposed)

**Data:** `~/exp/results/pfcmp/all-alethe3/` (pfchk cache
`pfchk_cache.v2.parquet`), plots in `~/exp/pfcmp/plots-alethe3/`.
**Toolchain (bin3):** cvc5 alethebv @ `5973a56a1d` (shared derivations
printed once at the outermost well-scoped frame: content-level dedup and
context-dependency analysis at translation time, consumed by a frame-based
printer), carcara bv-fixes @ `61f71b4c`. Same 45,171-benchmark union and
limits as all-alethe2 (only the cvc5 printer differs).

## Headline

45,159 / 45,171 valid (alethe2: 45,169). **Zero size regressions** over
44,516 paired benchmarks: no proof grew by more than 2%. Totals
283.6 GB -> 270.6 GB, steps 1,478M -> 1,369M; check time 7.0h -> 6.8h;
solve+print time unchanged (174h), i.e. the translation-time analysis is
free at corpus scale.

Where the shrink lands (total bytes, alethe2/alethe3):

| logic    | n      | alethe2 GB | alethe3 GB | total x | median x |
|----------|-------:|-----------:|-----------:|--------:|---------:|
| QF_BV    | 23,674 | 226.16     | 225.65     | 1.00    | 1.00     |
| QF_UF    |  4,285 | 28.03      | 26.05      | 1.08    | 1.09     |
| QF_LIA   |  2,548 | 4.49       | 3.28       | 1.37    | 1.00     |
| QF_IDL   |    540 | 4.48       | 3.82       | 1.17    | 1.00     |
| QF_LRA   |    544 | 3.36       | 2.46       | 1.37    | 1.16     |
| QF_UFBV  |    535 | 3.34       | 1.94       | 1.72    | 1.16     |
| UFLIA    |  7,442 | 3.02       | 2.05       | 1.47    | 1.02     |
| LRA      |  1,144 | 1.18       | 0.49       | 2.42    | 1.01     |
| LIA      |    266 | 0.35       | 0.17       | 2.12    | 1.31     |

Biggest single shrinks are the Monniaux QE cluster: formula_216
204.5 MB -> 0.67 MB (**305x**, matching the local probe), formula_040 188x.
QF_BV is flat as expected: bitblasting proofs are mostly anchor-free, so
there is nothing to hoist.

## The 12 non-valid cases, diagnosed

- **2 pre-existing errors** (Goel `TreeArb` QF_UFBV): also error in alethe2,
  unrelated to the printer.
- **3 real regressions** (Certora QF_UFLIA): carcara
  `step id 't1920.t1' is not defined`. Root cause: a hole in the frame
  targeting — a step's dependency-based target frame can be shallower than
  the frame where one of its premises was actually placed, in particular a
  premise pinned inside a subproof as its concluding derivation, whose id
  dies when the subproof closes (also reachable via frames set aside for an
  anchor printed below its target). First corpus-scale exposure of the
  hoisting design; the 13-probe sweep never tickled it.
- **4 memouts + 3 print timeouts** on borderline cases (380-640 MB proofs
  that sat at 9.5-9.8 GB / 450-575 s in alethe2). The memory regression came
  from the printer's deferred rendering: the whole proof was built as items
  and rendered at the end, so huge flat proofs were held in memory, which
  the old streaming printer never did.

## Fixes (cvc5 alethebv)

- `f5133b6d9d` — placement clamped to premises' frames: each printed step
  records its frame; a step is placed no shallower than any premise's active
  frame; a premise whose frame does not enclose the current position is
  printed again in the current chain; a closing frame only undoes ids that
  still belong to it; the re-printed concluding step of an anchor takes its
  id from the frame counter (the hardcoded `t0` could collide with a hoisted
  step). All three Certora benchmarks check valid (44788 also shrinks
  8.3 MB -> 3.3 MB). Additionally, frame-0 items are now rendered to the
  output stream as they are created (append order is output order), so flat
  proofs stream again: lfsr_008_015_032 (cluster memout) completes locally
  at 8.4 GB peak under a 10 GB limit, 640 MB proof.
- Probe sweep byte-identical, alethe regressions 8/8, jain6 solve+print
  unchanged.

## Follow-ups triggered by the CPC size-gap question

Re-attribution of the Alethe-vs-CPC total-bytes result (correcting an
earlier wrong guess that credited `:named`): CPC hash-conses every subterm
into `(define @tN () ...)`, so term sharing is a wash. CPC is *smaller* in
every logic except QF_BV; the whole 1.34x aggregate Alethe win is QF_BV
(203 GB vs 128 GB), from two causes:

1. **`--dag-thresh=0` artifact** (our workaround for the eo printer emitting
   SMT-LIB `let` in define bodies, which ethos cannot parse): benchmarks
   with many `:named` input terms re-declare them as fully expanded
   `(define ref!N ...)` — 70% of the Sydr predicate_2668 proof. Fixed in
   cvc5 `a7449491d2`: the eo define command hoists its body's shared
   subterms into preceding `(define @d<id>_N () ...)` commands (local per
   definition, so ordering is preserved). Sydr: 6.86 MB -> 3.94 MB,
   let-free, ethos-correct at default dag threshold; CPC no longer needs
   `--dag-thresh=0` at all.
2. **Resolution pivots**: CPC's `chain_m_resolution` spells out every
   pivot/polarity (median step 561 B, max 10 KB, 2.66 MB of
   countbitsrotate008's 3.2 MB); Alethe resolution carries none (median
   94 B) and carcara reconstructs them. Symmetric evaluation:
   `--proof-alethe-res-pivots` verified working (12-probe sweep valid);
   countbitsrotate008 grows 1.64 -> 3.35 MB with pivots, landing almost
   exactly on CPC's size — confirming pivots as the step-weight difference.

## Round-4 runs (submitted 2026-09-03, quad, bin4 = cvc5 `a7449491d2`)

- `all-alethe4`: full union, Alethe **with** res-pivots (pivot cost vs
  checking-time benefit, and format-fair size comparison against CPC).
- `all-cpc2`: full union, CPC **without** `--dag-thresh=0` (fair CPC sizes).
- `all-alethe3fix`: the 12 lost benchmarks in the alethe3 configuration
  (patches the alethe3 tally).

Report refresh (tables, plots, corrected size-gap attribution) follows once
these land.

## Addendum: the LIA "slow Alethe production" cluster is a cold-start artifact

The solve+print scatter against CPC shows a LIA cluster at ~5 s on the
Alethe axis (ratio up to 300x). It is not pipeline cost: task CPU time is
identical across pipelines (LIA totals 56 s Alethe vs 55 s CPC), and the
same benchmark measures 0.024 s (round 1, long-resident `bin/`), 5.8 s
(round 2, fresh `bin2/`), 6.3 s (round 3, fresh `bin3/`), 0.021 s (CPC,
warm `bin/`) at ~0.08 s CPU in all four. Each Alethe round ran freshly
uploaded 37 MB cvc5 + 40 MB carcara static binaries from scratch storage;
LIA is the job's first array and its 266 sub-0.1 s tasks start as a
thundering herd, so every task stalls paging the cold images in. Median
wall-minus-CPU gap: +5.24 s for alethe3 LIA, ~0 everywhere else and in all
of CPC. Corpus-wide: ~735 s of 627,000 s (0.1%); but the LIA table row's
solve/check ratio reads 6.27 where the true value is ~30.

Handling: report annotated (figure caption, caveats, table footnote);
round-4 runs share fresh bin4 on both pipelines so their comparison stays
fair; local runner templates now warm the binaries (`--version`) before the
timed invocation for future rounds.
