# Justifying arbitrary Alethe equality steps with egglog — orientation notes

Branch: `egglog/elaborator` (23 commits on top of `main`).
Written 2026-09-13 after reproducing the flow end to end locally.

Companion thesis: `/home/hbarbosa/papers/these/msc-tiago` (Tiago Campos,
*Independent justification of rewrites in SMT proofs via equality saturation*).

---

## 1. The shape of proof the technique expects

The input is a **cvc5 Alethe proof produced at `theory-rewrite` granularity**.
At that granularity cvc5 does *not* justify its preprocessing/rewriting
equalities; it emits them as trusted holes:

```
(step t3 (cl (= <lhs> <rhs>)) :rule hole
      :args ("TRUST_THEORY_REWRITE" (= <lhs> <rhs>) 1 6))
```

* The first `:args` element is the literal string `"TRUST_THEORY_REWRITE"` —
  this is the *only* thing `rare_hole::is_theory_rewrite_hole` keys on
  (`src/elaborator/rare_hole.rs`).
* The equality repeated in `:args`, plus the two trailing integers, is what
  `--parse-hole-args` makes Carcara parse as real terms. Without that flag the
  args stay uninterpreted and the pipeline cannot read the obligation.
* The step's **clause must be a single literal** — an equality. A multi-literal
  clause is rejected at the `setup` stage.
* The proof must be a **refutation** (conclude `(cl)`). A bare hole file such as
  `demo.smt2.alethe` is rejected with *"proof does not conclude empty clause"*
  before elaboration even starts. This is why per-hole work goes through
  `carcara slice`, which appends a synthetic
  `(step slice_end (cl) :rule hole :premises (tN) :args ("trust"))`.

Produce such proofs with (this repo's `scripts/solve.sh`):

```
cvc5 problem.smt2 --produce-proofs --dump-proofs \
  --proof-format-mode=alethe --proof-granularity=theory-rewrite \
  --proof-alethe-res-pivots --proof-elim-subtypes --print-arith-lit-token \
  > problem.smt2.alethe
```

### What comes out

`--elaborate-hole-rewrites` replaces each such hole with a subproof. The core
of that subproof is one of:

| Certificate node | Emitted Alethe rule | Trusted? |
|---|---|---|
| `Rule` with a name in the RARE db | `rare_rewrite :args ("<rule>" <inst>...)` | no — `check_rare` re-checks it |
| `Rule` engine-internal (no RARE name) | `hole :args ("TRUST_THEORY_REWRITE" "<name>")` | **yes** |
| `Computational::Evaluation` | `evaluate` | no |
| `Computational::AciNorm` | `aci_simp` | no |
| `Computational::ArithPolyNorm` | `poly_simp` | no |
| `Computational::DistinctElim` | `distinct_elim` | no |
| `Computational::ArithPolyNormRel` | `hole :args (... "arith_poly_norm_rel")` | **yes** |
| `Refl/Symm/Trans/Congruence` | `refl` / `symm` / `trans` / `cong` | no |

All of the non-trusted rules above are implemented in
`src/checker/shared.rs` (lines 299–488), so the elaborated proof re-checks
with a plain `carcara check`.

Observed output for a `bool-double-not-elim` hole (real QF_LIA benchmark):

```
(anchor :step t2.t1)
(assume t2.t1.t2.h (not (= (not (not (>= ...))) (>= ...))))
(step t2.t1.t2.1 (cl (= (not (not (>= ...))) (>= ...)))
      :rule rare_rewrite :args ("bool-double-not-elim" (>= ...)))
(step t2.t1.t2.2 (cl) :rule resolution :premises (t2.t1.t2.1 t2.t1.t2.h))
(step t2.t1 (cl (not (not (= ...))) false) :rule subproof :discharge (t2.t1.t2.h))
(step t2.t2 ... :rule not_not)
(step t2.t3 (cl (not false)) :rule false)
(step t2.t4 (cl (= ...)) :rule resolution :premises (t2.t1 t2.t2 t2.t3))
```

The subproof shape comes from `external::insert_solver_proof`: the equality
proof is closed by resolving against the negated conclusion, exactly as an
external solver's proof would be inserted.

---

## 2. Building

Nothing special. `rust-toolchain.toml` pins 1.93; `rustc 1.93.1` is installed.

```
cd /home/hbarbosa/carcara/wt-tiago
cargo build --release        # ~41 s from a warm cargo registry
./target/release/carcara --version
# carcara 1.1.0 [git f1f22055 egglog/elaborator]
```

egglog 0.4.0 is a normal `Cargo.toml` dependency (the production engine).
egglog 3.0.0 (`egglog-proofs`) is a **dev-dependency only**, used by the
reconstruction unit tests to build proof-producing fixture e-graphs; the
shipped pipeline never uses it. There are no feature flags to enable
(`debug-egglog` is only extra logging).

The pre-existing `target/release/carcara` in the worktree was from Jul 9 and
predates the elaborator commits — rebuild before using it.

---

## 3. Running Carcara with egglog

Two distinct modes:

### (a) Check only — validate the hole, keep it a hole

```
carcara check proof.smt2.alethe problem.smt2 \
  --rare-file tests/rare/big.rare --check-hole-rewrites \
  --expand-let-bindings --allow-int-real-subtyping --parse-hole-args
```

egglog saturates and answers "the two sides are in the same e-class". Nothing
is reconstructed; the proof is simply accepted. This is the mode the **thesis
evaluation (RQ1/RQ2) measures**.

### (b) Elaborate — reconstruct a checkable Alethe subproof

```
carcara elaborate proof.smt2.alethe problem.smt2 \
  --rare-file tests/rare/big.rare --elaborate-hole-rewrites --pipeline hole \
  --expand-let-bindings --allow-int-real-subtyping --parse-hole-args \
  --no-print-with-sharing > elaborated.alethe
```

This is the command in `instructions.txt` and in
`tests/rare/sliced_proofs/Running.MD`.

Shared egglog knobs (they apply to both modes):
`--continuous-saturation`, `--rare-check-timeout <ms>`, `--print-egglog`.

RARE databases available in-tree: `tests/rare/big.rare` (674 lines, the real
one), plus `rules.rare`, `rules2.rare`, `prop.rare`, `bug.rare`, `demo.rare`.

#### Gotchas found while running this

1. **`carcara elaborate` prints the pre-elaboration status as the first line of
   stdout.** `> elaborated.alethe` therefore yields a file starting with
   `holey`, and feeding it back to `carcara check` fails with
   `unexpected token: 'holey'`. Strip line 1 (`tail -n +2`).
   The RQ1 runner did the equivalent with a perl one-liner.
2. **`--sliced-output`'s help text is reversed.** `app.rs` declares
   `value_names = ["SLICED_PROBLEM", "SLICED_PROOF"]` but `main.rs:304` reads
   `(proof_filename, problem_filename) = (&files[0], &files[1])`. The correct
   order on the command line is **proof first, then problem**.
3. **A slice always checks as `holey`**, because `slice_end` is itself a
   `hole` step with `:args ("trust")`. Success must be measured by counting
   remaining `TRUST_THEORY_REWRITE` occurrences, not by the verdict — which is
   exactly what the JSON in `instructions.txt` does
   (`"verdict": "holey"`, `"remaining_holes": 0`, `"fully_checked": true`).
4. `--pipeline hole` is required: the `hole` pass must be in the pipeline, and
   restricting to it avoids paying for polyeq/local/uncrowd/reordering.
5. The CLI already runs on a 512 MiB stack thread (`main.rs`), so the
   deep-recursion stack overflows reported in the thesis' `Err` column should
   be less frequent than they were.

---

## 4. Is the e-graph → Alethe reconstruction present on this branch?

**Yes.** It is the substance of the branch. `src/rare/reconstruction/`:

| File | Role |
|---|---|
| `snapshot.rs` | `EGraphSnapshot::capture_production` serializes the saturated egglog 0.4 e-graph into a **provenance-free** snapshot: e-nodes, interned operators, canonical e-class ids, three indices (by class, by (class, op), by signature). |
| `search.rs` (44 k) | Searches that snapshot for a replayable rewrite chain between the goal's lhs and rhs. |
| `certificate.rs` | The `Certificate` tree (`Refl`/`Rule`/`Computational`/`Symm`/`Congruence`/`Trans`) and `verify_in`, which re-checks the certificate **without consulting the e-graph** — rule instantiation is re-matched, ACI/poly/evaluation steps are recomputed. |
| `computation.rs` | The non-RARE computational kinds (ACI norm, poly norm, evaluation, distinct elim). |
| `program.rs` | Recovers the goal terms, the compiled rewrite rules and the arithmetic sorts *from the generated egglog program text* (`generated_goals`, `rules_from_generated_program`, `ArithSorts::from_generated_program`). |
| `term.rs` | Decoding back from the `Mk`/`Args`/`Empty`/`@f` encoding to Alethe syntax. |

The orchestration is `src/elaborator/rare_hole.rs::elaborate`:
`run_egglog` → `capture_production` → `reconstruct_with_sorts` →
`AletheElaborator::elaborate_full` → parse + **check the emitted steps with the
real checker** → `insert_solver_proof`.

Note the design point: egglog is used only as an *oracle*. It is not asked for
a proof (egglog 0.4 has no provenance). The certificate is rediscovered by
searching the saturated e-graph afterwards, and is then independently verified
— so a buggy search cannot produce an unsound proof, only a failure.

Tests: `src/rare/reconstruction/tests/mod.rs`, notably
`elaborates_cvc5_theory_rewrite_holes_end_to_end` (RF-12), and the
`#[ignore]`d corpus sweep `reconstructs_benchmark_corpus`, driven by
`BENCH_LIST` (TSV: `<slice.alethe>\t<problem.smt2>\t<hole id>`), `BENCH_RARE`,
optional `BENCH_SKIP`/`BENCH_LIMIT`/`BENCH_OUT`/`BENCH_DUMP`/`BENCH_PRINT`.

---

## 5. What `instructions.txt` asks for, and how it relates

`instructions.txt` gives two things:

1. The **single-proof command** (§3b above) — verified working.
2. A **`pipeline.py <root> --rare-file ... --max-holes-per-proof N --jobs 8
   --carcara <bin> --slice-timeout-sec 120 --elab-timeout-sec 900
   --check-timeout-sec 300`** driver that, per the JSON record, does:
   slice each `TRUST_THEORY_REWRITE` hole out of each proof → elaborate the
   slice → check the elaborated slice → record timings and hole counts into
   `pipeline_runs/<root>/<logic>/<problem>/` plus a final JSON at the root.

**`pipeline.py` is not in this repository and is not anywhere under
`/home/hbarbosa`.** It has to be obtained from Tiago (or rewritten — it is a
thin driver over three `carcara` invocations; see §6).

The JSON record in `instructions.txt` is reproducible by hand today. Its fields
map one-to-one onto:

```
carcara slice  <proof> <problem> --from <hole>
               --sliced-output <slice.alethe> <slice.smt2> ...   # proof FIRST
carcara elaborate <slice.alethe> <slice.smt2> --elaborate-hole-rewrites ...
carcara check     <elaborated>   <slice.smt2> ...
```

I reproduced the exact record from `instructions.txt`
(`QF_LIA/ex8200_2600_100.smt2`, hole `t2`): slice has 1 hole, elaboration
succeeds (0.12 s here vs 1.07 s in the record), `remaining_holes` 0, check
verdict `holey`. The obligation is a `bool-double-not-elim`. In my cvc5
(1.3.4.dev) the hole `t2` lands on line 6 rather than line 5 — a one-line
prelude difference from the cvc5 version used for the record.

---

## 6. The `small_benchmark` set — status in this worktree

`small_benchmark/` contains `non-incremental.tar.gz` and 12 per-logic
tarballs (QF_LIA, QF_LRA, QF_IDL, QF_RDL, QF_UF, QF_UFIDL, QF_UFLIA,
QF_UFLRA, UF, UFIDL, UFLIA, UFLRA). Nothing is extracted.

**These are SMT-LIB *problems* only — 45,717 `.smt2` files and zero
`.alethe` files.** The `instructions.txt` JSON, by contrast, refers to
`small_benchmark/QF_LIA/ex8200_2600_100.smt2.alethe`, i.e. a *flat*
`<logic>/<name>.smt2` + `<name>.smt2.alethe` layout with proofs already
present.

So there are two gaps before the experiment can run:

* the proofs must be generated (cvc5 `theory-rewrite`, §1), and
* the layout must be flattened to `<root>/<logic>/<name>.smt2[.alethe]`,
  because the tarballs nest `<logic>/<family>/<subfamily>/<name>.smt2`.

Per-logic `.smt2` counts:

```
QF_LIA 13306   UF 7590      QF_UF 7503    UFLIA 10128
QF_IDL 2528    QF_LRA 1753  QF_UFLRA 1284 QF_UFLIA 659
QF_UFIDL 628   QF_RDL 255   UFIDL 68      UFLRA 15
```

Note the thesis evaluates six logics (QF_LIA, QF_LIRA, QF_LRA, QF_UF,
QF_UFLIA, QF_UFLRA); this tarball set has no QF_LIRA and adds
QF_IDL/QF_RDL/QF_UFIDL/UF/UFIDL/UFLIA/UFLRA.

---

## 7. Reproducing the thesis' partial experiments

The raw data is committed in the thesis repo:

* `raw/data_rq1.tar.gz` (98 MB, ~1,002,070 entries) — one directory per proof
  obligation, `<problem>.smt2.proof__<step-path>.proof/{run.out,output.log}`,
  grouped under `carcara_theory_check_outputs_modified_arith_poly_norm/<LOGIC>_random_sample/`,
  each with `benchmarks`, `script.sh`, `options`, `carcara_theory_check.sh`
  and assorted `grep_*` / `cmpr` / `salida` post-processing files.
* `raw/data_rq2.tar.gz` — six CSVs `data_<logic>` with header
  `item,dsl-theory,carcara` (problem path, `t_DSL − t_REWRITE` in ms,
  pipeline checking time in ms). Row counts: qf_lia 1425, qf_uf 1592,
  qf_lra 143, qf_uflia 113, qf_uflra 12, qf_lira 1.

Both experiments ran on the **barrett cluster**, under
`/barrett/scratch/mallku/rare_paper_benchmarks/`, via
`/barrett/scratch/local/bin/submit-job.sh`. The RQ1 QF_LIA job was a SLURM
array of 171,534 tasks, partition `octa`, `-j 7`, `--time-limit 600`,
`--memory-limit 8000`, `--cpus 8`, each task wrapped in
`runexec --walltimelimit 600 --memlimit 8000MB`.

### The important caveat

The RQ1 runner (`carcara_theory_check.sh`) invoked:

```
carcara elaborate /tmp/$proof /tmp/$problem \
  --expand-let-bindings --allow-int-real-subtyping \
  --hole-solver=rare-rewrite --rare-file $rare_file \
  --parse-hole-args --continous-saturation
```

**Neither `--hole-solver=rare-rewrite` nor `--continous-saturation` (sic)
exists on this branch.** The binary was
`carcara_arith_poly_norm_tiago/target/release/carcara` — a different Carcara
tree. Its log lines (`Elaborating t9282:`, `Running goal check schedule round
1...`, `Elaboration succeeded in 0.093638s`) appear nowhere in this source.

On `egglog/elaborator` the equivalents are:

* `--hole-solver=rare-rewrite`  →  `--check-hole-rewrites` (check mode, what
  RQ1/RQ2 actually measured) or `--elaborate-hole-rewrites --pipeline hole`
  (reconstruct mode, new on this branch).
* `--continous-saturation`  →  `--continuous-saturation`.

`--hole-solver` is gone entirely; the current `hole_solver` field is fed by
`--smt-solver` and only handles `all_simplify`/`rare_rewrite` steps via an
external SMT solver — a different mechanism.

Also note the RARE file used there was `scripts/rq1/.../rules.rare`, not
this repo's `tests/rare/big.rare`; they are not guaranteed to match.

So the thesis numbers are **not** directly reproducible with this branch's
binary. Re-running RQ1/RQ2 means re-running with the current flags, which
produces comparable-but-new numbers.

### Recipe sketch, current branch

RQ1 (single-step, checking):

```
# 1. proofs
cvc5 <p>.smt2 --produce-proofs --dump-proofs --proof-format-mode=alethe \
  --proof-granularity=theory-rewrite --proof-alethe-res-pivots \
  --proof-elim-subtypes --print-arith-lit-token > <p>.smt2.alethe
# 2. one slice per TRUST_THEORY_REWRITE hole
carcara slice <p>.smt2.alethe <p>.smt2 --from <hole> \
  --sliced-output <slice>.alethe <slice>.smt2 \
  --expand-let-bindings --allow-int-real-subtyping --parse-hole-args -v
# 3a. check mode (the thesis metric)
carcara check <slice>.alethe <slice>.smt2 --rare-file big.rare \
  --check-hole-rewrites --continuous-saturation \
  --expand-let-bindings --allow-int-real-subtyping --parse-hole-args
# 3b. or reconstruct mode (this branch's contribution)
carcara elaborate <slice>.alethe <slice>.smt2 --rare-file big.rare \
  --elaborate-hole-rewrites --pipeline hole \
  --expand-let-bindings --allow-int-real-subtyping --parse-hole-args -v \
  | tail -n +2 > <slice>.elaborated.alethe
carcara check <slice>.elaborated.alethe <slice>.smt2 --rare-file big.rare \
  --expand-let-bindings --allow-int-real-subtyping --parse-hole-args
```

Steps 2–3 for a whole corpus are precisely what `pipeline.py` automated, and
what the `reconstructs_benchmark_corpus` sweep does in-process from a
`BENCH_LIST` TSV.

RQ2 additionally needs, per problem, a second cvc5 run at
`--proof-granularity=dsl-rewrite`, and records `t_DSL − t_REWRITE`.

---

## 8. Measured cost and sizing (added 2026-09-13)

### 8.1 Per-slice distribution, from the thesis' own RQ1 raw data

Parsed all 333,901 `run.out` records in `raw/data_rq1.tar.gz` (walltime,
cputime, peak memory, `terminationreason`). Recomputed success rates match the
thesis table (QF_LIA 90.16% vs 90.27%, QF_UF 99.21% vs 99.16%), so the parse is
sound. Note the archive holds exactly 2x the obligation count the table
reports, but the rates agree.

At the original 600 s / 8 GB limits:

| logic | N | ok% | TO | MO | p50 | p90 | p99 | max |
|---|---|---|---|---|---|---|---|---|
| QF_LIA | 171,534 | 90.16 | 660 | 16,224 | 0.24 | 0.84 | 20.44 | 599.0 |
| QF_LIRA | 405 | 96.79 | 6 | 7 | 0.12 | 0.39 | 342.95 | 448.6 |
| QF_LRA | 125,919 | 97.36 | 257 | 3,048 | 0.79 | 4.17 | 28.14 | 589.5 |
| QF_UFLIA | 7,985 | 90.17 | 1 | 784 | 0.15 | 0.59 | 0.74 | 39.7 |
| QF_UFLRA | 4,892 | 97.75 | 54 | 56 | 0.44 | 0.78 | 7.15 | 570.4 |
| QF_UF | 23,166 | 99.21 | 95 | 88 | 0.15 | 0.24 | 19.09 | 502.3 |
| **ALL** | **333,901** | **93.62** | **1,073** | **20,207** | 0.30 | 1.57 | 27.61 | 599.0 |

**Failures are memory, not time: 20,207 memouts vs 1,073 timeouts.** Successful
runs use trivial memory (QF_LIA p99.9 = 529 MB) while memouts saturate 8 GB in a
median of 38 s. That is a cliff, not a tail.

Cumulative success (% of all obligations) vs wall cap, at 8 GB:

| cap | 20 s | 60 s | 120 s | 180 s | 300 s | 600 s |
|---|---|---|---|---|---|---|
| QF_LIA | 89.25 | 89.68 | 89.95 | **90.02** | 90.08 | 90.16 |
| QF_UFLIA | 90.16 | 90.17 | 90.17 | 90.17 | 90.17 | 90.17 |
| QF_LRA | 95.94 | 96.93 | 97.13 | 97.19 | 97.28 | 97.36 |
| QF_UF | 98.29 | 98.92 | 99.00 | 99.01 | 99.20 | 99.21 |
| **ALL** | 92.54 | 93.18 | 93.41 | **93.47** | 93.54 | 93.62 |

Cluster cost for a sample of this size (333,901 obligations), 168 concurrent
slots:

| cap | CPU-hours | wall | success |
|---|---|---|---|
| 20 s | 212.8 | 1.27 h | 92.54% |
| 60 s | 363.9 | 2.17 h | 93.18% |
| 120 s | 497.6 | 2.96 h | 93.41% |
| **180 s** | **583.0** | **3.47 h** | **93.47%** |
| 600 s | 841.9 | 5.01 h | 93.62% |

### 8.2 Recommended sizing on `quad`

`quad` = 24 nodes x 8 cores x 64,110 MB (8.0 GB/core — the same ratio as the
`octa` nodes the thesis used).

```
submit-job.sh -w -t 180 --memory-limit 8000 --cpus 1 -j 7 -p quad ...
```

* **180 s wall** is where every logic clears 90% (QF_LIA crosses at exactly
  180 s). 120 s costs 15% less CPU with QF_LIA at 89.95%. 600 s buys +0.15 pp
  for +44% CPU.
* **`-j 7`, not 8**: 8 x 8000 MB = 64,000 of the node's 64,110 MB leaves nothing
  for the OS. This is almost certainly why the original runs used `-j 7`.
* **`-w` matters**: `submit-job.sh -t` is CPU seconds by default; the original
  experiment's `runexec --walltimelimit` is wall.

### 8.3 Per-benchmark (complete certificate)

From `raw/data_rq2.tar.gz` (per-certificate pipeline time, ms; the QF_LIA sum
119,882.9 s matches the thesis table's 119,882.87 exactly):

| logic | rows | sum (s) | p50 | p90 | p99 | max |
|---|---|---|---|---|---|---|
| qf_lia | 1,424 | 119,882.9 | 6.20 | 304.00 | 887.44 | 1,189.0 |
| qf_lra | 142 | 1,957.6 | 3.08 | 12.95 | 276.96 | 609.8 |
| qf_uf | 1,591 | 468,196.3 | 237.01 | 505.44 | 2,455.34 | 5,340.9 |
| qf_uflia | 112 | 3,615.9 | 0.42 | 98.86 | 330.64 | 343.3 |
| qf_uflra | 11 | 489.3 | 2.05 | 116.75 | 126.11 | 126.1 |

Sequential whole-certificate: 900 s covers 99.1% of QF_LIA's *checkable*
certificates and 97.4% of QF_UF's; 1200 s (the submit-job.sh default) is ample.

**But ~90% per benchmark is not attainable, and no timeout fixes it.** RQ2 fully
checked 1,488/2,513 QF_LIA paired certificates (59%) and 11/497 QF_UFLRA (2%).
A certificate is fully justified only if *every* hole succeeds; with per-hole
success ~0.90 over proofs carrying hundreds to thousands of holes, the product
collapses. Report *fraction of holes justified per benchmark* rather than
all-or-nothing, or attack the memory side.

Raising memory is worth testing before paying for it: successful runs sit three
orders of magnitude below the 8 GB limit while memouts saturate it in seconds.
On quad, 16 GB means `-j 3` — a third of the throughput. Re-run just the ~20k
memouts at 16/32 GB first and measure the rescue rate.

### 8.4 Local measurements on this branch

40 holes sampled uniformly from the 1,836-hole QF_LIA proof
(`ex8200_2600_100.smt2`), each sliced and elaborated separately, 900 s / 6 GB:

* slicing is free: max 0.04 s.
* elaboration wall: p50 1.27 s, p75 5.00 s, p90 8.16 s, max 144.52 s.
* 39/40 completed; one (`t120.t37.t289`) hit the 900 s timeout.
* Sum over the sample = 452.6 s for 39 holes + one 900 s timeout.
  Extrapolated to 1,836 holes: **~17 CPU-hours for this single proof.**

That settles the whole-proof question: `carcara elaborate` over a full cvc5
proof in place **does not finish** at this scale (a 900 s run and a 7,200 s run
both failed to produce output; the file is written only at the end, so nothing
is salvaged from a kill). Per-hole slicing is a necessity, not a
parallelization convenience — and at ~17 CPU-h spread over 168 slots it is
~6 minutes of wall time.

**`--elaborate-hole-rewrites` success is not the same as full justification.**
14 of the 39 completed elaborations (**36%**) produced a subproof that still
contains one trusted `hole :args ("TRUST_THEORY_REWRITE" "arith_poly_norm_rel")`
step. This is by design (`rare_hole.rs`: Carcara's native `poly_simp_rel` needs
a scaled-difference premise and matching relation operators, which these
certificates do not supply). Notably, every one of the slowest completions
carries this residue — the expensive holes are exactly the arithmetic ones that
stay partly trusted. The RQ1 rates in 8.1 are *check* mode, where this
distinction does not arise.

---

## 9. Throughput for the 30 s/hole + 1200 s/benchmark + 60 s cvc5 plan

### 9.1 Measured inputs

**cvc5 at 60 s**, on 150 problems sampled uniformly from `small_benchmark`
(30 each from QF_LIA, QF_LRA, QF_UF, QF_UFLIA, QF_UFLRA):

| logic | n | proofs | yield | holes p50 | p90 | max | mean holes |
|---|---|---|---|---|---|---|---|
| QF_LIA | 30 | 10 | 33% | 144 | 3,391 | 3,391 | 806 |
| QF_LRA | 30 | 10 | 33% | 117 | 3,491 | 3,491 | 676 |
| QF_UF | 30 | 17 | 57% | 434 | 749 | 753 | 398 |
| QF_UFLIA | 30 | 7 | 23% | 4 | 828 | 828 | 122 |
| QF_UFLRA | 30 | 9 | 30% | 587 | 2,591 | 2,591 | 951 |
| **ALL** | **150** | **53** | **35%** | | | | **585** |

31,000 holes across 53 proofs. cvc5 wall (48-problem subsample): mean 7.4 s,
p50 0.4 s, p90 42.0 s; proofs land in 1.9 s mean, failures burn 11.4 s mean
(most fail fast, not at the cap).

**Per-hole carcara cost under a 30 s cap**, from the RQ1 records
(mean of `min(t, 30)`, so failures charge their full 30 s):

| logic | mean | p50 | p90 | success @30s |
|---|---|---|---|---|
| QF_LIA | 3.33 s | 0.25 | 16.71 | 89.35% |
| QF_LRA | 2.65 s | 0.82 | 7.42 | 96.64% |
| QF_UF | 0.85 s | 0.15 | 0.25 | 98.40% |
| QF_UFLIA | 2.33 s | 0.29 | 1.18 | 90.16% |
| QF_UFLRA | 1.31 s | 0.45 | 0.82 | 97.32% |
| **ALL** | **2.84 s** | 0.30 | — | **~92.9%** |

### 9.2 The 1200 s benchmark cap is the binding constraint

Sequential per-benchmark cost = mean holes x mean per-hole cost:

| logic | mean cost | fraction over 1200 s |
|---|---|---|
| QF_LIA | 2,685 s | 30% |
| QF_LRA | 1,792 s | 20% |
| QF_UFLRA | 1,246 s | 44% |
| QF_UFLIA | 284 s | 14% |
| QF_UF | 338 s | 0% |
| **ALL** | **1,202 s** | **19%** |

The mean lands *exactly* on the 1200 s cap, and 19% of proofs exceed it. With
one job per benchmark you discard those regardless of the 30 s hole limit.

### 9.3 Slot count on quad

24 nodes x 8 cores x 64,110 MB.

* `-j 7 --memory-limit 8000` = **168 slots** (56,000 MB/node, 8 GB headroom).
* `-j 8 --memory-limit 7500` = **192 slots** (60,000 MB/node, 4 GB headroom) —
  **+14% throughput for free.** Justified by the data: successful runs use
  under 600 MB at p99.9, so the 8000 -> 7500 cut loses essentially nothing.

### 9.4 Throughput

| scheme | rate (192 slots) |
|---|---|
| one job per hole, 30 s cap | **243,000 holes/hour** |
| one job per benchmark, 1200 s cap | **576 benchmarks/hour** (19% hit the cap) |
| end to end, per 1,000 problems submitted | cvc5 0.01 h + carcara 0.61 h = **0.62 h** |

cvc5 is **1.3%** of the pipeline; carcara is ~98.7%. Do not spend effort
tuning the 60 s proof-production limit.

Whole-corpus estimate: 45,717 problems x 35% yield = ~16,000 proofs x 585 holes
= **~9.4M holes** = ~7,400 CPU-hours = **~38 h of quad wall time** at 192 slots.
Sample if that is too much; the RQ1 precedent was 0.5% of holes.

### 9.5 The 30 s per-hole limit is not enforceable in-process

Measured: `--rare-check-timeout 30000` on the hole that took 900 s in the
sample of 8.4 ran the full **300 s** until an external `timeout` killed it, and
produced nothing — 10x over budget.

Cause: `goal_run_schedule` (`src/rare/engine.rs:1194`) emits
`Saturate{list-ruleset}`, `Saturate{evaluation}`, then a bounded `Run`.
`run_goal_schedule_round` gives `Saturate` `repeats = 1` and calls
`run_and_record_statements`, which runs it to fixpoint inside egglog 0.4.
`check_timeout` only fires *around* that call (lines 1341/1343), never within
it. A saturation that blows up is uninterruptible.

Consequence: **threads alone will not stop workers getting stuck.** A blown-up
saturate pins its worker for the life of the job.

### 9.6 Making hole checking parallel — options

**(a) Process per hole. No code change. Use this.**
Slice, then `timeout 30 carcara elaborate` per slice. SIGKILL is a hard bound,
isolation is total, and a SLURM array or `xargs -P` parallelizes it. Overhead
measured at max 0.04 s slicing plus ~0.1 s startup, against a 2.84 s mean.
It also dissolves the 1200 s/benchmark cap, since the benchmark stops being a
unit of work — recovering the 19% lost in 9.2 and the full 243k holes/hour.

**(b) Make the cooperative timeout real.**
Replace the two unbounded `Saturate` statements with bounded
`Run { iterations: k }` loops. The machinery exists: the non-saturating
statement is already stepped with `check_timeout` before and after each
iteration; the saturating ones opt out via `repeats = 1`. Contained change.
Risk: rulesets needing a true fixpoint may stop early, so re-validate against
the RQ1 corpus before trusting success rates.

**(c) Threads inside Carcara.**
Hole elaboration is embarrassingly parallel — each hole needs only its clause,
the prelude, and the RARE database. Obstacles:

* `Elaborator` holds `pool: &'e mut PrimitivePool` (exclusive borrow), and
  `elaborate_hole` runs inside `mutate_impl` (`src/elaborator/mod.rs:429`), a
  single-threaded DFS with `FnMut` and `&mut ContextStack`. Restructure into
  three passes: collect the `TRUST_THEORY_REWRITE` steps, run them on a thread
  pool, splice results back with a lookup-only second `mutate`. Passes 1 and 3
  stay sequential and cheap.
* The term-pool merge is easier than it looks: `rare_hole::elaborate` already
  round-trips through text (it formats Alethe steps and re-parses via
  `parse_and_check`). A worker can return a `String` for the main thread to
  parse into the main pool, sidestepping pool merging. `ParallelProofChecker`
  also demonstrates the `Arc<PrimitivePool>` + per-thread `ContextPool`/
  `LocalPool` pattern if sharing terms is preferred.

**(c) without (b) still gets stuck** — a thread inside an uninterruptible
saturate cannot be killed in Rust. (c)'s real benefit is one-job-per-benchmark
accounting, not avoiding slow holes.

Recommended order: **(a) now, (b) as the one worthwhile code change, (c) only
if one-job-per-benchmark is a requirement.**

---

## 10. Implementation: bounded budgets, parallel holes, `poly_simp_rel`

Three changes on top of `f1f22055`.

### 10.1 (b) The per-hole budget is now real

`--rare-check-timeout` previously bounded nothing: measured at 10x over budget
(§9.5). Three separate unbounded phases were involved, fixed in turn.

**Saturation** (`src/rare/engine.rs`). `run_statement_within_deadline` replaces
the direct execution of every statement. With no deadline a `Saturate` runs to
its fixpoint in one egglog call, exactly as before. Under a deadline it is
instead stepped as single `Run { iterations: 1 }` calls, with `check_timeout`
between them and the loop ending as soon as `egraph.num_tuples()` stops growing
— egglog 0.4 cannot be interrupted inside one `(saturate ...)`, so the fixpoint
has to be approached rather than requested. Used by `run_goal_schedule_round`
and by both setup loops of `run_goal_fallback_attempt`.

**The certificate search** (`src/rare/reconstruction/search.rs`). `SearchStrategy`
gains a `deadline`, checked where `max_states` already was (`neighbors`), in the
bidirectional driver loop, and in `expand_level`. Expiry trips the existing
`over_budget` path, so no new failure mode is introduced.

**The e-graph snapshot** (`src/elaborator/rare_hole.rs`). Serializing the
saturated e-graph is one uninterruptible copy proportional to its size. A
deadline already spent now stops the hole before the snapshot, and
`MAX_SATURATION_TUPLES` (4M, deadline path only) stops saturation from building
an e-graph too large to copy in the first place.

The budget is shared: `reconstruct_steps` computes one deadline and passes it to
both egglog and the search, so a hole's total cost is bounded, not each phase
separately.

Measured, on the hole that previously ignored a 30 s budget for 300 s:

| budget | before | after |
|---|---|---|
| 1 s | — | 1.06 s |
| 5 s | — | 5.13 s |
| 10 s | — | 28.0 s (snapshot-bound, pre-cap) |
| 30 s | 300 s+, no output | see §10.4 |

It remains a **soft** budget: one egglog iteration and one snapshot are
uninterruptible, so overshoot is possible on pathological holes. The hard bound
is still the external process timeout — which is what the cluster provides.

### 10.2 (c) Holes are reconstructed in parallel

`--hole-threads N` (default 1, so the old path is untouched).

`rare_hole::elaborate` was split at its natural seam:

* `reconstruct_steps(pool, node, step, rules, options) -> Vec<String>` — all the
  cost (egglog, snapshot, search, Alethe emission). Takes `&mut dyn TermPool`,
  reads only the immutable proof node and rule database, and returns **text**.
* `insert_steps(elaborator, step, steps)` — parses that text against the problem,
  checks it, and splices it in. Always on the proof's own pool.

`Elaborator::reconstruct_holes_in_parallel` collects every hole
(`theory_rewrite_holes`, a DFS over the forest), runs `reconstruct_steps` on
`hole_threads` workers via `std::thread::scope` — each with a fresh
`PrimitivePool` — and returns a `step id -> Vec<String>` map. `elaborate_hole`
then splices from the map, falling back to the sequential path for any hole
whose worker failed, so errors are still reported at the right step.

Terms cross threads safely because Carcara's `ast::Rc` wraps `sync::Arc`
(`src/ast/rc.rs`). The text round-trip is what avoids merging term pools: each
worker's terms stay in its own pool and die with it; only strings come back,
and they are interned once by `insert_steps`.

Verified: on `tests/rare/elaborate/RF-12`, `--hole-threads 1` and
`--hole-threads 4` produce **byte-identical** output, both re-checking `valid`.

### 10.3 `arith_poly_norm_rel` is discharged via `poly_simp_rel`

Previously every relation certificate became a trusted hole, which was 36% of
completed elaborations in the §8.4 sample. The code comment claimed these were
"negated, mixed-operator, integer-tightened relations" that `poly_simp_rel`
could not serve. Inspecting the actual obligations showed three regular shapes:

| shape | example | route |
|---|---|---|
| `>=` vs `>=` | `(= (>= a (+ -3776 b c d)) (>= (+ a -b -c -d) -3776))` | direct |
| `=` vs `=` | `(= (= a (+ 3603 b -c -d)) (= b (+ -3603 a c d)))` | direct, sign flip allowed |
| `<=` vs `(not (>= ...))` | `(= (<= x 8472) (not (>= x 8473)))` | integer tightening |

`AletheElaborator::poly_simp_rel_chain` handles all three:

* Equalities go straight to `poly_simp_rel`, whose `Equals` case permits
  opposite-sign coefficients.
* Everything else is routed to a `>=` form on both sides by `to_geq`, using the
  RARE rules `arith-elim-leq`, `arith-elim-lt` and `arith-elim-int-lt` — emitted
  as checkable `rare_rewrite` steps — and the two `>=` forms are then related by
  a single `poly_simp_rel`. The routing steps are glued back with `trans`/`symm`.
* `scaling` derives the premise coefficients from the polynomial normal forms:
  with `d1`, `d2` the two scaled differences and `p1`, `p2` their pivots,
  `c1 = p2`, `c2 = p1` satisfies `c1*d1 = c2*d2`. The identity is **verified**
  before emission and denominators are cleared, so the premise is an integer
  `poly_simp` obligation. A sign-reversing pair is tried only for `=`, which is
  exactly `poly_simp_rel`'s own restriction.
* Integer tightening is applied only when `Poly::is_int_valued` says the
  difference really is integer-valued.
* Anything not covered keeps the trusted hole, and a partially emitted chain is
  rolled back (`steps.truncate(mark)`) so the fallback is not appended to a
  half-built chain.

The premise is proved by `poly_simp`, which is exactly the "scaled difference"
`poly_simp_rel` asks for:

```
(step p (cl (= (* c1 (- x1 x2)) (* c2 (- y1 y2)))) :rule poly_simp)
(step c (cl (= (>= x1 x2) (>= y1 y2))) :rule poly_simp_rel :premises (p))
```

Measured on the eight captured obligations: **6 fully justified, 0 trusted**,
2 exceeded the test's own 120 s cap (they succeed with a longer one). The
integer-tightening family — the majority — is covered.

All 244 library tests pass.

### 10.4 Validation

Per-slice, the way the pipeline actually runs (slice each hole, elaborate it,
re-check), across the three requested logics, 15 s per-hole budget, 8 GB:

| logic | holes | elaborated | avg | `arith_poly_norm_rel` left | any trusted step left |
|---|---|---|---|---|---|
| QF_UF | 20 | 20 | 78 ms | **0** | **0** |
| QF_LRA | 15 | 15 | 311 ms | **0** | **0** |
| QF_LIA | 10 | 10 | 3.9 s | **0** | **0** |
| **all** | **45** | **45** | | **0** | **0** |

Against the §8.4 baseline where 36% of completed elaborations kept an
`arith_poly_norm_rel` trust hole, this is 0 of 45. 12 of the elaborated proofs
were re-checked from their printed text with a plain `carcara check`: all 12
returned `holey`, whose only remaining hole is the synthetic `slice_end`
`("trust")` step the slicer appends — i.e. every reconstructed step checks.

Note this is on top of a guarantee already in the pipeline: `rare_hole` runs
`parse_and_check` on the reconstructed steps *before* splicing them in, so an
elaboration that succeeds has already passed Carcara's own checker.

Plus, separately: 244 library tests pass, and RF-12 elaborates byte-identically
at `--hole-threads 1` and `4`, re-checking `valid`.

### 10.5 Two findings from the validation

**Slicing is not just a scheduling convenience — it changes the work.** The
first hole of a 77-hole QF_LIA proof elaborates in **99 ms as a slice**, while
the same proof elaborated in place did not finish in 600 s. `run_egglog` seeds
the e-graph from `proof_node.get_assumptions()`; in a slice that is a handful of
assumptions, in a full proof it is the entire transitive premise set. This, not
parallelism, is the dominant cost difference, and it is the real reason the
`pipeline.py` design slices.

**The budget remains soft on pathological holes.** Hole `t9.t9` of RC-02 took
36.9 s under a 15 s budget — a 2.5x overshoot, from the uninterruptible egglog
iteration and e-graph snapshot described in §10.1. `MAX_SATURATION_TUPLES` caps
the worst case but does not make the bound exact. On the cluster this is
harmless (`runexec` provides the hard bound); in-process it means
`--rare-check-timeout` should be read as a target, not a guarantee.

### 10.6 Internal validation via the in-repo corpus sweep

The right harness for this was already in the repo: `reconstructs_benchmark_corpus`
(`src/rare/reconstruction/tests/mod.rs`), driven by a `BENCH_LIST` TSV of
`(slice, problem, hole)`. It runs the real pipeline per case and round-trips the
emitted steps through Carcara's checker (`check_with_carcara`), panicking on any
reconstruction, elaboration, or check failure. So `reconstructed=N` means N cases
passed the checker.

Two changes make it usable on a sample:

* `BENCH_TIMEOUT_MS` — per-case budget, passed to both `RunEgglogOptions.timeout`
  and `SearchStrategy::with_deadline`. Without it one diverging case stalls the
  whole sweep.
* The same pre-snapshot guards as the production path: skip the case when the
  budget is spent, and when the e-graph exceeds `MAX_SNAPSHOT_TUPLES`.

Run over 74 slices (24 QF_LIA, 30 QF_LRA, 20 QF_UF) at a 3-5 s per-case budget:

| cases | reconstructed | oracle-failed | stalled |
|---|---|---|---|
| 0-12 | 13 | 0 | — |
| 13 | — | — | 1 |
| 14-21 | 8 | 0 | — |
| 22-25 | 3 | 1 | — |
| 26-37 | 11 | 1 | — |
| 38-73 | 36 | 0 | — |
| **total** | **71 / 74** | **2** | **1** |

Zero reconstruction failures, zero Alethe-elaboration failures, zero checker
failures. The two oracle failures are egglog not closing the goal inside the
budget. Case 13 (`RC-02` hole `t9.t29.t28`) is the honest limit of §10.1:

**egglog 0.4 has no cancellation hook, so a single rule-matching iteration is
uninterruptible.** The budget is honoured at every boundary that exists —
between statements, between saturation iterations, in the search, before the
snapshot — but one iteration that runs for minutes cannot be cut short from
outside. `MAX_SATURATION_TUPLES` and `MAX_SNAPSHOT_TUPLES` cap the e-graph so
this is rare, but they cannot make the bound exact. A hard per-hole bound needs
either a process boundary (what `runexec` and `pipeline.py` provide) or a
cancellation hook added to egglog.

---

## 11. Hard per-hole limit: `--hole-isolate` (child process per hole)

The in-process budget cannot interrupt one egglog iteration (§10.6), and a
Rust thread cannot be killed, so the only hard bound is a process boundary.
`--hole-isolate` keeps the whole-proof, N-worker model of `--hole-threads`
but runs each hole's reconstruction in a child process:

* the worker builds `hole_input`: the problem prelude, a boundary line, the
  hole's depth-0 assumptions as top-level `assume`s and the hole citing them
  as premises — exactly what `run_egglog` reads off the in-process node
  (`get_assumptions` collects the depth-0 assumptions beneath it), so the
  child works from the same inputs; nothing is written to disk;
* it spawns the same binary's hidden `reconstruct-hole` subcommand, feeds
  that text on stdin, drains stdout/stderr on threads, and **kills the child
  outright** when `--rare-check-timeout` elapses; `--hole-memory-limit MB`
  applies `ulimit -v` to the child through `sh -c '... && exec ...'`, so the
  pid stays on carcara and the limit is on the child alone;
* a killed or failed child leaves its hole **as it was** (warned as
  `hole <id>: kept as trusted: <reason>`), so one bad hole no longer fails
  the whole elaboration. In thread mode the previous behaviour is unchanged.

Measured (`--hole-threads 4`, `tests/rare/big.rare`):

| case | result |
|---|---|
| RF-12, threads vs isolate | byte-identical output, 0.17 s |
| QF_LIA `pb2010__normalized-j907_8-unsat` (29 holes), 1 s/hole, isolate | **3.7 s** wall, 2 holes killed at 1.0 s, 27 justified, rc 0 |
| same proof, same 1 s/hole, in-process | **61 s** wall — the soft budget blown ~60x |
| RF-12, `--hole-memory-limit 30` | every child dies at start (the 512 MiB stack reservation needs ~700 MB), parent exits 0 with both holes kept |

Cost: ~0.1 s per hole for the child to parse the prelude and RARE file.

### Cluster run (`~/exp/egglog-holes/`)

`run-holes.sh` follows the pfchk runner contract (extra keys `elab_rc`,
`elab_time`, `holes_before`, `holes_after`, `holes_kept`; `ok=1` when the
elaborated proof re-checks valid or holey). cvc5 60 s at theory-rewrite
granularity, then `elaborate --hole-threads 4 --hole-isolate
--hole-memory-limit 5000 --rare-check-timeout 30000` under `timeout 600`,
then a `check` of the result. `gen-sets.py` takes the alethecore-eval sample
(seed 20260816) restricted to benchmarks whose local proof has at most 600
holes, 15 per logic. `submit-egglog-holes.sh`: quad, `-j 2 --cpus 4`,
24 GB, 900 s wall.

### cvc5 renamed the hole tag

cvc5 #12639 (`11c7a24fc1`, after April 2026) changed what the Alethe printer
emits for `ProofRule::TRUST_THEORY_REWRITE`: `:args ("TRUST_THEORY_REWRITE"
<eq> 1 6)` became `:args ("untranslated rewrite")` — same rule, same code path
(`src/proof/alethe/alethe_post_processor.cpp`). Builds from newer main (and
the `aletheLagFixes` static cvc5) print the new tag, so a run keyed on the old
one finds zero holes. `is_theory_rewrite_hole` now accepts both
(`THEORY_REWRITE_TAGS`); the runner counts both. On a newer-cvc5 QF_UF proof
with 43 such holes, four isolated workers at 30 s justified 40 and kept 3
(each killed at the 30 s bound), 30 s wall, and the result re-checks.

---

## 12. Cluster run `egglog-holes/small` (2026-09-14)

quad, 45 jobs (15 per logic from the alethecore-eval sample, proofs of at most
600 holes), one job per benchmark: cvc5 `main@f9e5d3c312` at theory-rewrite
granularity (60 s) → `carcara c7cc24a4 elaborate --hole-threads 4
--hole-isolate --hole-memory-limit 5000 --rare-check-timeout 30000` under
`timeout 600` with `big.rare` → `carcara check` of the result. Whole run:
**11 minutes** wall. Results in `~/exp/results/egglog-holes/small/`;
`~/exp/egglog-holes/analyze.py` summarizes.

| logic | proofs | ok | holes | justified | kept | elab p50 | elab max | peak mem |
|---|---|---|---|---|---|---|---|---|
| QF_LIA | 15 | 14 | 347 | 145 | 3 | 2.1 s | 600 s (timeout) | 3.5 GB |
| QF_LRA | 15 | 12 | 1,343 | 521 | 70 | 13.4 s | 379 s | 12.6 GB |
| QF_UF | 15 | 13 | 4,689 | 3,413 | 146 | 112 s | 272 s | 11.2 GB |
| **all** | **45** | **39** | **6,379** | **4,079 (63.9%)** | **219** | | | |

**Correction (2026-09-15):** the first version of this table claimed 6,037
justified (94.6%); the analysis script had counted the holes of proofs that
errored or timed out as justified. `justified` here is strict: holes of
proofs that finished elaboration and are no longer any trusted step in the
output (so it also excludes the elaborator's own residual trusted steps,
which `kept` does not count). The six proofs that produced nothing hold
1,958 of the 6,379 holes — the strongest argument for keeping partial results.

`ok` = the elaborated proof re-checks (valid or holey). Every `ok` proof's
reconstructed steps passed the checker; the holes that remain are exactly the
`kept` ones plus, in QF_LIA/QF_LRA, a few `arith_poly_norm_rel` shapes.

Why holes were kept (219): **killed at the 30 s hard budget 166** (QF_UF 117,
QF_LRA 48, QF_LIA 1), **memory limit 35**, **egglog could not prove 12**,
**no certificate found 6** (egglog proved it, the search found no replayable
chain). The hard budget held: no hole ran past ~30.2 s, and no worker took a
proof down with it.

The six non-`ok` benchmarks are not hole failures:

* 2 QF_LRA (`pd_not_sc_seen`, `pd_no_op_accs`) — **the up-front check of the
  original cvc5 proof fails** on a `rare_rewrite` step citing `ite-eq`, which
  `big.rare` lacks (rewrites.eo has it, but declares `t2 @T1` without a
  `(@T1 Type)` parameter, so that file does not parse). Fixed for the next run
  by `holes.rare` = big.rare + `ite-eq` (with `@T1` declared) + `distinct-false`.
* 2 QF_UF (`iso_icl850`, `iso_icl941`) — the original proof's `resolution`
  step is rejected ("pivot was not found in clause"): the cvc5-main resolution
  defect the alethe-lag notes already record; not reproducible with a main
  cvc5 without that branch's fix.
* 1 QF_LRA (`no_op_accs`, 203 holes, 379 s) — a reconstructed `evaluate` step
  was rejected by the checker (`(ite false x t) = t` is not what `evaluate`
  proves), and because that rejection happened on the main thread it failed
  the whole proof. `a6bf0d00` makes isolate mode keep such a hole instead.
  The `Evaluation` → `evaluate` mapping for `ite` with a constant condition
  is a real gap to fix (RARE's `ite-false-cond` is the right rule).
* 1 QF_LIA (`ring_2exp6_6vars`, 199 holes) hit the runner's 600 s elaborate
  cap: 199 holes at up to 30 s each over 4 workers is 1,492 s worst case.
  All partial work is lost on that path; a larger cap or per-hole result
  streaming would keep it.

Time per hole is dominated by the kills: QF_UF's 117 killed holes alone are
58 CPU-minutes of the run.

---

## 13. Runs `small2` and the partial-result design (2026-09-15)

`small2` = `small` with carcara `a6bf0d00` (a reconstruction the checker
rejects keeps its hole) and `holes.rare`:

| run | justified | ok | what changed |
|---|---|---|---|
| small | 4,079 / 6,379 (63.9%) | 39/45 | |
| small2 | **4,404 / 6,379 (69.0%)** | **41/45** | `no_op_accs` and `pd_no_op_accs` now `ok`; `pd_not_sc_seen` gets past the up-front check but hits the 600 s cap; `iso_icl850/941` unchanged (cvc5 resolution defect) |

The remaining non-`ok` proofs are exactly the lost-partial-work cases and the
cvc5 defect, which motivated the next changes (`3ba399fe`):

**`--hole-total-budget MS`** — a per-proof budget for all holes together.
Workers start no new hole past it, isolated children still running are
killed at it, and the proof is printed with whatever was justified in time;
holes never started are logged as `skipped`, holes cut short as `kept`. On the
43-hole QF_UF proof an 8 s budget returns in 8.1 s with 17 justified, 4 kept,
22 skipped, and the output re-checks.

**`--hole-check-only`** — the same workers and limits, but each child only
asks egglog whether the equality holds; nothing is reconstructed or spliced.
This separates *checking* (the thesis' RQ1 notion) from *elaboration*, which
is dearer and can fail where checking succeeds: on the 43-hole proof checking
proves 41, elaboration justifies 40 — the difference is a hole egglog proves
but the search finds no certificate for.

Per-hole verdicts and timings are logged at `info` (`hole t3: proved in
0.194s`, `hole t7: justified in 1.2s`, kept/skipped likewise) with a closing
`hole summary: total= proved|justified= kept= skipped= time=` line; the runner
reads that line. In every budgeted, isolated or check-only run a prepass
result is final for its hole — nothing is retried in-process.

`run-holes.sh` now does both passes per proof (check-only, then elaboration),
each under a 240 s hole budget and a 300 s safety net, cvc5 90 s, final check
120 s; new keys `upfront`, `chk_*`, `holes_skipped`, `elab_holes_time`.
Run `small3` is prepared with it.

---

## 14. Run `small3`: checking vs elaboration, partial results (2026-09-15)

Same 45 benchmarks; cvc5 60 s; two passes per proof with carcara `3ba399fe`,
four isolated workers, 30 s / 5 GB per hole, **600 s hole budget per pass**;
final `check` of the elaborated proof. Whole run ~30 minutes wall (the two
600 s proofs bound it). Results in `~/exp/results/egglog-holes/small3/`.

Two QF_UF proofs (`iso_icl850`, `iso_icl941`, 987 holes) still fail the
up-front check on cvc5-main's resolution defect; "attempted" below excludes
them. Every other proof is `ok` (43/45) — the two that lost everything to the
600 s cap in `small2` (`ring_2exp6`, `pd_not_sc_seen`) now return partial
results.

| logic | proofs ok | holes attempted | **checking: proved** | c-kept | **elaboration: justified** | kept | elab p50 |
|---|---|---|---|---|---|---|---|
| QF_LIA | 15/15 | 347 | 341 (98.3%) | 6 | 276 (79.5%) | 71 | 1.0 s |
| QF_LRA | 15/15 | 1,343 | 1,199 (89.3%) | 144 | 1,133 (84.4%) | 208 | 30 s |
| QF_UF | 13/15 | 3,702 | 3,634 (98.2%) | 68 | 3,413 (92.2%) | 146 | 111 s |
| **all** | **43/45** | **5,392** | **5,174 (96.0%)** | **218** | **4,822 (89.4%)** | **425** | |

`justified` is strict (no trusted step left for the hole); over all 6,379
holes it is 75.6%, up from 69.0% in `small2`. `skipped` is 0 everywhere: with
four workers the 600 s budget was never reached before every hole had been
started; the holes cut short at the budget are the 5 "proof's hole budget ran
out" kills (3 QF_LIA, 2 QF_LRA).

**What separating the passes shows.** Checking proves 352 more holes than
elaboration justifies (5,174 vs 4,822, 6.8% of the proved). The gap is almost
entirely time, not logic: reconstruction adds the e-graph snapshot and the
certificate search on top of egglog's run, and pushes holes that egglog alone
proves inside 30 s past the same bound. The clearest case is
`ring_2exp6_6vars` (QF_LIA, 199 holes): checking proves 195 in 108 s total;
elaboration justifies 131 in the full 600 s, 65 of its holes killed at 30 s.
The logic-level part of the gap is small: 6 "no certificate found" (egglog
proved it, no replayable chain), 2 reconstructions the checker rejected.

Kept-hole reasons across both passes: killed at the 30 s bound 480, memory
limit 126, egglog could not prove 24, no certificate 6, checker rejected 2,
proof budget 5. Peak memory 12.9 GB (QF_LRA), against the 24 GB job limit.

Against the thesis' RQ1 (single holes, 600 s / 8 GB, 0.5% sample): this
check pass, at 30 s / 5 GB with four workers, proves 96.0% of the attempted
holes, in the same range as the thesis' 90–99% per logic.

---

## 15. Where elaboration loses its holes: the snapshot (2026-09-15)

Per-hole analysis of `small3` (`~/exp/egglog-holes/perhole.py`), 5,389 holes
seen by both passes:

| | elaboration justified | elaboration kept |
|---|---|---|
| **checking proved** | 4,964 | **207** |
| checking did not prove | 0 | 218 |

The 207 holes checking proves but elaboration loses: 198 killed at the 30 s
bound, 6 no certificate, 2 checker-rejected, 1 proof budget. Memory kills are
63 in *both* passes — they happen in the egglog phase. Per finished hole,
elaboration costs 1.4–1.7x checking at the median but ~10x at p90 in the
arithmetic logics.

Phase attribution (child reports each phase; `4e0458d7`), re-running the two
proofs with the most losses locally under `small3`'s elaboration limits:

| proof | egglog | **snapshot** | search | emit | killed during |
|---|---|---|---|---|---|
| `ring_2exp6` (QF_LIA, 200 holes) | 29.6% | **69.7%** | 0.7% | 0.0% | snapshot 54, egglog 4 |
| `pd_not_sc_seen` (QF_LRA, 528 holes) | 38.2% | **57.8%** | 3.9% | 0.0% | egglog 42, snapshot 16 (+24 memory in egglog) |

For the 27 `ring_2exp6` holes whose snapshot took over 5 s, egglog took a
median 0.2 s and the snapshot a median 12.5 s (max 27.5 s): the equality is
proved almost instantly, then serializing the saturated e-graph
(`EGraphSnapshot::capture_production` → `egraph.serialize`) eats the budget.
The certificate search is never the problem.

Consequences:

* The elaboration-only losses are a **Carcara** problem — the full e-graph
  serialization — not an egglog one. The fix is to snapshot less: only the
  e-classes reachable from the goal terms (what the search actually walks),
  or a direct read of the e-graph without going through egglog's serializer.
  `MAX_SNAPSHOT_TUPLES` (4M) is far too loose to prevent this.
* An egglog 3.0 migration targets the *other* losses: the 63 memory kills per
  pass and QF_LRA's 42 egglog-phase kills (growth inside one iteration). It
  does not touch the snapshot cost, except indirectly by keeping e-graphs
  smaller.

## 16. The snapshot cost was egglog's serializer; fixed by vendoring 0.4.0 (2026-09-15)

§15 blamed the losses on "Carcara's full e-graph serialization". Splitting the
snapshot phase into egglog's `serialize()` and Carcara's indexing of its
output (`serialize` / `index` phases, `EGraphSnapshot::serialize_production`)
put the whole cost in egglog: indexing is ~0, and the serialized graphs are
small (a 1,452-node graph took 0.72 s, a 5,493-node one 10.8 s — ~2 ms per
node and super-linear). Instrumenting a vendored copy of egglog 0.4.0
(`EGGLOG_SERIALIZE_STATS`) showed the time entirely inside the per-node loop,
with no stale-row problem (`offsets ≈ live`, 175 tables, 28.5k live rows).

The cause, in `src/serialize.rs::serialize_value`: to print a *primitive*
value (an `i64`, a big rational, a string) egglog constructs a fresh
`Extractor` — whose `new` runs `find_costs`, a fixpoint cost computation over
**every row of every function in the e-graph** — for every primitive node it
emits, then calls the sort's `extract_term`, which for primitives never looks
at the extractor. Polynomial e-graphs are full of coefficient primitives, so
serialization was (#primitive nodes) × (#rows): quadratic. (3.0 serializes
through a different path but exposes no row iteration publicly either, so
migrating would not have been the shorter route — see the 20:02 status.)

**Fix:** `third-party/egglog-0.4.0/` is the released crate with one change
(`serialize-one-extractor.patch`): one `Extractor` built lazily per
`serialize` call, shared by all primitive nodes; `Cargo.toml` selects it via
`[patch.crates-io]`. The crate's tests/benches are left out
(`CARCARA-PATCHES.md`). Serializing a 1,452-node graph went from 0.72 s to
0.002 s; a 70k-node graph takes 0.22 s.

**Validation on `ring_2exp6`** (QF_LIA, 200 holes; local, `small3`'s
elaboration limits: 4 isolated workers, 30 s / 5 GB per hole, 600 s per
proof; `~/exp/egglog-holes/local/fix-ring.sh`, output `*.fix.err`):

| | before (§15) | after |
|---|---|---|
| justified / kept | 142 / 58 | **197 / 3** |
| pass time | 566 s | **91 s** |
| killed during | snapshot 54, egglog 4 | egglog 3 |
| phase share: egglog / serialize / index / search | 29.6 / 69.7 (snapshot) / – / 0.7 % | 89.9 / 6.6 / 1.2 / 2.3 % |
| serialize p50 / p90 / max | 0.48 / 10.9 / 27.5 s | 0.006 / 0.145 / 3.2 s |

The elaborated proof (4 holes left, 172 `poly_simp`, 20 `rare_rewrite`,
12 `evaluate` steps) re-checks `holey`. The three remaining kills are the
egglog phase itself (saturation past 30 s), the same holes checking loses.
Elaboration now costs what checking costs plus a few percent, so the
"proved & kept" column of §15's 2×2 (207 holes, 198 of them 30 s kills)
should mostly vanish on the next cluster run (`small4`, same parameters as
`small3`); what remains for both passes is the egglog-phase losses (memory,
saturation blow-up), which are the egglog 3.0 question.

The `reconstruction` tests pass against the vendored crate. `cargo build`
prints four `hiding a lifetime` warnings from the vendored `gj.rs`; they are
upstream's, untouched.

## 17. Run `small4`: the serializer fix on the cluster (2026-09-15)

Same sample, parameters and runner as `small3` (§14); carcara `e7f7b048`
(vendored egglog 0.4.0 with the one-extractor serializer, §16). Results in
`~/exp/results/egglog-holes/small4`; 16 min wall for the whole run. Checking
is unchanged by the fix and reproduced exactly (5,174 proved, same kept
reasons); elaboration:

| logic | holes | proved | justified small3 → **small4** | kept small3 → small4 | elab max / proof small3 → small4 |
|---|---|---|---|---|---|
| QF_LIA | 347 | 341 | 276 → **341** | 71 → 6 | 600 s → 115 s |
| QF_LRA | 1,343 | 1,199 | 1,133 → **1,190** | 208 → 151 | 600 s → 469 s |
| QF_UF | 4,689 | 3,634 | 3,413 → **3,489** | 146 → 70 | 271 s → 162 s |
| all | 6,379 | 5,174 | 4,822 → **5,020** | 425 → 227 | |

Of the 5,392 holes the passes attempted (two QF_UF proofs still fail upfront,
987 holes, as before): checking proves 96.0%, elaboration now justifies
**93.1%** (was 89.4%); 43/45 proofs `ok`. No proof hit the 600 s budget in
either pass (`skipped=0`, no proof-budget kills).

Per hole (§15's 2×2), 5,389 holes seen by both passes:

| | elaboration justified | elaboration kept |
|---|---|---|
| **checking proved** | 5,162 (was 4,964) | **9** (was 207) |
| checking did not prove | 0 | 218 |

The 9: 6 no certificate, 2 checker-rejected, 1 killed at 30 s (QF_UF, in
the search). The 198 snapshot-time losses are gone. Elaboration now costs
1.15–1.33x checking at the median and ≤1.45x at p90 (was ~10x at p90 in the
arithmetic logics); per finished hole the phases are egglog 74–90%,
serialize 5–11%, search 4–12%, index ≤2.4%.

What remains is the same in both passes and is all the egglog phase:
killed at 30 s 140/144 (chk/elab), memory limit 66/63, egglog could not
prove 12, i.e. saturation that blows up inside one egglog iteration
(QF_LRA: 99 of its 144 egglog-phase kills). That is the egglog 3.0 question
(§9, §15): a scheduler-bounded saturation and smaller e-graphs, not anything
on the reconstruction side.

## 18. The full run: design (2026-09-15)

Every unsat-status benchmark of QF_UF, QF_LIA and QF_LRA — the alethe-core
sets (`benchmark_set_unsat_<LOGIC>`, SMT-LIB 2025 catalog): 4,361 + 4,748 +
703 = **9,812 benchmarks**, copied to `~/exp/egglog-holes/sets/` from the
alethe-core task list. Runner `run-holes.sh` (per-pass parameters), submit
script run `full`:

| stage | limit |
|---|---|
| cvc5 solve + Alethe proof (theory-rewrite granularity) | `--tlimit` 60 s, external kill 75 s |
| counts as unsat only if the proof is complete | exit 0, last step `(cl)`, closing `)` printed (`proof_complete`) |
| checking pass (4 isolated workers) | **600 s for the whole pass**, 30 s and 5 GB per hole |
| elaboration pass (4 isolated workers) | **900 s for the whole pass**, 45 s and 5 GB per hole |
| re-check of the elaborated proof | 180 s |
| SLURM: quad, `-j 2`, 4 cpus, 24,000 MB, wall | 2,000 s |

"For the whole pass" is now literal: `--hole-total-budget` is a deadline
counted from the CLI's start (`elaborate_command` takes the clock before
parsing), so parsing and checking the non-hole steps come out of the same
budget; a 5 s budget on `ring_2exp6` ends the run at 5.02 s wall with
25 proved, 4 kept, 171 skipped. The external `timeout` per pass (660 s /
990 s) is only a safety net.

Expected yield, from the alethe-core cvc5 run (120 s `tlimit`, dsl-rewrite
granularity) restricted to proofs delivered within 60 s: QF_UF 4,245,
QF_LIA 2,526, QF_LRA 499 — about **7,270 proofs** (74%), the rest
sat/unknown/timeouts costing ≤ 75 s each. Proof sizes are much larger than
the small samples' (QF_UF p50 18.6k steps, p90 136k), so the pass budgets
will bind often. Wall-time estimate on 48 slots (24 nodes × 2): 11 h at a
250 s mean per proof task, 26 h at 600 s, hard cap 84 h if every proof task
ran to its 2,000 s limit.

## 19. The full run: results (2026-09-16)

Submitted 2026-09-15 19:52 (cluster time), aggregator stopped 2026-09-16
13:21: about 17.5 h wall, of which the first hours ran on a handful of
slots because the `max2` QOS pool was shared with other jobs; 48 slots for
the rest. Binary: static build of `444621fa` (before the two fixes of
`49c3e518`, see the end of this section). Results in
`~/exp/results/egglog-holes/full/` (`results.json.gz`, 125 MB);
`analyze.py`, `perhole.py` and the task-level script used here are in
`~/exp/egglog-holes/`.

### Yield

| logic | tasks | complete proofs | proofs with an `ok` end-to-end | holes | holes per proof p50 / p90 / max |
|---|---|---|---|---|---|
| QF_UF | 4,361 | 4,326 | 4,126 | 2,421,863 | 553 / 828 / 5,136 |
| QF_LIA | 4,748 | 2,542 | 2,495 | 5,528,247 | 47 / 2,617 / 104,276 |
| QF_LRA | 703 | 537 | 515 | 4,395,839 | 595 / 27,520 / 117,845 |

"Complete" is the `proof_complete` criterion of §18; no cvc5 run that
exited 0 printed a truncated proof. The proofs that did not reach `ok`:
QF_UF 198 upfront failures (all `pivot was not found in clause`, the
QG-classification `iso_*` family: a cvc5 resolution-pivot problem, not
ours), 1 checking-pass timeout, 1 re-check timeout; QF_LIA 5 upfront
failures (2 pivot, 3 unspecific), 29 checking-pass external timeouts
(660 s), 4 elaboration external timeouts (990 s), 9 re-check timeouts
(180 s); QF_LRA 7 upfront (pivot), 15 checking-pass external timeouts.
The external timeouts fire when the pass deadline expires inside a step
the budget cannot interrupt (parsing, or the non-hole checking of a proof
with hundreds of thousands of steps). Five QF_LIA tasks
(`30_Function_Pointer3_vs-O0`, `SpamAssassin-loop-O0`, `cggmp2005_variant-O0`,
`linear-inequality-inv-a-O0`, `prp-3-18`) hit the 24 GB job limit before
printing anything, so they count as cvc5 failures.

### Holes: the budgets bind on the arithmetic logics

| logic | checking: proved / kept / skipped | elaboration: justified / kept / skipped |
|---|---|---|
| QF_UF | 2,266,130 / 31,762 / 15,865 | 2,194,555 / 33,290 / 14,638 |
| QF_LIA | 1,574,011 / 23,028 / 3,921,150 | 1,626,925 / 26,638 / 3,790,597 |
| QF_LRA | 380,758 / 19,837 / 3,685,946 | 434,653 / 23,985 / 3,618,144 |

Skipped means the pass budget (600 s / 900 s) ran out before the hole was
tried. The skipped mass is concentrated in a few hundred giant proofs:

| logic | proofs that hit the checking budget | holes in them | share of the logic's holes in proofs > 10k holes |
|---|---|---|---|
| QF_UF | 10 | 24,480 | 0% |
| QF_LIA | 225 | 4,549,797 | 74% (104 proofs) |
| QF_LRA | 244 | 4,032,981 | 88% (107 proofs) |

Families: QF_LIA `rings` and `rings_preprocessed` alone hold 2.8 M holes,
of which 2.56 M were kept or skipped; QF_LRA `uart`, `sc`, `LassoRanker`
and `UltimateInvariantSynthesis` similar. Whatever the pass budget, a
proof with 100k holes at 0.2 s each needs 5.5 CPU-hours per pass.

Among the holes that were actually attempted the picture is the same as
in the small runs:

| logic | attempted (checking) | success | attempted (elaboration) | success | proofs left hole-free |
|---|---|---|---|---|---|
| QF_UF | 2,297,892 | 98.6% | 2,299,119 | 98.6% | 505 of 4,326 |
| QF_LIA | 1,597,039 | 98.6% | 1,700,833 | 98.4% | 1,258 of 2,542 |
| QF_LRA | 400,595 | 95.0% | 468,397 | 94.9% | 130 of 537 |

Per-hole time (holes the pass finished): checking p50 0.22 s (QF_LIA),
0.23 s (QF_LRA), 0.09 s (QF_UF); elaboration 1.2× to 1.33× checking at
the median. Phase shares of elaboration time: egglog 71% (QF_UF) to 85%
(QF_LIA), serialize 5.5% to 14% (QF_UF), search 9% to 11%, index and
emit under 3%. The serializer fix (§16) holds: only 255 holes were killed
in the serialize phase across the run, 32k in the egglog phase.

### Why holes are kept (per pass, all logics)

| reason | checking | elaboration |
|---|---|---|
| killed at the per-hole limit (30 s / 45 s) | 40,932 | 30,568 |
| killed at the 5 GB per-hole memory limit | 24,391 | 39,805 |
| egglog could not prove (saturated, goal not reached) | 6,667 | 7,329 |
| killed by the pass budget while running | 1,905 | 1,791 |
| no certificate found in the snapshot | 2 | 2,960 |
| independent checker rejected the reconstruction | – | 544 |
| worker errors (below) | 63 | 120 |

So 96% of the kept holes die inside egglog's saturation, by time or by
memory, exactly the loss profile of §17 and EGGLOG-3-ROUTE.md; the
reconstruction side (no certificate + checker rejected + decode) is 3.5k
of 83k in the elaboration pass. Holes proved by checking but kept by
elaboration: 3,919 of 4.14 M proved (0.09%), mostly `no certificate`
(2,711) and `checker rejected` (525).

Worker errors, all reproducible offline:

* 120 `identifier 'x' is not defined`: holes under `bind` anchors that
  bind variables. In these quantifier-free logics that comes from
  parameterized `define-fun`: cvc5 keeps `f` as
  `(= f (lambda ((x Int)) body))` and rewrites the body under an anchor
  with `:args ((x Int) (:= (x Int) x))`. Fixed in `49c3e518` (the hole's
  problem text declares the anchor-bound variables). Affected: 13 QF_LIA
  `2019-ezsmt/incrementalScheduling` benchmarks; parameterized
  `define-fun` exists in 23 QF_LIA and 19 QF_LRA benchmarks of the sets,
  none in QF_UF. Minimal reproducer: `define-fun-anchor.smt2` +
  `.smt2.alethe` in the repo root (untracked), fixture
  `tests/rare/elaborate/anchor-vars.smt2`.
* The same `define-fun` applications also produce one beta-reduction hole
  each, `(= ((lambda ((x Int)) body) a) body[a/x])`. The engine has no
  beta reduction: `Term::App` names the egglog function after the head's
  printed text, so the lambda-headed application is an opaque symbol and
  the goal is unreachable. With the goal unreachable the rewrite ruleset
  does not saturate: the seed rules that build `(= t s)` for every pair
  of available terms feed `eq-symm`/`arith-eq-elim` → `and` of `>=`/`<=`
  → `arith-elim-leq`/`arith-leq-norm`/`arith-geq-norm1`, whose outputs
  become available and pair up again; quadratic growth per iteration
  (160 → 4,421 eq-elim matches in two iterations) and a memory kill after
  ~10 s. Open. Cheapest fix: refuse lambda-headed goals up front; right
  fix: substitute the parameters before encoding.
* 29 panics at `search.rs:1087` (`a reconstructed certificate must pass
  the independent checker`): now a warning that keeps the hole
  (`49c3e518`).
* 29 `a certificate term failed to decode`, 6 `Illegal merge attempted
  for function to_formula` (QF_UF), 59 `e-graph too large to capture`
  (QF_LIA): open.

### What a rerun should change

1. The static binary must be rebuilt from `49c3e518` or later.
2. The pass budgets are the wrong knob for the arithmetic logics: 3.9 M of
   5.5 M QF_LIA holes and 3.7 M of 4.4 M QF_LRA holes were never tried.
   Either accept that (report per-hole rates over attempted holes, which is
   what the small runs measured) or cap the proof size and give the giant
   proofs their own run with a budget proportional to the hole count.
3. The re-check limit (180 s) is too short for the elaborated giant
   proofs (10 timeouts); the external pass timeouts (49) mean the
   `--hole-total-budget` deadline needs to be observed inside the non-hole
   checking too.
4. The 24 GB job limit was hit by 5 tasks before cvc5 finished; either
   raise it or accept those as cvc5 failures.

### 19.1 Two corrections found while writing the report (2026-09-16)

**"Justified" overstates.** `QF_UF_h_b05_ab_reg_max` (2018-Goel-hwbench):
25 holes, summary says 22 justified, 3 kept, but the elaborated proof has
4 `hole` steps. Hole t133, `(= (and X true) X)`, is emitted as a subproof
whose only step is `:rule hole :args ("TRUST_THEORY_REWRITE" "gen-14")`:
the certificate used one of the unconditional egglog rewrites of the
generated program that is not a named RARE rule (the n-ary `and`/`or`
normalisations; `rules_from_generated_program` names them `gen-N`), and
the emitter has no Alethe step for it, so it emits a hole. Counting the
hole steps left in the emitted proofs minus kept minus skipped gives the
residual: QF_UF 71,009 (3.1% of the closed holes), QF_LIA 1,992, QF_LRA
4,457. The honest elaboration rate over attempted holes is therefore
95.5% / 98.3% / 93.9% (checking: 98.6 / 98.6 / 95.0). The report and
`make-report.py` count these as "closed with a gen hole".

**Time/memory kills are largely unreachable goals.** The three kept holes
of the same proof are `(= (or X true) true)`, `(= (and true true true X) X)`
and `(= (= false X) (not X))`; two died at the memory limit. Both
identities, run as isolated holes, blow 3 GB in ~10 s. `holes.rare` has 27
`bool-*` rules and no `bool-or-true`, `bool-and-true` or flattening, so
the goal is unreachable, and an unreachable goal triggers the quadratic
pair-equality growth described for the beta-reduction holes. So the 70k
kills per pass are not evidence of hard holes; a to-be-measured share are
rule-coverage gaps. Two cheap checks: add the missing Boolean rules and
re-run the kept holes of a sample; make an unreachable goal fail fast
(bound the pair seeding or check the goal before the open ruleset).

Report: `~/exp/egglog-holes/report/report.pdf` (`make-report.py` renders
every table and plot from `results.json.gz`).

## 20. Batching hole justifications (2026-09-16)

Question: does batching holes the way the skeletons paper batches theory
lemmas (one query for a disjunction of k lemmas, batch size 50) help the
hole engine attempt more holes within a budget?  Two designs were built
behind `--hole-batch N` (checking pass only), both grouping holes that
share their assumptions into batches of N in proof order, one child per
batch, and retrying a batch's holes one by one when the batch dies:

* **Shared e-graph** (commit `c91fd8ec`): the batch's goals go into one
  e-graph, saturated once, every open goal checked after each round.
  Budget `--hole-batch-timeout`, default 4× the per-hole one.
* **Sequential** (`--hole-batch-sequential`, commits `b05cea24`,
  `2d8e846a`): the child prepares the rule database once and checks its
  holes one at a time, each in its own e-graph, printing each verdict as
  it is reached; a watchdog kills a hole at the per-hole budget, and a
  killed child loses only the holes it had not reached.

Sample: 10 arithmetic proofs of the full run with 1k–4.5k holes that the
run had fully attempted (7 QF_LIA: c_inference, FISCHER9, ring_2exp10,
cut_lemma_01_008, SMPT RwMutex RF-09, MULTIPLIER_3, bofill ex4880; 3
QF_LRA: vpm2-0, clocksynchro_3clocks, tgc_io-safe-6), re-proved locally
(cvc5 1.3.4.dev, same flags), 29,479 holes.  Local machine, 8 cores, two
runs at a time, each with 4 workers, 30 s and 3 GB per hole.  Runner and
logs: `~/exp/egglog-holes/batch/` (`run-batch-exp.sh`, `run-seq-exp.sh`,
`summarize.py`, `results/`).

### The fixed cost of a hole

A child on a trivial goal (`a = a`) takes 0.18 s; with an empty RARE file
0.01 s.  So the 163-rule database (its egglog program, and the per-rule
overhead of each saturation round even with nothing to match) is most of
a median hole (0.17–0.25 s).  That is the amortizable part; the rest is
the goal's own saturation.

### Shared e-graph: a loss at every size

Three-proof subset with every size run (c_inference, FISCHER9, vpm2;
7,750 holes; verdicts identical in all configurations, 7,682 proved):

| batch | wall s | failed batches | holes in them |
|---|---|---|---|
| 1 (per hole) | 571 | 0 | 0 |
| 10 | 1,351 | 59 of 777 | 586 |
| 50 | 1,403 | 58 of 156 | 2,850 |
| 100 | 1,594 | 40 of 79 | 3,850 |
| 500 | 1,113 | 16 of 17 | 7,250 |
| 1000 | 896 | 10 of 10 | 7,750 |

Two effects.  Batches die, mostly at the 3 GB limit, after 60–70 s, and
their holes are redone one by one.  And batches that succeed are slower
than their holes alone: on RwMutex the successful batches of 10 took 21 s
at the median where the ten holes take ~9 s (RwMutex and bofill at size
10 were stopped after 30 min with 51 of 216 and 39 of 236 batches failed;
their baselines are 8 and 7 min).  The goals interact: every goal's
subterms are available to every rule, and the pair-equality seed rules
(§19.1) grow quadratically in the available terms, so the batch's
saturation costs more than the sum of its holes and blows up where none
of them would.  At 500 and 1000 every batch dies within a minute or two
and the run is the baseline plus that.  Batching holes in one e-graph is
therefore out, at least while the seeding is what it is.

### Sequential batches: the amortizable cost is small

Sequential batches of 10 on all ten proofs (`results/*.b10s.err`, final
binary with the watchdog and the death attribution):

| proof | holes | per hole (s) | sequential 10 (s) |
|---|---|---|---|
| c_inference | 2,143 | 131 | 114 |
| RwMutex RF-09 | 4,343 | 471 | 449 |
| bofill ex4880 | 2,517 | 437 | 435 |
| MULTIPLIER_3 | 3,374 | 460 | 486 |
| FISCHER9 | 2,116 | 193 | 200 |
| cut_lemma_01_008 | 1,944 | 704 | 722 |
| ring_2exp10 | 3,818 | 269 | 230 |
| vpm2-0 | 3,491 | 246 | 280 |
| clocksynchro_3clocks | 1,663 | 480 | 551 |

Gains of 5–16% where the holes are cheap (c_inference, ring), nothing
outside this machine's ±10% noise elsewhere.  A micro-test says why: 20
copies of `(< a i) = (not (>= a i))` cost 1.4 s sequentially against
0.21 s each alone, but 20 copies of an arithmetic normalization goal cost
10.0 s against 0.51 s each: nothing amortized.  A trivial goal's program
has 397 rules and 3 schedule runs; an arithmetic goal's has 681 rules, 183
functions and 63 schedule runs, 58 of them iterations of the polynomial
normalizer, all declared and run per goal (`declare_goal_eliminations`,
`declare_opaque_arith_poly_rules`, the `arith_poly` fallbacks).  The
sequential mode removes the 0.14 s database cost and nothing else.

### Overlap grouping (commit `90334e2e`)

`--hole-batch-by-overlap [--hole-batch-terms CAP]`: a hole joins the open
batch of its context sharing the most compound subterms (16 open batches
per context), closed at the hole count or the distinct-subterm cap.
Measured potential first (`overlap.py` over the proof texts): distinct
subterms over summed subterm occurrences is 0.10–0.33 per proof, but
0.71–0.82 in proof-order batches of 10, and adjacent holes share nothing
at the median on three of five proofs.  Results on the subset (7,750
holes, `results-overlap/`):

| configuration | wall s | failed batches | sharing achieved |
|---|---|---|---|
| per hole | 571 | 0 | – |
| proof order, 10 | 1,351 | 59 | 0.74–0.82 |
| overlap, up to 10 | 992 | 42 | 0.59–0.77 |
| overlap, up to 50 / 100 / 500 / 1000 | 1,237 / 1,246 / 1,086 / 1,126 | 40–42 | 0.39–0.75 |
| overlap, cap 30 / 60 / 120 subterms | 928 / 1,291 / 1,071 | 54 / 54 / 42 | 0.74–0.80 / 0.58–0.76 / 0.40–0.75 |

Only c_inference gains (109 s at up to 10, 92 s at cap 30, against 131 s);
FISCHER9 (56 hopeless holes) and vpm2 lose everywhere.  The greedy pass
makes batches of 3–4 holes and 10–17 distinct subterms and reaches
sharing 0.4–0.8, far from the proof's 0.1–0.3; and a batch inherits its
worst hole: every batch with one of FISCHER9's hopeless holes dies at the
memory limit after 20–30 s and is retried.

### Conclusion

No batching for the next run.  The costs a batch could amortize are
small (the database) or not shared (the per-goal arithmetic machinery),
and the shared e-graph turns every unreachable goal into a dead batch.
The same losses are attacked directly by making an unreachable goal fail
fast (§19.1) and by adding the missing Boolean rules; after that, overlap
batching may be worth re-measuring as a pure hash-consing gain.

### Fail-fast attempt 1: seed conditional rules' premises from the goal only (commit `29e4f7f3`)

`--rare-seed-from-goal` (`--seed-from-goal` for the hole worker): the
premise instances of conditional RARE rules (`create_avaliable_premise`,
e.g. `((Avaliable i1) (Avaliable j1)) → (Mk (@= i1 j1))` for
`array-read-over-write2`'s premise) range over an `Origin` relation that
holds the goal's sides, the proof premises and their subterms, asserted
per goal and never propagated, instead of over every available term.
Check-only pass on the ten sample proofs (`scratchpad batch/seed/`):

| proof | per hole (s) | seed-from-goal (s) | verdicts |
|---|---|---|---|
| c_inference | 131 | 101 | same |
| RwMutex RF-09 | 471 | 459 | same |
| bofill ex4880 | 437 | 377 | same |
| MULTIPLIER_3 | 460 | 518 | same |
| FISCHER9 | 193 | 125 | same |
| cut_lemma_01_008 | 704 | 712 | same |
| ring_2exp10 | 269 | 299 | same |
| vpm2-0 | 246 | 240 | same |
| clocksynchro_3clocks | 480 | 426 | 6 fewer proved |
| tgc_io-safe-6 | 373 | 307 | 3 fewer proved |

5% less time overall, up to 35% on the proofs with many equalities in
their goals, but 9 provable holes lost: linear normalizations such as
`(<= t 0) = (>= (- t) 0)`, proved in 0.6 s by the baseline through a
conditional rule whose premise is instantiated over a term the
polynomial normalizer produces; with the seeds restricted that path is
cut, the goal is unreachable, and it then dies at the memory limit.  Not
verdict-preserving, so not for the next run as it stands.

**The blow-up's real driver is sort-blind rule application.**  With the
seeds bounded, the debug trace of `(or x true) = true` still shows
`arith-eq-elim` firing 12k times on a goal whose only equality is over an
uninterpreted sort, `bool-not-eq-elim` turning `(not (= x y))` into new
equalities `(= x (not y))`, and the arithmetic normalizers rewriting the
resulting nonsense `>=` terms, round after round.  The encoding has one
untyped `Term` sort; the Int/Real/Bool parameter sorts of the RARE rules
are never checked.  With the arith/bv/str/array/set/seq rules removed
from the file (68 rules left) both Boolean goals fail in 0.19 s.  The
fail-fast to build is therefore **sort guards**: a sort relation on
classes, seeded from Carcara's sorts for the goal's subterms and
propagated by operator heads and declared function result sorts
(`application_result_sort`), with a guard premise on every rule parameter
declared Int, Real or Bool (`TypeParameter::sort`).  About a day; it also
removes the ill-sorted terms from every reachable goal's saturation.

The 8 GB shared-batch run was stopped after its first result
(c_inference, batches of 10, 300 s budget: 146 s against 131 s) with
FISCHER9 at 146 good and 36 dead batches; more memory only lets a doomed
batch take longer to die.

### What the ACI normalization covers, and the Boolean gaps (2026-09-17)

Isolated holes, `holes.rare` (163 rules) against the same file without the
arith/bv/str/array/set/seq rules (68 rules):

| identity | full file | without arith |
|---|---|---|
| nested `and`/`or` flattening (3 forms) | proved 0.06 s | proved 0.03 s |
| `(or p p) = p`, `(or p q p) = (or p q)`, `(and p) = p` | proved | proved |
| `(and p true) = p` | proved | proved |
| `(= false p) = (not p)`, `(= p true) = p`, `(ite true p q) = p`, `(=> p q) = (or (not p) q)` | proved | proved |
| `(and true true true p) = p` | fails 6.3 s | fails 0.10 s |
| `(or p true) = true` | fails 6.6 s | fails 0.08 s |
| `(and p false) = false` | fails 0.5 s | fails 0.07 s |
| `(not (and p q)) = (or (not p) (not q))` | fails 1.9 s | fails 0.17 s |

The ACI rules (`aci_norm.rs`) handle flattening, duplicates, singletons
and the two-element identity form `(op x identity)`; in the `Assoc` set
representation the identity stays an element, so `(and true true true p)`
stops at `{true, p}`.  Missing: list-form identity elimination
(`bool-and-true`, `bool-or-false`), absorbing elements (`bool-or-true`,
`bool-and-false`) and De Morgan (`bool-not-and`, `bool-not-or`), all in
cvc5's `rewrites.rare` and absent from `holes.rare`.  The b05 proof's
kept holes were the first two: coverage gaps, not engine limits.  Fix:
add the six rules to the file (list-form rules already work, cf.
`bool-xor-*` and the bv rules) or extend the ACI identity rule to the set
form plus an absorbing-element rule.  The timing column repeats the
sort-blindness point: the same unprovable goal fails in 0.1 s without the
arithmetic rules and takes 6 s to die with them.

## 21. ACI identities, sort guards, growth bound (2026-09-17)

Three engine changes from the full run's loss analysis (§19.1, §20),
measured with the check-only pass on the ten sample proofs of §20
(baseline: per hole, 4 workers, 30 s / 3 GB per hole, `results/*.b1.err`;
today's passes ran two at a time with one job each under heavy load from
another worktree's experiment, so only verdicts are compared).

### ACI identity and absorbing rules (commit `1c280cd5`)

The ACI normalization handled flattening, duplicates, singletons and the
two-element identity form only; three `list-ruleset` rules on the set form
(`(op (Assoc s))`, which the conversion unions into the formula's class
without `Mk`) now remove an identity element from the set, collapse the
empty set to the identity, and collapse a set holding the absorbing
element to it.  `(and true true true p) = p`, `(or p true) = true` and
`(and p false) = false` are proved in ~0.1 s where they died at the memory
limit.  The reconstruction has no certificate kind for the set-form rules,
so in the elaboration pass these holes are proved by egglog but come out
as no-certificate holes, like the other ACI steps (`gen` holes, §19.1).
De Morgan stays out: cvc5's `bool-and/or-de-morgan` are `define-rule*`
fixed-point rules with a context hole, which Carcara's RARE format does
not have, and no hole of that shape occurs in the 29k holes of the sample.

### Sort guards (commit `58bc6945`, `--rare-sort-guards`)

The blow-up driver of §19.1/§20 was sort-blind rule application (one
untyped `Term` sort).  Relations `SortInt`/`SortReal`/`SortBool` on
classes, seeded from the goal's and the premises' subterms (sort computed
structurally from the term: constants, variables' declared sorts, the
operator table, declared function result sorts), propagated by rules per
declared function (Bool for the logical and comparison operators, Real for
`/` and `to_real`, Int for `to_int`/`div`/`mod`, the first argument's sort
for `+ - * abs`, the then-branch's for `ite`, the declared result sort for
uninterpreted functions, and the constants the rewrites produce), and a
guard premise on every non-list Int/Real/Bool rule parameter the LHS
binds.  Named rewrites keep their name with the guards as conditions; the
reconstruction strips the guard facts when reading the rules back, so
elaboration and re-check work unchanged.  Micro-tests: the unprovable De
Morgan goal fails in 1.4 s instead of 6.2 s (still not milliseconds: the
Boolean rules keep growing the e-graph within their sort), the arithmetic
micro-goal drops from 0.51 s to 0.28 s.

### Verdicts on the sample

| proof | baseline proved / kept | ACI only | ACI + guards |
|---|---|---|---|
| c_inference | 2,143 / 0 | 2,143 / 0 | 2,143 / 0 |
| RwMutex RF-09 | 4,339 / 4 | 4,339 / 4 | 4,339 / 4 |
| bofill ex4880 | 2,497 / 20 | 2,513 / 4 | 2,513 / 4 |
| MULTIPLIER_3 | 3,374 / 0 | 3,366 / 8 (load) | 3,370 / 4 (load) |
| FISCHER9 | 2,060 / 56 | 2,116 / 0 | 2,116 / 0 |
| cut_lemma_01_008 | 1,881 / 63 | 1,879 / 65 (load) | 1,879 / 65 (load) |
| ring_2exp10 | 3,818 / 0 | 3,818 / 0 | 3,818 / 0 |
| vpm2-0 | 3,479 / 12 | 3,479 / 12 | 3,479 / 12 |
| clocksynchro_3clocks | 1,615 / 48 | 1,622 / 41 | 1,658 / 5 |
| tgc_io-safe-6 | 778 / 64 | 807 / 35 | 807 / 35 |
| total kept | 267 | 169 | 129 |

"(load)" marks losses that are holes at 16–29 s in the baseline killed at
30 s under the day's doubled load, not verdict changes.  The ACI rules
recover FISCHER9's 56, bofill's 16 and tgc's 29; the guards add
clocksynchro's 36 (and 4 on MULTIPLIER).  No hole the baseline proved
comfortably was lost.

### Normalizer in the baseline: measured and rejected

Preparing the polynomial normalizer's rules (goal-independent, in their
own rulesets) once per child instead of per goal was implemented and
measured on the micro-goals: non-arithmetic holes went from 0.09–0.13 s to
0.19–0.25 s (every hole clones a bigger baseline e-graph) and the
arithmetic hole did not change (0.5–0.7 s either way: its cost is the
normalizer's ~60 iterations, not the declaration).  Reverted; the note
stays in `prepare_database`.

### Growth caps and the soft memory cap (commits `1aac6c13`, `04f36c2b`)

Calibration (in-process pass logging each goal's tuples after loading and
at the end, by class): a goal's e-graph holds 17–120 tuples after its
program is loaded; provable goals without the normalizer end below 400
tuples on cut_lemma and tgc but at 25k–45k on tgc's large Boolean
formulas; provable goals with the normalizer end at a median of ~500,
p99 208k, max 348k (cut_lemma).  So a factor on the initial size means
nothing and the caps are absolute, per class: `--rare-growth-cap-arith`
(1,000,000 used) and `--rare-growth-cap-plain` (200,000; a first try at
20,000 lost five provable tgc goals), checked after every statement and
saturation step.  `--rare-memory-soft-cap MB` fails a goal when the
worker's resident set passes the cap between statements; at 1,000 MB it
never fired: the memory deaths are single 4 GB allocations (a table or
container doubling) inside one statement, at a modest tuple count, so
neither cap sees them coming.

Final configuration (guards + ACI rules + caps 1M/200k + soft cap 1 GB),
check-only, isolated, 4 workers, 30 s / 3 GB per hole, machine lightly
loaded, against the unloaded baseline:

| proof | baseline proved / kept, wall s | final proved / kept, wall s |
|---|---|---|
| cut_lemma_01_008 | 1,881 / 63, 704 | 1,881 / 63, 500 |
| tgc_io-safe-6 | 778 / 64, 373 | 807 / 35, 162 |
| clocksynchro_3clocks | 1,615 / 48, 480 | 1,659 / 4, 171 |
| FISCHER9 | 2,060 / 56, 193 | 2,116 / 0, 81 |
| MULTIPLIER_3 | 3,374 / 0, 460 | 3,374 / 0, 304 |
| vpm2-0 | 3,479 / 12, 246 | 3,479 / 12, 205 |
| total | 243 kept, 2,456 s | 114 kept, 1,423 s |

Verdicts: 129 holes recovered, none lost.  Time: 42% less on these six,
from three sources: the guards (fewer rules fire per round), the
identities (holes that ran to the kill now close in 0.1 s), and the
tuple cap (on cut_lemma 18 of the 63 hopeless holes stop at the cap
instead of 30 s; 28 still run to 30 s in small but slow e-graphs, 17
still die at the memory limit).  What remains for the hopeless holes is
therefore a bound on rule work per round rather than on size, and a
memory check inside a statement (an allocator hook or egglog 3.0's
scheduler), not more caps of this kind.

### Ground `and`/`or` calls as unions (commit `fc3e2100`, from the egglog-3 branch)

`aci_call_rules` emitted, for every concrete `and`/`or` call of the step,
a rewrite whose left-hand side is the ground call itself: matched at most
once, searched on every iteration of the default ruleset, one rule per
call.  The egglog-3 work found it (there the search is a join and took
21 s per iteration on one hole; `wt-egglog/EGGLOG-ACI-GROUND-CALLS.md`)
and replaced it with a `(union lhs rhs)` at load time; on this branch the
groundness test is `Literal(_) => false` (the globals are unprefixed and
never occur inside a step's call).  Measured on four QF_UF proofs of the
`chk1200` run, same settings (8 workers, 1200 s, 60 s and 8 GB per hole,
guards and caps), against the run's own numbers:

| proof | chk1200 kept, pass s | union kept, pass s |
|---|---|---|
| gensys_icl072 | 19, 156 | 18, 34 |
| iso_icl054 | 18, 160 | 9, 27 |
| iso_icl942 | 14, 142 | 4, 10 |
| iso_icl946 | 13, 183 | 3, 11 |

Five to fifteen times faster passes on QG-classification (long `and`/`or`
chains), half to a quarter of the kept holes.  `chk1200` itself ran the
binary without it.

## 22. Fewer holes to check: hoist and prune, the verdict memo, reuse (2026-09-18)

`chk1200` (§21) was cancelled after QF_UF and half of QF_LIA.  Its QF_UF
numbers, final: 2,297,441 proved, 15,395 kept (31,762 in the full run), 921
skipped (15,865), 4,127 of 4,326 complete proofs fully checked.  QF_LIA at the
cancellation (2,162 complete proofs): 99.0% of the attempted holes proved but
349k skipped, 53 proofs hit the 1200 s budget and one job the 60 GB node.

The budget losses are a count problem, not an engine problem: cvc5's Alethe
printer expands the proof DAG once per subproof, so the same rewrite hole
appears many times.  On ten sample proofs 43–75% of the hole conclusions
repeat an earlier one.  Three measures, in the order they apply:

### Hoist and prune (commit `6364ff71`, from the coreAlethe work)

`--pipeline hoist prune`: every closed derivation that repeats (same digest,
holes included when `share_holes`, which the CLI always sets) is lifted once
to depth 0 and its copies become references; `prune` then drops what nothing
uses.  The context stack learned which anchors bind nothing, so derivations
under such anchors count as closed.  Holes on the ten samples:

| proof | holes | hoisted | pass s |
|---|---|---|---|
| MULTIPLIER_3 | 4,388 | 1,108 | 2 |
| RF-09 | 4,389 | 2,716 | 3 |
| c_inference | 2,143 | 822 | 1 |
| bofill | 2,715 | 1,453 | 2 |
| cut_lemma | 2,660 | 1,512 | 2 |
| FISCHER9 | 2,246 | 1,819 | 12 |
| ring | 4,457 | 1,027 | 3 |
| clock_synchro | 1,741 | 1,198 | 2 |
| vpm2 | 3,747 | 2,093 | 3 |

The hoisted proofs re-check with the same verdicts.  The runner's pass 0
(`run-holes.sh`, `HOIST_TIMEOUT` 300 s) writes the hoisted proof; the
checking passes see only that.

### Verdict memo (same commit)

In check-only mode `reconstruct_holes_in_parallel` keys each hole by
`(conclusion, sorted assumptions)` pointers; only representatives go to the
workers, duplicates copy the verdict (`hole memo: X of Y holes repeat an
earlier goal; Z distinct goals to check`).  It catches what hoisting cannot
merge (holes under differing anchors, holes in proofs that hoisting failed
on): MULTIPLIER_3 891 distinct goals among 3,374 holes, 173 s with 8 workers;
c_inference 822 of 2,143, 53 s (131 s baseline, 4 workers); vpm2 1,838 of
3,491, 127 s.

### Proved equalities as premises (commit `27e4b56c`, `--hole-reuse-proved`)

A later hole whose side terms occur in an equality already proved gets that
equality as an extra premise (table keyed by side pointer, at most 64 per
hole, only equalities whose assumptions are a subset of the hole's).  On
FISCHER9 hoisted: 17,391 equalities handed out for 1,697 holes, same
verdicts, 48 s against 40 s plain.  Whether it pays on other proofs is what
`chk1200h` measures.

### Run `chk1200h` (submitted 2026-09-18 01:15, arrays 29105879/80/81)

As `chk1200` (quad, one job per node, 8 workers, 60 s and 8 GB per hole,
guards, caps 3M/500k, binary `27e4b56c` with the ground-call union) but per
benchmark: cvc5 once, hoist and prune once, then the checking pass twice on
the hoisted proof, plain (`chk_*`, `ok`) and with `--hole-reuse-proved`
(`chkr_*`, `chkr_reused`, `okr`), 1200 s budget each; wall limit 3100 s.
Results `exp/results/egglog-holes/chk1200h`; `analyze.py` prints both passes
side by side.

### Distinct solver aborts (found in chk1200h2, fixed in the next commit after bb384366)

Six kept holes in QF_UF's `chk1200h2` results read "worker exited with status
1: ... Illegal merge attempted for function to_formula".  Reproduced with a
one-hole proof of `(= (distinct v n3 v) false)`; the same three proofs
(blocks.3, firewire_tree.1/.3) lost the hole in the full run and in
`chk1200`.  Cause: the base program's list re-association rewrites
(`(Args (Args t1 t2) t3)` <-> `(Args t1 (Args t2 t3))`, the encoding behind
RARE's `:list` variables) put nodes whose head is an improper sublist into
every argument list's class after the first `(run)`; in round 2 the
distinct-elimination rules bound such a sublist as an element, set a second
value for the same `to_formula` key, and egglog aborted -- every distinct
with three or more elements not proved in round 1, provable or not.  Fix:
element positions matched as `(Mk _)`.  The same investigation showed that
`(distinct a b a) = false` was unprovable even without the abort: the
compiled `distinct-false` rule needs non-empty segments before, between and
after the repeated element (segment variables cannot be empty), and the
`(and ...)` the solver builds is a list that never reaches the ACI set form
(the conversion exists only for the step's own calls).  The solver now marks
its conjunct lists and unions the conjunction with false when a list holds
false; restricted to those lists, the cost elsewhere is within noise
(gensys_icl072 hoisted, 1,395 holes: 26.7-28.4 s old vs 28.3-29.1 s new;
clocksynchro, 1,120 holes: 66.1-66.3 s vs 67.0-67.4 s).  Two engine tests
cover both cases.

### Run `chk1200h2`: results (2026-09-19)

Resubmission of `chk1200h` with the runner paging the binaries in before
timing (the first task on each node had paid ~0.2 s in its first checking
pass).  9,812 tasks, 344 node-hours.  Plain checking pass on the hoisted
proofs, against the full run (600 s budget, 30 s and 5 GB per hole, original
proofs) and `chk1200` (QF_UF only):

| | QF_UF | QF_LIA | QF_LRA |
|---|---|---|---|
| complete proofs | 4,325 | 2,543 | 537 |
| holes before / after hoisting | 2,420,688 / 2,348,353 (−3%) | 5,526,018 / 1,827,863 (−67%) | 4,395,839 / 1,691,984 (−62%) |
| proved | 2,233,232 | 1,274,199 | 702,767 |
| kept (full run) | 7,015 (31,762; chk1200 15,395) | 26,073 | 27,003 |
| skipped at the budget (full run) | 0 (15,865) | 523,268 (3.9 M) | 652,916 (3.7 M) |
| proved, % of attempted | 99.7 | 98.0 | 96.3 |
| proved, % of all holes | 95.1 | 69.7 (full ≈ 29) | 41.5 (full ≈ 15) |
| hole-free proofs (full run) | 1,599 = 37.0% (634 = 14.7%) | 1,698 = 66.8% (1,377 = 54.2%) | 236 = 43.9% (166 = 30.9%) |
| proofs hitting the budget | 0 | 100 | 128 |
| pass p50 / p90 / max, s | 10.9 / 19.7 / 852 | 2.1 / 228 / 1,303 | 144 / 1,208 / 1,300 |

Proofs whose upfront check fails (cvc5 proof defects: 198 QF_UF, 24 QF_LIA,
12 QF_LRA) also fail the hoist pass and are counted neither way, as before.
Kept-hole reasons, plain pass: QF_LIA 33,873 at the 60 s hole limit, 14,186
at the 8 GB limit, 4,045 unprovable, 2,041 at the pass budget; QF_LRA 26,107 /
22,932 / 1,290 / 2,392; QF_UF 810 / 446 / 12,681 / 32, plus the six distinct
aborts fixed above.  The remaining losses are the budget (the cut_lemma and
uart families: 23k–32k holes per proof, 3k–7k proved in 1,200 s) and the
arithmetic holes that exhaust 60 s or 8 GB.

Reuse of proved equalities as premises (`--hole-reuse-proved`, second pass on
the same hoisted proofs): a loss on every set -- QF_UF −4,559 holes, slower on
3,912 of 4,127 proofs (65,912 s vs 58,186 s); QF_LIA −35,864 holes, slower on
1,756 of 2,537; QF_LRA −45,753, slower on 397 of 530.  Why: a premise `l = r`
is a `(union l r)` plus `Avaliable` facts for every subterm of both sides, so
the normalizer and every other rule still fire on `l` (an e-graph union adds,
it never replaces) and additionally on `r`; the pair-equality seeding grows
with the square of the available terms; and the selection (any proved
equality with a side occurring in the goal, up to 64 per hole) is loose.
peg_solitaire.5: 46,042 equalities for 2,256 holes, 124 s -> 1,063 s, kept 11
-> 114.  The variant that would give the intended effect substitutes each
proved `l` by its normal form `r` in the goal before translation, so `l`
never enters the e-graph; not implemented.

## 23. Reuse across holes: substitution, and Carcara's normalizers as a preprocessor (2026-09-19)

### Why premise reuse lost

`chk1200h2` measured `--hole-reuse-proved` as a loss on every set.  A premise
`l = r` becomes `(union l r)` plus `Avaliable` facts for every subterm of
both sides; an e-graph union adds and never replaces, so the normalizer and
every other rule still fire on `l`, and additionally on `r`; the
pair-equality seeding grows with the square of the available terms; and the
selection (any proved equality with a side occurring in the goal, up to 64
per hole) is loose.  peg_solitaire.5: 46,042 equalities for 2,256 holes,
124 s -> 1,063 s.

### Substitution-based reuse (`--hole-reuse-subst`, check-only)

The variant that replaces instead of adding.  Every hole's compound subterms
are hashed structurally (`structural_hash`, the same in every process and
pool); the owner of a subterm is the smallest hole holding it and a hole
depends on the owners of its subterms; owners run first (smallest first),
the other holes keep the proof's order, and a worker takes the first hole
whose owners are done (window 512), else the first hole left.  After a
proved owner the child snapshots its e-graph, aligns the goal's compound
subterms with the encoded goal tree, and reports `nf <hash> <term>` for each
subterm whose class holds a strictly smaller decodable term (premise-only
variables rejected).  A later hole receives up to 64 such normal forms as
`(step nfK (cl (= t t)) :rule nf-hint :args (H))` lines in its input and the
child substitutes them into the goal (outermost first) before translation.
Interleaved measurement (plain / subst, two rounds each, 8 workers, 60 s and
8 GB per hole, hoisted proofs; the CPU throttles under sustained load, so
only back-to-back pairs compare):

| proof | plain s | subst s | substitutions |
|---|---|---|---|
| vpm2 | 114 / 110 | 100 / 105 | 2,179 |
| ring | 57 / 59 | 61 / 61 | 894 |
| c_inference | 39 / 39 | 41 / 41 | 197 |
| FISCHER9 (hole pass) | 37 / 38 | 40 / 41 | 63 |
| clock_synchro | 68 / 64 | 73 / 72 | 350 |
| MULTIPLIER_3 | 166 / 166 | 188 / 183 | 1,202 |

Verdicts unchanged (one more kept hole on cut_lemma in one run).  Gains only
where genuine normalization is shared (vpm2, −8%); 5–12% losses elsewhere:
after hoisting the holes share few subterms, the shared ones are constant
folds or sums already in cvc5's normal form, and the export snapshots cost
more than the substitutions save.  A double-negation hole over an
arithmetic atom takes 0.15 s in-process (0.11 s over a Boolean atom) while
RF-09 costs 0.47 s per hole in the isolated parallel run: the per-child
fixed cost (spawn, RARE load, prelude parse) dominates the cheap holes.  Kept
as an option, off by default.

### Carcara's normalizers first (`--hole-prenormalize`, check-only)

The trailing arguments of a hole are cvc5's (theory, method) ids: `3 7` and
`3 6` are the arithmetic rewriter's post- and pre-rewrites, `1 6`/`1 7` the
Boolean rewriter's, `2 7` UF's.  In the nine arithmetic samples 60–95% of the
holes are arithmetic rewrites, i.e. the rewriter's normal forms: polynomial
normalization, constant evaluation, canonical linear relations.  Carcara has
the decision procedures (`poly_simp`, `evaluate`, `aci_simp`) but not as
term normalizers, so `src/elaborator/prenorm.rs` is a bottom-up normalizer
in the proof's pool: constants evaluated; `not-not`; `and`/`or` flattened,
identity and absorbing elements and complementary pairs handled, arguments
sorted by pointer and deduplicated; `=>` to `or`; `ite` on constants and on
equal branches; `(= p true)`/`(= p false)`; `(= x x)`; symmetric `=` in one
order; `distinct` expanded to the pairwise disequalities (so a repeated
element gives false); `+ - * / to_real` to a canonical polynomial term
(monomials sorted, `(* c a1 .. an)`, constant last, `to_real` distributed);
relations `(op a b)` to `(op' P c)` with the difference polynomial scaled to
integral coefficients of gcd 1 (Int) or leading coefficient 1 (Real), a
positive leading coefficient with the relation flipped, the constant on the
right, Int bounds tightened (`>` to `>=` plus one, non-integer `=` false).
Before scheduling, both sides of every hole are normalized: equal sides
close the hole without egglog, otherwise the goal becomes the equality of
the normal forms.  Every step is an equivalence Carcara's rules justify
(`poly_simp`, `poly_simp_rel`, `evaluate`, `aci_simp`, `not_not`,
`distinct_elim`, `cong`), so certificates can cite them; only checking is
wired up.

Measurement (plain / prenorm, interleaved, same settings), pass time in s:

| proof | plain | prenorm | closed by normalization | kept plain -> prenorm |
|---|---|---|---|---|
| gensys_icl072 (QF_UF) | 29.3 | 0.04 | 1,395 / 1,395 | 18 -> 0 |
| RF-09 | 121.8 | 27.6 | 1,666 / 2,693 | 4 -> 0 |
| c_inference | 44.8 | 11.9 | 554 / 822 | 0 -> 0 |
| bofill ex4880 | 113.2 | 21.3 | 1,080 / 1,347 | 5 -> 0 |
| MULTIPLIER_3 | 220.0 | 2.9 | 802 / 891 | 0 -> 0 |
| cut_lemma_01_008 | 615.7 | 10.8 | 1,303 / 1,370 | 63 -> 0 |
| FISCHER9 | 47.7 | 12.4 | 1,394 / 1,697 | 0 -> 0 |
| ring | 70.5 | 3.3 | 830 / 911 | 0 -> 0 |
| clock_synchro | 68.3 | 0.8 | 1,054 / 1,120 | 1 -> 0 |
| vpm2 | 116.9 | 4.4 | 1,502 / 1,838 | 7 -> 0 |

Normalization itself takes 7–53 ms per proof.  Every hole egglog kept in
these proofs (98) is closed by normalization: the large `or`/`and` chains
of gensys, the arithmetic holes that exhausted 60 s in cut_lemma.  The
remaining holes reach egglog in normal form and prove quickly.  Soundness
checks: 27 equivalences and 5 non-equivalences as unit tests; a cross-check
of every closed hole against egglog's plain verdicts (no hole newly kept);
and an independent oracle, 60 random closed holes per proof sent to cvc5 as
the negation of the hole's equality over the benchmark's declarations
(`scratchpad/prenorm/oracle.py`): 600 of 600 unsat.

What is left for egglog after normalization is the RARE rewriting proper;
the guarantee the user asked about -- rewrites that never produce terms
needing further normalization -- would let the normalizer run once before
and once after egglog; today the engine's own normalizers cover the
in-between.  Next: the same measurement on the QF_UF families with kept
holes, then a cluster run with `--hole-prenormalize`.

## 24. Holes from another producer: folding veriT's rewrite derivations (2026-09-19)

The hole checking so far only sees cvc5 proofs, because only cvc5 prints
`TRUST_THEORY_REWRITE` holes.  veriT justifies the same rewrites with a
derivation: `*_simplify`, `ac_simp`, `la_rw_eq`, ... steps rewrite subterms
and `cong`, `trans`, `refl`, `symm` assemble them into the rewrite of the
term.  A new pass, `fold` (`src/elaborator/fold.rs`, `--pipeline fold`),
turns those derivations into cvc5-shaped holes so a veriT proof goes through
the same checking and elaboration.

**What is folded.**  A *rewrite derivation* is a closed sub-DAG of steps
whose rules are the 20 Alethe rewrite rules (`REWRITE_RULES`: the
`*_simplify` family, `ac_simp`, `la_rw_eq`, `distinct_elim`, `nary_elim`,
`connective_def`; quantifier rules, `ite_intro` and `bfun_elim` left out) or
the four glue rules, each concluding a unit `(= l r)` with no arguments, no
discharge and premises only inside the derivation.  Membership is decided
bottom-up; the roots -- members some outside step uses -- become
`(step id (cl (= l r)) :rule hole :args ("TRUST_THEORY_REWRITE" "<rules>"))`
with the same id, depth and clause, the second argument listing the rewrite
rules folded in (`ac_simp:3,and_simplify:1`); the other members are dropped
when nothing kept reaches them.  Glue-only derivations (a `cong` over
`refl`s) are left alone, and so is any `cong`/`trans` with a premise outside
a derivation -- an assumed equality, a congruence-closure argument -- which
is what keeps the pass from folding theory reasoning.

**Granularity.**  veriT rewrites a whole assertion in one derivation, a
`cong` at the top over the rewrites of every conjunct: on vpm2-0 (QF_LRA,
11,628 steps) unlimited folding gives 3 holes covering 9,052 steps, each an
equality of the entire assertion, and every one exhausts the 8 GB worker
limit.  `--fold-limit N` bounds the steps of a folded derivation (counted as
a tree): a step whose derivation would be larger is not a member, so it
stays and the derivations of its premises are folded instead.  On vpm2-0,
plain checking (8 workers, 60 s and 8 GB per hole, sort guards, growth
caps):

| limit | holes | steps folded | proof lines | proved | kept | pass time |
|---|---|---|---|---|---|---|
| 1 | 3,854 | 3,854 | 11,628 | 3,854 | 0 | 100 s |
| 10 | 3,547 | 9,641 | 6,938 | 3,547 | 0 | 201 s |
| 100 | 3,164 | 10,457 | 5,879 | 3,163 | 1 | 248 s |
| 1000 | 3,127 | 10,592 | 5,706 | 3,126 | 1 | 250 s |
| none | 3 | 9,052 | 2,580 | 0 | 3 (memory) | -- |

The hole count barely moves past limit 10 because most of veriT's rewrite
steps are leaves feeding a `cong` at the top; the kept hole at 100 and
above is a 49-summand `(* 1.0 x)` elimination that exhausts 60 s in egglog
(the prenormalizer closes it).  With `--hole-prenormalize` at limit 1: 2,960
of 3,854 holes closed by normalization, the 894 `la_rw_eq` goals rewritten
and proved, pass 34 s.

**Inputs.**  veriT 2026.05 (the tarball in the worktree, built copy from
wt-corealethe), `--proof-prune --proof-merge`.  Benchmarks are first
expanded with `cvc5 -o raw-benchmark --parse-only --dag-thresh=0`: a `let`
in the input makes veriT prove under `:=` anchors (`let` steps), the hole
checker does not apply anchor assignments, and Carcara's `let` checker
rejected the unexpanded proofs anyway (tgc_io-safe-6, step t2....t27).
Let-free veriT proofs check valid.  Corpus: 40 random unsat benchmarks under
400 KB per logic (QF_UF 40, QF_LIA 30 proved, QF_LRA 4 proved), in
`scratchpad/verit/corpus`; the runner `scratchpad/verit/corpus-run.sh`
folds (`fold hoist prune`, limit 100), checks the folded proof, then
hole-checks it plain and prenormalized.

**What the corpus shows so far** (26 of 106 proofs, smallest first per
logic, interleaved; binary d44e0c81 with the §23 normalizer):

| logic | proofs | steps before -> after | holes | plain proved / kept / skipped | plain hole-free | plain time | prenorm closed / proved / kept | prenorm hole-free | prenorm time |
|---|---|---|---|---|---|---|---|---|---|
| QF_UF | 9 | 10,025 -> 8,815 | 312 | 215 / 97 / 0 | 1 | 173 s | 312 / 312 / 0 | 9 | 0 s |
| QF_LIA | 9 | 288 -> 216 | 40 | 36 / 4 / 0 | 5 | 90 s | 23 / 40 / 0 | 9 | 1 s |
| QF_LRA | 8 | 948 -> 295 | 86 | 21 / 60 / 5 | 1 | 565 s | 19 / 39 / 47 | 5 | 404 s |

Every folded proof checks `holey` (the holes are the only unchecked
steps).  The plain engine does much worse on veriT's holes than on cvc5's,
for three reasons that are all about term shape, not rewrite content:

1. **`ac_simp` over nested binary `and`/`or`** (QF_UF, `iso_*`: 87 of 97
   kept in seconds): the flattening of a deep binary tree of `or`s inside
   `and`s hits the 500k growth cap.  cvc5 flattens in its own printer, so
   its holes never ask this.
2. **Relations under Boolean connectives** (QF_LRA `cbrt`, `Chua`): the
   engine's arithmetic normalization is a goal-level fallback, so
   `(* x (- 1.0))` = `(* (- 1.0) x)` proves as a relation or a negated
   relation (`scratchpad/verit/diag/d1`, 0.7 s each) but not one level
   down, inside an `and` (guard `arithRelBoolCanMatch` fails).  With
   `--fold-limit 1` such holes are leaves and prove.
3. **`bool_simplify` and buried `la_rw_eq`** (QF_LRA): a five-symbol
   `(not (=> A (=> B B)))` = `(and A B (not B))` exhausts 60 s or 8 GB in
   egglog (`diag/d2`), and a single `la_rw_eq` deep inside a 4 KB DNF
   (`windowreal-safe2-2`) exhausts 60 s: the Boolean rules explode on the
   surrounding term.

**Normalizer additions** (d72ba1bd), each an equivalence: negation normal
form; a negated bound is the opposite bound (Int tightened); two bounds on
one polynomial that make an equality (`(and (<= P c) (>= P c))` is
`(= P c)`) or, under `or`, a disequality are replaced by it -- the inverse
of `la_rw_eq`; and a conjunct that is a disjunction whose every member is
complemented among the conjuncts makes the conjunction false (dually for
`or`), which the flattening had hidden (`(not (=> (and A C) (=> (or B C)
(or B C))))` is false).  The dual-complement rule matters because NNF
pushes `not` through the compound literal the old complement test matched.
Unit tests: 41 equivalences, 9 non-equivalences.  With these, all three
`diag/d2` shapes, all 14 `windowreal-safe2-2` holes and all 3
`intersection-example` holes close without egglog.

**And on cvc5's holes: every one.**  Re-running the ten §23 sample proofs
with the final normalizer (`scratchpad/prenorm3`): 100% of the holes of
every proof are closed by normalization alone -- gensys 1,395/1,395, RF-09
2,693/2,693, 30_30_18 822/822, ex4880 1,347/1,347, MULTIPLIER_3 891/891,
cut_lemma 1,303 -> 1,370/1,370, FISCHER9 1,697/1,697, ring 911/911,
clock_synchro 1,120/1,120, vpm2 1,838/1,838 -- egglog is never called and
the passes take 0.01–0.04 s of hole time (0.3–3 s wall, 37 s for FISCHER9's
parse).  What was left to egglog before were negated bounds and
equality-to-bounds rewrites, which the additions cover.  The cross-check
(no hole newly kept; every hole egglog kept is closed) and the cvc5 oracle
(400 of 400 sampled closed holes unsat) both pass, as they did for the
NNF-only intermediate (`scratchpad/prenorm2`, same closed counts as §23).
The chk1200p run in progress uses the §23 normalizer; the natural next
cluster run is the same comparison with this one.

Pending: the rest of the corpus (the runner continues; its prenormalized
column is redone with the final binary by `scratchpad/verit/corpus-prenorm.sh`
once it ends), the same at `--fold-limit 1` for the granularity
comparison, and a cluster run over veriT proofs of the three sets.

**Bound-aware complements** (commit after d72ba1bd).  The negated-bound
normal form hid a complement: `(or (not (>= x 1)) (>= x 1))` became
`(or (<= x 0) (>= x 1))`, and a `comp_simplify` hole of RF-01 (QF_LIA)
went to egglog and failed.  The complement checks now reason about bounds
per polynomial: under `and`, bounds with no common value (or a point
outside a bound) are a complement pair and the tightest lower and upper
bound are the only ones kept; under `or`, bounds covering every value are
one and the weakest are kept; a member of a dual argument that is
complemented is dropped from it (`(or p (and (not p) q))` is `(or p q)`).
Unit tests 56 / 14.  The ten cvc5 sample proofs still close completely,
cross-check and oracle clean (`scratchpad/prenorm4`).

**Correction: the `let`s were never the obstacle.**  Two claims in the
"Inputs" paragraph above are wrong.  Carcara checks veriT's `let` proofs
valid as they are (tgc_io-safe-6, clock_synchro, FISCHER9, gensys: valid);
what failed was my own `--expand-let-bindings`, which expands the `let`
terms of the proof too, so the `let` rule had no `let` to match.  And the
rewrites do not depend on the anchor assignments: veriT's `let` subproofs
contain only `refl`, `cong` and the closing `let` (vpm2-0: 1,838 `refl`,
1,874 `cong`, 37 `let`, nothing else), while every `*_simplify`, `ac_simp`
and `la_rw_eq` step is at depth 0.  So `fold` applies to the original
proofs unchanged, the `let` subproofs stay as glue-only derivations, and
the holes are depth-0 and context-free.  On the original proofs at limit
100 (`scratchpad/verit/lets`): gensys 141 holes, clock_synchro 89,
tgc_io-safe-6 51, 30_30_18 30, FISCHER9 3,107, ring 26; every folded proof
checks `holey`, and the prenormalized pass closes every hole of every one
(hole time 0.000–0.022 s).  What the cvc5 round-trip had actually done for
vpm2-0 is unrelated to `let`: the original benchmark writes Real constants
as integer numerals, veriT then prints `(step t1602 (cl (= (- 1.0) (- 1)))
:rule unary_minus_simplify)`, and Carcara's parser rejects the mixed-sort
equality (`sort error: expected 'Real', got 'Int'`) even with
`--allow-int-real-subtyping`.  The corpus was run on the round-tripped
benchmarks, which is a valid experiment (the proofs differ only in the
absence of `let`s and in numeral spelling), but the plan is to run the
original benchmarks directly; `scratchpad/verit/gen-orig.sh` is producing
their veriT proofs and checking each, to count how many the numeral issue
affects.

## 25. The normalizer, exactly (2026-09-19)

**The normalizer, exactly** (`src/elaborator/prenorm.rs`, as of 9027d5ac).

*Driver.* With `--hole-prenormalize`, before any hole is scheduled, one `Normalizer` (one memo shared by all holes of the proof) normalizes both sides of every hole `(= l r)`. If the two normal forms are the same pooled term the hole is closed without egglog; otherwise the hole's clause becomes `(= nl nr)` and that is what egglog sees. The log line `hole prenorm: A of B holes closed by normalization, C goals rewritten` counts the two outcomes.

*Traversal.* Bottom-up and memoized per term (pointer identity in the term pool). An application `(f t1 .. tn)` gets its arguments normalized. An operator term gets its arguments normalized first, then one of the cases below applies to the already-normal arguments. Everything else is left as it is: constants, variables, and binders (`forall`, `exists`, `lambda`, `choice`, `let`), whose bodies are not entered.

*Operator cases.*

1. `not`: `(not (not p))` is `p`; `(not true)` is `false` and `(not false)` is `true`. `(not (rel P c))` for `rel` among `<`, `<=`, `>`, `>=` over Int or Real is the opposite relation, re-normalized as a relation (Int `(not (<= P c))` becomes `(>= P c+1)`, Real `(> P c)`). `(not (and a1 .. an))` is the `or` of the `(not ai)`, and `(not (or ..))` the `and` of them, each `(not ai)` going through this same case, then the connective through the `and`/`or` case: negation normal form. Any other `(not p)` stays (`(not (= a b))`, `(not (ite ..))`, `(not x)`).
2. `and`, `or`: the ACI procedure below.
3. `(=> a b)`: the `or` of `(not a)` (through case 1) and `b`, through the ACI procedure.
4. `ite`: `(ite true a b)` is `a`, `(ite false a b)` is `b`, `(ite c a a)` is `a`; otherwise kept.
5. `+`, `-`, `*`, `/`, `to_real` (term of sort Int or Real): the term is read as a polynomial and printed in canonical form. The polynomial has rational coefficients over *atoms*, the maximal subterms that are none of these operators: a numeral (also `(- 1)`) is a constant; `+` adds; unary `-` negates; n-ary `-` subtracts; `*` multiplies polynomials, so a product of atoms is a monomial and nonlinear terms are fine; `(/ p c)` with `c` a nonzero constant scales by `1/c`, any other division is an atom; `(to_real p)` is `p`'s polynomial with every atom wrapped in `to_real` and the constants converted. A monomial is the multiset of its atoms sorted by pointer. Canonical term: the monomials ordered by number of atoms, then by their atoms' pointers; each printed as the atom, `(* c a)` or `(* c a1 .. an)` with the coefficient omitted when it is 1; the constant last; a single monomial without the `+`; the zero of the sort when empty. Constants print as Int literals when the sort is Int and the value integral, else as Real literals (rationals).
6. Relations `<`, `<=`, `>`, `>=` with two arguments, and `=` with two arguments of sort Int or Real. The sort is Real as soon as one side is Real (Int numerals may stand on either side under subtyping), else Int. The difference `lhs - rhs` is taken as a polynomial. If it is constant, the relation is decided: `true` or `false`. Otherwise the constant moves right (`P + k op 0` is `P op -k`) and `P` is scaled: Int, by the lcm of the coefficients' denominators over the gcd of the resulting numerators, so the coefficients are integers with gcd 1; Real, by the reciprocal of the absolute leading coefficient (the first monomial in canonical order), so it is 1. A negative leading coefficient negates both sides and flips `<` with `>` and `<=` with `>=` (`=` stays). Int bounds are tightened: a non-integer bound is rounded, `>=` up, `<=` down, `>` becomes `>=` of the floor plus one, `<` becomes `<=` of the ceiling minus one, and `=` becomes `false`; an integer bound turns `>` into `>=` of the bound plus one and `<` into `<=` of the bound minus one. The result is `(op' P c)`.
7. `=` otherwise: `(= a a)` is `true`; `(= p true)` and `(= true p)` are `p`; `(= p false)` and `(= false p)` are `(not p)` through case 1; else the two sides are put in pointer order (one orientation per pair) and, when both are constants, evaluated.
8. `distinct`: with two arguments, `(not (= a b))` through cases 6/7 and 1; with more, the `and` of the pairwise `(not (= ai aj))`, `i < j`, through the ACI procedure, so a repeated element gives `false`.
9. Any other operator (`xor`, `div`, `mod`, `abs`, `select`, bit-vector operators, ...) is kept, evaluated when all its arguments are constants.

*The ACI procedure* for `(op a1 .. an)`, `op` being `and` (identity `true`, absorbing `false`) or `or` (identity `false`, absorbing `true`), with the `ai` already normal:

a. Arguments that are themselves `op` terms are flattened in (they are flat already, so one level suffices).
b. Identity elements are dropped; an absorbing element makes the result absorbing.
c. The rest is sorted by pointer and deduplicated.
d. Complements make the result absorbing: a negated argument `(not p)` with `p` also present, and `(not (= P c))` with a bound on the same polynomial `P` that excludes the point `c` under `and` or that covers it under `or`. "Excludes" and "covers" are the interval tests below.
e. An argument of the dual connective (an `or` inside an `and`, or the reverse) is examined member by member: a member is *complemented* if it has a literal complement among the arguments, or if it is a bound `(rel P c)` or a point `(= P c)` or `(not (= P c))` and some argument is a bound on the same `P` that excludes it (under `and`) or covers it (under `or`). If every member is complemented the result is absorbing; otherwise the complemented members are dropped from that argument (`(or p (and (not p) q))` is `(or p q)`), the argument is rebuilt through the ACI procedure for the dual connective, and the whole list is re-run through this procedure.
f. Bounds are merged per polynomial (same pooled `P`). Under `and`, only the tightest upper and the tightest lower bound stay (at equal value the strict one); if they have no common value the result is `false`; if they meet at one non-strict point they are replaced by `(= P c)`. Under `or`, only the weakest upper and lower stay (at equal value the non-strict one); if they cover every value the result is `true`; if they leave out exactly one point they are replaced by `(not (= P c))`: Int `low = up + 2` gives `(not (= P (up+1)))`, Real `low = up` with both strict gives `(not (= P c))`. Int bounds are never strict after case 6. If anything changed, the list is re-run through the procedure.
g. No argument left gives the identity, one gives that argument, more give `(op ..)` in pointer order.

*Interval tests* (upper `u` from `<=`/`<`, lower `l` from `>=`/`>`, Int bounds non-strict): two bounds exclude each other when `l > u`, or `l = u` and one is strict; a point `c` is excluded by `(<= P u)` when `u < c`, by `(< P u)` when `u <= c`, by `(>= P l)` when `l > c`, by `(> P l)` when `l >= c`, and by `(not (= P c))`. Two bounds cover everything when, Int, `l <= u + 1`, or, Real, `l < u`, or `l = u` and not both strict; a bound covers a disequality `(not (= P c))` when it is implied by `(= P c)`: `(<= P u)` with `u >= c`, `(< P u)` with `u > c`, `(>= P l)` with `l <= c`, `(> P l)` with `l < c`.

*What it is not.* No De Morgan below binders, no distribution of `and` over `or` (no DNF/CNF), no `ite` lifting, no reasoning across different polynomials, no theory reasoning beyond linear bounds on one polynomial. Canonical orders are pointer orders, so a normal form is canonical within one run's pool, which is all the check needs. Every step is an equivalence; the checker's rules that justify them (`poly_simp`, `poly_simp_rel`, `evaluate`, `aci_simp`, `not_not`, `distinct_elim`, plus the bound reasoning as `la_generic` instances) are what a certificate would cite, but only checking is wired up.

**Two fixes on the way** (f841cd24, 9027d5ac).  The parser fix from wt-diff
(92d8a42f) is ported: under `--allow-int-real-subtyping` the polymorphic
positions (`=`/`distinct` arguments, `ite` branches, uninterpreted function
arguments) accept an Int where a Real is expected, which is what rejected
the original vpm2-0 proof (`(= (- 1.0) (- 1))`).  With it the original
proof checks valid, folds to the same 3,164 holes as the round-tripped one
at limit 100, and -- after the normalizer takes a mixed Int/Real relation's
sort as Real rather than from its left side, which had kept
`(<= (- 300) P)` as an Int bound and `(<= P (- 300))` as a Real one -- every
one of them closes by normalization (hole time 0.047 s).

**Corpus complete** (106 proofs; 2 do not parse: `simple_startup_12nodes`
and `NEQ006_size5`, an undefined identifier on the last line of the veriT
output).  Plain checking, limit 100, 4 workers at 4 GB, 60 s per hole,
300 s per proof; the prenormalized column redone with 9027d5ac
(`scratchpad/verit/run100/results.txt`, `results-prenorm.txt`):

| logic | proofs | steps before -> after | holes | plain proved / kept / skipped | plain hole-free | plain time | prenorm closed / proved / kept | prenorm hole-free | prenorm time |
|---|---|---|---|---|---|---|---|---|---|
| QF_UF | 39 | 1,974,555 -> 1,663,096 | 2,401 | 2,012 / 389 / 0 | 2 | 683 s | 2,401 / 2,401 / 0 | 39 | 0 s |
| QF_LIA | 30 | 29,685 -> 11,376 | 8,169 | 8,159 / 10 / 0 | 20 | 1,289 s | 8,169 / 8,169 / 0 | 30 | 0 s |
| QF_LRA | 35 | 463,425 -> 363,685 | 10,254 | 812 / 1,496 / 7,946 | 2 | 7,805 s | 10,149 / 10,221 / 33 | 19 | 948 s |

Rules folded: QF_UF `ac_simp` 7,324, `or_simplify` 557, `and_simplify`
466, `eq_simplify` 193; QF_LIA `la_rw_eq` 10,403, `comp_simplify` 1,887,
`sum_simplify` 1,309; QF_LRA `la_rw_eq` 29,823, `ac_simp` 12,359,
`sum_simplify` 5,604, `prod_simplify` 5,552, `comp_simplify` 1,480, and
smaller counts of eleven others.  The 33 QF_LRA holes left are in 16
proofs, one to four each, and go to egglog after normalization and time
out there.  The original benchmarks' veriT proofs (`gen-orig.log`) check
valid with the subtyping port; the one `invalid` in that log was the
runner passing two benchmark paths for a repeated basename (`RF-01`).

This is the last measurement of the normalizer in this form: the design is
being redone as the composition of Carcara's own rule procedures
(`evaluate`, `poly_simp`/`poly_simp_rel`, `aci_simp`), so that elaboration
can emit the same steps, with everything else left to RARE rules.

## 26. The normalizer as four checker procedures, with certificates (2026-09-19)

The §23–25 normalizer was a general-purpose decision procedure for the
holes; that was not the point.  The point is one machinery for checking
and elaboration: normalization steps that are Carcara rule applications,
so that the same derivation that closes a hole in the checking pass is the
certificate that replaces it in the elaboration pass, and whatever the
normalizer does not reach is egglog's job through RARE rules (with a rule
file per producer, cvc5's and veriT's, as needed).

**What it is now** (`src/elaborator/prenorm.rs`, commit 013405c6).
Bottom-up and memoized; at each operator term, after the arguments, at
most one of the four procedures applies at the top, and its result is
normalized again (a `distinct` expands to equalities that `poly_simp_rel`
then canonicalizes, under an `and` that `aci_simp` then sorts):

- `evaluate`: a term whose arguments are all values is its value
  (`Term::evaluate`).
- `poly_simp`: `+`, `-`, `*`, `/`, `to_real` terms of sort Int or Real are
  printed as the canonical term of the checker's own polynomial
  (`checker::rules::polynomial::Polynomial`, now `pub(crate)`): monomials
  by size then atom pointers, `(* c a1 .. an)`, constant last, Int atoms
  in a Real polynomial wrapped in `to_real` (the checker's polynomial sees
  through it).  Bit-vectors not yet.
- `poly_simp_rel`: `(op x1 x2)` for `<`, `<=`, `>`, `>=`, `=` over Int/Real
  (Real when either side is) becomes `(op P c)`: the difference of the
  sides scaled by a positive factor (integral coefficients of gcd 1 for
  Int, leading coefficient of absolute value 1 for Real), constant on the
  right.  An equality is additionally oriented to a positive leading
  coefficient, which `poly_simp_rel` allows for `=` only.  No flipping of
  order relations and no Int tightening: those are RARE rules.  The step
  carries its `poly_simp` premise `(= (* s (- x1 x2)) (* 1 (- P c)))`.
- `aci_simp`: `and`, `or`, `bvand`, `bvor`, `bvxor`, `bvadd`, `bvmul`
  flattened, identity element removed, deduplicated when idempotent, sorted
  by pointer.  No absorbing element, no complements.
- `distinct_elim`: two arguments to `(not (= a b))`, more to the `and` of
  the pairwise disequalities in the checker's order, more than two
  Booleans to `false`.

Nothing else: NNF, negated bounds, bound merging, complements, absorbing
elements, `=>`, `ite`, `(= p true)`, `(= x x)` are gone.

**Certificates.**  Every step is one rule on one subterm, so the
derivation of a normal form is `cong` over the arguments' derivations,
the top step(s), the tail's derivation, joined by `trans`; a closed hole
`(= l r)` gets the two derivations joined by `symm` and `trans` (or
`refl`), a rewritten goal gets egglog's proof of `(= nl nr)` bridged to
`(= l r)` the same way.  `--hole-prenormalize` therefore works in the
elaboration pass too.  The unit tests check every certificate with the
checker (`certificates_check`).

**Two checker fixes on the way** (1d3cdec4): the evaluator compared an
Integer and a Real value structurally, so `evaluate` accepted
`(= (= 1.0 1) false)` under subtyping; and `aci_simp` deduplicated the
arguments of every associative operator, accepting `(= (+ a a) a)` and
`(= (* a a) a)`; deduplication is now confined to `and`, `or`, `bvand`,
`bvor`.

**Measured on the ten cvc5 sample proofs** (4 workers, 4 GB, 60 s per
hole; `scratchpad/prenorm5`, `scratchpad/elab5`):

| proof | holes | closed by normalization | rewritten for egglog | check-only: kept / pass | elaboration: justified / kept / pass | elaborated proof |
|---|---|---|---|---|---|---|
| gensys_icl072 | 1,395 | 462 | 6 | 0 / 8.5 s | 1,395 / 0 / 20 s | valid |
| RF-09 | 2,693 | 1,163 | 59 | 0 / 36 s | 2,693 / 0 / 72 s | holey (23 other holes) |
| 30_30_18 | 822 | 450 | 292 | 0 / 10 s | 822 / 0 / 24 s | valid |
| ex4880 | 1,347 | 911 | 252 | 0 / 22 s | 1,345 / 2 / 40 s | holey (108) |
| MULTIPLIER_3 | 891 | 766 | 36 | 0 / 3 s | 891 / 0 / 6 s | holey (217) |
| cut_lemma | 1,370 | 1,258 | 76 | 0 / 4 s | 1,370 / 0 / 8 s | holey (142) |
| FISCHER9 | 1,697 | 1,191 | 321 | 0 / 12 s | 1,697 / 0 / 22 s | holey (122) |
| ring | 911 | 747 | 95 | 0 / 6 s | 911 / 0 / 8 s | holey (116) |
| clock_synchro | 1,120 | 782 | 271 | 0 / 14 s | 1,119 / 1 / 22 s | holey (79) |
| vpm2 | 1,838 | 739 | 3 | 1 / 75 s | 1,837 / 1 / 82 s | holey (256) |

Normalization alone closes 33–92% of the holes per proof; the rest go to
egglog, either as rewritten goals or untouched (the Boolean shapes:
`(= p true)`, `not_not`, absorbing elements, complements, which are
`bool-*` RARE rules), and egglog proves all of them but one: `ho27` of
vpm2, a `(<= ...)` over a 49-summand sum whose sides normalize to
different relations (a flip), which egglog then cannot handle at that
size in 60 s.  Every hole the plain engine kept in §23 (98) is closed or
proved.  Pass times sit between the plain engine's (29–616 s) and the
§23 normalizer's (0.04–28 s).  Oracle: 400 of 400 sampled closed holes
unsat; cross-check: no hole newly kept.  In the elaboration pass every
certificate was accepted by the checker at insertion (no "checker
rejected" hole); the four kept holes are three egglog snapshots without
a certificate and the vpm2 timeout.  The "holey" verdicts of the
elaborated proofs are cvc5's other hole kinds (`ARITH_PRED_CAST_TYPE`,
`THEORY_INFERENCE_ARITH`, `THEORY_BV`), which were never in scope; gensys
and 30_30_18, which have none, come out valid.

**veriT.**  The corpus's prenormalized column is being redone with this
normalizer (`results-prenorm.txt`; the §24 column is kept as
`results-prenorm-old-normalizer.txt`).  What the old normalizer closed and
this one does not (veriT's `bool_simplify`, `la_rw_eq`, `comp_simplify`
shapes) is what a `verit.rare` file has to supply.

## 27. The residue: what egglog gave up on without a kill (2026-09-19)

The question was whether the rule set is enough: the holes egglog "could
not prove" after saturating (§19: 6,667 in the full run's checking pass)
are the only candidates for missing rules, and they were never classified.
`scratchpad/residue/residue.py` extracts them from a run's
`results.json.gz` and classifies the goals; `report.md` has the tables.

**chk1200h2 (growth caps, 60 s per hole).**  8,048 such holes in 2,863
proofs: QF_UF 6,440 (2,496 proofs, 6,339 from QG-classification), QF_LIA
1,101 (317), QF_LRA 507 (50).  Not one is a saturation: every one ends in
"the e-graph grew past the bound" (500k for the plain cap, 3M for
arithmetic), still growing when stopped, on goals of 100 to 8,000 nodes.
Structurally, 5,752 of the 8,048 have sides that coincide after sorting
and flattening `and`/`or`/`+` (5,552 of them QF_UF `or`/`and` chains) or
after deduplication or double negation; of the 2,296 whose sides really
differ, 794 QF_UF `or` goals differ by a `false` disjunct and 28 `and`
goals by a `true` conjunct, 20 are `(ite (not c) a b)` against
`(ite c b a)`, 12 are `(= s t)` against `true`, 8 `(ite false ..)`, and
the rest are arithmetic: `+` against `+` with more than ten differing
summands (656), sums that cancel to a constant (453), `<` against
`(not (>= ..))` (153), `<=`/`>=` flips and negations (90), `*` against
`+` (38).  No De Morgan shape, no `distinct`, nothing Boolean without UF
atoms.  A further 411 (90 LIA, 321 LRA) failed the relation fallback's
own key comparison (`arithRelBoolKeyOf`), i.e. relation goals whose
canonical keys differ: flips and tightenings again.

**The full run (no caps, 30 s per hole).**  The same reason is reported as
egglog's final check failing, `(= (goal_lhs) (goal_rhs))`: 6,591 holes
(QF_LIA 3,578 in 202 proofs, QF_UF 2,753 in 790, QF_LRA 260 in 56), plus
47 relation-key failures; those logs carry no goal text, but the proofs
are the same families that chk1200h2 stops at the cap.

**Conclusion.**  The residue is not evidence of missing rules.  It is the
e-graph blowing up on associativity and commutativity over long chains
and on polynomial arithmetic over many summands, on goals that the
§26 normalizer takes care of before egglog: `aci_simp` (flattening,
sorting, deduplication, the `false`/`true` units) and `poly_simp` (the
cancelling sums, the coefficient collection) cover about 7,700 of the 8,048
outright, and what remains after normalization for egglog is small: the
relation negations and flips (`<` vs `(not (>= ..))`, `<=` vs `>=`) and
the `ite` condition swap, which are single RARE rules on small goals.
The one structural gap found earlier, De Morgan (§19), does not occur in
the residue at all.  So the rule set, with the normalizer in front of it,
is sufficient for everything egglog was ever asked and failed to answer
by saturation; the unknown that remains is the never-attempted holes of
the budget-bound proofs, and the run with the §26 normalizer is what
measures those.

**In the checker too** (commit after 817c9516).  The normalizer had only
been wired into the elaborator's hole pass, for the historical reason that
the isolated workers and budgets live there.  `carcara check
--check-hole-rewrites --rare-file ...` now normalizes every
`TRUST_THEORY_REWRITE` hole before its in-process egglog call, logging
`closed by normalization` for the ones that need none; that path still has
no isolation and no hard per-hole limit (only the cooperative
`--rare-check-timeout`), which is why the evaluation keeps using the
elaborator's pass.  A plain `carcara check` without the flag leaves holes
as holes, as before.

## 28. Relations below the goal: the all-relations fallback (2026-09-19)

veriT's `la_rw_eq` rewrites an arithmetic equality into the conjunction of
its two bounds (`arith/LA-pre.c`, one of the preprocessing rules the
`fold` pass turns into holes), so a hole's goal is
`(= (= a b) (and (<= a b) (<= b a)))`.  Both the normalizer and egglog
failed on it, for the same reason: a relation and its mirror image have
the same content but different terms, and nothing identified them below
the goal.  The normalizer cannot: `poly_simp_rel` scales by a positive
factor (a negative one is allowed for `=` only), so `(<= a b)` and
`(<= b a)` become `(<= P c)` and `(<= -P -c)`.  egglog could not either:
`arithRelBoolKeyOf` is demanded for the goal's two sides only, so the
canonical keys were never computed for an atom inside an `and`.

**The fallback** (`arith_rel_all`/`arith_rel_merge` in
`arith_poly_norm_rel.egglog`, plan `arithRelAll` in the engine).  A third
goal fallback, tried only after the goal check and the two goal-level
arithmetic checks have failed: demand the key of every relation atom in
the e-graph (the nine shapes the key rules cover), run the guard and
`arith_poly` rulesets, union the atoms whose keys agree, then run the main
schedule once more and check the goal as it is.  A goal the earlier checks
prove never reaches it, so cvc5's holes pay nothing; the cost falls only on
goals that would otherwise be kept.

**Reconstruction.**  The unions the fallback makes are not rewrites, so the
certificate search had to learn them: a relation pair with equal keys is
one `poly_simp_rel` computation (`prove_by_arith`, in-class), and `and`/`or`
sides whose literal sets differ only in unioned literals are proved by
`aci_simp` on the matching literals plus in-class proofs of the pairs
(`prove_by_aci_modulo`, also a candidate edge of the path search).  The
computational strategies run after the rule search, so a checkable rule
path is still preferred.

**A soundness fix on the way.**  `rules_from_generated_program` stripped the
sort guards from the generated rules, so the search would ground
`arith-eq-elim-real` on an integer equality and emit a `rare_rewrite` step
the checker rejects ("trying to substitute term 's1' with a term of a
different sort"); the guards are now kept and checked when a rule is
grounded, with `encoded_sort` recomputing an encoded term's sort.

**Policy.**  In the elaboration pass the normalizer no longer rewrites the
goals it cannot close: the certificate search works on the e-graph of the
goal it was given, and on a normalized goal egglog proves more while the
reconstruction replays less (the `arith-eq-elim-int` instance it needs is
not a stored node, since the normalized sides are terms the rules were not
compiled around).  Closing a hole outright still applies, with the
normalizer's certificate.  Trying the normalized goal first and the
original on a reconstruction failure would get both, at one extra child run
per lost hole; not done.

**Measured** on the three `la_rw_eq` shapes (`scratchpad/verit/diag/d4`),
which were kept by both passes before: checking proves 3 of 3, elaboration
justifies 3 of 3, and the elaborated proof checks **valid** with no hole
left.  The unit tests cover the e-graph side
(`mirrored_inequalities_meet_inside_a_conjunction`) and the certificate
side end to end (`elaborates_mirrored_bounds_in_a_conjunction`).

## 29. `:list` parameters, and the complement rules that never fired (2026-09-19)

Probing the veriT corpus's kept holes turned up something that had been
distorting every measurement since §17.  A RARE rule's `:list` parameter
is compiled into **exactly one argument slot** of the `Args` chain (a bare
pattern variable, which the list re-association lets bind a *sublist*, but
never an empty one).  So a rule with k list parameters only matches when
all k lists are non-empty.  `bool-or-taut`, with three of them, proves

| goal | verdict |
|---|---|
| `(or a p b (not p) c)` | proved in 0.07 s |
| `(or a p (not p) c)` | kept |
| `(or a b p (not p))` | kept |
| `(or p (not p))` | kept |

and the kept ones are not merely unproved: an unreachable goal is what
triggers the quadratic pair seeding, so `(= (not (or (not A) A (not B)))
false)` with three-literal `A`, `B` exhausts 2 GB in 60 s
(`scratchpad/verit/diag/d3`).  The same holds for `bool-and-conf` and for
every other `:list` rule; Carcara's own `rare_rewrite` checker shares the
convention, substituting one term per parameter, so an empty list has no
form there either.

**The fix, on the set form.**  The ACI machinery converts every `and`/`or`
call into a set and already has set-level rules for the identity, the
singleton, idempotence and the absorbing element.  One more rule unions a
set that holds `w` and `(not w)` with the absorbing element, which finds
the pair whatever the arity and the positions
(`aci_norm.rs`, rule 9).  The reconstruction certifies it with a new
computation kind, `AciComplement`, whose Alethe step is
`or_simplify`/`and_simplify` -- Carcara's procedures for those rules
short-circuit on exactly this pair.

**Measured** on the six shapes of `scratchpad/verit/diag/d5`, all kept
before: checking proves 6 of 6 in under 0.1 s each, elaboration justifies
5 of 6 (the sixth has the pair under a `not`, where the search does not
chain the step onto `bool-not-true` yet).  Two tests cover it, at the
engine and end to end.

**The general fix** (commit ef1d4d8d) followed.  The compiler emits one
variant of a rule per subset of its `:list` parameters, with those dropped
from the argument chains; a variant that would leave an operator without
arguments is not emitted, and the count is capped at four list parameters.
For the three logics this turns 322 rules into 366.

Two things were needed for the certificates.  Every variant carries the
rule's name, so the verifier now accepts a certificate that *some* rule of
that name states rather than the first one found -- several sort
instantiations of a rule already shared a name, so this was a latent bug.
And a `rare_rewrite` step has no form for an absent argument, so an
instance whose list parameters were dropped is stated on the terms padded
with the connective's identity (`false` in an `or`, `true` in an `and`, `0`
in a sum, `1` in a product), which is exactly what the checker recomputes
from the rule's declaration, with an `aci_simp` step on each side bridging
the padding.  The padded terms come from instantiating the full variant's
pattern, so they agree with the checker by construction.

With the ACI set rule switched off, so that only this path can prove them,
the six complement shapes give 6 of 6 proved in checking and 5 of 6
justified in elaboration -- the same as the set rule, at about 1.4 times
the time and three steps per certificate instead of one.  Both are kept:
the set rule is the cheaper route for the shape that dominates, and the
variants cover every other list rule (`distinct-false`, the bit-vector and
string ones).  `tests/rare/list-empty.rare` holds a rule that only an
empty-list variant can apply, so the general path is pinned by a test of
its own rather than by the complement family.

**What is still open.**  A list parameter that binds *several* arguments
still cannot be written in a `rare_rewrite` step, so such an instance is
proved but not certified; that needs a form for a list argument in the
step's `:args`, which is a proof-format decision.

## 30. One rule on the set form, and the set form for every term (2026-09-19)

§29 left the `:list` gap closed by brute force: one compiled variant per
subset of a rule's list parameters, 2^k of them, capped at four.  The
variants are gone for the connectives.  A rule whose left-hand side is an
`and`/`or` over `:list` parameters is now compiled **once**, against the
ACI set form:

```
(rule ((= (@and (Assoc elements)) result)
       (set-contains elements (Mk w1))
       (set-contains elements (Mk (@not (Args (Mk w1) (Empty)))))
       (SortBool (Mk w1)))
      ((union result (Mk (Bool false)))) :ruleset list-ruleset)
```

The fixed arguments become membership conditions and the list parameters
disappear, because a set has no positions to fill: the rule fires whatever
the arity, wherever the fixed arguments sit, and with any of the lists
empty.  `set_form_rule` in `engine.rs` builds it, and a rule that gets one
emits no variants (`on_the_set_form`).  For the three logics the database
is 342 rules, against 322 with no empty-list handling at all and 366 with
the variants.  The hand-written complement rule of §29 is gone with them:
`bool-or-taut` and `bool-and-conf` are ordinary RARE rules again, and the
certificate cites them by name instead of an `AciComplement` computation.

**The set form has to exist for terms the rewriting derived**, not only
for the ground `and`/`or` calls the step spells out, or the compiled rule
has nothing to match.  `aci_norm::general_set_conversion` gives every
class of an `and`/`or` term its set form.  Its rules are declared with the
program but put in a ruleset of their own, `set-ruleset`, which no ordinary
round runs; the last **goal fallback plan**, `aciSets`, saturates that
ruleset and runs one more schedule round.  Three reasons, all measured:

- A goal the ordinary rules prove needs none of it and pays nothing.  On
  two cvc5 proofs with no kept holes (`dead_dnd014`, 624 holes;
  `prime_cone_unsat_20`, 398) the plan is invisible: 8.901 s against
  8.904 s and 18.610 s against 18.711 s with the plan removed entirely,
  same verdicts.  (Both are about 20% and 10% slower than the binary the
  cancelled `chk1200n` run used, which is the cost of everything on this
  branch since; moving the compiled set-form rules out of `list-ruleset`
  does not recover it and costs d3 and d5 a fallback round, so they stay.)
- The plans run in order on the *same* e-graph, so by the time the set
  conversion runs, the arithmetic plans have already added their relation
  rows.  A goal proved by the set form alone loses those, and the
  certificate search loses with them (d4 went 3 of 3 to 0 of 3 with the
  conversion first).
- Nothing else in the program depends on it, so it cannot slow down the
  rounds that do the ordinary work.

**A wrapper congruence was hiding the ACI and relation steps.**  The set
form merges an `and`/`or` term with its permutations, which makes
`Mk(@and(a,b))` and `Mk(@and(b,a))` congruence-compatible at the `Mk`
wrapper: same operator, one child, children in the same class.  The
candidate-graph builder preferred that edge, and justifying it pushed the
obligation one level down, onto the *unwrapped* applications -- where
`aci_modulo_pairs`, `aci_equal` and `arith_kind` all bail out, because
they read a term through `encoded_application`, which wants the wrapper.
The path then failed to justify, four bans later the search gave up, and a
hole that used to be justified was kept.  `expand_vertex` now offers the
ACI, ACI-modulo and relation edges *before* the congruence one; each is a
single step the checker replays, while the congruence edge between two
permuted n-ary applications is almost always a dead end.

**Measured** on the diagnostics, against the binary the cancelled
`chk1200n` run used:

| | before | after |
|---|---|---|
| d1 checking | 7/7, 0.52 s | 7/7, 0.50 s |
| d1 elaboration | 6/7, 60.0 s (one hole hit the 60 s cap) | **7/7, 0.56 s** |
| d2 checking | 2/3, 34.4 s | **3/3, 0.14 s** |
| d2 elaboration | 1/3, 33.5 s | 1/3, **0.60 s** |
| d4 | 3/3, 3/3 | 3/3, 3/3 |
| d5 | 6/6, 5/6 | 6/6, 5/6 |
| d3, d8, d9 | unchanged | unchanged |

d2's two kept holes and d3's one are not list-rule cases; they remain
open.  The full test suite passes, `tests/rare/list-empty.rare` included,
which is now pinned by the set-form path rather than by the variants.

**Both encodings are kept and selectable**, `--rare-list-encoding
set-form|chain` (default `set-form`; the isolated hole worker gets it
passed through, and the prepared database is keyed on it alongside the
seeding and the sort guards).  `chain` is the §29 compilation: the
argument chain plus one variant per subset of the list parameters.  It has
to stay, and not only for the comparison -- the set form is available only
because `and` and `or` are ACI, so the order-sensitive n-ary operators
(`str.++`, `re.++`, bv `concat`) and every other list rule go through the
chain path under either setting.  Measured side by side on the
diagnostics:

| | `set-form` | `chain` |
|---|---|---|
| d2 checking | 3/3, 0.17 s | 1/3, 60.2 s |
| d2 elaboration | 1/3, 0.85 s | 1/3, 60.2 s |
| d3 elaboration | 0/1, 0.16 s | 0/1, 2.85 s |
| d5 elaboration | 5/6, 0.26 s | 5/6, 0.48 s |
| d1, d4, d8, d9 | — | same verdicts, 5-100% slower |

`tests/rare/list-empty.rare` is checked under both.

**Still open**, unchanged from §29: a list parameter that binds several
arguments is proved but cannot be *cited*, since a `rare_rewrite` step has
no form for it.  Commit 18d43bf0 writes such an argument as a `rare-list`
term, which the parser and printer now round-trip, so the form exists in
Carcara; whether it belongs in Alethe is a proof-format decision.

## 31. What the encodings actually buy, and what cvc5's holes are blocked on (2026-09-20)

Both list encodings are now selectable (`--rare-list-encoding`), so the
question "does the set form help?" can be asked of a corpus rather than of
the diagnostics.  Two measurements, one of them the more useful for being
negative.

### cvc5's kept holes are not blocked on rules

Reading every `kept as trusted` line of the `chk1200h2` run (9,812
benchmarks, two checking passes, 120,841 kept-hole events):

| reason | events |
|---|---|
| per-hole time budget exhausted during egglog | 60,790 |
| worker killed: memory allocation failed (8 GB) | 37,564 |
| e-graph grew past the tuple cap | 17,079 |
| the proof's own hole budget ran out | 4,465 |
| every goal fallback failed (rounds exhausted) | 933 |

Every one of the 17,079 "egglog check failed" holes says *grew past the
bound*; **not one** says the goal was unreachable after the rounds.  So
0.8% of cvc5's kept holes are coverage misses and the rest are resource
kills.  A better rule encoding cannot move that corpus: no cvc5 hole is
waiting for a rule.  What would move it is saturation cost, and there the
set form is the wrong lever -- it *adds* to the e-graph rather than
replacing the chain.

The biggest identifiable family confirms it.  Of the cap kills, 10,446
have an `or` left-hand side and 2,343 an `and`; `Referendum-PT-1000/RF-06`
is typical, four holes that flatten a nested `or` over 1,000 literals.  At
the production cap (3M tuples) both encodings keep all four; at 30M both
prove all four, the chain in 58 s and the set form in 72 s.  The set form
is not what those holes need, and the cap is.

### veriT is where the list rules matter

The shapes that need an empty `:list` are veriT's, not cvc5's: the
diagnostics move from 2 of 3 to 3 of 3 on d2's checking (34.4 s to 0.14 s)
and the corpus run of §30 loses a quarter of its kept holes.  The corpus
A/B under one binary is running as this is written.

### The remaining diagnostic failures

d3 and d5's sixth shape -- the complementary pair under a `not` -- are
closed by commit be7d8658 (the constant intermediate).  d2's `bool_simplify`
holes are the one shape left, and they are a certificate-search failure,
not an engine one: checking proves them in 0.2 s, the reconstruction gives
up in the same time.  It is not a budget (256, 1024, 4096 and 16384 states
all fail identically, and so do 4, 32 and 256 rejustification attempts) and
not a verification rejection (nothing is logged as a rejected step).  The
path simply is not in the candidate graph: the derivation rewrites *inside*
a nested implication, so no rule instance grounds at the root, and the only
way to walk to a class-mate that differs deep inside is to substitute a
subterm.  Two widenings were tried and neither moves it.  Substituting an
arbitrary class-mate rather than a constant changes nothing: grounding the
alternative's children goes through the preferred representatives, which
are the goal's own subterms.  Counting only *wrapped* positions against the
substitution bound -- the encoding spends six nodes on a variable, so 32 raw
positions cover barely two arguments of a real term -- reaches deeper but
also changes nothing, and costs 2 to 3 times the elaboration time on the
small proofs, so it was dropped.

The diagnosis that remains is that the intermediate terms never become
vertices at all.  `ground` binds every pattern variable to
`self.representative(class)`, so a rule instance is spelled with the goal's
own subterms; a derivation that rewrites inside a nested implication
produces no instance anchored at the root, and the root enode itself never
changes, since rewriting merges the inner class rather than replacing it.
Grounding a match through the matched enode's own children, instead of the
class's preferred representative, is the change that would give the search
those vertices.

## 32. The cancelled run, read (2026-09-20)

§31's taxonomy came from `chk1200h2`, which is complete but runs neither
the normalizer nor the elaboration pass.  `chk1200n` does both; it was
cancelled after QF_UF, and its partial `results.json.gz` covers **951
proofs**, which is enough to say what the current pipeline actually leaves
behind.

| | holes |
|---|---|
| after hoisting | 513,596 |
| plain checking pass: proved / kept | 510,626 / 2,970 |
| normalized pass: proved / kept | 512,953 / **643** |
| closed by the normalizer alone, no egglog | 162,605 (31.7%) |
| remaining in the elaborated proof | **5,346** (1.0%) |

The elaborated proofs re-check: **390 valid**, 532 holey, 2 error, 10 with
no cvc5 proof, 17 tasks cut off.  Of the 532 holey ones, 23 are one hole
short of valid and 439 are within five.  Elaboration cost 15,298 s of wall
across the 951 proofs and the re-check 2,202 s.

The normalizer is worth more than any cap: it closes a third of all holes
outright and cuts the checking pass's kept holes by 78%.  §31's conclusion
stands but its emphasis was wrong -- cvc5's holes are not blocked on rules,
and the largest slice of what `chk1200h2` called a cap kill never reaches
egglog at all once the normalizer runs (`Referendum-PT-1000/RF-06`: four
holes, 50 s to fail at the production cap, 72 s to succeed at ten times it,
**0.003 s** to close under `--hole-prenormalize`).

What the residue is made of, across both passes:

| reason | holes |
|---|---|
| e-graph grew past the tuple cap | 2,507 |
| no certificate found (the search) | 2,214 |
| per-hole time budget | 1,240 |
| the reconstructed steps were rejected by the checker | 517 |
| memory | 430 |
| the proof's hole budget | 16 |

So the certificate search, not the engine, is now the largest addressable
class: 2,214 + 517 against 2,507 cap kills.  And all 517 rejections are one
bug, fixed in 1feffecc: the reconstruction emitted `(ite true t u) = t` as
an `evaluate` step, and Carcara's evaluator decides an application of
interpreted operators to *values* -- it needs every argument to evaluate,
so an `ite` with arbitrary branches is not one of those.  It is the first
case of `ite_simplify`, which is what the step now cites.

## 33. The encodings, side by side (2026-09-20)

### veriT, one binary, 98 proofs, normalizer on in both arms

| | holes | proved | kept | skipped | time |
|---|---|---|---|---|---|
| `set-form` | 17,067 | **10,761** | **1,370** | **4,936** | 9,893 s |
| `chain` | 17,067 | 5,866 | 1,558 | 9,643 | 10,606 s |

Same binary, same folded proofs, same budgets, the two arms run one after
the other so they never shared the machine.  The set form proves 83% more
holes, keeps 12% fewer, and -- the number that explains the other two --
skips half as many.  Both arms are budget-bound at 300 s per proof, so the
proof runs out of budget with two thirds of its holes untried.  Per proof
the set form keeps fewer holes on 39 and more on 10, and is more than 10%
faster on 35 against 1.

**This is a throughput win, not a coverage win.**  The residue reasons of
the two arms contain *no* "goal not reached" at all: on the holes each arm
got to, `chain` -- with its empty-list variants -- reaches the same goals
the set form reaches.  What it does not do is reach them as cheaply.  The
cost is where the two encodings differ: a rule with a `:list` parameter
compiles to one set-form rule but to 2^k-1 chain variants, and on an n-ary
`and`/`or` a list parameter has to bind a *segment*, which the chain can
only produce by re-associating the argument chain.  That is why the gap
shows up on veriT and not on cvc5: measured per hole, 59% of the folded
veriT holes contain an `and`/`or` of arity 3 or more, against 3% of cvc5's
theory-rewrite holes, 76% of which contain no `and`/`or` at all.  The
earlier reading of this table -- that `chain` loses on the empty-list case,
and a depth-based reading of the same difference -- are both wrong.

### cvc5, the cap-kill sample

Three proofs whose `chk1200h2` residue was entirely growth-cap kills, at
the production cap and at ten times it, with and without the normalizer:

| proof (holes) | plain, 3M | normalizer, 3M | normalizer, 30M | normalizer, 3M, `chain` |
|---|---|---|---|---|
| RC-06 (76) | 66 proved, 10 kept, 283 s | 73, 3, 240 s | 73, 3, 240 s | 73, 3, **159 s** |
| v25_problem_2__029 (108) | 106, 2, 81 s | 108, 0, 17 s | 108, 0, 19 s | 108, 0, 18 s |
| problem__006 (102) | 100, 2, 60 s | 102, 0, 60 s→4 s | 102, 0, 4 s | 102, 0, 4 s |

Three readings.  The normalizer removes the residue and cuts the pass by
3 to 15 times.  **The ten-times cap adds nothing once the normalizer is
on** -- identical verdicts, identical time -- so the 17,079 cap kills of
§31 are not a cap problem.  And `chain` is no worse than the set form here
and sometimes faster (RC-06, 159 s against 240 s), which is the same
conclusion §31 reached from `RF-06`: cvc5 does not need the set form.

So the two producers want different things, and the run submitted as
`enc4` measures exactly that on cvc5 at scale, four configurations over one
hoisted proof per benchmark.

## 34. Coarse holes from the producer: veriT's preprocessing (2026-09-20)

The folded veriT holes of §33 are made by Carcara: `--pipeline fold` glues a
chain of `*_simplify`/`ac_simp` steps back together after veriT has already
spelled it out.  veriT can print the hole itself, which is both cheaper and
honest about where the granularity comes from.  The vendored copy in
`verit-2026.05/` now has

```
--proof-coarse-preprocessing
```

Its patch, against the 2026.05 sources, is kept in
`~/exp/egglog-holes/verit-coarse-preprocessing.patch`.

### What it does

`src/pre/pre.c` has two parallel pipelines, `pre_process` (no proof) and
`pre_process_array_proof` (proof).  The option does not switch between them.
Each stage of the proof pipeline still runs, unchanged, but inside a
subproof whose steps are thrown away (`proof_subproof_begin` ...
`proof_subproof_remove`), and what is logged in its place is one step

```
(step tN (cl (= F G)) :rule hole :args ("preprocessing" "<stage>"))
```

followed by the same `equiv_pos2` + resolution the detailed pipeline ends
with.  So the transformation, the formula it produces, and the search that
follows are bit for bit what they are without the option; only the
justification changes.  The stages that get a hole are `lang_red` (n-ary
and distinct elimination), `simplify_formula` (every call site, including
the ones inside `pre_ite_proof` and `pre_quant_ite_proof` and the one in
instance preprocessing) and `eq_rewrite`.  `bfun_elim`, `ite_intro` and
skolemization already log one step each and are left alone, and **let
elimination keeps its derivation**: its equivalence is a substitution, not a
rewrite any RARE rule states, and its `let` step is one Carcara checks
natively, so a hole there can only lose.

The `hole` rule is new on the veriT side (`ps_type_hole`), carries no
premises, and prints a tag Carcara matches on.  `"preprocessing"` joins
`THEORY_REWRITE_TAGS`, so the whole existing pipeline -- `--hole-check-only`,
elaboration, `hoist` -- treats these holes exactly like cvc5's.

### That the search is untouched, measured

`gensys_icl328` (QF_UF, QG-classification), same binary, `--proof-prune
--proof-merge`, rule histograms of the two proofs:

| | detailed | coarse |
|---|---|---|
| `resolution` | 6043 | 6043 |
| `and_pos` / `and` / `or` / `not_and` / `not_not` | 733 / 200 / 98 / 110 / 110 | identical |
| `eq_transitive` / `eq_congruent` / `eq_reflexive` / `contraction` | 1381 / 113 / 30 / 94 | identical |
| `cong` + `refl` + `trans` + `ac_simp` + `*_simplify` + `let` | 4454 | 0 |
| `hole` | 0 | 135 |
| steps | 15,059 | 10,731 |

Every search-level count is the same; 4,454 preprocessing steps become 135
holes.

### What the holes are worth

Checked through the RARE/egglog pipeline (8 workers, 20 s per hole, the
production caps), `gensys_icl328`: **123 of 135 holes proved in 6.8 s**.
The 12 kept split 6 `let_elim` and 6 `simplify_formula`, all of them the
large ones -- a `let_elim` hole is a substitution over a whole assertion,
which is not a rewrite any RARE rule states.

Over 40 benchmarks -- a slice of QG-classification plus the QF_UF, QF_LIA
and QF_LRA eval sets -- 32 give an unsat proof and **528 holes, 456 proved
(86%), 72 kept, none skipped** (with let elimination left detailed; when it
was a hole too the same set gave 578 holes, 469 proved, 81%, and 24 of the
109 kept were `let_elim` -- dropping it removes 50 holes and 37 of the
residue).  The shape is uneven and worth keeping in view:

- whole proofs close: `BART-PT-020__RC-00` 144/144, `BART-PT-050__RC-05`
  49/49, the Bromberger slack benchmark 11/11, `gensys_icl328` 119/125,
  `gensys_icl077` 125/133;
- the QF_UF hwbench family produces **no holes at all** -- veriT's
  preprocessing does nothing there, so there is nothing to make coarse;
- the residue concentrates in QF_LRA/QF_LIA with heavy arithmetic
  preprocessing: `clocksynchro_*.induct` 0/2,
  `ReachSafety-Loops__deep-nested-O0` 1/7, the two Heizmann proofs 11/25
  and 17/28.

The residue is 37 `simplify_formula` and 5 `eq_rewrite`, plus per-hole
budget kills at 20 s on the large ones.  There is one cause, not two: a hole
that covers a whole assertion is too big for one attempt, either past the
growth cap or past the budget.  A per-assertion `simplify_formula` hole is
much coarser than a cvc5 theory-rewrite hole, and the natural next knob is a
bound on how much a single hole may cover -- the analogue of the fold pass's
`--fold-limit`, but at the point the derivation is made.

### Bounding how much one hole covers

A hole per stage per assertion is very coarse, and the residue above is
entirely holes that are too big for one attempt.  `--proof-hole-size=N`
bounds it, in DAG nodes:

```
--proof-coarse-preprocessing --proof-hole-size=50
```

The stage still runs once, on the whole assertion, so the result is
unchanged.  What changes is how its equivalence is written down:
`pre_hole_equiv` walks `src` and `dest` in parallel and, while the two have
the same top symbol and arity and the pair is bigger than the bound,
descends into the arguments that differ and puts the pieces back together
with one `cong` step.  A hole is emitted where the pair is small enough, or
where the two sides stop having the same shape -- which is as far as
congruence can go.  Binders are never entered (that would need `bind`).

```
(step t3 (cl (= (or false (f A) (f A)) (f A)))   :rule hole ...)
(step t4 (cl (= (or (g A) (g A) false) (g A)))   :rule hole ...)
(step t5 (cl (= (and true (h A)) (h A)))         :rule hole ...)
(step t6 (cl (= (and (or false (f A) (f A)) ...) (and (f A) (g A) (h A))))
     :rule cong :premises (t3 t4 t5))
```

Over the same 40 benchmarks, at `N = 50`, leaving out one outlier treated
below (31 proofs):

| | holes | proved | kept | time |
|---|---|---|---|---|
| `N = 0` | 521 | 455 (87.3%) | 66 | 571 s |
| `N = 50` | 1,804 | **1,729 (95.8%)** | 75 | **500 s** |
| `N = 50` + normalizer | 1,804 | **1,745 (96.7%)** | 59 | **281 s** |

Bounding the hole buys 8.5 points of closure and costs *less* wall-clock,
because what it removes is the 20 s each impossible whole-assertion hole was
burning.  On the two worst proofs:

| proof | holes, N=0 | proved | holes, N=50 | proved |
|---|---|---|---|---|
| `clocksynchro_7clocks.induct` | 2 | **0** | 52 | **51** |
| Heizmann `bubblesort` | 25 | 11 (44%) | 900 | **851 (95%)** |

It is not free: the `cong` glue is steps (Heizmann 2,562 -> 3,575), and on a
proof with many rewrites the many small holes cost more wall-clock in total
than a few impossible ones (Heizmann 34 s -> 228 s).  But it is time spent
on goals that close.

**The outlier, and what it says about the knob.**
`ReachSafety-Loops__deep-nested-O0` goes from 7 holes to **16,236**, and the
300 s per-proof budget gets through 5,497 of them -- 18 kept, the other
10,721 never attempted.  The bound is not what produces that number: at
`N = 200` and at `N = 1000` the count is the same 16,227, because the
formula is a deep spine with a separate small rewrite hanging off nearly
every level.  Descending the spine, each differing child is already far
below the bound, so the bound never gets to bundle anything.  Its holes do
not fail, there are simply too many of them for the budget: for this shape
the knob to turn is the budget, not the granularity.  Given 1,200 s instead
of 300 s, the same proof closes **16,213 of 16,227 holes (99.9%) in 854 s**,
the 14 left over being per-hole budget kills -- against 1 of 7 at `N = 0`.

**What it cannot split.**  When the stage rewrites the *root* into a
different shape, congruence has no footing.  The one hole left in
`clocksynchro_7clocks.induct` is `ac_simp` flattening a left-nested binary
`and` chain into a flat 159-ary one: arity 2 against arity 159 at the root,
so the split stops immediately and the hole is the whole assertion.  egglog
dies on it either way (38,215,762 tuples against a 3M cap at 180 s).  The
hole normalizer closes it in 0.02 s -- it is exactly an `aci_simp` -- so
with `--hole-prenormalize` that proof goes **52 of 52**.

### Giving the unbounded holes room: it is the cap, not the clock

If the bound is off, a proof has few, very large holes, and the 20 s per
hole of the production runs was chosen for the opposite case.  Given 300 s
per hole and ten times the caps (30M arith / 5M plain), on the six
QG-classification proofs that had residue:

| proof | holes | plain | + normalizer | plain | norm | at 20 s / 3M |
|---|---|---|---|---|---|---|
| `dead_dnd001` | 8 | 6 | 7 | 16 s | 3.5 s | 3 |
| `gensys_icl037` | 65 | 63 | 64 | 12 s | 3.2 s | 61 |
| `gensys_icl077` | 133 | 129 | 130 | 27 s | 6.5 s | 125 |
| `iso_icl022` | 13 | 11 | 12 | 17 s | 3.4 s | 8 |
| `iso_icl062` | 10 | 8 | 9 | 17 s | 3.5 s | 5 |
| `iso_icl102` | 10 | 7 | 8 | 18 s | 3.4 s | 5 |

Nothing here times out.  Every kept hole ends "the e-graph grew past the
bound", at 5.6M to 13.3M tuples against the 5M plain cap -- the extra time
only lets a hole *reach* the cap sooner.  Raising it settles them:

| proof | plain cap | plain | norm | peak RSS, plain | peak RSS, norm |
|---|---|---|---|---|---|
| `iso_icl102` | 5M | 7/10 | -- | | |
| | **20M** | **10/10**, 35 s | | | |
| | 50M | 10/10, 37 s | | | |
| `dead_dnd001` | 5M | 6/8, 30 s | 7/8, 4.9 s | 1.5 GB | 0.8 GB |
| | **20M** | **8/8**, 33 s | **8/8**, 6.1 s | 2.6 GB | 1.3 GB |
| `iso_icl062` | 5M | 8/10, 26 s | 9/10, 4.0 s | 1.8 GB | 0.8 GB |
| | **20M** | **10/10**, 30 s | **10/10**, 4.8 s | 3.1 GB | 1.3 GB |

So for whole-assertion holes on this corpus: **cap 20M plain / 120M arith,
about 3 GB for one worker, and 50M buys nothing over 20M**.  The normalizer
is worth more here than at fine granularity -- it closes one extra hole in
every proof at the 5M cap, and where both succeed it is five times faster on
half the memory, because a whole-assertion hole is very often pure ACI that
`aci_simp` settles without building an e-graph at all.

The exception is the deep-nested shape.  `ReachSafety-Loops__deep-nested-O0`
unbounded is 7 holes, and at 300 s per hole with the 30M/5M caps it proves
**1**: five holes exhaust the 300 s, one dies allocating past a 9 GB worker
limit.  Bounded at `N = 200` the same proof is 16,213 of 16,227.  That is
the whole argument for running both sets.

### `--expand-let-bindings` is a cvc5 flag

Checking these proofs with `--expand-let-bindings`, as the cvc5 runners do,
makes veriT proofs that contain `let` steps come out `invalid`: the flag
expands the very `(let ...)` term the `let` rule is about, and the rule then
reports the premise is "of the wrong form, expected `(let ...)`".  Dropped,
the same proofs are `valid`.  Nothing to do with veriT or with this option;
a veriT runner must not pass it.

### The `eq_rewrite` residue is a cap kill, not a missing rule

`eq_rewrite` is veriT's `pre_eq`, on in QF_IDL/RDL/LRA/LIA/LIRA: it replaces
every arithmetic equality by a conjunction of two inequalities, which
veriT justifies with `la_rw_eq`, `(= (= t u) (and (<= t u) (<= u t)))`.
RARE states the same rewrite the other way round -- `arith-eq-elim-int` and
`arith-eq-elim-real` give `(and (>= t s) (<= t s))` -- and `arith-elim-leq`,
`(= (<= t s) (>= s t))`, bridges the two orientations, so the engine does
have what it needs.  A minimal hole `(= (= x y) (and (<= x y) (<= y x)))`
over two reals is proved in **0.19 s**.

What fails is the size.  An `eq_rewrite` hole is a whole assertion: on
`clocksynchro_7clocks.induct` it is 33 KB of arithmetic in which every
equality splits at once, and the run ends "the e-graph grew past the bound
(14,157,290 tuples, cap 3,000,000)".  The same proof's `lang_red` and
`simplify_formula` holes, also whole assertions, are killed by the 20 s
per-hole budget.  So the arithmetic residue here is the granularity, not the
rule set -- the same conclusion §31 reached about cvc5's cap kills, arrived
at from the other side.

## 35. `enc4` read at three quarters: the normalizer decides, the encoding does not (2026-09-20)

The four checking configurations over cvc5 proofs -- the two `:list`
encodings, each with and without `--hole-prenormalize` -- on one hoisted
proof per benchmark, 600 s per pass, 60 s and 8 GB per hole.  QF_UF is
complete (4,361 benchmarks, 4,127 of them checked: 36 gave no complete proof
in cvc5's 60 s, 198 failed to hoist), and so is QF_LIA (4,748 benchmarks,
2,535 checked).  QF_LRA is 16 proofs in of 703.

### QF_UF, 4,127 proofs, 2,240,247 holes

| | proved | kept | skipped | closed by the normalizer | time |
|---|---|---|---|---|---|
| `set` | 2,232,298 (99.6%) | 6,911 | 1,038 | -- | 17.65 h |
| `chain` | 2,232,207 (99.6%) | 6,954 | 1,086 | -- | 18.16 h |
| `nset` | **2,238,956 (99.9%)** | **576** | 715 | 683,858 | **11.37 h** |
| `nchain` | 2,238,870 (99.9%) | 586 | 791 | 683,858 | 11.75 h |

### QF_LIA, complete: 4,748 benchmarks, 2,535 checked, 1,818,598 holes

Only 53% of the set gives cvc5 a complete proof in 60 s; 2,205 benchmarks
produce none at all, and 24 more fail to hoist.

| | proved | kept | skipped | closed by the normalizer | time |
|---|---|---|---|---|---|
| `set` | 1,105,961 (60.8%) | 17,136 | 695,501 | -- | 54.9 h |
| `chain` | 1,106,203 (60.8%) | 17,163 | 695,232 | -- | 55.2 h |
| `nset` | **1,804,052 (99.3%)** | **3,981** | 9,411 | 1,399,159 | **16.4 h** |
| `nchain` | 1,804,547 (99.2%) | 4,003 | 10,048 | 1,399,718 | 16.5 h |

### QF_LRA, just started: 16 proofs, 2,331 holes

| | proved | kept | closed by the normalizer | time |
|---|---|---|---|---|
| `set` | 2,324 (99.7%) | 7 | -- | 0.08 h |
| `chain` | 2,323 (99.7%) | 8 | -- | 0.08 h |
| `nset` / `nchain` | **2,331 (100%)** | **0** | 1,744 | 0.02 h |

### All three so far: 4,061,176 holes

| | proved | kept | skipped | time |
|---|---|---|---|---|
| `set` | 3,340,583 (82.3%) | 24,054 | 696,539 | 72.6 h |
| `chain` | 3,340,733 (82.3%) | 24,125 | 696,318 | 73.4 h |
| `nset` | **4,045,339 (99.6%)** | **4,557** | 10,126 | **27.7 h** |
| `nchain` | 4,045,748 (99.6%) | 4,589 | 10,839 | 28.3 h |

The normalizer closes **2,084,761 holes, 51% of all of them**, before egglog
runs.

### The two questions the run was submitted to answer

**The encodings are a wash on cvc5.**  Per proof, `set` has the smaller
residue on 107 proofs across the three logics and `chain` on 37, with 6,534
ties.  `set` is more than 10% faster on 244 proofs and `chain` on 34.  With
the normalizer on, both differences all but vanish: 18 proofs against 2 on
residue, and on time it even tips the other way (109 proofs against 106).
This is §31 and §33 at scale: cvc5's holes are not where the set form pays,
and either encoding is a defensible default -- `set` by a nose, and never
materially behind.

**The normalizer decides everything.**  On QF_UF it takes the residue from
6,911 to 576 and the pass from 17.65 h to 11.37 h; proofs with no residue at
all go from 1,603 to 4,088 of 4,127.  On QF_LIA it is the difference between
60.8% and 99.3%, and between 54.9 h and 16.4 h, with no-residue proofs going
from 1,689 to 2,370 of 2,535.  Per proof it is better on 2,495 QF_UF and 840
QF_LIA proofs and worse on 1 and 7; faster by more than 10% on 3,685 and
2,071.  It closes 30% of the QF_UF holes and **77% of the QF_LIA holes**
without egglog running at all.

### What the residue is now made of

With the normalizer, 4,557 kept and 10,126 skipped of 4.06M holes (0.36%),
against 24,054 and 696,539 without it.  The reasons have changed class: in
the normalized arms it is **per-hole time (1,597) and memory (1,406)**
against 109 growth-cap stops, where the plain arms are 9,814 / 3,886 /
7,403.  §31's picture -- 99.2% cap kills -- was a picture of the
*un-normalized* arm, and the normalizer removes precisely that class.  The
1,406 memory deaths are the case the new `--rare-memory-soft-cap` (90% of
the hard limit in both runners) turns into a clean stop with a reason.

The plain arms' QF_LIA number carries a caveat: 695,501 of their holes were
never attempted because the 600 s pass budget ran out, so 60.8% is a
statement about equal budget, not about what they could eventually prove.
That is the comparison the run was for.

## 36. `enc4` complete, and what the read at three quarters got wrong (2026-09-21)

The run finished 2026-09-21 01:43 (9,812 tasks; results synced to
`~/exp/results/egglog-holes/enc4`, md5 identical to the cluster copy).  The
final numbers are in the report addendum (`~/exp/egglog-holes/report`,
§7, tables from `make-enc4.py`); the totals over the three logics:

| | holes | proved | kept | unattempted | closed by norm. | hours |
|---|---|---|---|---|---|---|
| `set` | 5,441,531 | 3,847,142 (70.7%) | 39,351 | 1,555,038 | -- | 112 |
| `chain` | 5,441,531 | 3,843,654 (70.6%) | 39,484 | 1,558,393 | -- | 113 |
| `nset` | 5,440,377 | **5,347,231 (98.3%)** | **17,443** | 75,703 | 3,129,633 | **50** |
| `nchain` | 5,441,531 | 5,346,874 (98.3%) | 17,436 | 77,221 | 3,130,192 | 50 |

Coverage: 7,405 of 9,812 benchmarks give a complete cvc5 proof, 7,171
hoist, 7,192 reach the passes, and **6,775 come out with no trusted rewrite
under `nset`** (91% of the proved, 94% of the ran; a portfolio over the four
adds six).  QF_LRA, which §35 had not seen: 703 benchmarks, 537 proved, 525
hoisted, 317 fully justified; 1,382,686 holes, `set` proves 36.8% with
858,499 unattempted, `nset` 94.3% with 12,886 kept and 65,577 unattempted,
1,046,616 closed by the normalizer.  The encodings stay a wash there too
(`set` smaller residue on 96 proofs, `chain` on 20, 414 ties; with the
normalizer 30 / 5 / 495).

Three things the three-quarter read, and the first draft of the report
addendum, misrepresented; the raw records were re-tabulated
(`scratchpad/xcheck.py` of the 2026-09-21 session) to settle them:

- **The 234 proofs between proved and hoisted are not hoist timeouts.**
  207 of them are the upfront rejections of the full run's Table 2
  (`pivot was not found in clause`; 195 in `QG-classification/qg5`, one in
  `qg6`, two `2018-Goel-hwbench`, seven QF_LRA, two QF_LIA): `hoist_rc=1`
  and every pass `rc=1` within seconds.  Only 27 hit the 300 s hoist limit;
  21 of them were checked unhoisted (none fully justified, all but two cut
  at 700 s in every pass) and 6 (QF_LIA, 1--3k holes) never printed a
  summary in any pass.  So 213 proved proofs contribute nothing to the pass
  columns, and 7,405 − 213 = 7,192 is the `ran` denominator.
- **Five tasks have no record at all** -- `terminationreason=memory` at the
  60 GB job limit, 750--2,300 s in, i.e. during the checking passes, and the
  runner's stdout was lost with them: `QF_UF_hanoi.2.prop1_ab_br_max`,
  `SpamAssassin-loop-O0`, `fragtest_simple-O0`, `prp-2-17`, `prp-3-18`.
  They count as "no proof" in the coverage table although three had
  complete proofs in the full run (1,175 / 2,938 / 11,162 holes).  Eight
  workers at 8 GB address space each can exceed the job's 60 GB; the soft
  cap at 7.2 GB (57.6 GB over eight) is also only just under it.
- **`benchmark32_linear-O0`** lost its summary in `nset` only (700 s
  external kill), not in both normalized passes; `nchain` printed one (559
  closed by the normalizer, 595 unattempted), which is why the `nset` hole
  and closed counts are 1,154 and 559 short of `nchain`.

And two caveats on the residue table that the first draft did not state:
the runner logs at most 200 `kept as trusted` lines per pass, so the reason
tally covers 36,400 of 39,351 `set` kept holes and 15,836 of 17,443 `nset`
(four or five proofs per pass hold the rest); and "killed after Ns" is two
reasons, the per-hole hard limit (`set` 15,276 / `nset` 4,899) and the
pass's 600 s budget expiring mid-hole (2,748 / 784) -- the latter is a
budget loss and belongs with the unattempted holes.  The run had no
`--rare-memory-soft-cap` (added to both runners after submission); its
10,013 memory deaths under `nset` remain reasonless `SIGABRT`s.

## 37. What the QF_LRA residue of `enc4` is made of (2026-09-21)

With the normalizer on, QF_LRA holds 12,886 of the 17,443 kept holes and
65,577 of the 75,703 unattempted; 8,607 of its kept holes are memory kills,
concentrated in `sc` (4,009), `tta_startup` (1,840), `sal/pursuit` (1,062)
and `uart` (909), and the unattempted ones sit in 54 proofs of 11k--13k
holes each that the 600 s pass cannot get through.

`sc-14.base.cvc` reproduced locally (same cvc5 build, carcara cb6161af,
two workers, 4 GB per hole, 1200 s): the normalizer closes 3,608 of 5,281
holes, egglog proves 1,406 more, and **all 267 kept holes die of memory and
all have one shape**,

    (= (<= s t) (>= (+ (* -1 s') t') 0.0))

i.e. cvc5's arith-post rewrite of a `<=` atom into its `>=` mirror over the
negated difference, where the polynomial contains an `ite` (the min/max
encodings of these benchmarks).  Two separate facts, checked on a
two-assumption toy problem (`scratchpad/sc14/ite.alethe`, `plain.alethe`):

- **The normalizer does not close the shape even without the `ite`** ("0 of
  1 closed, 1 rewritten"; egglog proves it in 0.29 s).  `relation_step`
  keeps the relation symbol and scales `<=`/`>=` only positively, so `(<= P
  c)` and `(>= -P -c)` never meet.  `comp_simplify` already certifies
  `(>= a b) => (<= b a)`, `(> a b) => (not (<= a b))` and `(< a b) => (not
  (<= b a))`, so orienting every relation to `<=` (and `not <=`) before
  `poly_simp_rel` is a normal form the checker can cite.
- **With the `ite` inside the polynomial egglog allocates 4 GB within 10 s**
  and is killed; with a fresh variable in its place it is proved in 0.29 s.
  The arithmetic rules descend into the `ite` and its condition (itself a
  relation), and the growth caps do not catch a single allocation.

How much of QF_LRA this is (hoisted holes, by top-level operator pair of
the goal):

| proof | holes | `(<=)=(>=)` | `(<)=(not)` + `(not)=(>=)` | goals with `ite` |
|---|---|---|---|---|
| sc-14 | 5,281 | 706 (267 kept) | 1,365 | 3,280 |
| gasburner-prop3-19 | 1,703 | 342 | 320 | 588 |
| tta_startup simple_startup_10nodes.abstract.base | 2,178 | 323 | -- | 322 |
| pursuit-safety-14 | 1,742 | 329 | 218 | 603 |

So the mirror shape alone is 13--20% of every one of these proofs, the
negated-relation shapes another 10--25%, and today each of them costs an
egglog run (0.3 s when it works, 60 s and 8 GB when the `ite` is in it).
Closing them in the normalizer through `comp_simplify` takes those runs out
of the 600 s budget that the 54 giant `sc`-style proofs exhaust, and
removes the memory-kill class at its source; making `ite` an opaque atom
for the arithmetic rules is the engine-side fix for whatever is left.

## 38. A numeric `ite` is an atom for the polynomial normalizer (2026-09-21)

The engine-side fix for §37.  `declare_opaque_arith_poly_rules` already
turned every declared function of numeric result sort into an `AAtom` of the
polynomial normalizer; `ite` is an operator, not a function, so the
normalizer's `arithCopyOf` demand on a `(Mk (@ite ...))` term had no rule
and stayed open, the goal's relation key was never computed, and the main
rounds ran the arithmetic and `ite` rules into the `ite`'s condition (a
relation) and branches until a single 4 GB allocation failed.  Now a numeric
`ite` is an atom too, keyed on the `SortInt`/`SortReal` relation of the
term: with `--rare-sort-guards` those relations are seeded from the goal and
propagated per operator (`from_branch` for `ite`); without them only the
goal's own `ite` subterms are seeded (`sort_premises(.., only_ite)`), which
is all the atom rule needs.  Reconstruction reads the `ite` atom's sort off
its `then` branch (`ArithSorts::term_is_int`) for the Int-tightening checks.

- Toy hole `(= (<= (+ x (ite c y z)) w) (>= (+ (* -1 x) w (* -1 (ite c y z))) 0))`:
  4 GB kill at 10 s → proved in 0.31 s, elaborated into `arith-elim-leq`,
  `poly_simp`, `poly_simp_rel`, `trans`, re-checked `valid`.  Regression test
  `a_numeric_ite_is_an_opaque_atom_for_the_normalizer` (both guard modes;
  fails on the previous atom rules).
- `sc-14.base.cvc` (two workers, 4 GB per hole): checking **5,281/5,281 in
  120 s**, was 5,014 with 267 memory kills in 924 s.  Elaboration justifies
  5,273 in 162 s; the 8 misses are `(= (= false x) (not x))` and `(= (xor
  false x) x)`, "no certificate found" -- a reconstruction gap, not the
  engine.  The elaborated proof re-checks in 3.8 s, `holey`.
- Full suite green (272 lib tests).

What the elaborated sc-14 still carries, and what it says about §37's
first item: 195 `TRUST_THEORY_REWRITE` holes *inside* certificates, every
one the strict-relation step `(= (> P 0) (not (<= P 0)))` that reconstruction
emits as a hole tagged `arith_poly_norm_rel`.  That step is exactly
`comp_simplify`'s `(> t1 t2) ⇒ (not (<= t1 t2))`.  So the relation
orientation that §37 asked the normalizer for is not a `poly_simp` /
`aci_simp` / `evaluate` / `distinct_elim` matter at all -- `poly_simp_rel`
requires the same operator on both sides and a same-sign scale for
inequalities -- but `comp_simplify`'s, and it is already missing from the
certificates the reconstruction emits, not only from the prenormalizer.

## 39. Relation orientation stays with the RARE rules; the certificates now cite them (2026-09-21)

Decision on §37's first item: the prenormalizer is not extended with
`comp_simplify`; the mirror and negated relation shapes are egglog's job
through the database's `arith-elim-leq`, `arith-elim-gt`, `arith-elim-lt`
and `arith-elim-int-lt`.  The same conclusion had been reached for veriT's
`comp_simplify` / `la_rw_eq` holes (§26, §34), and there is no separate
veriT rule file: both runners read `holes.rare`, which carries these four
rules already.  So there was nothing to copy over; what was missing is that
the *certificates* did not cite them.

Why not: `expand_vertex` offers a computational edge from a vertex to its
recomputed relation form, and on `(= (> P 0) (not (<= P 0)))` that edge
lands on the target in one step, while the rule path needs two
(`arith-elim-gt`, then a congruence over `not` with `arith-elim-leq`).  The
bidirectional search takes the shorter one, and the elaborator's
`poly_simp_rel_chain` then had to spell the computation out: it routed
only `<=` and the integer `(not (>= ..))` to a `>=` form, so every strict
or negated relation fell back to a trusted `arith_poly_norm_rel` step --
the 195 certificate-internal holes of §38.

`to_geq` now returns a *polarity* with the `>=` term: `>` and real `<`
route to the negation of a `>=` (`arith-elim-gt`, `arith-elim-lt`),
integer `<` to the tightened positive form (`arith-elim-int-lt`), and
`(not R)` routes `R` under a `cong` with the polarity flipped, a
`not_simplify` stripping the double negation when `R` was itself negated.
The chain requires equal polarities, states `poly_simp_rel` on the two
`>=` terms (under one `cong` when both are negated), and skips the pair
when both routes reach the same term.  Toy `(> P 0) = (not (<= P 0))`:
`arith-elim-gt`, `arith-elim-leq`, `cong`, `symm`, `trans`, no `hole`,
re-checks `valid`.  `sc-14.base.cvc`: **0** `arith_poly_norm_rel` steps
(was 195), 1,887 `rare_rewrite` steps -- `arith-elim-leq` 901,
`bool-double-not-elim` 377, `arith-elim-gt` 195, `arith-elim-lt` 172,
`eq-symm` 153, `ite-eq` 28 -- 5,273 of 5,281 holes justified, the proof
re-checks in 5.2 s, `holey` only by cvc5's `THEORY_INFERENCE_ARITH` and
`ARITH_STATIC_LEARN` steps.  The 8 kept holes are still the §38
`(= (= false x) (not x))` / `(= (xor false x) x)` reconstruction misses.
Full suite green.

## 40. The runners after `enc4`: records that survive a kill, a complete residue tally, and the hoist blow-up (2026-09-21)

Runner fixes (`~/exp/egglog-holes/run-holes-enc.sh`, `run-holes.sh`,
`run-holes-verit.tmpl` and its two instances), verified locally on
`sc-10.base.cvc` with tiny budgets (97 `[pfchk]` keys, histogram and sample
present):

- **Every pass prints its keys as soon as they are known** (`emit_pass_keys`
  in the checking runners; inline in `run-holes.sh`), and the proof/hoist
  keys right after hoisting.  The final block repeats them, which the
  readers' `dict(KEY.findall(log))` absorbs.  A task killed in pass three
  now keeps passes one and two; `enc4` lost five whole tasks.
- **Per-worker memory is derived from the job's:** `HOLE_MEMORY_MB =
  (JOB_MEMORY_MB - DRIVER_RESERVE_MB) / HOLE_WORKERS`, 6,000 MB for eight
  workers under 60,000 with 12,000 for the driver (the veriT `nob` arm's
  four workers get 12,750 under 63,000, not 16,000).  All workers at their
  limit no longer exceed the task's limit.
- **The residue is counted by class, completely.**  The engine now tags the
  reason at its one log site -- `hole N: kept as trusted: [class] reason`,
  `rare_hole::residue_class`: `memory`, `memory-soft-cap`, `growth-cap`,
  `hole-time`, `pass-budget`, `no-certificate`, `checker-rejected`,
  `unproved`, `signal`, `worker-error`, `other` -- and the runners emit
  `<p>_kept_<class>=N` per pass from a `uniq -c` over the tags, plus
  `<p>_kept_untagged` for an older binary, and keep a 50-line sample.
  `analyze.py` and `make-enc4.py` read the tag when present.
- **The hoisted proof is printed with term sharing.**  Every cluster
  "hoist timeout" reproduced locally is the *printing* of the hoisted proof
  without sharing exploding: `gasburner-prop3-19` (2.4 MB in) writes 12 GB
  and is killed at 300 s, `Sz32_455` (70 MB in) writes 13 GB; with sharing
  they hoist in 0.2 s to 1.9 MB and in 6.5 s to 46 MB.  The passes read the
  result with `--expand-let-bindings` as before.  `Sz32_455` then checks
  6,720 of 6,723 holes in 124 s (cluster: unhoisted, 43,270 holes, 41,771
  proved, 1,499 kept of which 183 memory), the three left being two
  growth-cap stops and one per-hole timeout; the pass's wall is 425 s,
  three hundred of them parsing and checking the 46 MB proof's other steps
  before any hole -- the per-proof budget question of §6 again.

**The passes printed unshared too (2026-09-22).**  Every hole pass ends by
printing its proof, and the runners passed `--no-print-with-sharing` to
the checking passes as well, whose output goes to `/dev/null`: the same
blow-up, paid in time inside `<p>_time` on every pass -- locally the
check-only pass of `in-de62-O0` wrote 60 GB, `Sz32_455` 16 GB,
`gasburner-prop3-19` 12 GB (and filled the disk).  The flag is now gone
from every runner's `HOLE_OPTS`; the elaborated proof is printed with
sharing and re-checked with `--expand-let-bindings` as before.  So `enc4`'s
per-pass overhead has three parts -- parsing, the upfront check of the
non-hole steps, and this print -- and only a rerun separates them.

`gasburner-prop3-19` on its shared hoist (two workers, 1,200 s): 1,497
holes, the normalizer closes 839, egglog proves 596 more; **30 per-hole
timeouts at 60 s each** and 30 unattempted behind them, no memory kill.
Those thirty goals are equalities between `@p_` names whose expansion is
what blew the unshared print up: goals over very large shared DAGs, a size
problem rather than a shape one, and the family that dominates the
per-hole-time class of `enc4` (`sal/gasburner` 835).  Open.

## 41. The `(= false x)` reconstruction miss: dead congruence edges at the class signature (2026-09-22)

The eight holes `sc-14` still kept after §39 -- `(= (= false x) (not x))`
and `(= (xor false x) x)` -- are proved by egglog in two named rules
(`eq-symm` then `bool-eq-false`; `bool-xor-comm` then `bool-xor-false`:
the rules carry the constant on the right, the holes on the left) and
still came back "no certificate found".  Each rule alone reconstructed;
the pair did not.

The search matches rule sides at a vertex's *signature*, and for a wrapped
term that is the wrapper's: `(Mk, [class of the unwrapped application])`.
The engine keeps the unwrapped terms of a class together, so at the
signature of `(= false x)` the e-matcher also finds `(= x false)` and every
other member of the class; a side matched to such a member is not the
vertex, and the search offered it as a *congruence* edge ("same signature,
so congruent").  It is no congruence: the heads or the argument lists
differ, its child proof fails, the edge is banned and the search retried,
and the bounded four rejustifications were spent on the class's other
members before the two-rule path was reached.  (First suspect, wrongly:
the toy's own `assume` steps polluting the e-graph -- `get_assumptions`
walks the node's premises only, and a clean toy failed the same way.)

Fix (`search.rs`): a matched member is offered as a congruence only when
`inner_congruence_compatible` holds -- for two wrapped applications, the
same head and argument lists of one class, one level below the wrapper;
otherwise no edge, and the member is reached by the rule that relates it.
Making `congruence_compatible` itself look through the wrapper was tried
and broke three tests: the wrapper-level congruence with unequal inner
heads is exactly what literal renormalization (`Real` to `RatConst`, a
`refl`) and the constant-substitution candidates rely on.  Also: a side
that is a bare variable is grounded to the vertex rather than the class
representative (`grounded_match` pins it), so its instance is a rule edge
out of the vertex.  The search now logs, at debug, every path edge that
fails to justify.

Result: all four shapes reconstruct and re-check `valid`; `sc-14` goes to
**5,281 of 5,281 holes justified**, the elaborated proof re-checks in 4.6 s
(`holey` only by `THEORY_INFERENCE_ARITH` / `ARITH_STATIC_LEARN`).  One
test changed its expectation: the mirrored-bounds conjunction now comes
out entirely in database rules (`eq-symm`, `arith-eq-elim-int`,
`arith-elim-leq` under `cong`) instead of `aci_simp` + `poly_simp_rel`;
the test accepts either.  Regression test
`reconstructs_flipped_eq_false_from_production_egraph` on the new fixture
`tests/rare/computational_mix/eq_false.*`.  Full suite green (273).

## 42. veriT's own holes at scale: `vb50-2` complete (2026-09-22)

The bounded arm is in: 9,812 benchmarks, veriT solving and printing a proof
whose preprocessing rewrites are holes at `--proof-hole-size=50`, then four
checking passes over that proof.  The unbounded arm (`vnob-2`) is a fifth of
the way through QF_UF.

### What veriT gives

| | proofs | holes/proof (median, mean, max) | proofs with none | normalizer closes |
|---|---|---|---|---|
| QF_UF | 4,176 of 4,361 | 17, 73, 5,049 | 219 | 98.1% |
| QF_LIA | 2,506 of 4,748 | 6, 416, 57,772 | 28 | **3.5%** |
| QF_LRA | 566 of 703 | 123, 547, 12,362 | 0 | 35.6% |

veriT misses 1,957 QF_LIA benchmarks at the 65 s limit and 116 QF_LRA ones;
55 more fail on `define-fun`, which it does not support in proof mode.

### The four configurations, `vb50-2`

| | QF_UF (305,215 holes) | QF_LIA (1,041,503) | QF_LRA (309,653) |
|---|---|---|---|
| `set` | 93.7%, 16.9 h | 69.2%, 24.4 h | 39.6%, 43.0 h |
| `chain` | 92.9%, **41.1 h** | 68.3%, 29.0 h | 38.7%, 44.5 h |
| `nset` | **98.9%**, 12.0 h | **62.2%**, 37.4 h | **70.7%**, 44.4 h |
| `nchain` | 98.1%, 36.8 h | 37.8%, 62.7 h | 66.4%, 50.4 h |

**The encoding matters here, and it did not on cvc5.**  `chain` costs 2.4
times `set-form` on QF_UF (41.1 h against 16.9 h) and proves less; with the
normalizer it is 36.8 h against 12.0 h.  This is §33's prediction at scale:
veriT's holes carry n-ary `and`/`or`, where a `:list` parameter has to bind
a segment, and that is exactly what the chain has to re-associate.  On cvc5
the same two encodings were within 1%.

**The normalizer is not universally good.**  It closes 98% of the QF_UF
holes and 36% of the QF_LRA ones, but only **3.5%** of the QF_LIA ones --
and there it *loses*, 62.2% against 69.2%, because the per-hole cost it adds
pushes 72k more holes past the 600 s pass budget.  On veriT's QF_LIA proofs
the holes are arithmetic rewrites the normal forms do not reach.

### The bounded arm was given the wrong caps

`vb50-2` inherited the cvc5 run's growth caps (3M arith / 500k plain), as
intended -- it was to run "under the same limits cvc5 gets".  The residue
says that was the wrong call for this corpus.  On QF_UF:

| | growth cap | per-hole time | memory |
|---|---|---|---|
| `vb50-2` (caps 3M/500k, 60 s) | **18,757** | 561 | 31 |
| `vnob-2` (caps 120M/20M, 120 s) | 46 | 317 | 32 |

Nearly the whole of the bounded arm's 6.3% shortfall is cap truncation, not
the granularity.

### The paired comparison, and what it is worth

On the 853 QF_UF proofs both arms have so far:

| | holes | proved | kept | proofs fully justified | time |
|---|---|---|---|---|---|
| `N=50`, `set` | 60,592 | 95.5% | 2,706 | 236 | 4.4 h |
| `N=50`, `nset` | 60,592 | 99.1% | 549 | 496 | 3.6 h |
| no bound, `set` | 51,638 | 99.3% | 373 | 619 | 10.2 h |
| no bound, `nset` | 51,638 | **99.5%** | **272** | **642** | 7.9 h |

Per proof, the unbounded arm leaves less behind on 243 and more on 45.  But
the two arms differ in three things at once -- granularity, per-hole time
(60 s against 120 s) and caps -- so this is not yet a measurement of the
bound.  Splitting does what it promised (17% more holes, each smaller); what
the comparison shows is that **the caps, not the granularity, decide the
QF_UF outcome**.  Isolating the bound needs the bounded arm rerun at
120M/20M.

## 43. Why the normalizer loses on QF_LIA: `la_rw_eq` holes, flattened and reoriented (2026-09-22)

§42 recorded that `--hole-prenormalize` closes 3.5% of veriT's QF_LIA holes
and proves *fewer* of them than plain `set-form` (62.2% against 69.2%).
Two proofs from the losing families, reproduced locally (4 workers, 300 s
per pass, the `vb50-2` caps; `scratchpad/lia/passes2.sh`, `cmp.py`), and a
set of single-hole timings say what the mechanism is.

**What the holes are.**  Almost every QF_LIA hole is veriT's `eq_rewrite`
stage, i.e. `la_rw_eq`, `(= a b)` to `(and (<= a b) (<= b a))`, under a
small context: 9,844 of the 9,850 holes of `count_up_down-1-O0` (Dartagnan)
and 1,180 of the 1,183 of `ParallelPrefixSum_safe_blmc004` (Averest).
Typical goals, sides expanded:

```
(= (and exec (= r 0))            (and exec (and (<= 0 r) (<= r 0))))
(= (not (= m79 m84))             (not (and (<= m79 m84) (<= m84 m79))))
(= (and A1 .. A7 (= 0 X))        (and A1 .. A7 (and (<= 0 X) (<= X 0))))     X = (+ F28 (* (- 1) F515) (* (- 1) F516))
(= (ite c (= 1 Y) (= 0 Y))       (ite c (and (<= 1 Y) (<= Y 1)) (and (<= 0 Y) (<= Y 0))))   Y = (ite c 1 0)
```

**What the normalizer does to them.**  The four procedures (§26) do not
eliminate an equality -- §39 left both the elimination and the orientation
of relations to the RARE rules -- so the two sides never normalize to the
same term: 4 of 9,850 close (the cluster's 36,208 of 1,041,503).  The
normalization itself is free, 0.52 s for the 9,850 holes.  What the other
9,846 get is a *rewritten* goal: `poly_simp_rel`'s relation form puts the
constant on the right and, since the rule scales an inequality only by a
positive factor, keeps the sign, so `(= 0 r)` becomes `(= r 0)` but
`(<= 0 r)` becomes `(<= (* -1 r) 0)`; and `aci_simp` flattens the nested
`(and .. (and B1 B2))` into one `and`:

```
(= (and exec (= r 0))  (and exec (<= (* -1 r) 0) (<= r 0)))
(= (not (= (+ m79 (* -1 m84)) 0))  (not (and (<= (+ m79 (* -1 m84)) 0) (<= (+ (* -1 m79) m84) 0))))
```

**What that costs egglog.**  On the 2,116 Dartagnan holes both passes
proved, the same verdicts, the normalized goal takes 1.62 times longer per
hole (p10 1.46, p90 1.78): 0.30 s median becomes 0.49 s, in a distribution
so tight (p99 0.34 s and 0.61 s) that every hole pays it.  Under the pass
budget that is directly fewer holes: 3,611 against 2,120 locally, 9,840
against 7,446 on the cluster (throughput 13.4 against 8.3 holes/s over the
23 QF_LIA proofs that exhaust the budget in both passes).  The residue is
otherwise the same: 6 and 12 memory kills on the `ite` shape, the rest in
flight when the budget ended.  On the Averest proof, whose holes carry
seven or eight Boolean conjuncts beside the equality, the factor is
**4.5** (p10 2.7, p90 6.2): `set` proves 1,181 of 1,183 at 0.96 s median,
`nset` 308 at 3.8 s, the same verdicts on the 308 both proved.

Hole `t1209` of that proof, with its real context, one worker, the
normalizer's pieces applied one at a time:

| goal | s |
|---|---|
| veriT's: `(and C1 .. C7 (= 0 P))` vs `(and C1 .. C7 (and (<= 0 P) (<= P 0)))` | 0.54 |
| the bounds in the normalizer's form, kept nested: `.. (= P' 0)` vs `.. (and (<= -P' 0) (<= P' 0))` | 0.61 |
| the bounds in the normalizer's form, flattened into the outer `and` | **3.15** |
| everything normalized (what `nset` hands egglog: context, bounds, flattening) | 3.14 |

So the normalization of the seven context conjuncts costs nothing, the
orientation of the bounds costs 10%, and the flattening of the two bounds
into the outer `and` costs six times.

Single-hole timings (one worker, `set-form`, `holes.rare`, `vb50-2` caps;
an identity hole costs 0.10 s, the child's floor):

| goal, lhs against rhs | s |
|---|---|
| veriT's, nested: `(and e (= 0 r))` vs `(and e (and (<= 0 r) (<= r 0)))` | 0.36 |
| nested, `arith-eq-elim-int`'s own shape: `(and e (= r 0))` vs `(and e (and (>= r 0) (<= r 0)))` | 0.18 |
| nested, the normalizer's bounds: `(and e (= r 0))` vs `(and e (and (<= (* -1 r) 0) (<= r 0)))` | 0.45 |
| flat, eq-elim's shape: `(and e (= r 0))` vs `(and e (>= r 0) (<= r 0))` | 0.55 |
| flat, the normalizer's (what `nset` hands egglog): `(and e (= r 0))` vs `(and e (<= (* -1 r) 0) (<= r 0))` | 0.63 |
| Averest's `P = F28 - F515 - F516`: nested veriT / nested normalizer bounds / flat eq-elim / flat normalizer | 0.54 / 0.59 / 0.91 / 1.10 |
| the same with 1, 4 and 8 Boolean conjuncts | unchanged |

Two ingredients, both in the normalizer's definition, of very unequal
weight:

- *Flattening* is the cost: 1.4--1.9 times with a trivial context, six
  times with Averest's.  `arith-eq-elim-int` rewrites the equality to
  `(and (>= ..) (<= ..))`; against veriT's nested right side that is the
  inner `and` exactly and the outer `and` is a congruence, so the ordinary
  rounds prove the goal.  Against the flattened side the ordinary rounds
  do not, and the goal walks the fallback ladder (§30: the arithmetic
  plans first, the relation keys for every relation atom, the set form
  last), until the set-form conversion absorbs the inner `and` into the
  outer set and matches the two sets member by member; every plan on the
  way is paid on the whole context, which is why the factor grows with
  what the context holds.
- *Orientation* is minor: 10% on Averest's polynomial bounds, up to 2.5
  times only on atom bounds, where `(<= (* -1 r) 0)` reaches `(>= r 0)`
  through the polynomial relation canonicalization (`arith-elim-leq` gives
  `(>= 0 (* -1 r))`) while `(<= r 0)` against `(>= 0 r)` is one
  `arith-elim-leq`.

**An anomaly found on the way.**  Flat *and* in veriT's orientation is not
proved at all: `(and e (= 0 r))` against `(and e (<= 0 r) (<= r 0))` runs to
the 60 s kill, in `set-form` and in `chain`, with `(<= 5 s)` or `(<= (+ s
1) 5)` in place of `e`, and so does `(and e (= 0 r))` against `(and e (>= r
0) (<= r 0))`; the nested forms take 0.36 s, and the flat set with `(>= 0
r)` in place of `(<= r 0)` -- eq-elim's members verbatim -- 0.67 s.  So a
goal that needs one `and`-flattening *and* one relation rewrite inside the
same set is lost by the engine, while one that needs the flattening plus a
polynomial identification (the normalizer's `(* -1 r)` form) is found.
Neither pass walks into it (veriT's holes are nested, the normalized ones
are in the `-1` orientation), but it is the mechanism behind the slowdown
in its extreme form and a defect of the set-form encoding to chase.  The
files are in `~/exp/egglog-holes/local/lia-shape/`.

**The proof-level reading.**  The hole percentages are the Dartagnan
family: 22 proofs holding 503,542 holes, 48% of QF_LIA's, 9k--58k each,
21 of them exhausting the 600 s budget in both passes, so each pass proves
what its throughput allows (36.7% against 22.5% of that family).  Outside
it both passes sit at 98--100% on every family with more than 300 holes
except `rings` (49%, both), `calypto` (16.5 / 10.4), `cut_lemmas` (8.5 /
41.5) and Averest (99.8 / 82.8, the 3x shape).  Proofs with every hole
proved: `set` 1,979, `nset` 2,109; per proof `nset` is better on 192 and
worse on 62.  At the proof level the normalizer still wins QF_LIA; at the
hole level it loses because one family of very large proofs pays 1.6--3
times per hole for a rewrite that closes nothing.

**What follows.**  Two options, not exclusive:

1. Close `la_rw_eq` in the prenormalizer: an `=`-elimination case whose
   certificate is one `rare_rewrite` step citing `arith-eq-elim-int`, then
   the existing `poly_simp_rel` chain for the bounds.  §25's earlier
   normalizer closed 8,169 of 8,169 local QF_LIA holes with exactly this
   reasoning; it reopens §39 for `=` only, not for orientation.
2. Do not hand egglog a goal the normalizer made *larger*.  The elaboration
   pass already keeps the original goal (the comment at the rewrite site in
   `elaborate_holes` says why); the checking pass could keep it whenever
   the normal forms are not smaller than the originals, which separates
   cvc5's arithmetic rewrites (normal forms shrink, egglog proves more --
   §23's measurement) from veriT's `la_rw_eq` (normal forms grow by the
   `(* -1 ..)` and the flattening).  Cheaper still, given the numbers
   above: normalize the sides but do not flatten an `and`/`or` whose
   arguments the goal's other side keeps nested, i.e. run `aci_simp` only
   where it closes something.

Two side observations from the same run.  The Averest proof is 725 MB
with sharing (95,787 steps; the hole sides are wide conjunctions of
deep formulas), and on it every pass ends its holes at 297 s and is then
killed at the 700 s external limit, locally as on the cluster
(`set_rc=124` there): whatever the checker does after the hole summary of
such a proof takes over 400 s, and it inflates `<p>_time` without touching
the verdicts.  And the pipe through `cut` in `passes2.sh` block-buffers,
so a pass's per-hole lines appear only when it exits; that is what made
the earlier sampling of the post-summary phase miss the process.

The normalized goal of every rewritten hole is now logged at debug level
(`hole tN: goal normalized to ...`) so a comparison like this one needs no
patched binary.

### Done: `la_rw_eq` is the normalizer's first step (2026-09-22)

Haniel's call on the options above: the prenormalizer justifies the
trichotomy shape itself, through the Alethe rule, before anything else.
`prenorm.rs` now reads every conjunction *as written*, before its
arguments are normalized, and turns `(and (<= t u) (<= u t))` into
`(= t u)`; the derivation is one `la_rw_eq` step, stated the way the rule
states it and reversed by `symm`, and the equality then goes through the
relation procedure like any other.  Reading the term before its arguments
is the point: after `poly_simp_rel` the two bounds are `(<= P c)` and
`(<= -P -c)` and no longer mirror each other.

The same conjunction with either bound written as a `>=` -- cvc5's
`arith-eq-elim` shape, `(= (= t s) (and (>= t s) (<= t s)))` -- closes the
same way.  Its certificate first turns the `>=` bound round under `cong`,
and that equivalence, `(= (>= x y) (<= y x))`, is proved within Alethe and
without a `*_simplify` rule: each direction is an `la_generic` clause
(`(cl (not (>= x y)) (<= y x))` with coefficients 1, 1, and the converse),
and the two implications become the equivalence through `equiv_neg2`,
`equiv_neg1` and three resolutions.  Seven steps per turned bound.

Unit tests: the shapes `(and (<= x y) (<= y x))`, `(and (>= x y) (<= x
y))`, `(and (<= x y) (>= x y))`, `(and (>= y x) (>= x y))`, under `and`,
`not` and `ite`, on atoms and on polynomials, Int and Real, coincide with
the equality and their certificates check; `(and (<= x y) (<= y z))`,
`(and (<= x y) (< y x))` and `(and (>= x y) (>= x y))` stay apart.

On the two proofs of this section, `nset` with the new step (same
settings as before):

| proof | holes | closed by normalization | left to egglog | pass |
|---|---|---|---|---|
| Dartagnan `count_up_down-1` | 9,850 | **9,848** in 0.28 s | 2 (the `ite` shapes: one growth cap, one 60 s) | 60 s, was 300 s for 2,120 proved |
| Averest `blmc004` | 1,183 | **1,181** in 0.24 s | 2 (one 60 s, one memory) | 60 s, was 300 s for 308 proved |

The elaboration pass on the Dartagnan proof emits the certificates (9,855
`la_rw_eq`, 19,703 `symm`, 28,667 `poly_simp_rel`, 39,630 `cong` steps;
30 MB, 197,978 steps) and `carcara check` accepts the result as `holey`
in 0.9 s, the two egglog-kept holes being all that is left.  The pass
time is now the per-hole limit of the one hole that runs to it.

So for veriT's QF_LIA corpus the normalizer goes from closing 3.5% of the
holes to closing everything but the `ite` shapes, and the 1.6--4.5x
slowdown of §43 disappears with the goals it was paid on.  The cluster
binaries (`vb50-2`, `vnob-2`) predate this; a rerun of the two `nset`
arms is the measurement to make.

## 42. The QF_LIA residue of `enc4`, reproduced (2026-09-22)

`enc4`'s best configuration left QF_LIA with 3,981 kept and 9,411
unattempted holes.  Split by whether the proof hoisted: **10,537 of the
13,392 sit on the 15 proofs whose hoist timed out** (the unshared print of
§40), 2,855 on 149 hoisted proofs.  By family (kept / unattempted; the
reason classes of the kept): Dartagnan ReachSafety-Loops 821 / 7,222 (422
memory, 335 time; 9 of its 64 residue proofs unhoisted), calypto 753 / 1,117
(461 time, 90 memory; 4 of 13 unhoisted), fft 1,532 / 0 (Sz32_455 alone,
unhoisted), rings 527 / 0 (263 memory, 264 time, 35 proofs), Averest
parallel_prefix_sum 28 / 834, ezsmt incrementalScheduling 225 / 0 (208
memory, 13 proofs), SMPT a few dozen.  One representative of each family
was reproduced locally with the binary of §41, a shared hoist, four
workers of 3.5 GB, 60 s per hole and a 1,200 s pass:

| proof | holes | closed by normalizer | proved | kept | unattempted | pass |
|---|---|---|---|---|---|---|
| fft/Sz32_455 (cluster: 1,499 kept, unhoisted) | 6,723 | 5,986 | 6,720 | 3 (2 cap, 1 time) | 0 | 124 s |
| rings/ring_2exp8_4vars_2ite (cluster: 22 kept, 214 s) | 7,800 | 7,484 | **7,800** | 0 | 0 | **14 s** |
| Dartagnan/in-de62-O0 (cluster: 72 kept, 3,174 unattempted, unhoisted) | 5,783 | 3,388 | 4,411 | 78 (54 time, 20 memory) | 1,294 | 1,185 s |
| calypto/problem-001542 (cluster: 323 kept, 643 unattempted, unhoisted) | 2,200 | 1,554 | 1,856 | 74 (50 time, 20 memory) | 270 | 1,200 s |
| ezsmt/379-incremental_scheduling-78325-0 (cluster: 26 kept) | 1,143 | 646 | 1,118 | 25 (memory) | 0 | 98 s |

What each residue is:

- **rings**: gone.  The `_2ite` benchmarks put `ite` inside the
  polynomials; §38's atom rule closes the family (cluster 527 kept).
- **fft**: gone with the shared hoist; the three left are a growth cap
  and a timeout on a 46 MB proof whose non-hole steps take 300 s to check.
- **Dartagnan and calypto**: size.  The kept goals are Boolean rewrites
  (`(= (= A e) ...)`, `(not (not ...))`, `(ite ...)` = `(ite ...)`,
  `(=> ..)`) over terms whose expansion runs to millions of characters
  (in-de62: 1--180 M; calypto at three levels of names: up to 1.1 M), and
  the memory kills fail on 48-byte allocations at the 4 GB limit -- the
  e-graph is simply full.  The unattempted holes are the same proofs
  running out of pass budget behind those.  No rule is missing; the lever
  is granularity (a hole per subterm the sides differ on, as veriT's
  `--proof-hole-size` does, §34) or a per-proof budget in hole count.
- **incrementalScheduling**: all 25 kept holes are **beta reductions**,
  `(= ((lambda ((x Int) (y Int)) ...) a b) (ite (>= ..) 0 a))` from the
  benchmark's parameterized `define-fun`s (`max`, `min`), the shape the
  engine cannot prove (a lambda-headed application is an opaque symbol)
  and then blows memory on.  A prenormalizer step that beta-reduces a
  lambda application would close every one; cvc5 states them as
  `TRUST_THEORY_REWRITE`, so the certificate needs a rule -- which Alethe
  does not have -- or the checker's own reduction.  Open.

**A printer bug the shared hoist uncovered.**  The scheduling proof's
shared hoist did not parse back ("expected 0 arguments, got 2"): the
printer named the `lambda` heading an application and then wrote
`(@p_547 0 @p_540)`, and a name in head position is a nullary constant to
the parser.  With the runners now hoisting with sharing, every proof with
a parameterized `define-fun` -- 28 of `enc4`'s proved benchmarks: ezsmt
incrementalScheduling 13, ezsmt robotics 11, cmodelsdiff wireRouting 4 --
would have hoisted "ok" and then failed every pass at parsing.  Fixed in
`printer.rs`: a lambda is never given a sharing name (test
`test_sharing_leaves_lambda_heads_spelled_out`, a print/re-parse round
trip).

## 44. How big the replacements are: cvc5's own expansion at four granularities, and why egglog costs more (2026-09-22)

Setup: the local corpus `~/benchmarks/egglog-holes-eval` (the alethecore-eval
samples: 96 QF_UF, 47 QF_LIA, 67 QF_LRA unsat benchmarks), the local cvc5
`8f1863f2a5` (April 2026, the binary that produced that corpus), the same
flags at every granularity.  Scripts, per-proof JSON and the full tallies in
`~/exp/egglog-holes/granularity/` (`alethe/` for §44.1–2, `cpc/` for §44.3,
`micro/` for §44.2's one-rule holes).  A replacement is the premise closure
of the finer proof's step concluding the coarse step's formula, stopped at the
coarse step's own premises; terms are interned across the files, so matching
is structural, not textual.

### 44.1 Theory-rewrite holes: cvc5 needs about one step each

At `dsl-rewrite` every `TRUST_THEORY_REWRITE` of the theory-rewrite proof is
gone and the rest of the proof is unchanged (QF_UF 4,045,606 vs 4,045,789
steps).  Per distinct hole (Alethe):

| | QF_UF | QF_LIA | QF_LRA |
|---|---|---|---|
| distinct holes (matched) | 47,669 (100%) | 61,234 (100%) | 85,050 (27 unmatched) |
| steps per hole, mean / max | 1.00 / 3 | 1.43 / 9 | 1.46 / 198 |
| single-step holes | 100% | 78.1% | 80.4% |
| normalizer share of steps | 31% | 76% | 64% |
| RARE-rule steps per hole | 0.69 | 0.19 | 0.36 |
| distinct rules cited | 6 | 11 | 17 |

No `rare_rewrite` step of the whole corpus has premises: none of the 28
conditional rules of `holes.rare` is ever cited.  Only 130 of ~194k holes take
6 or more steps (the largest: 96–198-step `cong`/`trans` chains around one
`aci_simp`, clock_synchro; 35 holes of 20 steps chaining four rules, tta_startup).
The reason is where the hole sits: its tag is (theory, method) with method 6/7
only, i.e. one theory rewriter's pre/post call at one node, and the congruence
structure of the whole-term rewrite is already in the theory-rewrite proof.
`RewriteDbProofCons::proveEqStratified` tries refl/`EVALUATE`/distinct
values/a pre-DSL theory rewrite first and then iterative deepening from
depth 0, so it returns the shallowest proof; the search leaves no trace.

The egglog certificates (no `--hole-prenormalize`, enc4's `set` options;
the run was cancelled at 169/207 proofs, paired on the first 73) match that:
QF_UF 117/117 identical rule multisets; QF_LIA 87.1% identical, egglog larger
on 10.4% (711 vs 563 steps): cvc5 cites `arith-leq-norm` + `evaluate` (5 steps)
where the search takes the `arith_poly_norm_rel` edge and the elaborator
routes both sides through `arith-elim-*` (10 steps), and one engine-internal
`gen-16` step (14 vs 1); QF_LRA 93.7% identical, egglog smaller (935 vs 1,150).

### 44.2 Why egglog costs 0.2–0.4 s for a one-step hole

cvc5's expansion costs nothing measurable: solving at `dsl-rewrite` instead of
theory-rewrite changes total solve time by +8 s (QF_UF, 0.15 ms/hole) and −12 s /
−18 s (QF_LIA/QF_LRA, noise).  The egglog pass, per justified hole (local, 5
workers): median 0.195 / 0.387 / 0.337 s, of which the egglog phase is 58 / 84 /
69% and the certificate search 18 / 8 / 12% (enc4 agrees: 0.024 s per hole over 8
workers).  One-rule holes in an isolated child:

| hole | `holes.rare` (292 compiled rules) | only the rule it needs |
|---|---|---|
| `(= (not (not p)) p)` | 0.166 s (egglog 0.110, search 0.041) | 0.03 s (0.012, 0.003) |
| `(= (<= x 1) (>= 1 x))` | 0.196 s (egglog 0.144, search 0.035) | 0.06–0.07 s (~0.04, 0.015) |

So QF_UF's median hole *is* the fixed cost of loading and saturating the whole
database in a fresh child; arithmetic adds the normalizer rules; the tail is
e-graph growth.  cvc5 knows the node and the rewriter call, tries the
builtins, and matches at the root.  Since 100 / 78 / 80% of cvc5's own hole
derivations are a single root-level rule instance or a single normalizer step,
a cheap first pass (root match per rule plus Carcara's `evaluate`/`poly_simp`/
`aci_simp`, i.e. the prenormalizer) should close most holes before egglog.

### 44.3 Coarse granularities: where the structure is (CPC)

CPC proofs at `macro`, `rewrite`, `theory-rewrite`, `dsl-rewrite`
(`--proof-format-mode=cpc --proof-print-conclusion`); the printer's
`; trust <RULE>` comment names each trusted step.  206 benchmarks have all
four (cvc5 aborts on 3 QF_LIA benchmarks at `macro`; one LassoRanker times out
at 60 s everywhere).  Whole proofs:

| steps (trust) | QF_UF | QF_LIA | QF_LRA |
|---|---|---|---|
| `rewrite` | 1,588,014 (32,790) | 449,592 (57,229) | 476,996 (32,916) |
| `theory-rewrite` | 1,695,834 (47,907) | 633,131 (87,319) | 699,377 (82,167) |
| `dsl-rewrite` | 1,696,015 (73) | 667,120 (0) | 742,176 (0) |

Almost all the growth is rewrite → theory-rewrite (+108k / +184k / +222k), the
decomposition of whole-term rewrites into per-node rewriter calls; the DSL
stage adds +0.2k / +34k / +43k.  Per distinct coarse `rewrite`-granularity step:

| | QF_UF `MACRO_REWRITE` | QF_LIA `MACRO_REWRITE` | QF_LRA `MACRO_REWRITE` | QF_LRA `MACRO_SR_PRED_INTRO` |
|---|---|---|---|---|
| distinct (matched) | 24,699 (98.9%) | 29,595 (41.2%) | 13,816 (99.4%) | 14,177 (99.5%) |
| theory-rewrite leaves, mean / median / max | 3.75 / 1 / 439 | 12.7 / 3 / 15,513 | 12.3 / 10 / 56 | 3.4 / 1 / 1,358 |
| dsl steps, mean / median / p99 / max | 7.0 / 2 / 78 / 1,101 | 35.3 / 15 / 79 / 50,503 | 28.8 / 25 / 99 / 224 | 14.0 / 5 / 234 / 5,405 |
| step mix RARE / normalizer / glue | 45 / 9 / 46% | 3 / 40 / 57% | 3 / 40 / 57% | 14 / 27 / 59% |
| RARE steps per step, mean (max) | 3.13 (246) | 1.02 (2,858) | 0.92 (5) | 1.89 (341) |
| distinct RARE rules per step, mean (max) | 0.88 (4) | 0.76 (4) | 0.92 (3) | 1.13 (6) |

The replacements share sub-derivations: the union of all replacements per proof
is 155,772 / 285,488 / 308,564 steps against per-step sums 2.2–2.5 times larger.
Matching needed one fallback: a coarse `(= F true)` (proved by `MACRO_REWRITE` +
`true_elim`) has no counterpart when the finer proof proves `F` directly (QF_UF
11,790 of 24,432).  QF_LIA's 17,397 unmatched `MACRO_REWRITE`s are routes the
finer proof does not take: in the five benchmarks holding 16,480 of them (SMPT
BART/RwMutex, Dartagnan deep-nested) every one's user is absent from the
`dsl-rewrite` proof too, and 15,755 are solved forms for substitution
(`(= (= a1 (+ p111 p1)) (= p111 (+ (* -1 p1) a1)))`).  `SUBS` steps are not
isolable this way (their replacement reaches the assumptions through
`and_elim`).  At `macro` granularity the steps carry substitution and
reasoning too (QF_LRA `MACRO_SR_PRED_TRANSFORM`, 25,393 distinct: 84.7 steps
mean, 1.81 distinct RARE rules, 56% non-rewrite steps); QF_LIA's
`MACRO_SR_EQ_INTRO` matches only 16% for the same route reason.

Reading: from the coarse levels the expansion is large (tens of steps per
whole-term rewrite, up to 50k), but it is congruence glue and normalizer calls
around leaves that are still single rule instances from the same small set
(7 / 11 / 16 rules overall, `eq-symm`, `bool-double-not-elim`, `arith-elim-*`,
`arith-leq-norm`).  The DSL reconstruction's recursion is visible only in the
tail; the structure comes from the macro elaboration, which egglog does not
have to do because cvc5's theory-rewrite holes already sit at the leaves.

**Distinct steps per tier** (CPC, the 206 benchmarks with all four tiers:
96 QF_UF, 44 QF_LIA, 66 QF_LRA; distinct = deduplicated within a proof, steps
by rule and conclusion, trusted steps also by premise conclusions; `assume`
and scope steps not counted; `cpc/tiers.py`, `cpc/tiers.txt`):

| tier | QF_UF distinct trusted | QF_LIA | QF_LRA | all distinct steps |
|---|---|---|---|---|
| `macro` | 30,814 | 26,938 | 44,839 | 1,215,360 |
| `rewrite` | 32,790 | 28,341 | 32,916 | 1,342,833 |
| `theory-rewrite` | 47,907 | 48,394 | 82,161 | 1,746,062 |
| `dsl-rewrite` | 73 | 0 | 0 | 1,821,497 |

At `dsl-rewrite` the distinct RARE-rule plus normalizer steps are 47,843 /
68,992 / 112,902, i.e. 1.0 / 1.5 / 1.4 per distinct theory-rewrite hole.

### The limits, isolated: the cap decides, the clock adds a little (2026-09-22)

`vb50-2` and `vnob-2` differ in four things at once (the bound, the caps,
the per-hole clock, the worker count), so neither arm alone says what the
higher limits buy.  Two readings separate them.

**The paired QF_UF read is almost a controlled experiment.**  Of the 3,127
QF_UF benchmarks both arms have finished, **2,934 produce identical hole
counts**: veriT's QF_UF preprocessing holes are already under 50 DAG nodes,
so `--proof-hole-size=50` hardly ever fires there and the two arms are
checking the same holes.  On the 3,086 paired proofs, `set-form`:

| | holes | proved | kept | proofs fully justified | pass time |
|---|---|---|---|---|---|
| caps 3M/500k, 60 s, 8 workers | 241,522 | 94.2% | 14,080 | 236 | 11.5 h |
| caps 120M/20M, 120 s, 4 workers | 241,302 | **99.7%** | 751 | **2,528** | 26.0 h |

with the normalizer, 98.9% / 1,546 clean against 99.7% / 2,564.  The pass
time roughly doubles, but the high arm runs half the workers, so per worker
the work is comparable.

The residue names the knob.  Kept holes by reason (these runs predate the
`[class]` tag, so the text is classified: the `egglog check for tN failed`
message is the growth cap firing):

| | growth cap | per-hole time | memory |
|---|---|---|---|
| low limits | **13,670** | 388 | 22 |
| high limits | 46 | 675 | 32 |

Had the 60 s clock been binding, the low arm would show time kills; it
shows cap kills, and raising the cap removes 13,600 of them.  The clock
then becomes binding, and only mildly (388 to 675).

**Locally, one knob at a time.**  The same N=50 proofs of the five worst
QF_UF residues, the same 2 workers and 6 GB per hole, the same 600 s pass
budget, changing only the cap and then the clock
(`scratchpad/caps/ab.sh`; local binary, newer than the cluster's):

| proof | holes | A: 3M/500k, 60 s | B: 120M/20M, 60 s | C: 120M/20M, 120 s |
|---|---|---|---|---|
| `gensys_icl057` | 376 | 363, 108 s | 373, 182 s | 374, 194 s |
| `gensys_brn064` | 253 | 242, 48 s | 252, 80 s | **253**, 113 s |
| `gensys_icl055` | 226 | 215, 44 s | 224, 132 s | 225, 176 s |
| `dead_dnd014` | 14 | 2, 34 s | **12**, 105 s | 12, 166 s |
| `iso_icl_repgen006` | 37 | 2, 110 s | 7, 600 s | **20**, 600 s |
| total | 906 | 824 proved, 82 kept, 344 s | 868, 28 kept + 10 skipped, 1,098 s | 884, 7 kept + 15 skipped, 1,248 s |

So the cap alone (A to B) recovers 44 of the 82 kept holes and the clock
(B to C) another 16; on the one proof where the holes are individually hard
(`iso_icl_repgen006`) the clock is what matters, 7 to 20.  The price is
three times the time on proofs chosen for being the worst, and a new
failure mode: with the higher limits `iso_icl_repgen006` no longer finishes
inside the 600 s pass budget, so holes are skipped rather than kept.

**Reading.**  For veriT's QF_UF holes the caps `vb50-2` inherited from cvc5
are simply too small, and the 120M/20M pair costs nothing on the holes that
were already proved (they never approach it).  A rerun of the bounded arm at
the higher limits should take QF_UF from 94.2% to about 99.7% of holes and
from 236 to about 2,500 fully justified proofs, and would isolate the bound,
which is what `vb50-2` was supposed to measure in the first place.

### Arithmetic: the limits are not the constraint, the shape is (2026-09-22)

The same question for QF_LIA and QF_LRA.  `vnob-2` has not reached them
yet, so this is `vb50-2` plus local runs.

**Arithmetic does not lose where QF_UF loses.**  Kept holes are a rounding
error; the losses are holes never attempted before the pass budget ran out:

| `vb50-2`, set-form | holes | proved | kept | skipped | growth-cap kills |
|---|---|---|---|---|---|
| QF_UF | 305,215 | 93.7% | 6.3% | 0.0% | 18,757 |
| QF_LIA | 1,041,503 | 69.2% | 0.3% | **30.6%** | 133 |
| QF_LRA | 309,653 | 39.6% | 6.1% | **54.3%** | 24 |

The cap that decides QF_UF barely fires here.  What kept holes there are
die on memory (1,238 in QF_LIA, 10,343 in QF_LRA) and on the per-hole
clock.  The binding constraint is throughput: the pass budget divided by
the cost of a hole.

**So the higher limits do not help arithmetic; they hurt.**  Same knobs as
the QF_UF experiment, three QF_LRA proofs, 2 workers, 6 GB, 600 s per pass
(`scratchpad/arith/ab.sh`):

| proof | holes | A: caps 3M/500k | B: caps 120M/20M | N: A + normalizer | M: B + normalizer |
|---|---|---|---|---|---|
| LassoRanker `p-46 Loop_4` | 2,854 | 17 proved, 2,824 skipped | **11**, 2,825 skipped | **2,854**, 178 s | 2,854, 119 s |
| `tta_startup 14nodes.synchro.base` | 1,793 | 28, 1,735 skipped | 28, 1,735 skipped | **1,791**, 56 s | 1,791, 53 s |
| miplib `fixnet-1000` | 4,635 | 19, 4,596 skipped | 19, 4,596 skipped | **4,635**, 51 s | 4,635, 51 s |

Raising the cap on the first proof *loses* six holes: a hopeless hole now
runs to a larger e-graph before it fails, and the holes behind it in the
queue are never reached.  On the other two it changes nothing.  In every
arm the proof is decided by how many holes the budget covers, and the way
to cover them is to make a hole cheap, not to give it more room.

**Which is exactly what the shape does.**  Split by family, `vb50-2`:

| | holes in families the normalizer failed on | those: set / nset | the rest: set / nset |
|---|---|---|---|
| QF_LIA | 503,542 of 1,041,503 (48%), all Dartagnan | 36.7% / 22.5% | 99.6% / 99.4% |
| QF_LRA | 100,373 of 309,653 (32%): `tta_startup`, `uart`, `sal`, `sc`, `spider` | 22.1% / 16.0% | 48.0% / **96.9%** |

Outside those families the normalizer already decided arithmetic: 96.9% of
the QF_LRA holes and 99.4% of the QF_LIA ones, against 48.0% and 99.6%
plain.  Inside them it closed nothing and, per §43, made the goals dearer,
so it lost: 22.1% to 16.0%, 36.7% to 22.5%.

And those families are one shape.  A `tta_startup` hole is fourteen
`la_rw_eq` rewrites at once under a disjunction:

```
(= (or (= 1.0 x_43) .. (= 14.0 x_43))
   (or (and (<= 1.0 x_43) (<= x_43 1.0)) .. (and (<= x_43 14.0) (<= 14.0 x_43))))
```

each disjunct a mirrored pair, some written the other way round.  With the
step added today the arguments of the `or` close one by one on the way up,
the whole hole closes without egglog, and the family goes from 28 holes
proved in 600 s to 1,791 of 1,793 closed in 0.056 s.  The LassoRanker and
miplib proofs, which the old normalizer already half closed, go from 17 and
19 proved to complete.

**The arithmetic story, then.**  Not a resource story at all.  Both logics
are one rewrite shape wide: `la_rw_eq` is 100% of the QF_LIA residue and
the whole of the QF_LRA families that were failing, and closing it in the
prenormalizer converts both from throughput-bound to free.  The measurement
to make is a rerun of the two `nset` arms with the new binary; the caps
should stay where `vb50-2` has them, and the QF_UF arm is the only one that
wants the larger ones.

## 44. `vnob-2` complete: the bound wins arithmetic, the caps win QF_UF (2026-09-23)

The no-bound arm finished (9,812 tasks, aggregator stopped 2026-09-23).
Both veriT arms are now readable end to end.  Recall they differ in two
things: the granularity (`--proof-hole-size=50` against none) and the
limits (caps 3M/500k, 60 s, 8 workers against 120M/20M, 120 s, 4 workers).

**What the bound does to the holes.**

| | holes, N=50 | holes, no bound | ratio | median per proof |
|---|---|---|---|---|
| QF_UF | 305,215 | 304,978 | 1.00 | 18 / 18 |
| QF_LIA | 1,041,503 | 236,561 | 4.4 | 7 / 2 |
| QF_LRA | 309,653 | 8,225 | **37.6** | 122 / 3 |

QF_UF is untouched: veriT's preprocessing there produces holes already
under 50 nodes.  In arithmetic the bound is the whole experiment, and
QF_LRA's whole-assertion holes are 37 times coarser.

**Hole percentages favour the coarse arm, and mislead.**  `set-form`:
QF_LIA 69.2% of 1.04 M against 99.2% of 237 k, QF_LRA 39.6% of 310 k
against 41.2% of 8 k.  The denominators are not comparable; what is
comparable is whether a proof comes out with every hole closed.

**Proofs fully justified, best of the four configurations, paired:**

| | proofs | N=50 | no bound | only N=50 | only no bound |
|---|---|---|---|---|---|
| QF_UF | 4,176 | 2,106 | **3,542** | 0 | 1,436 |
| QF_LIA | 2,506 | **2,139** | 1,841 | 329 | 31 |
| QF_LRA | 566 | **213** | 168 | 46 | 1 |
| total | 7,248 | 4,458 | 5,551 | 375 | 1,468 |

Two different effects, and they do not interfere, because the bound is a
no-op on QF_UF and the caps are nearly irrelevant to arithmetic (§43):

- **QF_UF is the limits.**  Same holes, and the coarse arm's larger caps
  take it from 2,106 to 3,542 fully justified proofs.  Residue: 2,855
  growth-cap kills against 28.
- **Arithmetic is the bound.**  Splitting an assertion into 50-node holes
  wins 329 QF_LIA proofs and 46 QF_LRA ones, and loses 31 and 1.  A
  whole-assertion hole that fails costs the whole proof; a bounded hole
  that fails costs one rewrite.

**So neither arm is the configuration to run.**  The bounded proof with the
larger caps has never been measured, and on these numbers it should reach
about 3,542 + 2,139 + 213 = 5,894 fully justified proofs against `vnob-2`'s
5,551 and `vb50-2`'s 4,458 -- except that §43 measured the larger caps
*hurting* arithmetic throughput, so the caps want to be per-logic: large
for QF_UF, `vb50-2`'s for QF_LIA and QF_LRA.

**The encoding gap widened.**  On the no-bound QF_UF holes `chain` takes
106.3 h against `set-form`'s 34.7 h, a factor of 3.1 (it was 2.4 in
`vb50-2`), and proves less (97.4% against 99.1%).  Every arm of both jobs
agrees: for veriT's holes the set form is the encoding.

**Caveat on all the arithmetic numbers here.**  They predate today's
`la_rw_eq` step in the prenormalizer (§43), which closes the shape these
proofs are made of: on the three local QF_LRA proofs the same holes go from
17, 28 and 19 proved to complete.  The arithmetic half of this table is a
measurement of the old normalizer and should be redone.
## 45. Shared-subterm abstraction with a fallback, and what it does and does not reach (2026-09-22)

`--hole-abstract-shared N` (commit 0c50a1f4, `src/elaborator/abstraction.rs`):
before egglog, every maximal subterm both sides of a hole share, of `N`
nodes or more and binding nothing, becomes a fresh constant of its sort
(`@abs_K`, declared by the child as any free variable is); the abstract goal
is tried first on half the hole's budget, its certificate instantiated back
by putting the subterm's text where the name is, and a hole whose abstract
goal is *not proved* is retried as it stands.  Sound by instantiation -- a
rewrite proved for a constant holds for any term -- and incomplete exactly
when the proof has to rewrite inside the shared subterm to relate it to
something outside it (`(= (or (not (not p)) (not p)) (or true (not (not
p))))`: both sides are `true` only because the shared `(not (not p))` is
`p`), which the fallback covers.  A hole whose abstract attempt dies of time
or memory keeps that verdict: with the shared subterms gone the goal is as
small as it gets, and the retry would only die the same way, for the full
budget.  Tests: unit tests of the abstraction and the instantiation, and
`elaborates_through_shared_subterm_abstraction_with_fallback` (fixture
`tests/rare/elaborate/abstract-shared.*`: one hole abstracted and cited
on the original terms, one counterexample elaborated through the
fallback).  The runners pass `--hole-abstract-shared 16`.

Measured on the §42 proofs, four workers, 1,200 s (before the gating of
the fallback):

| proof | holes with a shared subterm of 16+ nodes | proved abstract | retried | of which proved | kept before / after | unattempted before / after |
|---|---|---|---|---|---|---|
| sc-14 | 0 of 1,849 | -- | -- | -- | -- | -- |
| in-de62-O0 | 0 of 2,596 | -- | -- | -- | -- | -- |
| calypto problem-001542 | 174 of 653 | 119 | 55 | 3 | 76 / 56 | 289 / 352 |

So the abstraction is not what the Dartagnan family needs: its sides
differ by a conjunct *inside* one big `and`, and what they share is a list
of three-node atoms, not one large subterm.  Where it applies (calypto) it
takes a quarter of the kept holes, but the 52 failed abstract attempts each
cost half a hole budget before the retry, and at a fixed pass budget that
was more unattempted holes than it saved -- hence the gating above, and
the reason a budget in holes rather than seconds (§6) is the companion
change.

With the fallback gated (calypto again, same budget): 363 of the 653
holes that reached a worker were abstracted, 245 proved abstract, 118
kept on the abstract attempt's own half-budget timeout, none retried;
**2,012 proved, 124 kept, 64 unattempted** against 1,835 / 76 / 289
without the abstraction.  So at a fixed pass budget the abstraction is
worth 177 holes on this proof, and what it leaves is now dominated by
holes whose *abstract* goal takes more than 30 s -- which says the half
budget is the next knob, and that a budget in holes would let the
abstract attempt have the whole per-hole limit without starving the
rest of the proof.

**A regression from a concurrent commit.**  These measurements were first
confounded by `19b64f64` ("Close the la_rw_eq shape in the prenormalizer,
before anything else"), committed to this branch by another session
between my runs: on `sc-14` the prenormalizer closes 3,432 holes instead of
3,608, the 176 it no longer closes are `(= A (and ...))` goals over a
dozen conjuncts that now reach egglog and die of memory (77 kills, was 0),
and the pass takes its whole 1,200 s instead of 120 s; on `in-de62-O0`
4,411 proved became 3,478 at the same budget.  Bisected by building the
tree at `b1acac8f` (3,608) and at HEAD (3,432) on the same file.  The
change reads every conjunction for a pair of opposite bounds before its
arguments are normalized; on cvc5's holes that turns conjunctions into
equalities the other side no longer matches.  Not reverted here -- it is
the veriT work's -- but it has to be resolved before a rerun.

## 46. `la_rw_eq` in the prenormalizer, after flattening (2026-09-22)

§45's regression, fixed on this branch.  `19b64f64` read `la_rw_eq` on the
term *as written*, before its arguments were normalized, matching only a
two-element `and` of mirrored bounds; on cvc5's conjunction-flattening
holes -- `(= (and (and (<= x 2) (>= x 2)) p) (and p (<= x 2) (>= x 2)))` --
that folded the nested pair on one side and left the flat one on the other,
so two terms that had normalized to the same flat conjunction now
normalized apart, and 176 holes of `sc-14` that closed for free went to
egglog as `(= (and equalities) (and bounds))`, the shape that fills the
e-graph: 77 memory kills where there were none, 1,200 s where there were
120.  The normalizer's cost never changed; its normal form stopped being
confluent.

The fold now runs as a top step *after* `aci_simp`, on the flat canonical
conjunction, and reads the bounds as the normal forms leave them: two
non-strict bounds among the conjuncts whose `Q <= 0` polynomials are each
other's negation (`(<= P c)` with `(>= P c)`, or with `(<= -P -c)`) are the
equality `(= t u)` in the rule's spelling, with `t <= u` read off the
first bound.  So a pair meets however the producer nested it, and the
equality is then normalized like any other, which is also what the veriT
shapes need (`(and (<= t u) (<= u t))` normalizes each bound first and
folds the mirrored pair after).  Certificate (`Emitter::emit_fold`):
`aci_simp` regroups the pair into its own `and` (the checker compares
multisets after flattening, so any positions and nesting), `la_generic` +
`equiv_neg` + `resolution` turn a bound into the rule's spelling where it
differs (under `cong`), `la_rw_eq` reversed by `symm`, and the pair
replaced by the equality under `cong`.  The as-written reading and its
`BoundFlip` premise are gone.  `sc-14`: 3,608 closed again.  The
concurrent commit's test that `(and p (<= x y) (<= y x))` and `(and p (= x
y))` stay apart encoded the limitation and is now a coinciding case; every
other case of its tests passes as before, plus nested-against-flat cases.

Re-measured with the fold (same files, budgets and workers as the QF_LIA residue section and §45):
`sc-14` **5,281 of 5,281 proved, 0 kept, 136 s** (with `19b64f64` as
committed: 4,517 proved, 81 kept, 1,200 s); `in-de62-O0` 3,388 closed by
the normalizer, 4,333 proved, 70 kept, 1,380 unattempted at 1,200 s
(before the regression 4,411 / 78 / 1,294; with it 3,478 / 128 / 2,177).

## 47. Coarser holes from cvc5: `--proof-granularity=rewrite` (2026-09-22)

Branch `egglog/rewrite-holes` (worktree `wt-rwgran`, off `bounded-parallel-holes`
at b3f21bf6), cvc5 branch `alethe-rewrite-granularity` (`~/cvc5/wt-rwgran`,
off main at 47f43bd012, commit 506592fc52).  Scripts and per-run outputs in
this session's scratchpad `rwgran/` (`run.sh`, `batch.sh`, `elab.sh`,
`tab.py`, `out/<bench>/<trw|rw>/`).

**The question.**  Every run so far checks cvc5 proofs at `theory-rewrite`
granularity, one hole per theory rewriter call at one node (§44.1).  Could the
producer be asked for coarser holes -- one per call of the *full* rewriter on a
term, which is what cvc5's `MACRO_REWRITE` step states -- and would the
pipeline still close them?

**What cvc5 offers.**  cvc5's granularities, from the coarsest: `macro` leaves
the `MACRO_SR_*` rules unexpanded (substitution plus rewriting, with premises
and non-equality conclusions); `rewrite` expands them into `SUBS`
(substitution) and `MACRO_REWRITE` (`(= t rw(t))`, no premises) glued by
`EQ_RESOLVE`/`TRUE_ELIM`/`TRANS`; `theory-rewrite` expands `SUBS` into
cong/trans and `MACRO_REWRITE` into one `THEORY_REWRITE` per node (the holes
we know); `dsl-rewrite` replaces those by RARE steps.  For Alethe, cvc5 forced
any granularity below `theory-rewrite` up to it, even one set by the user
(`set_defaults.cpp`, "Alethe requires granularity at least theory-rewrite"),
and the Alethe backend had no case for the macro rules: they would reach
`default:` and print as holes under the rule's name with the raw arguments
(method ids as bare integers).

On five QF_LIA/QF_LRA samples in cvc5's internal format (distinct steps), the
`macro` proofs hold 89–571 `MACRO_SR_PRED_TRANSFORM` steps each (one premise,
the source formula, no substitution premises except 5 of 94 on tgc_io-safe-6),
31–125 `MACRO_SR_PRED_INTRO` and 3–312 `MACRO_SR_EQ_INTRO` (a fraction with one
substitution premise, always `SB_DEFAULT SBA_FIXPOINT`), and 0–100
`MACRO_REWRITE`.  `macro` does not give coarser *rewriting* than `rewrite`; it
only leaves the substitution and resolution glue unexpanded, and has more
steps than `rewrite` because many `PRED_TRANSFORM`s each become two rewrites.
So `rewrite` is the level to take first: its holes are unit equalities with
no premises, the shape the pipeline already handles, only coarser.  (`macro`
is still on the table -- the Alethe backend printing the macro rules as holes
with their premises, and the engine taking a hole's premises as facts that the
certificate can cite -- but it needs both sides changed; this section is the
measurement of the cheap level.)

### 47.1 The patches

*cvc5* (three files, commit 506592fc52):

- `set_defaults.cpp`: an explicit `--proof-granularity` is kept for Alethe;
  only the default is `theory-rewrite`.
- `proof_manager.cpp`: at `rewrite` granularity with the Alethe format, `SUBS`
  is still eliminated (expanded into cong/trans over its premises, as at
  `theory-rewrite`), so no hole carries premises.
- `alethe_post_processor.cpp`: a case for `MACRO_REWRITE` and premise-free
  `MACRO_SR_PRED_INTRO` (what `--proof-elim-subtypes` makes of a
  `MACRO_REWRITE` it re-typed): a reflexive conclusion is `refl` (as for
  `TRUST`, the purification steps); otherwise
  `(step tN (cl (= t t')) :rule hole :args ("MACRO_REWRITE" "RW_REWRITE"))`,
  the rule name and the rewriter's method id as strings.  A macro step with
  premises keeps the untranslated form.

*Carcara* (commit 7b418d3a): the two tags join `THEORY_REWRITE_TAGS`; nothing
else, since the hole shape is the one the pipeline checks.  Fixture
`tests/rare/elaborate/RF-12-rewrite.smt2.alethe`: the theory-rewrite proof's
two holes and their cong/trans glue are one `MACRO_REWRITE` hole (11 steps
against 27); `elaborates_cvc5_rewrite_granularity_holes_end_to_end`
elaborates it and re-checks `valid`.

Holes of the same proof that neither granularity tags (identical in both arms):
`THEORY_INFERENCE_ARITH` (arithmetic preprocessing, 7–288 per proof),
`DIAMONDS`, and the subtype-elimination trust steps, `ARITH_PRED_CAST_TYPE` at
theory-rewrite (10–125 on the mixed Int/Real benchmarks) which become
`MACRO_THEORY_REWRITE_RCONS_SIMPLE` at `rewrite` (2–143).  None of them is
checked by the pipeline today.

### 47.2 Checking: ten samples, two arms

The ten §23/§24 samples, each proved twice (cvc5 `prod` 1.3.5.dev at
`theory-rewrite`, the patched cvc5 at `rewrite`, the same flags), `hoist
prune` once, then check-only passes `set` (plain) and `nset`
(`--hole-prenormalize`) at the production caps (3M/500k), 4 workers, 30 s and
3.5 GB per hole, 300 s per pass; the runs interleaved, one at a time.

| benchmark | arm | cvc5 s | proof MB | steps | holes hoisted (tagged) | `set` proved / time | `nset` proved / closed by normalizer / time |
|---|---|---|---|---|---|---|---|
| 30_30_18 (QF_LIA) | t-rw | 4.5 | 1.86 | 17,989 | 1,067 | 1,067 / 103 s | 1,067 / 563 / 30 s |
| | rw | 4.2 | 1.12 | 9,880 | 462 | 462 / 90 s | 462 / 123 / 43 s |
| FISCHER9 (QF_LIA) | t-rw | 1.8 | 3.36 | 26,867 | 1,760 | 1,760 / 70 s | 1,760 / 1,242 / 23 s |
| | rw | 1.6 | 3.07 | 23,625 | 1,511 | 1,511 / 89 s | 1,511 / 921 / 62 s |
| MULTIPLIER_3 (QF_LIA) | t-rw | 0.6 | 3.66 | 36,660 | 845 | 845 / 258 s | 845 / 726 / 5 s |
| | rw | 0.4 | 1.51 | 13,863 | 272 | 264 / 292 s | 272 / 130 / 9 s |
| RF-09 (QF_LIA) | t-rw | 7.2 | 2.77 | 22,167 | 2,735 | 2,731 / 186 s | 2,735 / 1,205 / 81 s |
| | rw | 6.6 | 2.50 | 18,925 | 2,079 | 2,078 / 175 s | 2,079 / 549 / 115 s |
| clocksynchro_3 (QF_LRA) | t-rw | 0.3 | 0.99 | 9,633 | 1,115 | 1,114 / 99 s | 1,108 / 739 / 92 s |
| | rw | 0.2 | 0.48 | 4,329 | 196 | 158 / 296 s | 191 / 60 / 37 s |
| cut_lemma_01_008 (QF_LIA) | t-rw | 0.9 | 1.99 | 18,655 | 1,000 | 711 / 300 s (budget) | 1,000 / 912 / 5 s |
| | rw | 0.6 | 0.48 | 4,289 | 126 | 93 / 274 s | 126 / 34 / 8 s |
| ex4880 (QF_LIA) | t-rw | 4.1 | 1.64 | 15,656 | 1,348 | 1,341 / 146 s | 1,348 / 901 / 28 s |
| | rw | 3.8 | 1.09 | 9,933 | 673 | 670 / 110 s | 672 / 233 / 77 s |
| ring_2exp10 (QF_LIA) | t-rw | 0.5 | 3.41 | 35,883 | 819 | 819 / 79 s | 819 / 674 / 8 s |
| | rw | 0.3 | 1.62 | 15,913 | 349 | 307 / 224 s | 349 / 189 / 13 s |
| tgc_io-safe-6 (QF_LRA) | t-rw | 0.2 | 0.56 | 5,255 | 764 | 764 / 34 s | 617 / 350 / 300 s (70 memory, 77 budget) |
| | rw | 0.2 | 0.36 | 3,171 | 140 | 106 / 244 s | 123 / 29 / 87 s (17 memory) |
| vpm2-0 (QF_LRA) | t-rw | 30.7 | 2.96 | 30,518 | 2,097 | 2,090 / 142 s | 2,096 / 878 / 66 s |
| | rw | 30.8 | 2.11 | 20,542 | 2,081 | 1,074 / 300 s (budget) | 2,079 / 761 / 96 s |

What it says:

- **Proofs shrink**: 1.1–4.4× fewer steps, 1.1–4.1× fewer bytes; tagged holes
  fall 3–8× on the Boolean-heavy proofs (cut_lemma 1,000 → 126, clocksynchro
  1,115 → 196, MULTIPLIER_3 845 → 272) and hardly at all where the holes were
  single arithmetic relations to begin with (vpm2 2,097 → 2,081, FISCHER9
  1,760 → 1,511).  cvc5's own time is unchanged (it is the solving).
- **With the normalizer the coarse holes close as well as the fine ones**:
  `nset` proves every hole of seven proofs, and 191/196, 672/673, 2,079/2,081,
  123/140 on the other four -- the theory-rewrite arm's rate on the same
  proofs.  The normalizer closes a smaller *fraction* outright (a coarse hole
  is closed only if every rewrite in it is one of its four procedures), and
  egglog proves the rest.
- **Without the normalizer the coarse holes are much worse**: plain `set`
  loses 8–52% per proof and runs to the budget (clocksynchro 158/196 in
  296 s against 1,114/1,115 in 99 s at theory-rewrite).  A whole-term
  rewrite is the size egglog pays for; the normalizer is what makes the
  granularity affordable, as it was for veriT's coarse holes (§34).
- **Wall-clock per proof** for `nset` is within a factor of two either way:
  the rw arm is faster where the fine holes were many (clocksynchro 37 s
  against 92 s, MULTIPLIER_3 9 s against 5 s, cut_lemma 8 against 5) and
  slower where each hole got heavier (30_30_18 43 s against 30, FISCHER9 62
  against 23, ex4880 77 against 28).
- **The residue** (rw, `nset`): clocksynchro 3 time and 2 growth-cap kills on
  whole-clause goals (`(= (or ...) (or ...))` over a dozen relations);
  ex4880 and vpm2 one and two 30 s kills; tgc_io-safe-6 17 memory kills.
  The tgc kills are the `arith-eq-elim` shape -- `(and (<= t u) (>= t u))`
  nested on one side and flattened into the outer `and` on the other -- which
  the trichotomy step (§46) only reads when the pair is a conjunction of its
  own, so the normalizer turns the nested side into `(= t u)` and leaves the
  flat side as bounds, and egglog blows up on the goal it is then handed.
  The same 70 memory kills hit the theory-rewrite arm's `nset` on that proof
  (its plain pass proves all 764 in 34 s), so this is a normalizer defect
  independent of the granularity: the pair should also be found among the
  flattened conjuncts.

### 47.3 Elaboration: two gaps the coarse holes exposed, both fixed

Elaboration (`--hole-prenormalize`, 45 s per hole, 600 s per pass, otherwise
as above) on five of the `rewrite` proofs, then `carcara check` of the
result.  Three binaries, one change each:

| proof | holes | as it stood (justified / pass) | + `bridge` (84c663a6) | + search fixes (42a2a85b) | theory-rewrite arm, same binary |
|---|---|---|---|---|---|
| clocksynchro_3 | 196 | 189 / 73 s | 189 / 112 s | **191** / 93 s | 1,114 of 1,115 / 127 s |
| cut_lemma_01_008 | 126 | 99 / 188 s | 99 / 189 s | **112** / 22 s | 1,000 / 6 s |
| MULTIPLIER_3 | 272 | 238 / 367 s | 238 / 417 s | **267** / 14 s | 845 / 6 s |
| tgc_io-safe-6 | 140 | -- | 113 / 279 s | **117** / 217 s | 757 of 764 / 408 s |
| ring_2exp10 | 349 | -- | 315 / 332 s | **339** / 30 s | 819 / 11 s |

Every elaborated proof re-checks `holey` with only the untagged holes, the
kept ones and the `arith_poly_norm_rel` trust steps (§1) left.

**Gap 1: the elaboration pass never used the normal forms.**  Under
`--hole-prenormalize` the checking pass checks `(= nf(l) nf(r))`, but the
elaboration pass handed egglog the hole as stated and took from the
normalizer only the holes it closed outright (the comment at the rewrite
site in `elaborate_holes` said why: a normal form is a different term from
the ones the rules were compiled around, and the search may replay less on
it).  `Normalizer::bridge` -- the derivations `l = nf(l)` and `nf(r) = r`
around egglog's certificate of the normal forms -- existed and was never
called.  Now (84c663a6) the normalized goal is tried first, its certificate
bridged, and a hole whose normalized goal is not reconstructed is retried as
stated.  On these five proofs it changes nothing in the totals -- the holes
it bridges were provable as stated too -- and costs a retry where the normal
form loses (tgc: 26 of 52 bridged, 3 of the 26 retries proved; at
theory-rewrite 59 of 162 bridged, 97 of the 103 retries proved).  The
mechanism is right and the numbers say the search, not the goal, was the
limit.

**Gap 2: the certificate search on `(= (= a b) true)`.**  102 of the 129
holes the first binary left were of this one shape (cut_lemma 27/27,
MULTIPLIER_3 34/34, ring 34/34): a `MACRO_REWRITE` whose term is an
equality the rewriter takes to `true`, typically `(= (= (not (not A)) A)
true)` from the double-negation elimination cvc5 states as a rewrite to
`true`.  egglog proves each in 0.3 s; the search ran to the 45 s limit or
gave up.  Reproduced on the 9-node goal `(= (= (not (not (>= x -2))) (>= x
-2)) true)` (`tests/rare/elaborate/eq-true.smt2`).  Two causes, both in
`expand_vertex`:

- The candidate congruence `(= X true)` to `(= true true)` -- `X` replaced
  by the constant of its class -- has the goal `X = true` itself as its
  obligation.  The in-progress guard prunes it, a prune is not cacheable
  (correctly: it depends on the stack), and each of the four
  rejustifications banned one such edge and found the same shortcut at
  another level of the `Mk`/`Args` spine.  A congruence candidate is now
  skipped when a differing child pair, at any depth of the spine the two
  terms share, is already on the proof stack.
- The backward search from `true` expanded the constant: `eq-refl` and
  `eq-symm` anchored at `true` ground to the reflexive and symmetric
  instances over every member of the `true` class, hundreds of `(= s s)`
  terms in a saturated e-graph (`(= (str.len true) (str.len true))` among
  them), and the 256-state budget was gone before the forward search's
  two-edge path `X` -> `(= A A)` -> `true` was met.  A constant vertex now
  gets no rule edges; the edges into it are found from the term side.

The micro goal reconstructs in 3 s.  On the five proofs the search fixes
justify 79 more holes and cut the passes 2--30 times (MULTIPLIER_3 417 s ->
14 s).  The 35 `no-certificate` holes left (cut_lemma 14, ring 10, tgc 6,
MULTIPLIER_3 5) are the same shape with a *polynomial* relation on each
side, `(= (= (not (not (>= P c))) (>= P' c)) true)` with `P'` a reordering
of `P`, where the obligation `(not (not (>= P c))) = (>= P' c)` needs a
double-negation step and a relation step in sequence; the goal-directed
relation edge exists only towards a sub-search's own goal, so the chain is
not found.  Open, and the natural next search fix.  The other residue is
tgc's `arith-eq-elim` memory kills (§47.2) and clocksynchro's whole-clause
goals.

### 47.4 Verdict, and what is next

At `rewrite` granularity the pipeline closes cvc5's holes at the
theory-rewrite rate in checking, with proofs 1.1--4.4x smaller and 3--8x
fewer holes on the Boolean-heavy proofs, provided the normalizer is on.
Elaboration is a step behind (95--98% justified against 99.9--100%), on
one search shape that is now characterized.  Costs and gains beyond the
sample need the three sets on the cluster: cvc5 at `rewrite` from the
patched binary, the same passes as `enc4`, with elaboration on the
`nset` arm.  What the granularity does not change: the untagged holes
(`THEORY_INFERENCE_ARITH`, subtype elimination's trust steps) and the
`arith_poly_norm_rel` steps the elaborator still leaves as trust.

`macro` proper stays the plan after `rewrite`: the Alethe backend printing
the `MACRO_SR_*` rules as holes with their premises (their conclusions are
not equalities and the substitution premises are facts), the engine taking
a hole's premises as ground unions, the search citing them as leaves (a
ground `premise:k` rewrite in the rule list needs no new certificate
variant), `insert_solver_proof` discharging `(not P_k)` and citing the
outer premise nodes as `sat_refutation` does, and `eq_mp` for the
non-equality conclusions.

### 47.5 Run `rw1` (submitted 2026-09-22)

The three sets on `octa` (arrays 30291166 QF_UF, 30291167 QF_LIA, 30291168
QF_LRA; two tasks per node, 8 cores and 60 GB each, wall 3,100 s; results
`exp/results/egglog-holes/rw1`): the static cvc5 of 506592fc52 at
`--proof-granularity=rewrite` (60 s), `hoist prune`, the `nset` checking pass
under enc4's budgets (600 s per pass, 60 s and 6 GB per hole) but with the
whole-assertion caps 120M/20M -- on the ten samples 3M/500k and 120M/20M gave
identical verdicts, so the higher caps only matter on the proofs the sample
does not have -- then elaboration (900 s, 45 s per hole, normalized goal
first) and a re-check (900 s), with the static carcara of 387b0882 (the two
tags, the bridge, the search fixes, and the shared-subterm abstraction
commits of `egglog/hole-abstraction`).  Runner `~/exp/egglog-holes/
run-holes-rw.sh`, keys as chk1200n's minus the plain pass, plus
`holes_untagged` and `elab_bridged`.  Baselines: enc4's `nset` arm for
checking, chk1200n for elaboration.

### 47.6 `rw1` half-way: the QF_UF checking gap is the engine's demand rules

Read on 2026-09-23 with QF_UF complete and QF_LIA at 2,227 of 4,748
(partial `results.json.gz`, truncated at a record boundary; the same
benchmarks in enc4's `nset` arm as the baseline, proofs complete in both):

| | rw1 (`rewrite`) | enc4 (`theory-rewrite`) |
|---|---|---|
| QF_UF proofs fully checked (of 4,315) | 2,406 | 4,078 |
| QF_UF proofs with a kept hole | 1,711 | 39 |
| QF_UF holes proved | 99.6% | 99.9% |
| QF_UF checking pass, summed | 49 h | 11 h |
| QF_LIA (first 2,018) proofs fully checked | 1,849 | 1,902 |
| QF_LIA holes proved | 93.2% | 98.8% |
| QF_LIA holes skipped by the pass budget | 20,522 | 8,056 |

The kept-hole classes from the run's own keys: QF_UF checking 4,509
`hole-time`, 281 `growth-cap`, 15 `memory`; QF_UF elaboration 11,481
`hole-time`, 508 `no-certificate`; QF_LIA elaboration 17,311
`no-certificate`, 3,190 `hole-time`.  1,652 of the 1,711 QF_UF proofs
with a kept hole are QG-classification, 57 Goel-hwbench.

**The hole.**  Reproduced locally on the two smallest cases (`bridge.2`,
5 holes, one kept; `dead_dnd005`, 21 holes, one kept).  Both are
`MACRO_REWRITE` steps of pure Boolean simplification over an uninterpreted
sort: a 28-conjunct `and` of disequalities holding `(not (= x x))`,
rewritten to `false`; an `or` of six `(and (= e (op e (op e e))) (not (= e0
e)))` blocks losing the one with `(not (= e0 e0))`, with every equality
reoriented.  At theory-rewrite these are one node-sized step each and enc4
checks the proofs in under a second; at `rewrite` egglog died at 6 GB after
15--25 s, and at 14 GB still hit the 60 s limit.  Abstraction, the
normalizer, the list encoding and `--rare-seed-from-goal` change nothing.
(Boolean simplification does not go into the prenormalizer: the normalizer
is limited to what core Alethe rules compute, and general rewriting is the
egglog route's job.)

Shrunk copies (`and` of k disequalities over sort U, one reflexive):

| k | with `(not (= c0 c0))` | with a literal `false` |
|---|---|---|
| 4 | 0.8 s | 0.1 s |
| 8 | 4.3 s | 0.1 s |
| 12 | 16.5 s | 0.1 s |
| 16 | 45.7 s | 0.1 s |
| 24 | memory kill | 0.1 s |

The closing rewrite needs three rounds (`eq-refl`, `(not true)` by
evaluation, `and` with `false`); with the literal it fires in round one.
The per-rule reports of the 12-conjunct case say what fills the rounds in
between:

- Every `define-cond-rule` had a demand rule instantiating its premise
  over *all pairs of available terms* (`rule ((Avaliable s1) (Avaliable r1))
  ((Mk (@str.in_re s1 r1))))`), sort-blind: eight such rules fired 2,175
  times each in round two and 12,775 each in round four, building
  `str.in_re`, `str.<=`, `>=` and `=` nodes over uninterpreted constants.
  The RARE rule is sort-guarded; its demand was not.
- Once a disequality's `(= s r)` sat in the `false` class, `eq-cond-deq`
  (`(= (= t s) (= t r)) -> (and (not (= t s)) (not (= t r)))` when
  `(= s r) = false`) and its demand rule matched 530k times in one round
  over the demand-made equalities: the 8 s rounds.

**Fix 1 (engine): premises demanded where the left-hand side occurs.**
`construct_rules` now emits, per conditional-rule premise, `rule ((=
demand_site <LHS pattern>) ...) (<premise lhs> <premise rhs>)`: the premise
terms are built for the bindings of every occurrence of the rule's
left-hand side, which is exactly where the rule could fire, and nowhere
else.  A premise variable the left-hand side does not bind still ranges
over the seed relation (`Avaliable`, or `Origin` under
`--rare-seed-from-goal`), under its sort guard.  On the way: `SortString`
and `SortRegLan` relations (constants, `str.*`/`re.*` heads, declared
result sorts) so string parameters are guarded like the numeric ones.
The k-series is 0.2--0.3 s at every k up to 28; `bridge.2` checks in 0.3 s
and `dead_dnd005` in 0.9 s, all holes proved.

**What the old demand had been masking (fix 2, fix 3).**  The ten-sample
`nset` pass with the new demand lost 16 arithmetic holes (30_30_18: 8,
FISCHER9: 8) of the shape `(< x t) = (>= (+ ...) 1)` while gaining 23
(tgc's 17 memory kills among them).  On the reproducer `(= (< m e) (>= (- e
m) 1))` the halves held (`(< m e) = (>= e (+ m 1))` by `arith-elim-int-lt`;
`(>= e (+ m 1)) = (>= (- e m) 1)` by the relation keys) and the whole did
not.  Dumping the key tables at the failure: the class of `(< m e)` -- which
by then also held `(not (>= m e))` and `(>= e (+ m 1))` -- carried
`GeqKey (e - m)`, the untightened polynomial, while `(>= (- e m) 1)` carried
`GeqKey (e - m - 1)` and the strict-order rule had correctly computed the
latter for `e - m`.  `relPolyOf` is one value per class with `:merge old`;
the `<` node's rules had written the polynomial that is *positive* (`e -
m`), and the `>=` node's key rule, matching the same class, read it back
as a `GeqKey`.  With the all-pairs demand the `>=` node's write happened to
land first.  Nothing reads the strict `relPolyOf` (the strict keys come from
`strictOrderBoolKeyN`), so the ten rules writing it for `<` and `>` are
gone (`arith_poly_norm_rel.egglog`).  And on the way there, the bounded
saturation loop (`run_statement_within_deadline`) stopped when the tuple
count was unchanged between iterations, which an iteration that inserts one
tuple and merges one away satisfies with its demands still pending; it now
stops on egglog's own `updated` report.

Ten samples, `rewrite` arm, `nset` pass (30 s per hole, 300 s per pass,
3M/500k caps, 4 workers), 387b0882 against the three fixes:

| sample | 387b0882 proved / holes, pass s | with the fixes |
|---|---|---|
| 30_30_18_1 | 462 / 462, 43 s | 462 / 462, 28 s |
| clocksynchro_3 | 191 / 196, 37 s | **196** / 196, 16 s |
| cut_lemma_01_008 | 126 / 126, 8 s | 126 / 126, 10 s |
| ex4880 | 672 / 673, 77 s | **673** / 673, 49 s |
| FISCHER9 | 1,511 / 1,511, 62 s | 1,511 / 1,511, 43 s |
| MULTIPLIER_3 | 272 / 272, 9 s | 272 / 272, 10 s |
| RF-09 | 2,079 / 2,079, 115 s | 2,079 / 2,079, 115 s |
| ring_2exp10 | 349 / 349, 13 s | 349 / 349, 13 s |
| tgc_io-safe-6 | 123 / 140, 87 s (17 memory) | **140** / 140, 8 s |
| vpm2-0 | 2,079 / 2,081, 96 s | 2,079 / 2,081, 56 s (2 growth-cap) |

Every hole of the sample except vpm2's two growth-cap holes, and the
passes 1.3--10x faster where the old demand had been feeding the e-graph.

Regression tests (`rare::engine::tests`): the 16-conjunct reflexive
conjunction over an uninterpreted sort under 20 s, `eq-cond-deq` firing on
`(= (= x 1) (= x 2))`, and `(< m e)` / `(> e m)` against `(>= (- e m) 1)`.

**Left for the elaboration side.**  The same Boolean holes now check in
milliseconds but do not reconstruct: the search on the 16-conjunct goal
ends with `no certificate` and zero rule instances, so the `and`-with-`false`
step in the set-form encoding is not a candidate edge.  That is the next
gap for QF_UF elaboration, with the polynomial-relation shape of §47.3 for
QF_LIA.  The run `rw1` continues with the old binary; the next run gets
these fixes (with the checking pass folded into elaboration: one 1,500 s
pass at 60 s per hole).

### 47.7 Run `rw1` complete (2026-09-23): the read

All 9,812 benchmarks, binary 387b0882 (before the §47.6 fixes).  Against
enc4's `nset` arm on the proofs complete in both:

| | QF_UF (4,315) | QF_LIA (2,531) | QF_LRA (524) |
|---|---|---|---|
| proof text, rw1 / enc4 | 22.0 / 22.3 GB | 3.2 / 6.3 GB | 1.9 / 3.2 GB |
| holes, rw1 / enc4 | 1.17 M / 2.23 M | 723 k / 1,766 k | 435 k / 1,234 k |
| holes proved, rw1 / enc4 | 99.6% / 99.9% | 95.8% / 99.2% | 85.7% / 94.8% |
| proofs fully checked, rw1 / enc4 | 2,406 / 4,078 | 2,264 / 2,361 | 268 / 310 |
| fully checked in one arm only, rw1 / enc4 | 0 / 1,672 | 5 / 102 | 41 / 83 |
| checking pass, summed, rw1 / enc4 | 49 / 11 h | 28 / 17 h | 15 / 21 h |
| holes skipped by the pass budget, rw1 / enc4 | 101 / 715 | 24,090 / 9,411 | 58,147 / 51,742 |

Solved by cvc5 (60 s) at `rewrite`: QF_UF 4,316 (enc4 4,325), QF_LIA
2,541 (2,547), QF_LRA 524 (537) -- the granularity costs it a dozen
proofs per logic, printing time mostly.

**What the granularity buys.**  Half the proof text and 2.4--3.6x fewer
holes on the arithmetic logics (QF_UF proofs are the same size: their
holes were already node-sized).  QF_LRA checks in less time with the same
hole rate on what it reaches, and is the one logic where the rewrite arm
fully checks proofs the baseline cannot (41 against 83).

**What it loses, and why it is the engine (§47.6).**  QF_UF: 1,652
QG-classification and 57 Goel proofs with one or a few Boolean holes over
an uninterpreted sort that the all-pairs demand rules blew up; fixed, both
reproducers check in under a second.  QF_LIA: Dartagnan, 76 proofs, none
fully checked, 44 at the pass budget with 20.5 k holes skipped (enc4: 5
checked, 14 at budget), whole-assertion goals each fed for seconds by the
same demand.  QF_LRA: the three families with 40--110 k holes per few
proofs (`sc`, `uart`, `tta_startup`) are skipped in both arms and are a
throughput question; the loss that is the engine's is LassoRanker, 17 of
67 fully checked against enc4's 65, on `hole-time` kills.  Of the eight
smallest QF_LIA/QF_LRA proofs with a kept hole replayed under d78da84d,
all four QF_LRA cases prove the holes that timed out (three under a
second, one in 19 s) but one 154-node `MACRO_SR_PRED_INTRO` disjunction
that still saturates past 60 s; the four QF_LIA cases fail fast (0.6 s)
with honest `unproved` verdicts instead of 60 s time-outs.

**Two rule-side gaps those fast failures expose.**  Integer infeasibility
`(= (+ (* 3 x1) (* 3 x2)) 1) = false` (no rule).  And nested Boolean
simplification: each piece proves alone (`and`-flattening, double
negation, `(<= x x) = true` with the normalizer), but `(and s (not (not
(and p q)))) = (and s p q)` fails without the normalizer and passes with
it, while the full RF-12 goal it comes from passes without and fails with:
flattening a nested `and` in the set-form encoding is order-sensitive
once a rewrite unions the nested class.  Next egglog-side item after the
elaboration search.

**Elaboration.**  Fully justified against fully checked: QF_UF 1,167 /
2,406, QF_LIA 1,445 / 2,265, QF_LRA 185 / 268.  Per-hole kills in the
elaboration pass by phase: QF_LIA egglog 5,035 / search 275 / serialize
16; QF_LRA 1,096 / 64 / 9; QF_UF egglog 5,205 / search 4,232 / serialize
1,937.  The arithmetic kills are egglog's and fall to the demand fix; the
QF_UF search and serialization cost on coarse holes remains.
`no-certificate`: QF_LIA 23.4 k, QF_LRA 6.4 k (the §47.3 relation shape),
QF_UF 508 (the Boolean shapes above: the search sees zero rule instances
for the set-form `and`-with-`false` step).

**The untagged ceiling.**  Proofs with an untagged hole (`THEORY_LEMMA`,
`THEORY_INFERENCE_ARITH`, subtype-elimination trust steps): QF_UF 1,890 of
4,316, QF_LIA 1,148 of 2,541, QF_LRA 320 of 524; no Carcara change moves
them.  Of the proofs without one, re-check `valid`: QF_UF 257 of 2,426,
QF_LIA 962 of 1,393, QF_LRA 181 of 204.

**`rw2`.**  The d78da84d static binary, the checking pass folded into one
1,500 s elaboration pass at 60 s per hole, the same sets; read against
this run's tables.

### 47.8 The elaboration side of the coarse Boolean holes (2026-09-24)

After §47.6 the QF_UF holes check in milliseconds and do not reconstruct:
`no certificate`, zero rule instances.  Four things stood between the
search and the certificate, all in `reconstruction/search.rs` and
`term.rs` (commit c1b8f298):

- The engine proves the absorbing step `(and ... false ...) = false` on
  the set form, with a built-in rule: no rule instance in the e-graph for
  the search to follow, and no rule in the file for a step to cite.  The
  rule file now states `bool-and-true/false`, `bool-or-true/false`,
  `bool-and/or-flatten` and `bool-and/or-dup` (what cvc5's `ACI_NORM`
  does in one step), and a `:list` rule instance matched against the goal
  as a sequence is a goal-directed edge of the search
  (`CandidateEdge::ListRule`, justified by the existing
  `prove_by_list_rule`).  The rules also close the nested-`and` goals
  whose outcome depended on the normalizer's ordering (§47.7).
- The constant-substitution candidates of a vertex walked its positions
  depth first with a cap of 32; an encoded variable is a dozen nodes deep,
  so the budget went inside the first argument and the third element of
  four, the one holding the constant, was never a candidate.  Breadth
  first, atoms not entered, cap 256.
- The search keeps the first edge it meets to a neighbour and bans the
  pair when the edge fails to justify: a congruence towards the goal `F`
  (the whole application replaced by its class constant) came before the
  list rule towards `F`, and its failure took both down.  A vertex now
  keeps its most replayable edge per neighbour (rule, list rule,
  computation, ACI modulo, congruence).
- Grounded instances and list segments come from the e-graph in its
  re-associated chains, `(Args (Args a b) rest)`, and pair cells `(Args a
  b)`; such a term neither decodes to Alethe nor equals the flat vertex the
  search stands on.  Instances are read in flat chain form (which also
  turns the re-association rewrites into identities, so no `gen-N` step
  cites them) and a pair cell ends a chain as its last element.

The k-series reconstructs in 0.3--1.1 s and re-checks `valid` at k = 4,
16, 28; `bridge.2` (5 holes) and `dead_dnd005` (21 holes) elaborate fully
and re-check `valid`.  The three micro goals of the §47.3 relation shape
(`(= (= (not (not (>= P c))) (>= P' c)) true)` and its halves) elaborate
and re-check `valid` as well.  Five samples, `rewrite` arm, elaboration at
45 s per hole (the §47.3 table's last column against now):

| proof | holes | 42a2a85b justified / pass | c1b8f298 |
|---|---|---|---|
| clocksynchro_3 | 196 | 191 / 93 s | **195** / 90 s |
| cut_lemma_01_008 | 126 | 112 / 22 s | **126** / 17 s |
| MULTIPLIER_3 | 272 | 267 / 14 s | **272** / 16 s |
| tgc_io-safe-6 | 140 | 117 / 217 s | **140** / 12 s |
| ring_2exp10 | 349 | 339 / 30 s | **349** / 22 s |

The one hole left (clocksynchro, a `MACRO_SR_PRED_INTRO`) is the 154-node
disjunction class of §47.7.  Every re-check is `holey` on the untagged
holes alone (`THEORY_INFERENCE_ARITH`, `MACRO_THEORY_REWRITE_RCONS_SIMPLE`)
plus the `arith_poly_norm_rel` trust steps the certificates still carry
(§1).  Not done: the integer infeasibility `(= (+ (* 3 x1) (* 3 x2)) 1) =
false` of §47.7, one benchmark, which needs a `la_generic` recipe rather
than a rule.

Regression: `elaborates_reflexive_disequality_conjunction`
(`tests/rare/elaborate/and-reflexive.*`, six conjuncts, sort guards on).
## 48. Smallest goal first (2026-09-23)

`--hole-smallest-first` orders the checking pass's worklist by the DAG size
of each hole's goal (as egglog gets it) instead of the proof's order.  The
reason is §43's reading of arithmetic: where it loses, it loses holes that
were never attempted before the pass budget ran out (30.6% of QF_LIA's and
54.3% of QF_LRA's in `vb50-2`), and a proof counts only when all its holes
close, so the budget should go to as many holes as it can cover.  The
proof's order spreads the large goals over the pass, which is the
opposite.

Plain `set-form`, no normalizer, the budget binding, the same settings as
the baselines of §43 (`scratchpad/order/run.sh`):

| proof | holes | proof order | smallest first | goal sizes |
|---|---|---|---|---|
| Dartagnan `count_up_down-1` (4 workers, 300 s) | 9,850 | 3,845 | 4,167 | 7 to 21,254 nodes |
| LassoRanker `p-46` (2 workers, 600 s) | 2,854 | 43 | 526 | 5 to 429 |
| `tta_startup 14nodes` (2, 600 s) | 1,793 | 28 | 740 | 7 to 15,193 |
| miplib `fixnet-1000` (2, 600 s) | 4,635 | 19 | 1,427 | 4 to 126 |

Twelve to seventy-five times more holes proved in the same budget on the
three QF_LRA proofs.  It matters only where the budget binds: with the
normalizer these proofs close almost entirely before egglog (§43), so the
option is for the residue that stays budget-bound, and it costs nothing
where the budget does not bind.  Not combined with `--hole-reuse-subst`,
which has its own order.  (The `fixnet` pass in the proof's order ran
1,155 s of wall time against a 600 s budget; in the smallest-first order
600 s.  The post-summary stall of `VERIT-PLAN.md` item 4 again.)

## 49. Normalize to close only, or also rewrite the goal?  Settled locally (2026-09-24)

The question from §43: when the normalizer cannot close a hole, should the
checking pass hand egglog the equality of the normal forms (today) or the
hole as stated?  §43's evidence for "as stated" was veriT-only (the
flattened `la_rw_eq` goals, 1.6--4.5 times dearer), and nothing had been
measured on cvc5.

**Design.**  `--hole-prenormalize-close-only` makes the normalizer only
close; a hole it cannot close goes to egglog unchanged.  Two arms on the
same proofs, both normalizing, differing only in that choice: R (the
normal forms, today) and C (close only).  Pass budget 3,600 s, so every
hole is attempted in both and the comparison is per hole; 60 s and 5 GB per
hole, 4 workers, caps 3M/500k, `set-form`, arm order alternating by proof
(`scratchpad/closeonly/run.sh`, `analyze.py`).  Every hole the normalizer
leaves open is now logged at info level as `prenorm open, goal
rewritten|kept|unchanged` with the DAG sizes of the goal and its normal
form.  Holes whose normal form *is* the goal are the same goal in both
arms: the noise floor.

**Corpus.**  The normalizer rewrites almost nothing in QF_UF (178 of 48,183
hole steps of the 96 local cvc5 proofs), so the question is arithmetic's:
19,200 rewritten hole steps in QF_LIA, 46,718 in QF_LRA.  Ten local cvc5
proofs (`~/benchmarks/egglog-holes-eval`, same options as `enc4`) from the
families where it rewrites without closing: SMPT, bofill and mathsat in
QF_LIA, `sal` (gasburner, pursuit, tgc), `spider`, `tta_startup` (two) and
`uart` in QF_LRA; plus the two veriT QF_LRA proofs with rewritten holes
left after the `la_rw_eq` fold (`p-46`, `fixnet-1000`).

**Noise floor.**  3,962 unchanged open holes: identical verdicts, per-hole
time R/C geometric mean 0.99 (p10 0.89, p90 1.11).

**Verdicts on the 4,989 rewritten holes:** both prove 4,920, only the
normal form 61, only the goal as stated 1, neither 7.  The 61 are 56
gasburner holes and 5 of `p-46`: the stated goal runs to the 60 s kill,
the normal form proves in 0.17 s median (13.5 s at most).  The one the
other way is a memory kill in one `tta10` hole whose normal form is the
same size as the goal, i.e. noise.  A gasburner example: `(= (<= X c) ..)`
with `X` a chain of nested counter `ite`s under `(* -1 ..)`, 69 DAG nodes;
the normalizer takes the `ite` as an atom (§38) and hands egglog 33 nodes,
proved in 0.34 s, where egglog's own polynomial normalizer on the stated
goal never finishes.

**Per proof.**  Fully proved: R 10 of 12, C 9 of 12 (C loses gasburner and
`p-46`, R loses `tta10` on the one memory kill).  Egglog time on open
holes, summed: R 1,772 s, C 6,079 s; without gasburner and `p-46`, R 1,466 s
and C 1,575 s.  R also needs 4.4% fewer egglog runs (6,173 against 6,458):
normalization makes some distinct goals identical, and duplicates share a
verdict.

**Where the rewrite costs: the size of the normal form decides.**

| rewritten holes | holes | egglog time R | C | per-hole R/C, geo-mean (p10, p90) | verdicts |
|---|---|---|---|---|---|
| normal form smaller | 1,605 | **694 s** | 5,029 s | **0.72** (0.43, 1.29) | all 61 R-only wins |
| same size | 1,462 | 110 s | 148 s | 1.00 (0.90, 1.10) | the 1 C-only (noise) |
| normal form larger | 1,922 | 489 s | **380 s** | **1.46** (1.00, 2.39) | no difference |

The veriT goals are all in the last row: `fixnet`'s 500 rewritten holes are
all larger in normal form (113 s against 49 s), and so are 246 of `p-46`'s
288.  The polynomial normal form with its `(* -1 x)` monomials and
`to_real` wrappers is larger than what veriT printed, and costs egglog
more; that is §43's slowdown, measured directly.  The cvc5 goals are mostly
in the first two rows.

**Answer.**  Close-only is wrong: it gives up every hole in the first row
where the stated goal is out of egglog's reach, 61 here, and quadruples the
egglog time.  What the data supports is the size test I first proposed and
then withdrew: **hand egglog the normal form when it is not larger than the
goal, the goal as stated otherwise.**  On these proofs that keeps all of
R's verdicts and would cost 694 + 110 + 380 = 1,184 s of egglog time against
R's 1,293 s and C's 5,557 s.  The withdrawal argued that a flattened goal
is smaller yet dearer; the goals that are dearer here are the larger ones,
and the flattened `la_rw_eq` goals it was about are now closed by the fold.
(That estimate ignored merging; the measured figure is below.)

### The size rule, implemented and measured (2026-09-24)

`--hole-prenormalize-not-larger` (with `--hole-prenormalize` and
`--hole-check-only`) replaces the close-only switch, which is gone: an
unclosed hole takes the equality of its normal forms to egglog when that
is not larger in DAG nodes than the goal, and the goal as stated
otherwise.  Every open hole is still logged with both sizes (`goal
rewritten` or `goal kept`), and `hole prenorm kept: N goals as stated`
counts the second kind.  Off by default: without it, today's behaviour.

A first run of the new mode alone was not comparable: on identical goals it
ran up to twice as slow as the interleaved arms (`spider` 2.01, `tta6`
1.63), the local CPU's frequency drift.  So today's behaviour (R) and the
new mode (N) were rerun interleaved, proof by proof, arm order alternating
(`scratchpad/closeonly/run-rn.sh`, logs in `logs2/`); on identical goals
R/N is 0.98 overall.

| | egglog runs | egglog seconds | pass time | holes not proved | proofs fully proved |
|---|---|---|---|---|---|
| R, all 12 | 6,166 | 1,793 | 511 s | 8 | 10 |
| N, all 12 | 6,400 | **1,753** | **500 s** | 8 | 10 |
| R, the two veriT proofs | 789 | 398 | 100 s | 0 | 2 |
| N, the two veriT proofs | 789 | **285** | **72 s** | 0 | 2 |
| R, the ten cvc5 proofs | 5,377 | **1,395** | **411 s** | 8 | 8 |
| N, the ten cvc5 proofs | 5,611 | 1,468 | 428 s | 8 | 8 |

Verdicts are identical, hole for hole.  The time splits by producer:

- **veriT gains 28%** (`fixnet` 113 s to 51 s, `p-46` 285 s to 234 s): its
  normal forms carry `(* -1 x)` and `to_real` that the printed goal did not,
  and egglog pays for them.
- **cvc5 loses 5%**, and the cause is not the per-hole cost: cvc5's larger
  normal forms prove at the same speed as its stated goals (the per-proof
  split in the size table above is at parity for every cvc5 proof).  It is
  merging: normal forms coincide across holes that differ as stated, so R
  runs egglog 234 fewer times on the cvc5 proofs (`gasburner` 574 against
  652, `spider` 316 against 358), and at 0.3 s a run that is the 73 s.

So the size rule alone is right for veriT's proofs and slightly wrong for
cvc5's.  The earlier estimate of 1,184 s missed exactly the merging.

**Refinement: keep a larger normal form that another goal also reaches.**
The rule now keeps a hole's larger normal form when a hole with a
*different* stated goal, in the same context, reaches the same normal form
(an unchanged hole counts with its goal as its normal form); duplicates of
one stated goal do not count, since they merge anyway.  That is exactly
the case in which rewriting saves an egglog run.  The prenormalization
now runs in two passes, normal forms first, decisions second, and logs
`hole prenorm kept: K goals as stated, ...; S larger normal forms used,
another goal reaching them`.

Interleaved against the default on the same twelve proofs
(`scratchpad/closeonly/run-rn3.sh`, logs in `logs3/`):

| | egglog runs | egglog seconds | holes not proved | proofs fully proved |
|---|---|---|---|---|
| default, all 12 | 6,166 | 1,911 | 8 | 10 |
| refined rule, all 12 | **6,166** | **1,691** | 7 | 10 |
| default, ten cvc5 proofs | 5,377 | 1,505 | 8 | 8 |
| refined rule, ten cvc5 | **5,377** | 1,384 | 7 | 8 |
| default, two veriT | 789 | 407 | 0 | 2 |
| refined rule, two veriT | 789 | **306** | 0 | 2 |

Every merge comes back: the refined rule runs egglog exactly as often as
the default (the size rule alone ran it 234 more times).  Of the larger
normal forms, 311 are now used because another goal reaches them
(gasburner 78, spider 47, tta6 40, pursuit 38) and 1,633 are still kept as
stated, all veriT's 746 among them.

On cvc5 the gain is mostly one proof.  SMPT's control on identical goals
is 1.22, i.e. its default arm ran 22% slow; without SMPT the cvc5 proofs are
at parity (1,046 s against 1,032 s), which is what the size table
predicts once the merges are kept: cvc5's larger normal forms cost what its
stated goals cost.  veriT keeps its 25%.  The extra hole proved is in
`tta6`, one at its limit.  So the refined rule is at least as good as the
default on both producers, and it is the one to run.

**Now the default.**  With `--hole-prenormalize --hole-check-only` the rule
applies without any flag; `--hole-prenormalize-not-larger` is gone, and
`--hole-prenormalize-rewrite-all` restores the previous behaviour (every
unclosed hole as the equality of its normal forms), for comparisons with
the runs made before this change (`enc4`, `vb50-2`, `vnob-2`, `rw1`).  On
`fixnet-1000` the default keeps all 500 open holes as stated and the
opt-out rewrites all 500, verdicts identical.


### 47.9 Run `rw2` (submitted 2026-09-24)

Arrays 32360346 (rw_QF_UF, 4,316), 32360347 (rw_QF_LIA, 2,541), 32360348
(rw_QF_LRA, 524) on `octa`, two tasks per node, 8 cores and 60 GB each, wall
3,100 s; results `exp/results/egglog-holes/rw2`.  The sets are the
benchmarks cvc5 proved within 60 s in rw1 (`gen-rw-sets.py`), so no task
is spent on a cvc5 time-out.  Same cvc5 binary as rw1; carcara 3f982c71
(§47.6, §47.8, the merges of bounded-parallel-holes up to 873faa0c:
smallest goal first, the normal form handed to egglog only when not
larger or shared, and the phase on memory kills).  The checking pass is
folded into elaboration: hoist + prune, one elaboration pass of 1,500 s
at 60 s and 6 GB per hole (set form, normalizer, sort guards, abstraction
16, caps 120M/20M, smallest first), re-check 900 s.  Runner
`~/exp/egglog-holes/run-holes-rw2.sh`, keys as rw1's with the `chkp_*`
keys `none` and two new ones per pass, `elab_killed_during_egglog` and
`elab_killed_after_egglog`.

Read: checking-only = justified + no-certificate + checker-rejected +
killed after egglog (a worker that died in serialization or the search
had its hole proved); checking + elaboration = justified.  The caveat is
the budget: check and reconstruction share the 60 s per hole and the
1,500 s per proof, so the pass covers fewer holes than a pure checking
pass would; the checking baseline is rw1's `chkp` keys on the same
benchmarks (§47.7), the elaboration baseline rw1's elaboration keys.

### 47.10 Run `rw2` complete (2026-09-25): the read

All 7,381 tasks (the benchmarks cvc5 proved in rw1, so every task has a
proof).  Checking-only is read from the elaboration pass as justified +
no-certificate + checker-rejected + killed after egglog; rw1's checking
pass and enc4's `nset` arm on the same benchmarks are the baselines.

| | QF_UF (4,316) | QF_LIA (2,541) | QF_LRA (524) |
|---|---|---|---|
| holes | 1.22 M | 748 k | 505 k |
| **checked**, rw2 / rw1 / enc4 | 99.9% / 99.6% / 99.9% | 99.7% / 95.8% / 99.2% | 99.5% / 85.7% / 94.8% |
| proofs checked, rw2 / rw1 / enc4 | 3,844 / 2,406 / 4,078 | 2,280 / 2,265 / 2,361 | 332 / 268 / 310 |
| **justified** (holes), rw2 / rw1 | 99.5% / 98.9% | 99.5% / 94.3% | 99.4% / 86.2% |
| proofs fully justified, rw2 / rw1 | 1,907 / 1,167 | 2,263 / 1,445 | 326 / 185 |
| fully justified in one run only, rw2 / rw1 | 741 / 1 | 850 / 32 | 141 / 0 |
| re-check `valid` (proofs without untagged holes), rw2 / rw1 | 322 (2,426) / 257 | 982 (1,393) / 962 | 202 (204) / 181 |
| holes skipped at the budget, rw2 / rw1 (check+elab) | 33 / 401+1,007 | 481 / 24,090+13,673 | 29 / 58,147+58,758 |
| carcara time, rw2 / rw1 (check+elab) | 80 h / 166 h | 38 h / 81 h | 21 h / 41 h |

Checking at `rewrite` granularity now matches theory-rewrite on QF_UF
(99.9%) and beats it on the arithmetic logics (QF_LIA 99.7% against
99.2%, QF_LRA 99.5% against 94.8%), on a proof text half the size, in
half the time of rw1, with the pass budget no longer binding anywhere
(33 / 481 / 29 holes skipped against tens of thousands).  QF_LRA fully
justifies 326 of 524 proofs against 185, and re-checks `valid` 202 of the
204 proofs that have no untagged hole.

**Residue.**  QF_UF: QG-classification, 2,364 of 3,851 proofs not fully
justified on 2,103 `no-certificate` and 3,119 per-hole kills after
egglog (search and serialization on the coarse Boolean holes; 137 checker
rejections of an `and_simplify` step on a nested conjunction); Goel 37 of
227.  QF_LIA: Dartagnan 76 of 78 (1,063 no-certificate, 999 kills, 225
memory, 481 skipped), SMPT 113 of 1,520 (84 decode failures), rings 35 of
84 (216 decode failures).  QF_LRA: the hole-heavy families `sc`, `uart`,
`tta_startup`, `spider` (kills during egglog, 2,351 of QF_LRA's 2,377).

The no-certificate holes replayed locally are Boolean simplification
chains with many constant-valued arguments at once: `(not (=> (and ...)
(= x x))) = false`; a Goel conjunction of `true`s and reflexive
equalities with `(= (not true) (and ...))` among them; `(not (or (or (and
...) (or ...)) ...)) = false` over `<=` atoms; and the integer
infeasibility of §47.7.  The search substitutes one constant per
congruence edge and proves the children one at a time, so a goal with
eight reflexive equalities needs eight levels; a congruence candidate that
replaces every constant-valued argument at once is the natural next step,
with the decode failures (`a certificate term failed to decode`, SMPT and
rings) and the `distinct_elim` / `and_simplify` checker rejections on
Dartagnan and QG to reproduce and fix.  Untagged holes cap `valid` as
before: 1,890 / 1,148 / 320 proofs have one.

### 47.11 rw2's residue, reproduced and fixed (2026-09-25)

Replayed locally, the smallest proofs of each residue class of §47.10
(commits 36cc79fa, fedf0b31):

- **Decode failures** (SMPT 84, rings 216, Rodin): a congruence spine
  the search met from the far side arrives under `Symm` nodes, a
  reversed chain being the reversed legs in reverse order; the spine
  descent found no `cong` premises in it.  It reads `Symm` as a flip now.
- **Checker rejections of `and_simplify` / `or_simplify`** (QG 137,
  SMPT): the `AciComplement` computation finds the complementary pair
  through nested `and`/`or`, the checker's rule reads the direct arguments
  only.  The flat form is stated first by `aci_simp`.
- **`no-certificate` on Boolean chains with many constant arguments**
  (QG-classification, Goel, CLEARSY, SMPT): the search substituted one
  constant per congruence edge and spent its four rejustifications on
  congruences between an `and` and an equality, both wrapped members of
  the `true` class.  Now: a candidate with every constant-valued subterm
  replaced at once (outermost positions, not the application itself); the
  ACI computation as the checker's `aci_simp` in full (flatten, drop
  identities and duplicates, a lone element or the identity left); a
  one-step checker computation tried before the congruence and the search;
  no congruence between two heads (the application-level constant
  candidate is gone, `congruence_certificate` and the goal-directed
  congruence require one head below the wrapper); among several edges to
  one neighbour a congruence yields to any other kind.
- **`(<= p p)` inside a disjunction** (SMPT RC-07): no rule states a
  reflexive relation (cvc5 normalizes it), the normalizer closes it, and
  the not-larger rule had kept the stated goal (26 nodes against 27).  The
  rule is confined to the checking pass; the elaboration pass tries the
  normal form first whatever its size, the stated goal on a failure.

Every reproducer elaborates and re-checks (`valid`, or `holey` on the
untagged holes alone).  The Dartagnan proof of §47.10: 200 of 231
justified (198 before), no checker rejection or decode failure, 22
`no-certificate` left on arithmetic Boolean chains.  Five samples,
elaboration at 45 s per hole, against §47.8:

| proof | c1b8f298 justified / pass | fedf0b31 |
|---|---|---|
| clocksynchro_3 | 195 / 90 s | 195 / 65 s |
| cut_lemma_01_008 | 126 / 17 s | 126 / 7 s |
| MULTIPLIER_3 | 272 / 16 s | 272 / 7 s |
| tgc_io-safe-6 | 140 / 12 s | 140 / 5 s |
| ring_2exp10 | 349 / 22 s | 349 / 11 s |

Passes twice as fast: the one-step computations and the all-constants
candidate replace levels of search.  Regression fixtures:
`reversed-spine`, `nested-complement` (§47.8's `and-reflexive` covers the
rest).  Left: the arithmetic chains of Dartagnan, the hole-heavy QF_LRA
families (egglog time, not the search), the integer infeasibility of
§47.7.

### 47.12 The `rw2` report (2026-09-25)

`report-rw2/report.tex` (LaTeX, the structure of the first report; `make-rw2.py` renders its tables and plots from the results file) reads the run on its own terms (yield, cost,
residue by class and family, the state of the tooling at fedf0b31) and
plans the three open directions.  Two corrections to §47.10–§47.11 it
makes: the SMPT 84 and rings 216 `worker-error` holes are egglog `Check
failed` verdicts (goals egglog could not prove as stated), not decode
failures -- the decode class is 46 holes in all, 42 of them Dartagnan;
and 294 QF_LIA proofs that are fully justified with no untagged hole
re-check `holey` on the `arith_poly_norm_rel` trust steps the elaborator
emits when the relation routing does not cover an obligation.  A third
correction, found by checksum against the cluster's copy: rw2 ran on the
171-rule `holes-rw2.rare` (bit-vector and string rules included); the
local `holes.rare` was trimmed to 91 rules on 2026-09-24 after the
upload (§50), so every rw2 number is with the larger file.  New
facts from the local replays behind the plans: `sc-5.base.cvc` (415
holes) keeps 14 under fedf0b31 -- 7 goals of 59 nodes egglog cannot
prove, 5 of 114 nodes it does not finish in 60 s, 2 without certificate;
the integer infeasibility `(= (+ (* 3 x1) (* 3 x2)) 1) = false` has a
two-`la_generic` recipe the checker accepts (`scratchpad/gcd/p.alethe`,
`valid`), and the normalizer, contrary to §25's specification, does no
integer tightening: it scales the relation to `(= (+ x1 x2) 1/3)` and
stops.

### 47.13 Consolidating with `egglog/bounded-parallel-holes` (2026-09-25)

`main` itself has not moved (`bounded-parallel-holes` is 146 commits
ahead of it, `rewrite-holes` 167); the trunk of the egglog work is
`egglog/bounded-parallel-holes` in `wt-tiago`, merge base 873faa0c.  Since
the base it has four commits, this branch twenty-one (three of them
merges of it).  Item by item:

| trunk commit | this branch | verdict |
|---|---|---|
| 6fa30dbf premise sides seeded per left-hand-side match (`__premise_root`), set-form compilation refuses conditional rules, list-slot variants get their own seeds, test on `big.rare` | d78da84d the same idea two days earlier (`demand_site`): one demand rule per premise at the left-hand side's occurrence, unbound premise variables from the seed relation under their sort guard, no all-pairs seeding left at all; String/RegLan sort relations; strict `relPolyOf` writes removed; saturation stopped on egglog's report; three engine tests | same fix twice, both measured (trunk: 56 to 6 kept on 23 local proofs; here: rw1 to rw2 on 7,381).  Keep `demand_site`; port the two things it lacks, demand rules for the list-slot variants and the set-form refusal of conditional rules, and their test renamed |
| 173e122d the set-form element collection requires an `Mk` head (`aci_norm.rs`) | c1b8f298 reconstruction of set-form steps (`ListRule` edges) and the `bool-*` flatten/absorb/dup rules | complementary: the trunk fixes the e-graph's set of a derived `and`, this branch the certificate for a set-form step, which §50 lists as its open caveat.  Take both |
| 638711fe `big.rare` without the 80 bit-vector and string rules (161 to 81) | `big.rare` plus the eight `bool-*` rules (169) | take both: 89 rules, `holes.rare` already is that file.  The String/RegLan guards of d78da84d then guard nothing in the test database and stay |
| 141a6cbe `abstractable_size` memo fix in `abstraction.rs` | untouched here | take as is |

Nothing in the trunk's four commits is absent from or better than this
branch except the three details above; nothing of this branch's
reconstruction, elaborator, prepass and search work (fedf0b31) exists on
the trunk.  A dry-run merge conflicts in `engine.rs` (the two seedings),
`big.rare` (deletion against appended rules) and the notes (§50 against
§47.9–§47.12); `tests/mod.rs` and `abstraction.rs` merge clean.

Plan: (1) merge `bounded-parallel-holes` into `rewrite-holes` resolving
`engine.rs` for `demand_site`, `big.rare` as the 89-rule file, the notes
by keeping both sections; (2) port the variant demand rules and the
set-form refusal, adapt `premise_instances_are_seeded_from_left_hand_side_matches`
to `demand_site`; (3) `cargo test --lib` (286 + the trunk's 3 new tests)
and the five-sample local batch plus `tta_startup 6nodes` (§50's six
holes) as the regression gate; (4) fast-forward `bounded-parallel-holes`
to the result and have the other session rebase its worktree onto it, or
retire that branch name; (5) the static binary and `rw3`.  Later, a
squash onto `main` is a separate decision: the branch carries the
`EGGLOG-*` notes and the `tests/rare/elaborate` fixtures, which belong,
and the demo/scratch files of the worktree, which do not.
## 50. The set-form anomaly and the `ite` residue, resolved in the engine (2026-09-25)

Items 11 and 12 of the list that produced `VERIT-PLAN.md`, done after the
normal-form rule (§49) and the smallest-first schedule (§48).  All
measurements local, one run at a time; scripts in `scratchpad/micro/`
(`micro.py` builds one-hole proofs), `scratchpad/guard/`,
`scratchpad/seed91/` and `scratchpad/tta6/`.

**Item 11: the flattening anomaly was a set-form bug** (`173e122d`).
`(and e (= 0 r))` against `(and e (<= 0 r) (<= r 0))` ran to the budget
while the nested form proved at once (§43).  Queried in the live e-graph
after the first round: both rewrites had fired and the right side's set
form existed, but the left side's flattened set did not, because the set
of the `and` that `arith-eq-elim-int` made held the *pair*
`(Args a b)` as one element.  Args-associativity keeps
`(Args (Args a b) tail)` in the class of `(Args a (Args b tail))`; the
element collection matched `(Args head tail)` with `head` unguarded and
`elementsOf` keeps its first value.  The per-call conversions already
required `head` to be an `Mk` term; the general conversion now does too.
The anomaly had been masked in the experiment file since 2026-09-24 by
the `bool-and-flatten` rule another session added; on the 161-rule base
it reproduced exactly.  Twenty-three proofs, interleaved: verdicts
identical, Boolean-heavy veriT proofs faster (`repgen006` 351 s to 113 s).

**The rule files lose bit-vectors and strings** (`638711fe`).  The
evaluation is QF_UF, QF_LIA and QF_LRA; the 80 rules over bit-vectors and
strings (50 `bv-`, 14 `str-`, 14 `re-`, 2 `uf-int2bv-`) could only fire on
terms their own premise seeds manufactured.  `tests/rare/big.rare` goes
from 161 to 81 rules; the experiment file `~/exp/egglog-holes/holes.rare`,
outside the repository, from 171 to 91 (the old one is kept as
`holes-171-with-bv-str.rare.bak`).  The fixed cost of a hole roughly
halves (0.10 s to 0.05 s on one-hole proofs).  Every measurement before
this point used the larger files.

**Item 12: the `ite` residue was premise seeding** (`6fa30dbf`).  The
residue of the cvc5 `tta_startup` proofs under the default normalizer was
seven memory kills, one of them `(= (ite A B false) (and A B))` over two
ten-literal conjunctions.  Its six-literal version, with the right side
flattened as the normalizer hands it over, proves in 0.1 s unnormalized
(the first check succeeds) and died past 2 GB normalized.  egglog's per-
rule report showed why: the first iteration was dominated by seed rules
`(rule ((Avaliable x1) (Avaliable y1)) ((Mk (@= x1 y1))))`, 361 matches
each over 19 goal terms, building premise terms of conditional rules for
every pair of available terms, whatever their sorts (string and
bit-vector ones over Booleans and reals included).  When the first check
fails, the fallback plans run another iteration over all of them, and
the pairs grow with the terms.  The trimmed rule file alone does not fix
it: `eq-cond-deq`'s `(= s1 r1)` and the array rules' `(= i1 j1)` are still
pair seeds.  Seeding a premise side from the matches of the rule's
left-hand side, under its sort guards, does; the old seeding stays for a
side with a variable the left-hand side does not bind (none in the
current database).  The set-form compilation, which drops premises, now
refuses conditional rules (none were affected).

On the 23 proofs, interleaved per proof on the 91-rule file:

| | holes not proved | pass seconds |
|---|---|---|
| old seeding | 56 | 903 |
| new seeding | **6** | **475** |

All 50 verdict changes go from kept to proved.  By group: veriT QF_UF 49
kept in 278 s to none in 13 s; cvc5 QF_LRA 413 s to 296 s (per hole 0.83);
cvc5 QF_UF the same; cvc5 QF_LIA 6% slower per hole, the one cost found.
With the 171-rule file the new seeding had cost cvc5's QF_UF holes about
10% more; that cost went with the bit-vector and string rules, most likely
`str-eq-len-false`, whose left-hand side `(= x1 y1)` matches every
equality and seeded a string term for each.

**The last six: shared-subterm abstraction had a bug** (this commit).
The six holes left, all in `tta_startup 6nodes`, were sliced out and run
alone (`carcara slice --from`; its two output files come out swapped
relative to the help text).  Four are a one-step rewrite at the top of
two sides sharing an `ite` whose condition has hundreds of nodes, e.g.
`(= (< (ite C 4.0 6.0) 4.0) (not (>= (ite C 4.0 6.0) 4.0)))`; egglog
rewrites all of `C` and dies.  `--hole-abstract-shared` exists for exactly
this and found nothing above four nodes: `abstractable_size` memoized a
variable or constant as `None` (not abstractable by itself), and at its
second occurrence returned that `None` as its size, so any term in which
a variable or constant occurs twice was never abstracted.  It may also be
why §45 saw it fire on `calypto` but not on Dartagnan, where the shared
parts it found were three-node atoms; not re-measured.  The memo now
keeps sizes.

| hole | before | fixed abstraction (16 nodes), with or without the normalizer |
|---|---|---|
| `t6699`, `t6710`, `t6891` | memory kill, 38-41 s | proved, 0.2 s |
| `t17932.t21` | memory kill, 34 s | proved, 0.07 s |
| `t17932.t16`, `t17964` | memory kill, 34 s | memory kill, 13-21 s |

The two left are `(= X true)` with `X` a formula of 535 and 666 distinct
subterms, 24 equality atoms under nested `ite`s, that cvc5's rewriter
found valid in one step; nothing is shared, so nothing is abstracted, and
egglog has to rewrite the whole formula.  Abstraction is off by default;
the cluster runner `run-holes-rw.sh` passes 16.

**Caveats.**  The seeding regression has no unchanged-goal control, so the
6% QF_LIA figure is within what drift has produced before (§49).  The
elaboration pass was not measured on any of this: with the 161-rule base,
egglog now proves the flattening goals but the certificate search finds
no certificate for the set-form flattening; with the experiment file it
cites `bool-and-flatten` and re-checks valid.

**Applied (2026-09-25, merge 1124ff62).**  Steps 1–4 done: `engine.rs`
keeps `demand_site` and gains the per-variant demand rules with the rule's
sort guards and the set-form refusal of conditional rules; the trunk's
seeding test runs against `demand_site`; `big.rare` is 89 rules (the
trunk's 81 plus the eight `bool-*`), `holes.rare` unchanged at 91.
`cargo test --lib` 290 passed.  Gates: the six `tta_startup 6nodes` holes
of §50 behave as recorded (four proved in 0.1–0.3 s, `t17932.t16` and
`t17964` memory kills at 20 s and 16 s); the five samples of §47.11 keep
their justified counts (195, 126, 272, 140, 349), `clocksynchro` 65 s to
48 s, the rest unchanged.  `egglog/bounded-parallel-holes` is
fast-forwarded to 1124ff62 in `wt-tiago` (clean at the time); the static
binary is rebuilt at 1124ff62.  Step 5, `rw3`, needs a staged proposal.

### 47.14 Integer tightening, relation orientation, and the structural descent (2026-09-25)

Three changes, the first two in the normalizer's `relation_step`
(`prenorm.rs`), the third in the hole worker (`rare_hole.rs`); the report's
§7 planned the first and the third, the second is what the third found.

**Integer tightening.**  Over Int, a relation whose scaled bound is not an
integer is rounded (`>=` up, `<=` down) or decided (`=` is `false`), and a
strict relation becomes the non-strict one of the adjacent integer.  The
certificate is a `la_generic` pair through the `equiv_neg` tautologies
(the `emit_bound_flip` recipe, with the scale as the stated relation's
coefficient); a decided equality refutes the helper bound `(>= P ceil b)`
both ways and states `(= from false)` by `equiv_simplify` and `equiv2`.
`la_generic`'s integer strengthening does the rounding.  Fourteen
`certificates_check` cases, among them `(= (+ (* 3 x) (* 3 y)) 1)` to
`false` and `(and (> x 2) (< x 4))` to `(= x 3)` through the fold;
fixture `int-tighten` closes a hole with both shapes in the normalizer and
re-checks `valid`.  The specification of §25 said this was there; it was
not.

**Relation orientation.**  `<=` and `<` are the `>=` and `>` of the
negated difference, certified by the same `la_generic` pair when a
relation is mirrored (`poly_simp_rel` keeps the symbol and stays for the
rest).  This is §37's proposal, done in the normalizer with a core rule
rather than `comp_simplify`.  The `la_rw_eq` fold pairs bounds by
polynomial and is orientation-agnostic.  What it does not reach: a
negated relation, `(not (>= x 2))` for `(<= x 1)`, which is cvc5's
`>=`-only normal form over Int; the normalizer does not look through
`not`.

**Structural descent** (`--rare-descend-min-nodes N`, option
`descend_min_nodes`, passed to the child).  A goal of at least `N` nodes
whose sides share a Boolean skeleton (`and`, `or`, `not`, `=>`, `xor`, an
`ite` or `=` over Booleans) is proved by `cong` from its argument pairs,
recursively; a pair the skeleton does not share is a goal of its own,
`{id}.d{n}`, through egglog, the snapshot, the search and the elaboration,
under the hole's remaining budget.  Under `and`/`or` the arguments are
matched, not paired by position (the normal forms order them by address):
identical ones first, the rest by the leaves they share, with an
`aci_simp` step on each side around the `cong`.  `(= (= a b) (= b a))`
is `eq_symmetric`.  The whole goal is the fallback when a pair fails.
The checking pass has the same descent (`check_by_descent`), each pair an
egglog check.  The child reports `phase descent=<pairs>` on success and
`descent-failed=<seconds>` on a fallback, which the parent's phases line
carries.  Fixture `descent`: two atom pairs under an `and`/`or` skeleton,
`.d1`/`.d2` steps, `valid`.

**Measured** (four workers, the run's options, `--rare-descend-min-nodes
32` where said):

| proof | before (merge 1124ff62) | tightening | + orientation | + descent |
|---|---|---|---|---|
| `sc-5.base.cvc` (415) | 399, 445 s | 399, 439 s | **413, 11 s** | 413, 10 s (22 descents, 0 failed) |
| Dartagnan `benchmark20_conjunctive` (231) | 200 | 201 | 201 | 202 (15 descents, 32 failed) |
| `int_incompleteness1` | unproved | closed by the normalizer, `valid` | | |
| five samples (195/126/272/140/349) | | | unchanged | unchanged, 45 descents, 2 failed |

The orientation is the `sc` fix: 214 of 415 holes close in the normalizer
(139 before) and every normal form handed to egglog proves; the two left
are `no-certificate`.  The descent found it: run at debug on `sc-5`, its
fifteen failed pairs were all one atom, `(<= (+ x (* -1 (ite (<= (+ (* -1
a) b) 0) b a))) 0)` against `(>= (+ (* -1 x) (ite (>= (+ a (* -1 b)) 0) b
a)) 0)`, the §37 mirror with the `ite` condition mirrored the same way.
On Dartagnan its 28 failed pairs are all `no-certificate` on `and` blocks
whose arity differs between the sides: `(and (= x 1) ...)` against
`(and (not (>= x 2)) (>= x 1) ...)`, cvc5's negated `>=` form, which the
normalizer does not orient and the fold therefore does not close.  That
is the next normalizer item, `(not (>= P c))` to `(< P c)` and then the
tightening, certified the same way once the double negation is handled.
Caveat: before the orientation, `sc-5` with the descent had five memory
kills where the plain run had none, the sub-goal e-graphs of one worker
accumulating address space; with the orientation the kills are gone, but
a descent over many heavy pairs still runs them in one process.
`cargo test --lib`: 292.

### 47.15 Runs `rw3` and `dsl1` (submitted 2026-09-25, read 2026-09-26)

Two submissions on rw2's sets (7,381 benchmarks): `rw3`, the pipeline
with the carcara of f0a15e53 (§47.13's merge, §47.14's tightening,
orientation and descent at 32 nodes, the residue classes named), the
91-rule `holes-rw3.rare`, the re-check at 1,200 s; and `dsl1`, the new
comparison arm: the same cvc5 at `--proof-granularity=dsl-rewrite` in
60 s, the proof checked by `carcara check` with the 171-rule file (900 s),
no egglog.  Runner `run-dsl.sh`, scripts `submit-egglog-rw3.sh`,
`submit-egglog-dsl1.sh`, readers in `~/exp/egglog-holes/analysis-rw3/`.
Results `exp/results/egglog-holes/{rw3,dsl1}` (local copies under
`~/exp/results/`).

**`rw3` against `rw2`** (holes of the proofs that ran the pass):

| | QF_UF | QF_LIA | QF_LRA |
|---|---|---|---|
| justified, rw3 / rw2 | 99.85% / 99.52% | 99.49% / 99.45% | 99.75% / 99.33% |
| kept, rw3 / rw2 | 1,728 / 5,648 | 2,963 / 3,457 | 1,074 / 2,869 |
| skipped at the budget | 0 / 33 | 643 / 481 | 0 / 29 |
| closed by the normalizer | 13.3% / 13.3% | 51.5% / 49.0% | 56.3% / 43.7% |
| proofs, every hole justified | 2,907 / 1,907 | 2,350 / 2,263 | 325 / 326 |
| of those without an untagged hole, re-check `holey` | 661 / 22 | 11 / 294 | 0 / 0 |
| re-check `valid` | 675 / 322 | 1,350 / 982 | 203 / 202 |
| elaboration pass, summed | 48.8 h / 80.0 h | 38.2 h / 37.8 h | 12.8 h / 21.2 h |
| descent: holes proved / failed | 7,606 / 44,924 | 20,208 / 4,276 | 33,856 / 1,599 |

Kept classes, rw3: QF_UF hole-time 1,110, checker-rejected 534,
no-certificate 47, memory 37; QF_LIA no-certificate 985 (852 Dartagnan),
hole-time 952 (790 Dartagnan), unproved 789 (rings 522, ezsmt 212),
memory 255, pass-budget 80; QF_LRA hole-time 580, no-certificate 484
(uart 339), memory 10.  Fully justified proofs: QF_UF both 1,904, rw3 only
1,003, rw2 only 3; QF_LIA 2,253 / 97 / 10; QF_LRA 311 / 14 / 15.

The orientation is what moved QF_LRA (the normalizer closes 56% of the
holes, `sc`'s kills are gone, 21 h to 13 h) and the search fixes what
moved QF_UF (kept 5,648 to 1,728, half the time).  QF_LIA's `valid` rose
from 982 to 1,350 because the routing's trust steps went from 294 proofs
to 11.  Two defects the run exposed, both in the elaborator, both fixed
after the read (6824bb8a):

- **534 QF_UF `checker-rejected`**, all a `cong` whose premises were out
  of argument order (a spine met from the far side, or a chain composed
  out of order; `cong` reads premises by position).  The premises are
  sorted by the argument they justify now.
- **661 QF_UF proofs fully justified and re-checked `holey`** on
  `TRUST_THEORY_REWRITE` steps the elaborator emitted for engine-internal
  `gen-N` rewrites (the set-form identity removal, `(and A true) = A`,
  and its kin) -- the old "justified with a `gen` hole" accounting gap,
  reopened by the search finding these edges where it found nothing
  before.  A `gen-N` step whose sides are equal modulo ACI is now the
  checker's `aci_simp`.  Twelve of the 661 replayed: nine re-check
  `valid`; the three Goel ones keep a `gen-44` that is a *conditional*
  rule's instance (`ite-true-cond` under a context equality), which has
  no name in the program and stays trusted -- the class left.  In QF_UF
  every `TRUST_THEORY_REWRITE` left is the elaborator's (cvc5 prints none
  there), so rw3's honest QF_UF count is 2,907 fully justified of which
  1,336 have no untagged hole and 675 re-check `valid`; the fixes lift
  most of the 661.

The descent's cost shows in QF_LRA's 15 proofs fully justified in rw2 and
not in rw3: LassoRanker proofs of 1--3k holes with 1--10 hole-time kills
each, after tens to hundreds of descents of which a few failed; a failed
descent spends the hole's budget before the whole goal is tried.  And
QF_LIA's skipped rose to 643 (Dartagnan's pass at the budget).  A
fallback with its own share of the budget, or a descent that gives up
after the first failed pair, is the next tuning.

**`dsl1`, cvc5's own expansion at `dsl-rewrite`**, checked by Carcara:

| | QF_UF (4,316) | QF_LIA (2,541) | QF_LRA (524) |
|---|---|---|---|
| proofs complete in 60 s | 4,316 | 2,531 | 510 |
| re-check `valid` / `holey` / error / time-out | 2,230 / 1,789 / 297 / 0 | 2,510 / 0 / 17 / 4 | 505 / 0 / 5 / 0 |
| holes left (all `THEORY_LEMMA`) | 4,149 in 1,789 proofs | 0 | 0 |
| rules cited outside the file | `bool-implies-or-distrib`, 99 proofs | 15 proofs | 0 |
| cvc5 time, median / p90 | 0.98 / 6.9 s | 0.09 / 6.7 s | 0.40 / 29.6 s |
| check time, median / p90 / sum | 0.17 / 1.0 s / 0.64 h | 0.02 / 0.7 s / 2.4 h | 0.08 / 2.5 s / 0.11 h |
| proof text | 20.8 GiB | 3.9 GiB | 1.9 GiB |
| `rare_rewrite` steps | 1.67 M | 1.66 M | 0.94 M |

The errors are the 205 resolution-pivot proofs (198 / 2 / 5, the same
cvc5 defect at every granularity) and the 114 proofs citing
`bool-implies-or-distrib`, which neither rule file has; the four QF_LIA
check time-outs are Dartagnan proofs of 5--12 MB at 900 s.  At this
granularity the arithmetic preprocessing holes (`THEORY_INFERENCE_ARITH`,
`MACRO_THEORY_REWRITE_RCONS_SIMPLE`) are gone from the proofs; only
QF_UF's `THEORY_LEMMA` remains, in 1,789 proofs.  cvc5 loses 24 proofs to
the 60 s limit that it had at rewrite granularity (10 QF_LIA, 14 QF_LRA;
Dartagnan, LassoRanker).

**Head to head**, the same benchmarks, a proof with no hole left at all:

| | QF_UF | QF_LIA | QF_LRA |
|---|---|---|---|
| `valid`, dsl1 / rw3 | 2,230 / 675 | 2,510 / 1,350 | 505 / 203 |
| dsl1 only / rw3 only | 1,555 / 0 | 1,160 / 0 | 302 / 0 |
| time to a checked proof, median, dsl1 / rw3 | 1.2 s / 29.8 s | 0.1 s / 2.3 s | 0.5 s / 31.2 s |
| summed | 4.0 h / 53.8 h | 4.1 h / 42.7 h | 1.1 h / 14.0 h |

Every proof the pipeline closes, cvc5's expansion closes too, and it
closes 3,017 more, in a tenth to a twentieth of the time: the ceiling on
`valid` in `rw3` is the untagged holes cvc5 prints at rewrite granularity
and does not print at `dsl-rewrite`, not the engine (rw3 justifies 99.5--
99.85% of the holes it is given).  Against the pipeline's own numbers the
comparison at the hole level stands: where cvc5 leaves a `THEORY_LEMMA`
(QF_UF, 1,789 proofs) the pipeline does not attempt it either.
