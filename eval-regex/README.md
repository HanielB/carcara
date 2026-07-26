# Regex-eval evaluation (IJCAR paper analog)

Evaluates this branch's regex-eval rules (`str_in_re_eval` etc., backed by the
automaton infrastructure) the way the IJCAR paper "Checking Regular Expressions
in cvc5 Proofs" evaluates Ethos side conditions — but on cvc5 **Alethe** proofs
checked by **Carcara**. The paper's artifact (`../artifact`) supplies the layout
conventions, the organic benchmark list, and the synthetic traces.

## Prerequisites

- `cargo build --release` (checking uses `target/release/carcara`)
- `runlim` in PATH (note: runlim 1.10 does not report the child's exit code;
  summarize.py therefore judges runs by Carcara's stdout verdict)
- SMT-LIB 2024 QF_S/QF_SLIA/QF_SNIA in `~/benchmarks/smtlib/non-incremental/`
  (Zenodo record 11061097, per-logic `*.tar.zst`; 103,405 files, ~2.4 GB)
- All generated data lives under `~/benchmarks/regex-eval/` (`DATA_ROOT` in
  `common.py`)

## Pipeline

1. **Benchmark list.** Either the paper's organic instances, mapped to local
   paths (shards `qf_slia_00/` → `QF_SLIA/` etc.):

   ```sh
   sed 's|evaluation/logs/cvc5/proofs/||; s|/proof.eo||; s|^qf_snia[^/]*/|QF_SNIA/|; s|^qf_slia[^/]*/|QF_SLIA/|; s|^qf_s[^/]*/|QF_S/|' \
     ../artifact/evaluation/benchmarks/benchmark_set_proofs \
     > ~/benchmarks/regex-eval/paper_organic_benchmarks
   ```

   or a full listing of all 103k benchmarks for the paper-scale sweep.

2. **Proof generation** (resumable; 60s/8GB per instance):
   `./generate-proofs.py <list> -j 7`
   runs `cvc5 --dump-proofs --proof-format-mode=alethe --proof-granularity=dsl-rewrite`.

3. **Organic set:** `./extract-organic.py` keeps unsat proofs applying at least
   one of the six regex-eval rewrites (as `:rule hole :args ("str-in-re-eval")`
   holes), then `./transform-holes.py` writes `proof-eval.alethe` with those
   holes turned into the checkable rules. The untransformed `proof.alethe` is
   the lower-bound (LB) configuration.

4. **Synthetic set:** extract the artifact's traces
   (`tar -xzf ../artifact/evaluation/logs/cvc5/traces.tar.gz -C <dir>`), then
   `./translate-traces.py <dir>` — each trace becomes an Alethe proof with one
   `str_in_re_eval` step per logged call (hole variant for LB), closed by a
   final `(cl) :rule hole` step since Carcara requires an empty-clause
   conclusion.

5. **Checking** (resumable): `./run-checking.py {organic,synthetic} --configs
   CarcaraEval CarcaraLB -j 7`. Both configs allow `rare_rewrite` and
   `evaluate` as holes (not implemented on this branch), so Eval vs LB differs
   exactly in the six regex-eval rules. Use `-j 1` for the cleanest timings.

6. **Summary:** `./summarize.py {organic,synthetic} [--common]` — a Table-3
   analog: #S, valid/holey split, total CPU time and memory (`--common`
   restricts totals to instances checked by every config).

## Caveats

- cvc5 main (1.3.4-dev) instead of the paper's 1.3.2, and Alethe instead of CPC
  proofs: the organic set will not be identical to the paper's 3,118 (Alethe
  proofs may time out or take different proof paths — both observed).
- Most organic proofs check as `holey` (they contain non-regex holes such as
  `rare_rewrite`); the comparison of interest is Eval vs LB timing, not
  valid/holey.
- The paper ran on a 23-machine cluster; local runs with `-j 7` add some
  contention noise to CPU times.
