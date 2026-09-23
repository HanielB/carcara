# veriT proofs through the hole checker: plan (2026-09-23)

What the two veriT cluster jobs (`vb50-2`, `vnob-2`; notes §41–§44) and
the local reproductions (§43) established, and what follows from it.  The
cvc5 side has its own list; the engine work that serves both is at the end
of the notes' §44 discussion and not repeated here.

## What is settled

- **The bound is a no-op on QF_UF and the whole experiment in arithmetic.**
  veriT's QF_UF preprocessing holes are already under 50 DAG nodes (305,215
  against 304,978 holes, 2,934 of 3,127 proofs with identical counts).  In
  QF_LIA the bound makes 4.4 times more holes, in QF_LRA 37.6 times.
- **The bound wins arithmetic at the proof level.**  Proofs with every hole
  closed, best of four configurations: QF_LIA 2,139 against 1,841 (329 won,
  31 lost), QF_LRA 213 against 168 (46 won, 1 lost).  A whole-assertion hole
  that fails costs the whole proof; a bounded hole that fails costs one
  rewrite.
- **The caps win QF_UF.**  Same holes, and 120M/20M in place of 3M/500k
  takes it from 2,106 to 3,542 fully justified proofs; the residue is 2,855
  growth-cap kills against 28.  Locally, changing only the cap on the five
  worst proofs recovers 44 of 82 kept holes, the 120 s clock another 16, at
  three times the time.
- **The larger caps hurt arithmetic.**  Arithmetic loses to the pass budget
  (30.6% and 54.3% of holes never attempted), not to the caps (133 and 24
  kills); raising the cap on a LassoRanker proof *loses* six holes, since a
  hopeless hole runs longer and starves the queue.
- **Set-form is the encoding.**  Chain costs 2.4 times (bounded) to 3.1
  times (no bound) the time on QF_UF and proves fewer holes on every arm.
- **The arithmetic residue was one shape.**  `la_rw_eq`, `(= a b)` to
  `(and (<= a b) (<= b a))`, is 100% of the QF_LIA residue (Dartagnan, 48% of
  the logic's holes) and all of the failing QF_LRA families (`tta_startup`,
  `uart`, `sal`, `sc`, `spider`, 32%).  The prenormalizer now closes it
  (commit `19b64f64`): 9,848 of 9,850, 1,181 of 1,183, 1,791 of 1,793 holes
  in a quarter of a second each, certificates accepted by the checker.  The
  old normalizer had made those goals 1.6–4.5 times dearer by flattening the
  two bounds into the surrounding conjunction.

## 1. The run neither arm was

Bounded holes with per-logic limits, on the current binary.

| | QF_UF | QF_LIA, QF_LRA |
|---|---|---|
| `--proof-hole-size` | 50 | 50 |
| caps arith / plain | 120M / 20M | 3M / 500k |
| per-hole clock | 120 s | 60 s |
| workers | 8 | 8 |
| encoding | set-form only | set-form only |
| passes | plain, normalizer | plain, normalizer |

Expected: about 3,542 + 2,139 + 213 ≈ 5,900 fully justified proofs before
the normalizer's new step, against 5,551 (`vnob-2`) and 4,458 (`vb50-2`),
and the arithmetic arms close to complete with it.  Keep the normalizer-off
pass so what the normalizer buys stays measured; drop chain.  Since QF_UF's
holes are the same at any bound, the QF_UF result also stands in for a
no-bound QF_UF run.

Runner: `run-holes-verit.tmpl` with the caps and clock chosen from the
benchmark path's logic (one template, one job, three arrays); the
`[class]` residue tag and the per-pass keys of `run-holes-enc.sh` are
already in it.  Static binary from the current head; `veriT` unchanged.

## 2. `eq_rewrite` as `la_rw_eq` steps, not holes

`--proof-coarse-preprocessing` replaces the `eq_rewrite` stage's derivation
by a hole, and the normalizer now reconstructs exactly what was thrown
away (`la_rw_eq`, `cong`, `trans`).  Keep that stage detailed, as
`let_elim` already is: one `PRE_STAGE` call in `src/pre/pre.c` back to
`pre_eq_rewrite_proof`.  The holes are then `simplify_formula` and
`lang_red` only, which is what the bound is for.

Measure before adopting: proof size (the Averest proof is 725 MB *with*
holes; the detailed `cong` chains may be larger or smaller), checking time
of the `la_rw_eq` steps (syntactic, should be negligible), and whether any
hole is lost that the normalizer would have closed.  Three local proofs
suffice (`count_up_down-1`, `blmc004`, `simple_startup_14nodes.synchro.base`).

## 3. Sweep the bound

50 was a guess.  Run 20, 50, 100, 200 on the arithmetic sets only, fully
justified proofs as the metric, holes per proof and pass time as the cost.
Cheap once the runner of item 1 exists: one more parameter.  Expect the
optimum to move once item 2 removes the `eq_rewrite` holes, so run it
after that decision.

## 4. The post-summary stall on large proofs

Every pass on the 725 MB Averest proof ends its holes at 297 s and is then
killed at the 700 s external limit (`rc=124`, locally as on the cluster):
something after the hole summary takes over 400 s.  Likely candidates: the
proof printed to `/dev/null` without sharing, or a re-check of the whole
proof.  Find it (`--log debug` timing lines, or `perf` on the local run),
and skip it in `--hole-check-only` mode.  Until then every `<p>_time` of a
large proof is inflated and five QF_LIA tasks per pass show as timeouts.
While there: the `--hole-total-budget` clock starts at the CLI's start, so
parsing a large proof is charged to the holes.

## 5. The report

`report/report.tex` has the cvc5 addendum only.  Add: the funnel table for
veriT (benchmarks, proved, holes, checked), the bound-versus-caps split of
§44, the encoding result, the `la_rw_eq` story of §43, and the CDF of the
four configurations on the bounded arm.  `report/make-enc4.py` is the
template; the veriT results are in `~/exp/results/egglog-verit/`.

## Not in this list

Engine work that serves both solvers (cheapest-first scheduling, keeping
the original goal when normalization does not close a hole, the set-form
flat-`and` anomaly, the `ite` shape) is tracked in the notes, §43–§44.
