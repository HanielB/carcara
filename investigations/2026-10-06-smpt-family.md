# QF_LIA/20220307-SMPT across the evaluations: no let/parsing problem

**Date:** 2026-10-06.
**Question:** did the parsing problem that the let and substitution changes fixed
(quadratic `--expand-let-bindings`, see
[2026-08-31-carcara-bv-perf.md](2026-08-31-carcara-bv-perf.md)) show up on the SMPT
family (5,852 QF_LIA benchmarks, 1,573 of them unsat)?

**Answer: no.** The let problem showed up in QF_BV `sage` and `Sage2`. Across the runs
on this family, carcara never had trouble parsing an SMPT proof. The SMPT failures
that did occur have other causes.

## cvc5 proofs: parsing is never an issue

Every run that checked cvc5 proofs of SMPT with carcara, from alethe-lag (2026-08-30,
before the let fix) to alethe-eval, parses them in a median of 2–8ms. The slowest
SMPT parse in any of these runs is 4.7s.

| run | carcara | SMPT checked | parse median / max |
|---|---|---|---|
| alethe-lag `all-lag` | pre-fix | 1,526 valid, 1 error | 2ms / 3.9s |
| alethe-lag `all-fix` | `parsing-subst-fixes` | 1,527 valid | 2ms / 3.9s |
| alethe-core `cvc5-smtlib2` | `coreAlethe-upstream` | 1,526 valid | 4ms / 4.7s |
| pfcmp `all-alethe-union` | `bv-fixes` | 1,527 valid | 7ms / 4.1s |
| cpcCarcaraEval `all2` | `cpcCheck-bv` | 1,527 valid | 8ms / 4.3s |

The one error is `Referendum-PT-0200/RF-00`, "pivot was not eliminated", in a
resolution step. It shows up in `all-lag`, pfcmp `all-alethe` and cpcCarcaraEval
`all`, and is valid from pfcmp `all-alethe2` (2026-09-02) on. It has nothing to do
with parsing.

None of the 5,852 SMPT problems contains a `let`, so the let expansion has nothing to
expand on the problem side.

## veriT proofs: 15 `ac_simp` rejections, fixed by 13e721d7

The alethe-core veriT runs (`verit-smtlib`, `verit-smtlib2`, carcara
`coreAlethe-upstream` 23cac212) reject 15 SMPT proofs. All 15 fail on an `ac_simp`
step that has `:premises`, for example `HypertorusGrid-PT-d2k1p8b00/RF-11`, step `t4`
(premise `t3`):

    expected terms to be equal: '(and (>= pbl_1_1 1) (>= pi_d2_n1_1_1 1)
    (and (>= pbl_1_1 1) (>= pi_d2_n1_1_1 1)))' and '(and (>= pbl_1_1 1) (>= pi_d2_n1_1_1 1))'

This is veriT's premise-carrying `ac_simp`. Carcara's checker ignored the premises, so
it rejected the step. It is the case fixed by `13e721d7` "checker: read ac_simp's
premises" (2026-09-11; `cac6af13` is the follow-up for premise-free under-flattened
steps). Families: Referendum 6, SmallOperatingSystem 3, HypertorusGrid 2, Sudoku 2,
RobotManipulation 1, SharedMemory 1. alethe-eval `verit-1`, with a carcara that has
both commits, checks all 1,556 veriT SMPT proofs valid.

Reproduced locally on all 15, using veriT 2026.05 static (`--proof-with-sharing
--proof-prune --proof-merge`). The `coreAlethe-upstream` binary (8ee73710, which
differs from 23cac212 only in a note) rejects all 15 at the premise-carrying step,
with or without `--expand-let-bindings`. `isa-noop-contraction` bd445c6d and
`bv-fixes` 85e1c2d4 accept all 15.

## egglog-holes `full`: slow, but not the let problem

In egglog-holes `full` (2026-09-16), the SMPT RwMutex and SharedMemory proofs report
29–51s of parsing, and 4 RwMutex proofs time out. None of the egglog branches
contains the let fix (`2587d5d4`). Even so, the let fix is not the cause: carcaras
with the same let code parse the same benchmarks' cvc5 proofs, which are the same
size, in under a second.

| benchmark | `all-lag` (pre-fix) | egglog `rw5` | egglog `full` |
|---|---|---|---|
| RwMutex-PT-r0010w1000/RF-12 | 8.2MB, 0.65s | 7.0MB, 0.72s | 7.8MB, 50.9s (10,186 holes) |
| RwMutex-PT-r0010w1000/RF-08 | 7.9MB, 0.64s | 6.5MB, 0.71s | 7.2MB, 34.1s (10,297 holes) |
| SharedMemory-PT-000020/RF-12 | 6.9MB, 0.39s | 4.5MB, 0.57s | 6.5MB, 29.9s (13,372 holes) |

In `full`, the parse time grows with the number of holes, not with proof size:
SharedMemory-PT-000200/RF-00 has a 14.6MB proof with 1 hole and parses in 5.8s. The
`full` run's proofs are cvc5 default-granularity proofs with thousands of holes. I
have not established where that per-hole cost comes from.

## Reproduce

Outcomes and parse times come from the `results.json.gz` of each run under
`~/exp/results/` (the SMPT tasks are the ones whose `job_args` contain `SMPT`). For
the 15 veriT proofs:

    veriT-2026.05-static --disable-banner --disable-print-success --proof=p.alethe \
        --proof-with-sharing --proof-prune --proof-merge <bench>.smt2
    carcara check --allow-int-real-subtyping p.alethe <bench>.smt2
