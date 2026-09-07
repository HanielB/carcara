# cpcCarcaraEval: CPC + carcara against CPC + ethos and Alethe + carcara

Experiment `cpcCarcaraEval` (2026-09-07), files in `~/exp/cpcCarcaraEval/`, results in
`~/exp/results/cpcCarcaraEval/{test,test2,all}`, report `~/exp/cpcCarcaraEval/report/report.pdf`
(separate from the pfcmp report, as asked). The CPC + carcara pipeline: cvc5 alethebv
`1eb17718e1` (static, the pfcmp bin12 binary; its CPC printer is untouched by every alethebv
commit) with `--dump-proofs --proof-print-conclusion --no-symmetry-breaker`, then carcara
`cpcCheck-bv` `e8081f25` (static-pie) with `check --stats --proof-format cpc
--allow-int-real-subtyping --rare-file rewrites.eo`; the pfcmp GNU-time runner contract
(`run-cpcc.sh`), 600 s / 1200 s / 10 GB, octa `-j 12`, warm-up by reading the binaries in
full. `proof_bytes` is cvc5's printed body without the outer parentheses, as in the CPC +
ethos runner (Haniel: keep it this way; the translated Alethe proof is never written). The
reference pipelines are the canonical `all-cpc-union` and `all-alethe-union` of [[pfcmp-eval]],
restricted to the same benchmarks. Tables: `cpcc-tables.py <dir> [cpc-union alethe-union]
[--tex]` (reuses `~/exp/pfcmp/logic-tables.py`); the report's table bodies are inlined
(`\input` inside a `tabular` broke `\bottomrule`).

## Test runs (510-benchmark sample, 20 per set, `make-sample-set.py`)

Run 1 (carcara `449b7e07`, batch 24276942): 446 valid, 3 errors. The errors were translation
gaps, all fixed: `arith_trichotomy` with a negated strict premise (the old three-case scheme;
cvc5's single-resolution scheme ported, `8b480d2a`), and two QF_UFBV hardware benchmarks
mixing curried `(_ (f a) b)` and flat `(f a b)` applications of one function in a `refl`
(curried applications of first-order functions flattened, `62e5ee71`). `--stats` was added to
the CPC path (`8b480d2a`), since the runner's stats came out empty. Run 2 (`62e5ee71`, batch
24277452): 449 valid, 1 holey, 0 errors; carcara's time split parsing 35% / translation 41% /
checking 24%. The proof-node round trip used for dead-step pruning was 20-45% of the
translation time on the largest regressions and was replaced by a direct reachability pass
over the command vectors (`e8081f25`; translation of the largest regressions -35%, verdicts
unchanged on 120 regressions and the test suite).

## Full run (batch 24278223, 26 sets, 74,601 benchmarks, ~2.5 h wall)

| | CPC + carcara |
|---|---|
| valid / holey / rejected | 72,613 / 32 / 3 |
| checking timeouts | 0 |
| cvc5 side | 1,788 unproved, 94 no proof, 71 memouts |

- **vs CPC + ethos** (71,973 common valid): checking 53,165 s vs 550,672 s, **10.4x
  faster** (median 4.5x, faster on 96.3%); bytes 1.12x (median 1.23; the printed
  conclusions), commands 1.48x, steps identical, solve+print 1.00; pipeline 0.62x. Unique:
  640 only CPC+carcara (452 cvc5 memouts of the older binary of that run, 180 ethos checking
  timeouts, 8 printing timeouts), 24 only CPC+ethos (17 congruence holes, 3 rejections, 4
  conclusion-printing timeouts).
- **vs Alethe + carcara** (72,576 common valid): checking 79,466 s vs 37,815 s, **2.10x
  slower** in total but median 1.17x (the gap is in the largest proofs); bytes 1.81x (median
  1.08), commands 1.64x, **steps 0.92x** (fewer on 72%); solve+print 0.91x; pipeline 0.96x
  (cheaper on 75%). Unique: 37 vs 33 (printing timeouts on either side, plus the 29
  congruence holes and the rejection on the CPC side).
- **Time split** (72,613 valid, 77,338 s): parsing 41%, translation 31%, checking 29%. The
  checking proper (22,158 s) is below the Alethe pipeline's checking of the same benchmarks
  (37,815 s); the translation (23,630 s) is below the extra cost of cvc5's Alethe printer
  over its CPC printer (86,137 s on the common benchmarks), which bounds cvc5's own
  translation + printing. Worst single check: QF_BV/bmc-bv/ex49, 486 s of checking after 4 s
  of parsing + translation (checker-bound, not translation-bound).
- **Failures**: the 3 rejections are 2 `choice` binders in QF_UFBV Goel-hwbench *problems*
  (carcara's SMT-LIB parser; same in the Alethe pipeline) and 1 "pivot was not eliminated"
  on QF_LIA/20220307-SMPT/Referendum-PT-0200/RF-00 (a resolution over a large disjunction;
  not yet reproduced, needs the benchmark downloaded). The 32 holey: 3 trust-only (the shared
  `macro-quant-var-elim-eq`), 29 `cong`/`ho_cong` over applications of `define-fun`s whose
  structure the beta-reduction destroys (mostly QF_LIA/2019-ezsmt/incrementalScheduling);
  these are valid for ethos and Alethe, so they are the one translation gap left in the
  corpus (also the biggest hole class of the cvc5 regressions).

## Follow-up (same day): the congruence holes and the RF-00 rejection

Both fixed on `cpcCheck-bv` (`7053cdcf`). cvc5 treats a `define-fun` as a symbol equal to its
definition (a lambda for functions): CPC proofs apply the symbol, justify `(= f (lambda ...))`
by `refl`, and rewrite with `ho_cong` + `beta-reduce`; cvc5's Alethe printer emits that
equation as an assumption. The CPC parser now leaves definitions unexpanded on both sides
(`apply_function_defs = false`, as the Alethe pipeline's carcara run), keeps the proof's
nullary `define` of a declared symbol as the symbol, keeps lambda applications as
applications, and the translator turns such `refl` steps into references to an `assume` of the
definition (top level, once per definition, `symm` when flipped). `contra` now rebuilds a
premise `F` concluded as a clause into `(cl (or ...))` like `resolution` does; RF-00 checks
valid in 4 s. Regression sweep with this binary: regress0 442/27/6, regress1 104/14/1 (from
439/29/7 and 98/20/1); no `cong`/`ho_cong` holes remain (38 of 41 holey files are trust-only,
3 are rewrites without RARE definitions); `proofs/issue11750` (higher-order partial
application) is valid too. Run 2 of the full evaluation with this binary (job `cpccall2`,
results `cpcCarcaraEval/all2`, the `all2` submission script in `~/exp/cpcCarcaraEval`) is
pending.

## Open items

1. Parsing is the largest share of the CPC + carcara time; the CPC file carries the
   conclusions and `define` sharing that carcara resolves at parse time.
