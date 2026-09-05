# Alethe arrays: cvc5 `alethebv` already carries the arrays translation; SMT-LIB probe checks clean

**Ask:** bring the arrays support of cvc5 branch `aletheArrays` into `alethebv`,
in line with carcara's array support on `alethe-toolkit`, excluding constant
arrays (irrelevant for SMT-LIB benchmarks).

## Finding: nothing to port

- cvc5 `aletheArrays` is two commits on top of 1bc974311a (`85f3ebfcba`
  "transient", `e86939b067` "doc"): the four Alethe rules `arrays_idx`,
  `arrays_row`, `arrays_row_contra`, `arrays_ext` (enum + strings + the
  translation of `ARRAYS_READ_OVER_WRITE{,_1,_CONTRA}` and `ARRAYS_EXT`),
  the `ARRAY_DEQ_DIFF` skolem converted to a `witness`
  `(witness ((x I)) (or (= a b) (not (= (select a x) (select b x)))))`, and
  the DISABLE-TESTER marker on `parse-skolem-test-array-deq.smt2`.
- **All of it is already on `alethebv`** (it came in with the
  aletheLagFixes/aletheSubs merge), including the doc comments and an
  *improved* `ARRAY_DEQ_DIFF` conversion (skolem caching). A cherry-pick
  conflicts only against identical content; `git diff aletheArrays alethebv`
  shows no ARRAYS delta in the translation.
- No constant-array code exists in either cvc5 branch, nor in carcara's
  `alethe-toolkit`, `carcaram/arrays` or `bv-fixes` — nothing to exclude.
- carcara: `bv-fixes` has `src/checker/rules/arrays.rs` with the four rules
  wired in `shared.rs`; it is a superset of `alethe-toolkit`'s array support
  (which lacks the `arrays_row_contra` fix 7458c816 and the tests d62d45cf).
  `~/carcara/rewrites.eo` already carries all 6 of cvc5's array RARE rules.

## Validation (local, cvc5 alethebv @ 4be2f20f1e, carcara bv-fixes @ 5620a82d)

Pipeline as in pfcmp (`--proof-format=alethe --proof-granularity=dsl-rewrite
--proof-alethe-define-skolems`; carcara `--expand-let-bindings
--allow-int-real-subtyping --allow-higher-order-indexed-ops --rare-file
rewrites.eo`), cvc5 60 s local budget.

- QF_AUFLIA (storecomm, Rodin, swap, storeinv, cvc, check) + QF_ABV
  (13 families): 186 benchmarks with status unsat.
- **164 proofs produced, 164 valid — 0 holey, 0 invalid, 0 errors**; the
  other 22 are cvc5 timeouts at 60 s (19 QF_ABV, 3 swap). One QF_ABV case
  (bf18) solves in 1 s but does not finish printing its bitblast+array
  proof within 60 s: proof production cost, not a checking gap.
- Rules exercised across the 186 proofs (343 MB): `arrays_row` 8,763,
  `arrays_idx` 2,087, `arrays_ext` 27, `arrays_row_contra` 11;
  `rare_rewrite` with `array-read-over-write` 183, `array-store-self` 79,
  `array-store-overwrite` 75. Zero `hole` steps.
- cvc5 arrays regressions (`ctest -R 'regress[01].*arrays'`, alethe tester
  on): 86/86.

## Follow-ups if arrays get a cluster round

- The natural sets are QF_AX, QF_AUFLIA, QF_ABV (+ AUFLIA-family with
  quantifiers); the pfcmp runners apply unchanged.
- QF_ABV proofs combine bitblasting and array steps; production time, not
  checking, is the limiting factor at the local budget.
