# Stress testing the CPC checking pipeline

Looking for valid CPC proofs Carcara breaks on, and invalid ones it accepts, exercising the
parser, the translation and the checker. Three harnesses, two of them committed
(`scripts/stress-cpc.sh`, `scripts/fuzz-cpc.py`); branch `cpcCheck-bv`. Four Carcara defects were
found and fixed, all of them robustness rather than soundness: no mutant of a valid proof was
accepted, and no proof was accepted against a problem that does not entail it.

## The harnesses

**Differential against Ethos** (`scripts/stress-cpc.sh`). For each benchmark, cvc5 produces a
CPC proof with conclusions (for Carcara) and one without (for Ethos, which derives them), and
the verdicts are compared. Ethos is the reference CPC checker, so a proof it accepts and
Carcara rejects is a Carcara defect, and the converse is a candidate unsoundness. Run over
**all of regress0 regardless of logic** (2,264 benchmarks, 1,154 proved): 879 both accept, 275
only Ethos, 14 only Carcara, 0 crashes, 14 both reject.

- The 275 are outside the supported fragment: strings, datatypes, floating point, finite
  fields, separation logic, sets, sequences, higher order (logics `ALL`, `QF_SLIA`, `QF_S`,
  `QF_FP`, `QF_FF`, `QF_DT`, `UFC`, `HO_ALL`, ...). Ethos accepts them because it never reads
  the problem; Carcara parses the problem, so it also rejects benchmarks written in cvc5's
  extended input syntax (`mod_total`, `/_total`, `(_ divisible n)` in the *problem*). Inside
  the AUFBVNIRA fragment the only rejections are the ones the regression sweep already
  records.
- The 14 the other way are Ethos failing to parse cvc5's own output: without
  `--proof-print-conclusion` the CPC printer shares terms with `let`, which Ethos has no
  symbol for ("Could not find symbol let"). Carcara handles them.

Over regress1 (1,151 benchmarks, 411 proved): 183 both accept, 187 only Ethos (same
unsupported theories), 14 only Carcara (the same `let` parse failures), 27 both reject, and
**one Carcara crash**, on a valid proof, which is defect 4 below.

**Mutation fuzzing** (`scripts/fuzz-cpc.py`). Takes proofs Carcara accepts as valid, corrupts
one step at a time — dropping, reordering or restating premises, conclusions, rules and
arguments, and tampering with assumptions — and requires rejection. Mutations are applied only
to commands the final step depends on (the translation prunes the rest, so mutating them is a
no-op), and the problem itself is corrupted as well. Over the 589 regression proofs, 5 mutants
per proof: 1,322 rejected, 246 holey, 266 still valid (all benign, classified below), 2 crashes
(fixed), 0 accepted after the problem was corrupted.

**Text-level fuzzing** (scratch script). Truncation, paren deletion and insertion, token
garbling, byte flips and duplicated lines, to stress the lexer and parser: 304 mutants over 40
proofs, no crash and no hang; 50 still valid, all no-ops (see below).

**Cross-problem checks.** Each proof checked against the *next* benchmark's problem: 57 checks,
all rejected, no crash.

## Defects found and fixed

1. **The translation indexed premises and arguments without checking them** (fixed in
   `f50e3b28`). Dropping the premise of a `contra` step, or renaming a rule to
   `chain_resolution`, whose arguments are read positionally, aborted the checker with an
   index-out-of-bounds panic. The arity each rule's translation reads is now checked before
   dispatch, and a step without a conclusion is rejected instead of indexed.
2. **Error messages rendered whole terms** (fixed in `14cef787`). Rejecting a step over
   bit-blasted bit-vector terms made Carcara allocate gigabytes formatting them:
   `bv/holes/srem-eliminate` aborted with "memory allocation of 8589934592 bytes failed"
   instead of reporting the rejection, and once the allocation was avoided it spent minutes
   walking the term. Terms in error messages now go through a printer that stops after 4 KB;
   the writer *fails* at the limit so the traversal stops too. That benchmark now reports its
   rejection in 0.05 s and 15 MB. Term printing outside error messages is untouched, since it
   feeds the external solvers.
3. **`bitvector_size` panicked on a non-bit-vector term** (fixed here). A mutated proof that
   reaches a bit-vector rule with a term of another sort aborted the checker
   ("trying to get size of non-bitvector term"). The helper and the four bit-blasting helpers
   that use it are now fallible, and the step is rejected with a new `ExpectedBvTerm` error.
4. **The sort of a tuple selection was computed from the wrong list** (fixed in `c659da7c`).
   `((_ tuple.select i) t)` indexed the application's arguments with `i`, the *operator's*
   argument, so any index past the single argument aborted the checker while parsing — the
   crash the regress1 differential found, on an unmutated proof
   (`regress1/rels/bv1p.cvc.smt2`). The sort is now the `i`-th component of the argument's
   tuple sort, and a non-tuple argument or an index out of range leaves the sort undefined.
   The proof is still rejected, since relations are outside the supported fragment, but with
   an error rather than a panic.
5. Two harness defects worth recording, since they produced false positives: a premise-drop
   mutation that re-evaluated its random choice per element (so it often dropped nothing), and
   a problem corruption that dropped or negated a *single* assertion — a proof that uses a
   subset of the assertions legitimately survives that, so the check now corrupts every
   assertion. Reachability also over-approximated scopes, marking unused assumptions as
   mutable; it now follows the `step-pop` that discharges an assumption.

## Mutants that survive, and why

Every surviving mutant falls into one of four classes, each of which leaves a *correct* proof:

- **Premise order that the checkers do not fix** (191 of 266): `trans` searches for a chain
  among its premises, resolution is checked as a set with a RUP fallback, and a `cong` premise
  that is a reflexivity is dropped by the translation, so swapping it with another is a no-op.
- **Steps whose conclusion the translation reconstructs** (24 conclusion, 28 rule mutations):
  `process_scope` builds its implication from the scope's assumptions and body, `implies_elim`
  reuses the scope's folded clause through the short-circuit, and a congruence whose conclusion
  is reflexive after conversion becomes `refl` whatever the stated rule. The stated conclusion
  is then not load-bearing — which is safe, since the reconstruction is derived from the
  premises and checked by the Alethe checker.
- **Arguments and attributes that are not read**: cvc5 prints `:args` on `refl` and `cong`
  steps as hints the translation does not need, and unknown step attributes are ignored, so
  corrupting them changes nothing.
- **Duplicated commands**: a repeated `define` or `step` line redefines the same thing.

No mutation produced a proof of `false` that Carcara accepted against a problem not entailing
it, and corrupting every assertion of the problem was rejected in all 677 attempts.

## Reproducing

```
scripts/stress-cpc.sh ~/cvc5/test/regress/cli/regress0      # differential against ethos
scripts/fuzz-cpc.py --carcara target/release/carcara --per-proof 5 <proofs>.cpc
```
Both take the binaries and the RARE file through environment variables or flags; the fuzzer
needs each proof's problem next to it, which is how `scripts/validate-cpc.sh` and
`scripts/stress-cpc.sh` leave their output directories.
