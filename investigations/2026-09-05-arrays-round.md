# Arrays round: Alethe+carcara vs CPC+ethos on the SMT-LIB array logics

**Data:** `~/exp/results/pfcmp/all-arr-alethe`, `all-arr-cpc` (pfchk caches
built). **Sets:** all unsat / inferred-unsat non-incremental benchmarks of 12
array logics per the SMT-LIB 2025 catalog, 30,525 in total (AUFLIRA 19,781,
QF_ABV 4,697, AUFLIA 2,554, AUFNIRA 1,083, QF_AUFLIA 760, ALIA 491, ABV 395,
AUFBV 355, QF_AX 279, QF_ALIA 72, QF_AUFBV 46, QF_AUFNIA 12).
**Toolchain (bin8):** cvc5 alethebv @ `4be2f20f1e`, carcara bv-fixes @
`4350bb39`, ethos 0b1a6dd9; octa, 12/node, 600 s solve+print, 1200 s check,
10 GB, warmed binaries.

## Headline

- **Alethe+carcara: 28,446 valid**, 2 holey (6 hole steps), 61 checker
  errors, ~150 print memouts/no-proofs; ~2,000 unproved within 600 s
  (ABV 350, ALIA 433, AUFLIA 524, AUFBV 214 — solver-limited).
  Solve/check ratio 18.65. Array rules: `arrays_row` 604,954, `arrays_idx`
  21,654, `arrays_ext` 695, `arrays_row_contra` 35. No array RARE rewrites
  at corpus scale.
- **CPC+ethos: 28,566 correct**, 3 holey, 0 errors, ratio 2.58.
- **Common 28,431:** carcara **6.65x faster** checking (median 5.0x,
  faster on 98.6%); commands 0.97; solve+print CPC 0.86x; pipeline CPC
  1.13x. **But Alethe proofs are 2x larger in total bytes** (38.8 vs
  19.0 GB; CPC smaller on 87.6%, median 0.69) — the reverse of the
  UFLIRA/BV corpus. Unique: 15 only-Alethe (CPC memouts/timeout), 135
  only-CPC (Alethe errors 61, no-proof 9, memouts).

## The size gap: the SCOPE translation

Local decomposition (QF_AUFLIA storecomm: 640 KB / 7,231 steps vs CPC
295 KB / 2,392 steps + 506 defines; QF_AX storecomm: 2.08 MB / 21,401 vs
0.94 MB / 8,984): the family of steps the Alethe translation of cvc5's
`SCOPE` produces — `subproof` + per-assumption `and_pos`/`or_neg` +
`resolution` + `reordering` + `contraction` + `implies_neg1/2` — is
**40–50% of the steps and 37–46% of the bytes**. CPC spends one `scope`
step per assumption (47 B) plus one `process_scope`. Array theory lemmas
are scoped implications, so this dominates array proofs. Since Alethe's
`subproof` already concludes the clause `(cl (not F1) ... (not Fn) G)`
and the consumer of the implication turns it back into exactly that
clause, the pattern can be short-circuited by a DAG analysis (see the
conversation log for the design discussion).

AUFBV is worse still: median 3,964 B/step vs CPC 124 (11.7 GB for 42
valid proofs) — not yet decomposed (needs a fat AUFBV sample).

## Failure classes and fixes

1. **AUFBV 29: `bv_bitwise_slicing` rejected** — cvc5 slices an n-ary
   `(bvor x y #b0001 z)` as constant vs remaining operands regrouped; carcara
   only accepted a binary sliced term. **Fixed** (carcara `580a36b7`):
   n-ary with a single constant operand accepted; 433_oggenc now valid.
2. **QF_AX 2 (swap): `step id 't3661.t0' is not defined`** — printer
   ordering hole: an anchor's re-printed concluding step was pushed into the
   anchor item before the frame's items (premises re-printed by
   `premiseLevel`) were moved behind it. **Fixed** (cvc5 `b73301b3cf`):
   emitted into the frame like every step; swap proof valid, probes
   unchanged.
3. **AUFBV 19 + AUFNIRA 11: cvc5 printed `(error "Proof unsupported by
   Alethe: contains operator INST_CONSTANT")`** — an instantiation constant
   leaks into a proof-node conclusion (an `and` of equalities inside a
   theory-lemma chain). cvc5-side issue in proof production for these
   quantified Alive2/FFT benchmarks; not yet fixed.
4. **Holes (2 proofs, 6 steps): all `macro-quant-var-elim-eq`** — an
   untranslated RARE macro (quantifier variable elimination); expected gap.

Round-4-style artifacts: none (warmed runners; wall vs CPU consistent).
