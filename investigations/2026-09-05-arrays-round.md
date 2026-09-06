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

## Follow-ups landed the same day

- **INST_CONSTANT (class 3) fixed** in cvc5 `1acbc03224`: an instantiation
  constant of `(forall x1..xn. F)` for variable i is converted as the
  `QUANTIFIERS_SKOLEMIZE` witness for x_i (the choice term the converter
  already builds), so `--proof-alethe-define-skolems` defines it by name —
  no new symbol is declared. 018_bzip2 now checks valid (14 skolem
  definitions, 0 holes).
- **AUFBV fatness explained** (018_bzip2: 546 MB / 85,708 steps): `bind`
  182 MB (19 KB/step), `trans` 163 MB, `qnt_rm_unused`, `miniscope_*` (up
  to 422 KB/step) — quantifier-rewriting steps whose conclusions carry two
  copies of huge quantified formulas. `:named` cannot share terms under
  binders (named terms must be closed), while CPC's `define` sharing can;
  a format-level constraint.
- **SCOPE short-circuit** in `reorganize` (cvc5, next commit after
  `1acbc03224`): the consumer of the SCOPE implication is an `implies`
  step re-deriving VP3 `(cl (not (and F1..Fn)) F)`; it is replaced by the
  VP3 step already in its premise's derivation, so VP4–VP8 and the
  `implies` step become unreachable. storecomm (QF_AUFLIA) 7,231 → 6,193
  steps (−14%), QF_AX storecomm 21,401 → 18,239, swap −14%; probe sweep
  equal or smaller everywhere, all valid; regressions pass. The remaining
  per-scope cost (subproof + n and_pos + resolution + reordering +
  contraction) is inherent to reaching VP3 from the subproof clause; the
  and_pos steps coincide with the SAT-level CNF_AND_POS clauses and are
  merged by content dedup.

## Second batch of follow-ups (cvc5 alethebv 41fead09af + let-binding commit)

- **`not_and` short-circuit** in `reorganize`: a `not_and` step unfolding
  `(cl (not (and F1..Fn)))` — obtained by resolving F away from VP3 — is
  replaced by the same resolution applied to the subproof clause (same
  premises and pivots, VP3 swapped for the subproof step). storecomm
  (QF_AUFLIA) 6,193 → 5,843 steps, `not_and` 50 → 0. The two
  short-circuits together: 7,231 → 5,843 (−19%). What remains per scope is
  the `(and A)`-atom detour used by the SAT-level resolutions (82 of 184
  VP3 consumers here), i.e. cvc5's proof shape; the cure is on the cvc5
  side (theory lemmas as clauses) or a resolution-rewriting pass.
- **AUFBV fatness: sharing under binders.** `:named` may name any *closed*
  term, even under a binder. The Alethe let binding now traverses binders
  and shares a term iff it has no free bound variable (the converter's
  `choice` = `APPLY_UF(choice, BVL, body)` counts as a binder). Two
  bookkeeping fixes were needed for correctness at scale: the first
  occurrence of a term is recorded when first *reached* in pre-order
  (recording at the parent's enumeration put a declaration after an
  occurrence in an earlier sibling → "identifier not defined"), and
  unshared terms whose conversion embeds a descendant's declaration are
  treated as declaration carriers (only their first occurrence embeds it;
  previously a term was declared 60x inside one assumption). Results:
  018_bzip2 546 MB → 169 MB (−69%), formula_216 671 → 561 KB, 433_oggenc
  969 → 604 KB; QF_BV proofs byte-identical; small (≤12%) growth on tiny
  proofs where naming overhead exceeds the saving. What is left in AUFBV
  is terms containing the bound variable repeated across `bind`/`trans`/
  `miniscope` steps — a genuine format constraint (CPC shares open terms).
- Probe sweep, arrays cases, alethe/arrays/quantifiers regressions
  (8/8, 455/455) all pass at each step.
