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

## Arrays round 2 (2026-09-06): the fixes at scale, and a regression

**Run:** `all-arr2-alethe` (bin9: cvc5 alethebv @ `bce1d54bef`, carcara
bv-fixes @ `d3e6a138`, same limits/octa/warmup; 47 min wall). The CPC
side was not re-run: no cvc5 change since round 1 touches anything but
`src/proof/alethe/`, so `all-arr-cpc` is the comparison partner (Haniel
cancelled the submitted CPC job). Scripts: `submit-pfcmp-arr2.sh`,
`run-arr2-alethe.sh`; tables from the new `logic-tables.py`.

**Outcome:** 28,566 valid (= CPC's 28,566), 3 holey, 11 errors, 59
memouts (from 128), 58 print timeouts; common valid 28,547. Unique: 19
each way (Alethe misses: 11 errors, 6 print timeouts, 2 memouts; CPC
misses: 16 print memouts, 3 ethos timeouts). carcara 8.90x faster in
total (median 4.95x); Alethe corpus 30 GB vs CPC 21 GB (from 39 vs 19;
CPC/Alethe 0.69 total, 0.68 median); commands 203 vs 129 M; pipeline
CPC 1.16x. AUFBV: 42 -> 126 valid, 11.7 GB -> 4.05 GB, median 182 B/step
(from 3,964; CPC 127). Round 1 -> round 2 on the 28,445 commonly valid:
bytes 42.8 -> 29.8 GB, steps 167.7 -> 148.2 M (short-circuits: QF_AX
-12%, QF_AUFLIA -12%, AUFLIRA -11%), check 4,300 -> 3,407 s.

**Regression found: sharing lost in `bind` subproofs.** 12,167 proofs
grew >5% (AUFLIRA median x1.06, AUFNIRA median x2.9; worst
`AUFLIRA/nasa/fol_simplify_array_only/quaternion_ds1_symm_1367`: 156 KB
-> 1.96 MB, 962 steps both). Cause: the closed-term rule of `bce1d54bef`
(`isOpen`) refused to name any term with a free bound variable — but
inside a `bind`/`sko` subproof the anchor's variables occur free in every
conclusion, and the old printer named those terms (which is what carcara
accepts and what round 1 measured). The quantifier-rewriting steps in
the subproof (cong/trans/rare_rewrite over 70-deep implication chains)
were printed in full. **Fix:** conversion keyed per occurrence: a term is
nameable at an occurrence iff none of its free variables is bound by a
binder enclosing that occurrence in the converted term (its variables
are then in scope, e.g. anchor-bound); under a capturing binder it is
printed in full (its closed subterms still by name). Keys pair the term
with its captured variables; the conversion of a key is context-free
since children's keys are determined by the parent's. Declarations and
carriers are keyed the same way. quaternion_1367: 1.96 MB -> 125 KB
(round 1: 156 KB), valid, no duplicate names; storecomm byte-identical.

**Errors (11, all AUFNIRA/FFT):** cvc5 prints `(error "Proof unsupported
by Alethe: contains Skolem (kind div_by_zero ...")` — the total-division
skolem `@div_by_zero` (Real -> Real) has no witness form for
`--proof-alethe-define-skolems` and no Alethe counterpart. Open: a
representation decision (it denotes the unspecified value of `(/ x 0)`).

**Holey (3):** ABV cs_szymanski_5, AUFBV 320_oggenc and 064_gcc, one
`hole` step each (proofs not retrieved; to be looked at in round 3).

## Arrays round 3 (2026-09-06): the canonical arrays dataset

**Run:** `all-arr3-alethe` (bin10: cvc5 alethebv `8975c05822` with the
anchor-bound sharing fix, carcara bv-fixes `e8b779b2`; octa, 12/node,
warmed; 47 min). CPC partner: `all-arr-cpc` (round 1). Plots in
`~/exp/pfcmp/plots-arr3`, tables from `logic-tables.py`; report Section 5
rewritten on these numbers.

**Outcome (with the fix run merged, `all-arr3-alethe-merged` =
round 3 + `all-arr3-alethe-fix`, bin11, on the 11 FFT benchmarks, all
valid; merged by `merge-results.py`):** 28,578 valid (CPC 28,566), 3
holey, 0 errors, 59 memouts, 59 print timeouts (52 QF_ABV), 1,826
unproved. Common 28,560: carcara 10.75x faster in total (median 5.48x,
faster on 99.6%); bytes 24 vs 21 GB (CPC/Alethe 0.87 total, 0.85 median;
CPC smaller on 84.6%); commands 201 vs 130 M; solve+print CPC 0.87x;
pipeline CPC 1.17x. Unique 18 vs 6 (Alethe misses: 5 print timeouts, 1
memout). Per logic: AUFLIRA at parity
(1.01), QF_AX/QF_AUFLIA/ALIA CPC 25-40% leaner, QF_ABV 1.26 and QF_AUFBV
1.68 in Alethe's favour, AUFBV 0.24 (3.9 GB vs 0.9 GB). Array rules:
arrays_row 650,130, idx 22,639, ext 692, row_contra 35.

**Round 1 -> 3** (28,443 common valid): bytes 41.8 -> 22.5 GB, steps
166.1 -> 146.7 M, check 4,199 -> 2,758 s, solve unchanged; NO proof grew,
21,529 shrank >5%. AUFBV 42 common: 11.7 GB -> 179 MB; AUFLIRA 14.6 ->
8.0 GB; AUFNIRA 127 -> 69 MB; QF_AX -9%, QF_AUFLIA -9%. **Round 2 -> 3**
(28,563): 33.6 -> 25.9 GB, no growth, 19,426 shrank >5% (the regression
undone: AUFNIRA 390 -> 71 MB, AUFLIRA 14.2 -> 8.8 GB).

### Why CPC is leaner on QF_AX / QF_AUFLIA after round 3 (Haniel's question)

Two components, measured on local QF_AUFLIA benchmarks with the round-3
toolchain (`~/exp/pfcmp` scratch `lean/`):

1. **Encoding, on identical proof DAGs.** storecomm_t1_np_nf_ni_00030_002
   is pure rewriting: Alethe 959 steps / CPC 956 steps + 218 defines, same
   rules (rare_rewrite=array-store-swap 212, cong 215, trans 212, evaluate
   212, refl 104); 92 KB vs 69 KB (0.75, the QF_AUFLIA median). Alethe
   states every step's conclusion `(cl (= lhs rhs))` (48.5 B/step avg,
   46.5 KB total) although the rule + args + premises determine it; CPC
   is conclusion-free and carries only the rule's arguments (:args 18.8
   KB) plus its defines (8.6 KB), i.e. 27 KB vs 46.5 KB — 19 of the 22.5
   KB gap. The rest: the RARE rule name as a string argument
   (`"array-store-swap"`, 3.6 KB here) where CPC uses it as the :rule,
   and `(! t :named @p_N)` vs `(define @tN () t)` being a wash.
2. **Structure, on lemma-heavy proofs.** swap_t1_pp_nf_ai_00004_002:
   Alethe 1,334 steps + 74 anchors vs CPC 1,002 steps + 151 defines; 110
   KB vs 70 KB (0.64, the QF_AX median). Per SCOPE the Alethe translation
   still spends `subproof` (97 B) + one `and_pos` per assumption (202 x
   65 B) + `resolution` (243 x 83 B, mostly these) + `reordering` (71) +
   `contraction` (89) + `or_neg` (98) + the assumptions inside the
   subproof (232 x 27 B) = ~64 KB of the 110 KB, against CPC's `scope`
   (242 x 49 B) + `process_scope` (80 x 65 B) = 17 KB: Alethe has no rule
   that discharges a subproof into the clause the SAT level uses, so the
   clause is assembled by resolution against the `and_pos` instances of
   the conjunction atom; that is the "(and A)-atom detour" left after the
   short-circuits. CPC also folds each resolution chain into one
   `chain_m_resolution` (25 steps, 3.8 KB).

### Why the subproof clause is not used directly (Haniel's follow-up)

Traced on swap_t1_pp_nf_ai_00004_002 (74 subproofs, 53 top-level
implication clauses VP3 = `(cl (not (and F1..Fn)) G)`):

- cvc5's proof of a theory propagation/conflict is two nested SCOPEs over
  the same literals (theory_engine.cpp:2112-2156, TheoryEngine's lazy
  explanation proof): the theory's own SCOPE proves `(=> (and F1..Fn) G)`,
  and the theory engine wraps it in SCOPE(F1..Fn){ AND_INTRO(F1..Fn);
  MODUS_PONENS }. Alethe renders the inner SCOPE as `subproof` t2 = the
  clause `(cl ¬F1 .. ¬Fn G)`; MODUS_PONENS needs the *implication*, so
  the translation rebuilds VP3 from t2 with n `and_pos` (= CNF_AND_POS
  clauses) + `resolution` + `reordering` + `contraction`; the outer SCOPE
  becomes subproof t1 (n assumes + `and_intro` + `resolution` with VP3)
  concluding the same literal set as t2, in another order. 12 of the 74
  subproofs are such duplicates (11 with a different literal order).
  Re-pointing them to the inner subproof (plus a `reordering` when the
  order differs) makes 122 steps unreachable (and_pos 50, resolution 24,
  subproof/contraction/and_intro/reordering 12 each): 10% of the bytes.
- Of the 53 VP3s: 35 are consumed inside such outer subproofs, 12 at top
  level by a `resolution` with `and_neg` `(cl (and F) ¬F1 .. ¬Fn)` on the
  conjunction — which yields the subproof clause *again* (the SAT-level
  CNF of the lemma `(=> A G)`): a second short-circuit candidate
  (re-point the resolution to the subproof, ~5-8% more). The remaining 14
  keep `¬(and F)` in the result: there the conjunction is a genuine SAT
  atom (cvc5 sends the lemma as the implication, Tseitin-encoded), so
  `¬A ∨ G` and the CNF clauses of A are what resolution needs; only a
  cvc5-side change (lemmas as clauses) removes that.
- Even with both short-circuits the swap proof stays ~90 KB vs CPC's 70:
  the rest is the conclusion encoding (component 1 above).

**Implemented** (cvc5 alethebv `1eb17718e1`): `reorganize` records the
subproofs reached outside anchors by the sorted literal ids of their
clause; a later top-level subproof, resolution, reordering or contraction
with the same literal multiset is re-pointed to that subproof (through a
`reordering` step when the order differs; only post-visited subproofs
are recorded, so no cycles). swap: 109.6 KB / 1,334 steps -> 93.6 KB /
1,125 (and_neg 20 -> 0, and_pos 202 -> 105, resolution 243 -> 197);
read6 268.8 -> 237.3 KB; swapmem002ue (QF_ABV, bitblasting-dominated)
-0.2%; storecomm (rewriting only) and nasa quaternion_1367 (quantified)
byte-identical; all valid. Regressions alethe|arrays|quantifiers|arith
658/658. Round 4 (`all-arr4-alethe`, bin12 = cvc5 `1eb17718e1` + carcara
`d5764544`) staged.

## Arrays round 4 (2026-09-06): the canonical arrays dataset

**Run:** `all-arr4-alethe` (bin12: cvc5 alethebv `1eb17718e1` = round 3 +
div_by_zero choice term + clause round-trip short-circuits; carcara
bv-fixes `d5764544`; octa, warmed; ~45 min). CPC partner: `all-arr-cpc`.
Plots `~/exp/pfcmp/plots-arr4`; report Section 5 on these numbers.

**Outcome:** 28,579 valid (CPC 28,566), 3 holey (unchanged: ABV
cs_szymanski_5, AUFBV 320_oggenc, 064_gcc), 0 errors, 59 memouts, 58
print timeouts (53 QF_ABV), 1,826 unproved. Common 28,561: carcara
12.16x faster (median 5.47x, 99.6%); **bytes 21 vs 22 GB (CPC/Alethe
1.05 total — Alethe smaller in total; 0.85 median, CPC smaller on
84.3%)**; commands 175 vs 134 M (0.77); solve+print CPC 0.89x; pipeline
CPC 1.21x. Unique 18 vs 5. Per logic (CPC/Alethe): AUFLIRA 1.52, QF_ABV
1.34, QF_AUFBV 1.72, AUFBV 0.24 (Alethe leaner); QF_AX 0.78, QF_AUFLIA
0.82, ALIA 0.61, AUFNIRA 0.76 (CPC leaner: the conclusion encoding).
Array rules: row 658,313, idx 22,713, ext 696, row_contra 35.

**Round 3 -> 4** (28,577 common): bytes 28.2 -> 23.8 GB (-16%), steps
159.9 -> 119.3 M (-25%), check 3,191 -> 2,890 s; no proof grew, 1,090
shrank >5% (the lemma-heavy ones; median ratio 1.000). AUFLIRA 9.4 ->
6.2 GB / 63.8 -> 35.9 M steps; QF_AUFLIA -19%, QF_AX -18%, QF_ALIA -14%,
QF_ABV -3.5%. **Round 1 -> 4** (28,443 common): 42.5 -> 19.3 GB, 172.8
-> 116.3 M steps, check 4,238 -> 2,526 s, no growth, 21,541 shrank >5%.

## Division by zero (cvc5 `@div_by_zero`) — decided and implemented

Haniel's decision: represent it with a suitable choice term. The Skolem
is a *function* `@div_by_zero : Real -> Real` applied to the numerator
(likewise `@int_div_by_zero`, `@mod_by_zero`), and it enters the proof
through one `ARITH_REDUCTION` step per division:
`(= (/ a b) (ite (= b 0) (@div_by_zero a) (/_total a b)))` (no axiom
conjunction). Implementation (cvc5 alethebv, commit after `8975c05822`;
carcara `d5764544`):
- The application `(@div_by_zero a)` converts to
  `(choice ((y Real)) (= y (/ a 0)))`, the value of the operator at the
  zero denominator (SMT-LIB leaves it unspecified; the term must depend
  on `a` — a constant stand-in would equate all divisions by zero, which
  is unsound). Under `--proof-alethe-define-skolems` the function is
  defined once, `(define-fun @div_by_zero_N ((x Real)) Real (choice ((y
  Real)) (= y (/ x 0/1))))` (printer extended to lambda definitions), and
  applications are kept.
- The eliminating equality was mis-translated (the DIVISION case assumed
  the `(and eq axiom)` shape of the linear cases); it is now one step of
  the new Alethe rule `div_by_zero_intro`, checked by carcara:
  `(= (op a b) (ite (= b 0) (choice ((y T)) (= y (op a 0))) (op a b)))`,
  op in /, div, mod, y not free in a, `to_real` casts inside tolerated.
- carcara's `div_intro` also accepts the two nonlinear axiom shapes cvc5
  emits for a division by an arbitrary denominator (real:
  `(=> (not (= b 0)) (= (* b (/ a b)) a))`; integer: the bounds under each
  sign), which the small regression `alethe-div-by-zero.smt2` needs.
- z3.638004 (FFT): 22.8 KB, valid both with and without defined skolems;
  cvc5 alethe/arith regressions 188/188 (Alethe tester on); carcara suite
  green. The 11 FFT benchmarks get a follow-up cluster run
  (`all-arr3-alethe-fix`, bin11) patched into round 3.
