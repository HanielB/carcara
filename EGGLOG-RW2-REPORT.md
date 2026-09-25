# Justifying cvc5's rewrite holes with egglog and RARE: run `rw2`, and the state of the tooling

Run of 2026-09-24/25 on the barrett cluster; report of 2026-09-25.  Branch
`egglog/rewrite-holes`; binary of the run 3f982c71, tooling described at
fedf0b31.  The run's tables are read from
`exp/results/egglog-holes/rw2/results.json.gz`; the notes behind every
number are §47.9–§47.11 of `EGGLOG-ELABORATION-NOTES.md`.

This report is about one run and the pipeline as it stands.  It does not
argue for or against the proof granularity the run used; the producer is
taken as given.

## 1. Summary

7,381 benchmarks of QF_UF, QF_LIA and QF_LRA, each with a complete cvc5
proof, went through hoist + prune, one elaboration pass and a re-check.

| | QF_UF | QF_LIA | QF_LRA | all |
|---|---|---|---|---|
| proofs | 4,316 | 2,541 | 524 | 7,381 |
| holes attempted | 1,221,095 | 747,899 | 504,702 | 2,473,696 |
| holes justified (Alethe steps emitted and checked) | 99.5% | 99.5% | 99.4% | 99.5% |
| holes proved by egglog or the normalizer (justified + reconstruction losses) | 99.9% | 99.7% | 99.5% | 99.8% |
| proofs with every hole justified | 1,907 | 2,263 | 326 | 4,496 |
| proofs re-checked `valid` | 322 | 982 | 202 | 1,506 |
| elaboration pass, summed | 80.0 h | 37.8 h | 21.2 h | 139 h |

Three ceilings sit outside the hole machinery and bound the proof-level
numbers: 3,358 proofs carry holes the pipeline never attempts (the untagged
trust steps of cvc5's arithmetic preprocessing and subtype elimination), 214
proofs fail before the pass (206 on a cvc5 resolution defect, 8 at the hoist
time limit), and 24 re-checks time out.  Of the 1,822 proofs that are fully
justified and have no untagged hole, 1,506 re-check `valid` and 316 re-check
`holey` on a hole step the elaborator itself emitted (§5.4).

The holes kept or skipped fall into these classes (counted from the
workers' messages, 12,650 in all): egglog killed at the 60 s per-hole limit
(3,823, two thirds of them in four QF_LRA families), no certificate found
in a saturated e-graph (3,856), the search or the serialization killed by
time after egglog had proved the goal (3,161, almost all on QF_UF's coarse
Boolean holes), memory kills (390), the checker rejecting a reconstructed
step (327), a goal egglog could not prove (360), a certificate the
elaborator could not decode (46), and the pass budget (144 killed, 543
skipped).  After the run the reconstruction and elaboration causes were
reproduced locally and fixed (§5.3); what is left is arithmetic:
Dartagnan's Boolean chains over integer bounds, the hole-heavy QF_LRA
families, and one integer infeasibility shape.  §7 plans each.

## 2. What ran

**Producer.**  cvc5 (branch `alethe-rewrite-granularity`, static
`bin/cvc5-rw`), 60 s, `--proof-format-mode=alethe --proof-granularity=rewrite
--proof-alethe-res-pivots --proof-elim-subtypes --print-arith-lit-token`.  A
rewrite the post-processor cannot expand is printed as
`(step t (cl (= t t')) :rule hole :args ("MACRO_REWRITE" "RW_REWRITE"))`
(or `"MACRO_SR_PRED_INTRO"`), premise-free; a step it neither expands nor
tags (`THEORY_INFERENCE_ARITH`, `MACRO_THEORY_REWRITE_RCONS_SIMPLE`,
`TRUST_THEORY_REWRITE` of subtype elimination, `DIAMONDS`) stays an
*untagged* hole the pipeline does not attempt.

**Benchmark sets.**  `rw_QF_UF` (4,316), `rw_QF_LIA` (2,541), `rw_QF_LRA`
(524): the benchmarks cvc5 proved within 60 s in the previous run `rw1`
(`gen-rw-sets.py`), so no task is spent on a solver time-out; all 7,381
proofs are complete.

**Pipeline** (`run-holes-rw2.sh`, one task per benchmark, 8 cores and 60 GB,
`octa` partition, two tasks per node, wall limit 3,100 s):

1. `carcara elaborate --pipeline hoist prune` (300 s): repeated hole
   subproofs are lifted to the top level (`ho*` steps) and duplicates
   dropped.  This is where QF_LIA's 1.97 M hole steps become 748 k
   distinct holes and QF_LRA's 1.24 M become 505 k; QF_UF loses 5%.
2. One elaboration pass, `--pipeline hole --elaborate-hole-rewrites`, 1,500 s
   per proof counted from the CLI's start, 60 s and 6 GB per hole (a hard
   kill of the worker), eight isolated workers, smallest goal first,
   set-form list encoding, the normalizer prepass, sort guards, growth caps
   120 M / 20 M tuples, memory soft cap 5.4 GB, shared-subterm abstraction
   at 16 nodes; external safety net 1,600 s.  A hole is *justified* when a
   certificate was found in the saturated e-graph, verified, and emitted as
   Alethe steps; otherwise it is *kept* with a reason class, or *skipped*
   when the pass budget ran out first.
3. `carcara check` of the elaborated proof (900 s), with the RARE file so
   that `rare_rewrite` steps check.

There is no separate checking pass.  "Proved" (checking-only) is derived
from the elaboration pass as justified + no-certificate + checker-rejected
+ killed after egglog: a hole whose worker died in serialization or in the
search had its goal proved by egglog.  The derivation is conservative in
one direction only: check and reconstruction share the 60 s, so a goal that
would have been proved in a pure checking pass but was killed *during*
egglog here is counted as lost.

**Rule file.**  `holes-rw2.rare`, 91 rules: cvc5's `big.rare` without the
bit-vector and string rules, plus `ite-eq`, `distinct-false`, and the
Boolean absorption, flattening and duplicate rules over `:list` parameters
(`bool-and-true`, `bool-and-false`, `bool-or-true`, `bool-or-false`,
`bool-and-flatten`, `bool-or-flatten`, `bool-and-dup`, `bool-or-dup`).
`tests/rare/big.rare` carries the same additions.

## 3. Yield

### 3.1 Holes

| | QF_UF | QF_LIA | QF_LRA |
|---|---|---|---|
| holes after hoist + prune | 1,221,095 | 747,899 | 504,702 |
| closed by the normalizer alone | 155,455 (12.7%) | 358,194 (47.9%) | 190,088 (37.7%) |
| handed to egglog in normal form | 339,484 | 168,025 | 160,816 |
| of which proved and bridged | 333,594 | 160,695 | 158,967 |
| of which retried as stated, proved | 5,890 → 387 | 7,330 → 3,030 | 1,849 → 45 |
| justified | 1,215,414 (99.5%) | 743,961 (99.5%) | 501,804 (99.4%) |
| kept | 5,648 | 3,457 | 2,869 |
| skipped at the pass budget | 33 | 481 | 29 |
| derived proved | 1,220,447 (99.9%) | 745,510 (99.7%) | 502,316 (99.5%) |

The normalizer (the prepass of `elaborator/mod.rs` over
`elaborator/prenorm.rs`) settles between an eighth and half of the holes
without egglog, and hands most of the rest to egglog in normal form, which
egglog then proves at 98–99%.  The retry of the stated goal after a normal
form fails is worth keeping on QF_LIA (3,030 of 7,330) and nearly worthless
on QF_LRA (45 of 1,849).

### 3.2 Proofs

| | QF_UF | QF_LIA | QF_LRA |
|---|---|---|---|
| proofs | 4,316 | 2,541 | 524 |
| failed before the pass (§5.1) | 198 | 10 | 6 |
| lost the pass to the external limit or the wall (§5.1) | 0 | 23 | 3 |
| every hole justified | 1,907 | 2,263 | 326 |
| every hole proved (derived) | 3,844 | 2,280 | 332 |
| proofs with an untagged hole | 1,890 | 1,148 | 320 |
| every hole justified and no untagged hole | 344 | 1,276 | 202 |
| of those, re-checked `valid` / `holey` | 322 / 22 | 982 / 294 | 202 / 0 |
| re-check: `holey` / `valid` / error / time-out | 3,796 / 322 / 198 / 0 | 1,533 / 982 / 2 / 21 | 313 / 202 / 6 / 3 |

`holey` means the re-check accepted every step it could check and only
`hole` steps remain: the untagged holes, a kept hole, or, in a proof with
an `arith_poly_norm_rel` certificate the relation routing did not cover, a
trust step the elaborator emitted itself (§5.4).  The 294 QF_LIA proofs
that are fully justified, carry no untagged hole and still re-check
`holey` are that last case: a quarter of the QF_LIA proofs the pipeline
could have closed.  The 22 QF_UF cases were not examined.  QF_UF's 2,426
proofs without an untagged hole re-check `valid` only 322 times because a
QG-classification proof has hundreds of holes and one kept hole keeps the
proof `holey`.

### 3.3 Against the previous run of the pipeline

`rw1` (2026-09-22/23, binary 387b0882, a 600 s checking pass and a 900 s
elaboration pass) on the same benchmarks: justified 98.9% / 94.3% / 86.2%,
proofs fully justified 1,167 / 1,445 / 185, 166 / 81 / 41 h of Carcara
time.  Between the runs: conditional-rule premises demanded where the
rule's left-hand side occurs instead of over all term pairs (the QF_UF
engine blow-up), the saturation loop stopped on egglog's own report, the
polynomial normalizer's strict-relation keys, the set-form reconstruction,
the Boolean absorption rules, smallest-first scheduling, the normal form
handed to egglog only when not larger, and the two passes folded into one.
The pass budget, which bound tens of thousands of holes in `rw1`, binds
543 here.

## 4. Cost

| | QF_UF | QF_LIA | QF_LRA |
|---|---|---|---|
| per justified hole: median / p90 / p99 / max | 0.50 / 0.57 / 1.8 / 118 s | 0.32 / 1.2 / 4.7 / 115 s | 0.39 / 0.93 / 1.9 / 117 s |
| holes over 10 s | 3,193 | 3,035 | 359 |
| hole time, summed over workers | 158 h | 135 h | 50 h |
| pass per proof: median / p90 / max | 35 / 134 / 1,508 s | 2.1 / 82 / 1,604 s | 26 / 348 / 1,602 s |
| proofs at the 1,500 s budget | 1 | 31 | 9 |
| task wall: median / p90 / max | 47 / 136 / 1,521 s | 3 / 88 / 2,803 s | 45 / 382 / 1,603 s |
| CPU over wall | 3.5 | 5.0 | 5.4 |
| task memory: median / p90 / max | 0.6 / 2.0 / 20 GB | 0.1 / 0.6 / 56 GB | 0.5 / 7.6 / 23 GB |
| hoist + prune: median / max | 0.3 / 165 s | 0.0 / 301 s | 0.1 / 19 s |
| re-check: median / max | 0.2 / 169 s | 0.0 / 901 s | 0.1 / 19 s |

The QF_UF median of 0.50 s per hole is a floor, not a distribution: a
worker is a child process that parses the rule file, builds the e-graph and
saturates, and the coarse Boolean holes of QG-classification all cost the
same.  QF_LIA's fat tail (115 k holes over a second) is the arithmetic
saturation on whole-assertion goals.  Eight workers reach 3.5–5.4 cores
of the 8: the parent's parsing, hoisting and re-check are serial, and the
smallest-first worklist drains into a few long holes at the end of a
proof.

## 5. Residue

### 5.1 Before and after the holes

- **206 proofs fail the hoist pass on a `resolution` step**: `pivot was
  not found in clause` (196 QG-classification `iso_*`, 2 Goel, 4
  Heizmann, 2 LassoRanker, 2 SMPT).  A cvc5 proof defect known from
  earlier runs, identical in `rw1`; nothing in this pipeline touches it.
- **8 Dartagnan proofs time out in hoist + prune** (300 s) and lose the
  whole task; the hoist of a proof with thousands of repeated subproofs
  is quadratic in places.
- **20 QF_LIA and 3 QF_LRA proofs hit the pass's external limit** (1,600
  s) instead of the 1,500 s budget: the budget cannot interrupt parsing
  or the non-hole checking, and the partial result is lost with the
  process.  Three further QF_LIA tasks have no pass record at all (the
  wall limit).
- **24 re-checks time out** at 900 s (21 QF_LIA, 3 QF_LRA): elaborated
  proofs of 1–2 GB where the checker's own polynomial steps dominate.
- **Untagged holes** cap `valid` at 2,426 / 1,393 / 204 proofs; the
  pipeline attempts none of them.

### 5.2 Kept holes, by class and family

| class | QF_UF | QF_LIA | QF_LRA | what it means |
|---|---|---|---|---|
| hole-time, during egglog | 461 | 1,163 | 2,199 | saturation did not reach the goal in 60 s |
| hole-time, after egglog (search, serialize, emit) | 2,885 | 250 | 26 | goal proved, certificate not extracted in time |
| no-certificate | 2,126 | 1,244 | 486 | goal proved, search exhausted its candidates |
| checker rejected the reconstructed steps | 138 | 189 | 0 | certificate found, the Alethe rule refused it |
| egglog could not prove (`Check failed`) | 0 | 355 | 5 | honest failure: no rule path |
| certificate term failed to decode | 3 | 42 | 1 | elaborator could not read the certificate back |
| memory (6 GB) | 27 | 249 | 114 | almost all during egglog |
| pass budget | 8 | 98 | 38 | |

The runner files the `Check failed` and decode failures under
`worker-error`; the split above is from the messages.

| family | proofs | fully justified | kept holes | dominant classes |
|---|---|---|---|---|
| QF_UF QG-classification | 3,851 | 1,487 | 5,359 | 3,119 hole-time (2,746 after egglog), 2,103 no-certificate, 137 rejected |
| QF_UF Goel-hwbench | 227 | 190 | 279 (+33 skipped) | 221 hole-time, 27 memory, 22 no-certificate |
| QF_LIA SMPT | 1,520 | 1,407 | 120 | 84 could not prove, 21 hole-time |
| QF_LIA Dartagnan | 78 | 2 | 2,538 (+481 skipped) | 1,063 no-certificate, 999 hole-time, 225 memory, 177 rejected, 95 worker-error |
| QF_LIA rings | 84 | 49 | 288 | 216 could not prove, 72 hole-time |
| QF_LIA 2019-ezsmt | 13 | 0 | 212 | 212 hole-time during egglog |
| QF_LIA calypto | 13 | 0 | 167 | 98 no-certificate, 77 hole-time |
| QF_LIA Averest | 10 | 0 | 36 | 22 hole-time, 13 memory |
| QF_LIA fft | 2 | 0 | 82 | 78 no-certificate |
| QF_LIA check | 4 | 2 | 2 | integer infeasibility (§7.3) |
| QF_LRA sc | 25 | 0 | 1,597 (+29 skipped) | 1,509 hole-time during egglog on 59–114-node goals |
| QF_LRA uart | 18 | 0 | 587 | 347 no-certificate on 43-node goals, 223 hole-time on 333-node goals |
| QF_LRA tta_startup | 39 | 0 | 230 | 198 hole-time, goals 900–11,000 nodes |
| QF_LRA spider | 42 | 6 | 283 | 166 hole-time, 68 memory (510-node goals), 49 no-certificate |
| QF_LRA sal | 96 | 61 | 79 | 57 hole-time, 20 memory |
| QF_LRA LassoRanker | 67 | 46 | 57 | 46 hole-time, goals 3,000–8,700 nodes |
| QF_LRA clock_synchro | 34 | 22 | 19 | 19 hole-time, goals 2,000–3,400 nodes |

### 5.3 What was reproduced and fixed after the run (fedf0b31)

The smallest proof of each class of §5.2 that is not an egglog time-out
was replayed locally with the run's options (notes §47.11, commits 36cc79fa
and fedf0b31):

- **Decode failures**: a congruence spine the search met from the far side
  arrives under `Symm` nodes; the spine descent found no `cong` premises
  in it.  `spine_arguments` now reads `Symm` as a flip.
- **`and_simplify` / `or_simplify` rejections** (QG-classification, SMPT,
  Dartagnan): the complementary pair was found through nested `and`/`or`
  while the checker's rule reads direct arguments only.  The flat form is
  stated first by `aci_simp`.
- **No certificate on Boolean chains with many constant-valued arguments**
  (QG-classification, Goel, CLEARSY, SMPT): the search substituted one
  constant per congruence edge and spent its four rejustifications on
  congruences between an `and` and an equality.  Now a candidate replaces
  every constant-valued subterm at once, the ACI computation is the
  checker's `aci_simp` in full, a one-step checker computation is tried
  before the congruence and the search, and no congruence is attempted
  between two different heads.
- **A goal egglog cannot prove as stated but the normalizer closes**
  (SMPT's `(<= p p)` inside a disjunction): the not-larger rule had kept
  the stated goal for egglog.  The rule is now confined to the checking
  pass; elaboration tries the normal form first whatever its size, the
  stated goal on a failure.  The `rings` unproved holes were not
  examined one by one; the smallest `rings` proof with them in the run
  justifies every hole under the fixed binary, and `uart-5.base.cvc`,
  whose family had 347 no-certificate holes in the run, keeps one hole
  of 299 (a memory kill inside egglog).

Every reproducer elaborates and re-checks.  The Dartagnan proof
`benchmark02_linear-O0` goes from 198 to 200 of 231 justified with no
rejection or decode failure left; `ring_2exp10_3vars_1ite_unsat`, the
smallest `rings` proof with unproved holes in the run, justifies 349 of
349.  Five larger samples keep their justified counts and run their passes
in half the time:

| proof | 3f982c71 | fedf0b31 |
|---|---|---|
| clocksynchro_3clocks | 195 justified, 90 s | 195, 65 s |
| cut_lemma_01_008 | 126, 17 s | 126, 7 s |
| MULTIPLIER_3 | 272, 16 s | 272, 7 s |
| tgc_io-safe-6 | 140, 12 s | 140, 5 s |
| ring_2exp10_3vars_1ite | 349, 22 s | 349, 11 s |

Not reproduced, hence not claimed: the QF_UF search kills after egglog
(2,885 holes) beyond what the halved pass times suggest, and the
`2019-ezsmt`, `calypto`, `Averest` and `fft` residue.

### 5.4 Limitations in the emitted proofs

- A certificate whose `arith_poly_norm_rel` obligation the relation routing
  cannot express through `poly_simp_rel` is emitted as a
  `TRUST_THEORY_REWRITE` hole step (`rare_hole.rs`, the `trusted` fallback).
  Such a proof re-checks `holey` although every hole was "justified": 294
  QF_LIA proofs in this run (§3.2).  The runner does not count the steps;
  the five local samples above carry 14–50 each.  Extending the relation
  routing (or emitting the `la_generic` pair of §7.3 for the tightened
  shapes) is the cheapest `valid` gain left on QF_LIA.
- The hole steps the pipeline never attempts are copied through unchanged.
- The runner's residue classes are read from worker messages; an egglog
  `Check failed` is a `worker-error` there, not an "unproved".

## 6. The tooling at fedf0b31

Everything below is on `egglog/rewrite-holes` (Carcara, `~/carcara/wt-rwgran`)
and the run scripts in `~/exp/egglog-holes`.

**Front end.**  `carcara elaborate --pipeline hoist prune` (hoist repeated
hole subproofs, prune duplicates); `--pipeline hole` with
`--elaborate-hole-rewrites` (or `--hole-check-only`).  Options in force:
`--rare-file`, `--rare-list-encoding set-form`, `--rare-sort-guards`,
`--rare-growth-cap-arith`, `--rare-growth-cap-plain`,
`--rare-memory-soft-cap`, `--rare-check-timeout`, `--hole-threads`,
`--hole-isolate`, `--hole-memory-limit`, `--hole-total-budget`,
`--hole-prenormalize` (with `--hole-prenormalize-rewrite-all` to hand
egglog every normal form in check-only mode), `--hole-smallest-first`,
`--hole-abstract-shared N`, `--parse-hole-args`, `--expand-let-bindings`,
`--allow-int-real-subtyping`.  Batching and reuse options exist
(`--hole-batch*`, `--hole-reuse-*`) and were not used.

**Normalizer prepass** (`elaborator/prenorm.rs`, driven from
`elaborator/mod.rs`).  Computes a normal form of every hole's two sides
with four checker-certified procedures: ACI normalization of `and`/`or`
(`aci_simp`), polynomial normalization (`poly_simp`), relation
normalization to a scaled difference with the constant on the right
(`poly_simp_rel`), and `distinct` elimination.  A hole whose sides
normalize equal is closed outright; otherwise the normal form is handed to
egglog first and bridged back to the stated goal with the certificate
steps.  It is deliberately restricted to what core Alethe rules certify;
no Boolean or equality simplification from the `*_simplify` family lives
here.  Integer tightening (a non-integral bound on an Int relation) is
*not* implemented, although the specification in the notes (§25) lists it;
§7.3 returns to this.

**Engine** (`rare/engine.rs`, `rare/computational/*`).  RARE rules
compiled to egglog with the goal's terms as seeds; sort guard relations
(Int, Real, Bool, String, RegLan) keep polymorphic rules on the right
sorts; a conditional rule's premise is demanded at the occurrence of its
left-hand side rather than over all term pairs; `:list` parameters use the
set-form encoding (`Assoc` cells with set-contains built-ins) so
flattening, absorption and duplicate rules fire in one step; polynomial
normalization and evaluation are built-in relations
(`arith_poly_norm.egglog`, `arith_poly_norm_rel.egglog`,
`evaluation.egglog`); saturation runs in bounded steps against the growth
caps, the memory soft cap and the deadline, and stops when egglog reports
no update.

**Reconstruction** (`rare/reconstruction/`).  A certificate search over
the saturated e-graph from the goal's left class to its right class:
candidate edges are rule instances (grounded by e-matching the rule's
sides), congruence (one child or every constant-valued subterm replaced at
once), computations (evaluation, ACI, polynomial, `distinct`), list rules
on the set form, and ACI-modulo matching; a `prove_in_class` strategy
order of list rule, one-step computation, congruence, transitivity, ACI,
arithmetic, ACI-modulo; four rejustifications per obligation.  Every
certificate is verified by an independent rule checker before it is
emitted.

**Elaborator** (`elaborator/rare_hole.rs`).  Certificates become Alethe
steps (`rare_rewrite`, `cong`, `trans`, `symm`, `refl`, `evaluate`,
`aci_simp`, `and_simplify`, `or_simplify`, `poly_simp`, `poly_simp_rel`,
`equiv_simplify`, `ite_simplify` and the rest of the checker's
computations), inserted at the hole with fresh ids and re-checked by the
checker in the worker before the parent accepts them.  Workers are
isolated processes with a memory limit and a hard deadline; a kill is
reported with its phase (egglog, serialize, index, search, emit) and the
time spent before it.

**Tests.**  286 library tests (`cargo test --lib`), among them the
end-to-end elaboration fixtures in `tests/rare/elaborate/` (13 proofs,
each elaborated and re-checked `valid`): `RF-12-rewrite`,
`and-reflexive`, `reversed-spine`, `nested-complement`, the `ite` and
bounds fixtures.

**Runner and analysis.**  `run-holes-rw2.sh` (the pipeline above, one
`[pfchk] key=value` record per stage, residue classes per hole),
`submit-egglog-rw2.sh` (sets, partition, limits), `gen-rw-sets.py` (sets
from a previous run's complete proofs), and the readers in
`~/exp/egglog-holes/analysis-rw2/` (`read3.py`, `rw2stats.py`,
`rw2hoist.py`, `rw2we.py`, `rw2lra.py`, `rw2fj.py`) whose output is
§3–§5.  The static
binary of fedf0b31 is built
(`target/x86_64-unknown-linux-gnu/release/carcara`) and not yet uploaded;
a further run needs a staged proposal.

## 7. Plans for the three open directions

### 7.1 Dartagnan's arithmetic Boolean chains (QF_LIA)

*What it is.*  78 proofs, 2 fully justified, 3,019 holes lost.  Locally,
after the fixes of §5.3, `benchmark02_linear-O0` still keeps 31 of 231: 22
no-certificate, 4 memory, 2 hole-time.  The goals are cvc5's rewrite of a
whole assertion: an implication whose antecedent is a conjunction of bound
pairs `(and (<= a b) (>= a b))` and equalities `(= x 1)`, rewritten into a
flat conjunction of `(not (>= …))` / `(>= … 1)` literals (the integer
tightening of `<` and `>`), with `ite`-valued terms inside the polynomials
and `(= x (ite c a b))` atoms, 50–800 nodes.  One 16-node case,
`(= (ite (>= (+ …) 1) true true) true) = true`, has no certificate either,
so at least one gap is a plain search gap.

*Plan.*

1. **Micro-reproducers.**  Cut the 22 goals into their conjuncts and
   disjuncts (`expand.py`'s iterative parser; `micro.py` needs its
   declaration extraction finished for Dartagnan's quoted symbols) and
   find the smallest sub-goal with no certificate.  The `ite` case first:
   egglog proves it, so the search does not see the rule instance
   (`ite-eq-branch`, or `ite-then-true` followed by `bool-or-true`) or
   discards the congruence into the `true` class.  Expected: a one-line
   fix in candidate generation or a missing `Certificate` kind.
2. **Structural descent before search.**  When both sides share the head
   and arity, prove the children pairwise and join with `cong`, recursing
   into each child; only a child pair whose classes differ after descent
   goes to the search.  This is the "split" pass the veriT holes needed
   (notes §34, §42) and the analogue of the all-constants candidate for
   non-constant children.  Bounds: whole-assertion goals have 10–80
   atoms; every atom is a small, independent relation goal the search
   already proves (the `(<= a b)` to `(not (>= b (+ a 1)))` shapes are
   `arith-elim-*` and `arith-geq-tighten` instances, and the bound pairs
   are `arith-eq-elim-int`).
3. **Rejustification budget by goal size.**  `MAX_REJUSTIFICATIONS` is 4
   for every obligation; log the count that would have sufficed on the
   22 goals with the debug `obligation … failed` trace and set it from
   the goal's atom count if the trace says so.
4. **Memory and time kills during egglog** (225 memory, 999 hole-time in
   the run): rerun the smallest such goal with the engine's run report
   per ruleset to name the ruleset that grows; the polynomial rules on
   `ite` arguments are the first suspect (notes §37–§38 made the `ite` an
   atom for the normalizer, not for the egglog polynomial relation).
   Then either guard the rule or lower `--hole-abstract-shared` so the
   repeated `ite` terms are abstracted before egglog.
5. **Measure locally, then a cluster run.**  All 78 Dartagnan proofs
   solve in under a second of cvc5 time; a local batch of the 78 with
   four workers and the run's limits is 2–3 hours and is the exit
   criterion: 70 of 78 fully justified, no no-certificate class left.
   Then `rw3` on the three sets with the fedf0b31 (or later) static
   binary.

### 7.2 The hole-heavy QF_LRA families

*What it is.*  `sc`, `uart`, `tta_startup`, `spider`, `sal`,
`LassoRanker`, `clock_synchro`: 2,852 holes lost, 2,351 of them egglog
time or memory kills.  Two different problems hide in the class:

- **Shape blow-ups on small goals.**  `sc`'s 1,509 kills are on goals of
  59 and 114 nodes; replayed locally on `sc-5.base.cvc` (415 holes, the
  run's options, fedf0b31): 401 justified, 7 holes of 59 nodes fail
  *fast* (`Check failed`, no rule path), 5 holes of 114 nodes saturate
  for 60 s, 2 have no certificate.  The goals are
  `MACRO_SR_PRED_INTRO` disjunctions of transition conjunctions where
  cvc5 flattened the `and`s, oriented the equalities, turned `<=` atoms
  into `(>= (+ …) 0.0)` mirrors and pushed `ite`s into the polynomials.
  These are rule and search gaps, not size.  `uart`'s 347 no-certificate
  holes (43-node goals) do not survive the fixes of §5.3: `uart-5.base.cvc`
  (299 holes) justifies 298 locally, the one loss a memory kill during
  egglog on a 179-node goal, the shape of the run's 17 `uart` memory
  kills.
- **Size.**  `tta_startup` (goals 900–11,000 nodes), `LassoRanker`
  (3,000–8,700), `clock_synchro` (2,000–3,400), `spider`'s memory kills
  (510 nodes): saturation over the whole assertion does not finish in
  60 s and 6 GB.

*Plan.*

1. **The `sc` 59-node goal, exactly.**  Take `t7` of `sc-5.base.cvc`
   (fails in under a second), split the disjunction into its three
   disjuncts and each into its conjuncts, and find the conjunct pair
   egglog cannot join.  The candidates from the shapes: the `<=` to `>=`
   mirror over a negated difference (notes §37 shows the normalizer does
   not close it and egglog needs `arith-*` routing), an equality
   `(= x_85 2.0)` against `(= (+ …) x_72)` after polynomial
   normalization, and `(= x (ite c a b))` lifting.  Each is one rule or
   one normalizer orientation; the normalizer fix is the relation
   orientation to `<=`/`not <=` before `poly_simp_rel`, which is what
   `comp_simplify` certifies and therefore stays within core Alethe.
2. **The `sc` 114-node goal**: profile the saturation (run report per
   ruleset at each bounded step) to see which ruleset produces the
   tuples; the same goal with the `ite` subterms replaced by fresh
   constants is the control (notes §37: 0.29 s against 4 GB in 10 s).
   If the `ite` polynomial descent is the cause, exclude `ite` from the
   polynomial relation's argument positions in `arith_poly_norm.egglog`,
   as the normalizer already does.
3. **`uart`'s memory kill** (`t262` of `uart-5.base.cvc`, 179 nodes, 6 GB
   inside egglog): the control of step 2 applies unchanged; the goal is
   in the local replay (`scratchpad/rw1/lra/uart-5.base.cvc`).  Its
   333-node egglog time-outs in the run (223 holes) are the same family
   one size up.
4. **Big goals**: the structural descent of §7.1 step 2 is the main lever,
   since a 3,000-node assertion is a conjunction of a few hundred
   independent atoms; combine with the normalizer bridging so that each
   atom pair is first normalized and only the pairs that differ go to
   egglog, each as its own small worker call.  Second lever: the per-hole
   limit scaled by goal size (60 s is the same for a 16-node goal and an
   11,000-node one) within the same pass budget.
5. **Exit criterion**: the smallest proof of each of the seven families
   fully justified locally, then `rw3`.  The families are small (cvc5
   median 0.2 s; 25 `sc`, 18 `uart`, 39 `tta_startup` proofs), so a
   local batch of one proof per family is minutes, and of every proof of
   the seven families under a day with four workers.

### 7.3 Integer infeasibility

*What it is.*  `(= (+ (* 3 x1) (* 3 x2)) 1) = false` (QF_LIA `check`,
`int_incompleteness1`; two holes in the run).  Egglog has no rule path:
`arith-int-eq-conflict` needs the `(= (to_real t) c)` shape and the goal
is Int on both sides.  The normalizer scales the relation by the
reciprocal of the coefficients' gcd, producing `(= (+ x1 x2) 1/3)`, an Int
relation with a non-integral bound, and stops there: its specification
(notes §25) says such an `=` is decided `false`, but `relation_step` has
no tightening at all, so the normal form is not `false` and egglog cannot
prove it either.

*The recipe, verified.*  A hand-written proof of the closed form checks
`valid` with the current checker (`scratchpad/gcd/p.alethe`):

```
(step t1 (cl (not (= (+ (* 3 x1) (* 3 x2)) 1)) (>= (+ x1 x2) 1))
      :rule la_generic :args (1/3 1))
(step t2 (cl (not (= (+ (* 3 x1) (* 3 x2)) 1)) (not (>= (+ x1 x2) 1)))
      :rule la_generic :args (-1/3 1))
(step t3 (cl (not (= (+ (* 3 x1) (* 3 x2)) 1))) :rule resolution :premises (t1 t2))
(step t4 (cl (= (= (= (+ (* 3 x1) (* 3 x2)) 1) false) (not (= (+ (* 3 x1) (* 3 x2)) 1))))
      :rule equiv_simplify)
(step t5 (cl (= (= (+ (* 3 x1) (* 3 x2)) 1) false) (not (not (= (+ (* 3 x1) (* 3 x2)) 1))))
      :rule equiv2 :premises (t4))
(step t6 (cl (= (= (+ (* 3 x1) (* 3 x2)) 1) false)) :rule resolution :premises (t5 t3))
```

`la_generic`'s integer strengthening (the gcd rule in
`checker/rules/linear_arithmetic.rs`) does the work: the negation of
`(>= (+ x1 x2) 1)` strengthens to `(<= (+ x1 x2) 0)`, and the equality
scaled by 1/3 contradicts each side.

*Plan.*

1. **Where it belongs.**  The normalizer's `relation_step` already decides
   a relation whose difference is constant; deciding an Int relation whose
   scaled bound is non-integral is the same kind of step, certified by a
   core rule (`la_generic`) and not by a `*_simplify` rewrite, so it stays
   inside the normalizer's remit.  Implement the tightening the
   specification lists: `=` with a non-integral bound is `false`; `>=` /
   `<=` round the bound up / down; `>` / `<` become `>=` / `<=` of the
   floor plus one / ceiling minus one.  Each case emits its `la_generic`
   pair (the recipe above generalizes: two `la_generic` steps per
   tightened relation, one per direction, then `equiv_simplify` /
   `equiv2` to state the equality).  This also gives the normalizer the
   `(> t 0)` to `(>= t 1)` step cvc5 applies everywhere in Dartagnan and
   SMPT, today left to the `arith-geq-tighten` rules in egglog.
2. **The alternative, if the normalizer is to stay as it is**: have the
   engine present an Int relation with a Real constant in the
   `(= (to_real t) c)` shape the RARE rules expect (a sort-guarded
   `to_real` insertion at seeding), so `arith-int-eq-conflict` and
   `arith-int-geq-tighten` fire; the certificate then cites the RARE rule
   and `poly_simp_rel`.  It covers the same shapes but only where the
   rule file has them.
3. **Fixture and test**: `tests/rare/elaborate/int-gcd-infeasible.*` from
   `int_incompleteness1`'s hole; `elaborates_an_integer_infeasible_equality`
   re-checks `valid`.
4. **Measure**: `int_incompleteness1` and `int_incompleteness3` fully
   justified locally; the count of `arith-geq-tighten` certificates in
   the Dartagnan and SMPT replays before and after, as the cost/benefit
   of step 1's wider effect.
