# Splitting `la_generic` into Farkas + tightening, RESOLUTE-style

*2026-08-28 — exploration, not implemented*

`la_generic` is one rule doing two jobs: a Farkas combination over the negated clause literals,
and, per row, an *integer tightening* — `t > b` becomes `t ≥ ⌊b⌋ + 1` when the row is
integer-valued. RESOLUTE splits them: `farkas` carries no integrality at all (mixed rows convert
to Real), and every integer fact comes from the separate axiom
`(total-int a c) ▷ (a ≤ c), (c + 1 ≤ a)`, stated for an arbitrary integer *term* `a`. This note
asks what it would cost Alethe to do the same.

## The split is clean

The two halves separate exactly, and the separation is observable. Take `x : Int` and the step

```
(step t1 (cl (not (< 0 x)) (<= 1 x)) :rule la_generic :args (1 1))
```

Its decomposition is three steps:

```
(step t1 (cl (<= x 0) (<= 1 x)) :rule total_int)                       ; the integrality
(step t2 (cl (not (< 0 x)) (not (<= x 0))) :rule farkas :args (1 1))   ; pure rational Farkas
(step t3 (cl (not (< 0 x)) (<= 1 x)) :rule resolution :premises (t2 t1) :args ((<= x 0) false))
```

Checked with `x : Real` instead — that is, with integrality unavailable — **`t2` still checks and
`t1` does not**. All the integer content of the original step is in the axiom, and nothing else
needs it.

## The general recipe

For a `la_generic` step whose rows are `R₁ … Rₙ` (the negated literals) and whose strengthened
rows are `Sᵢ`:

1. one `farkas` over `S₁ … Sₙ` — the same combination the rule verifies today, minus the
   strengthening, so a *rational* certificate;
2. per tightened row, three steps: the `total_int` axiom for that row's term and `⌊b⌋`, a two-row
   `farkas` refuting `{Rᵢ, t ≤ ⌊b⌋}`, and a resolution — yielding the implication `(cl ¬Rᵢ Sᵢ)`;
3. one n-ary resolution plugging the implications into the combination.

So **2 + 3t steps** for `t` tightened rows, and 1 step when `t = 0`. Where the whole step *is* a
tightening — the two-row case — the two `farkas` steps coincide and it collapses to **3**.

## What the corpus says

Measured by instrumenting `strengthen` and checking the elaborated proofs of the `core` rung
(83 799 `la_generic` steps sampled; the population is 339 261 steps corpus-wide, since the
reductions emit `la_generic` about twice as often as the solvers do):

| | |
|---|---|
| rows per step | mean 2.91, median 2, max 144 |
| two-row steps | 82.5% of all |
| rows that get tightened | 23% |
| tightened rows per step | 0.68 |
| steps needing ≥ 1 tightening | 62% |
| steps needing the *scaled* cut (coefficient gcd > 1) | **0.2%** |

The scaled cut — `la_generic`'s cleverest move, dividing by the gcd of the coefficients and the
constant before rounding — is what the rule's comments spend the most words on, and the corpus
needs it 184 times in 83 799 steps.

## The cost

Applying the recipe to the measured shape:

| | steps | checking |
|---|---|---|
| `la_generic` today | 339 261 | 1.605 s (7.9% of the 20.28 s total) |
| split form | ~875 000 (+1.6 steps/instance) | ~2.3 s |
| **as a share of the `core` rung** | **+3.5%** of 15.15 M steps | **+3.4%** of total checking |

At the `core-full` rung the rule is 541 724 steps of 65.8 M, so the same recipe is **+1.3%**
there. For comparison, the expensive rung costs 8.5× in steps: this is two orders of magnitude
cheaper than the tier the classification already calls expensive.

## What it buys

The arithmetic checker loses its integrality reasoning entirely. Three functions exist only to
serve it — `strengthen` (70 lines, including the gcd subtlety and its worked example),
`is_integer_valued`, and `coefficients_gcd` — and `strengthen` is the one piece of the linear
fragment whose correctness is not immediate from the Farkas lemma: it is a Gomory–Chvátal
rounding step performed silently, mid-rule, on a row the reader never sees written down. In its
place goes a premise-free axiom whose check is syntactic: match `(cl (<= a c) (<= (+ c 1) a))`,
confirm `a` is integer-sorted and `c` is an integer constant.

Three further consequences, each worth more than the line count:

- **The cuts become visible.** Today a proof that needs Gomory–Chvátal rounding does not say so;
  the rounding happens inside a checker function. Split, each cut is a step, with the term and
  the bound it rounds written out.
- **Cuts become reusable.** `total_int` speaks about an arbitrary integer *term*, so one cut can
  be resolved against many rows. `la_generic` re-derives its tightening inside every step that
  needs it — visible in the numbers above as 57 221 tightenings across 243 601 rows.
- **The Real fragment stops paying for the Int one.** A QF_LRA proof would be checked by a rule
  that has no integrality code in it at all.

## Naming, and the design choice hiding behind it

CPC calls it `INT_TIGHT_UB`/`INT_TIGHT_LB`, RESOLUTE calls it `total-int`, and the two names
describe *different rules* — which is worth settling before the name is picked, because the
choice is worth about a factor of two in the cost above.

- **RESOLUTE's is a split**: `(a ≤ c) ∨ (c + 1 ≤ a)`. Nothing is tightened in the statement; it
  says the integer order has no room between `c` and `c + 1`. That is the integer analogue of
  Alethe's existing **`la_totality`** (`(cl (<= t1 t2) (<= t2 t1))`), so in Alethe it would be
  `la_int_totality` — and calling it "tightening" would misname it.
- **CPC's is directed**: from `t > b` conclude `t ≥ ⌊b⌋ + 1`. *That* is a tightening, and as an
  Alethe clause it is `(cl (not (> t b)) (>= t ⌊b⌋+1))`.

**One rule, not two.** CPC needs `UB` and `LB` because its rewrites act on a bare term. An Alethe
literal carries its polarity, and `la_generic` already normalizes all four order operators by
negating and flipping — so the upper-bound case *is* the lower-bound case on the negated row
(`t < b` ⇔ `−t > −b` ⇒ `−t ≥ ⌊−b⌋ + 1` ⇔ `t ≤ ⌈b⌉ − 1`). A checker that reuses
`process_disequality`'s normalization covers both directions in one rule.

**The directed form is also the cheaper one.** With the split, each tightened row costs three
steps (axiom, two-row Farkas, resolution); with the directed rule it costs one, and a step that
*is* a tightening — 85% of steps have two rows, 58% of those tighten exactly one, and half of
those carry unit coefficients — becomes a one-for-one rename rather than an expansion. That takes
the corpus cost from **+3.5%** of the `core` rung to roughly **+1.8%**, and about a quarter of all
`la_generic` steps stop growing at all.

So: **`la_tightening`** — the `la_` family it belongs to, the noun form its neighbours use
(`la_disequality`, `la_totality`, `la_tautology`), and the word that is accurate for the rule it
names. `la_int_tightening` if the sort should be spelled out, though tightening means nothing
over the reals. Reserve `la_int_totality` for the split, should both ever be wanted: the split is
the more primitive statement, and the directed rule is one Farkas step away from it.

## What it would cost to *build*

The reduction is a `core` pass recipe of the same shape as the ones already written: read the
coefficients (`la_generic_partial` already exposes a `coeff_trace`), recompute per row whether
`strengthen` fires and with what `⌊b⌋`, emit the axiom, the two-row Farkas and the resolutions.
The pieces it needs — `Builder::resolve`, the `unit_farkas` helper from `poly_simp`'s reduction
— exist. The scaled-cut case (0.2%) needs one extra scaling step on each side of the cut, and can
be declined at first without materially affecting coverage.

The rule to add, `total_int`, is a spec-divergence proposal in the same family as `qnt_duality`,
`mult_neg` and `ite_then_intro`: an axiom carved out of a rule that was doing two things, so that
each is checkable on its own.

## Is `la_generic` easier to *produce*? What the three solvers actually do

The argument for keeping integrality inside the rule is a producer's argument: a solver that emits
`la_generic` never has to say where it rounded, so it never has to track it. Reading cvc5, veriT
and SMTInterpol, the argument turns out to be true of exactly one of them, and for a smaller
reason than it sounds.

### First, a correction: CPC's macro rule has no integer reasoning in it

`MACRO_ARITH_SCALE_SUM_UB` is often described as the rule with the integrality baked in. It is
not. `expandMacroSumUb` (`theory/arith/arith_proof_utilities.cpp`) unfolds it into, per premise,
an `EVALUATE`/`TRUE_ELIM` of the scalar's sign, `ARITH_MULT_POS`/`ARITH_MULT_NEG` and a
`MODUS_PONENS`, and then one `ARITH_SUM_UB` over the scaled relations. Its checker
(`theory/arith/proof_checker.cpp`) fuses strictness — any strict premise makes the conclusion
strict — checks the signs and refuses spurious mixed arithmetic, and rounds nothing. The "macro"
is a step-count optimisation over `ARITH_SUM_UB`, not a fusion of two kinds of reasoning.

CPC's integer reasoning is in `INT_TIGHT_UB`/`INT_TIGHT_LB`, which are separate rules with their
own checkers. **CPC is already the split calculus this note proposes.**

### Where the rounding happens

All three solvers round at the same moment — when a strict bound on an integer variable is
asserted — and differ only in what survives the rounding.

**veriT** rounds in place. In `LA_constraint_push2` (`src/arith/LA-mp.c`) a 25-line comment gives the
two tables — one for integral constants, one for `floor(c)` — and the block writes the tightened
values into `bounds->data[atom].delta` and `.delta2`. The atom keeps its identity; the bound
under it is replaced. There is no `proof_on` guard anywhere in that block. Proof bookkeeping does
happen in the same function, but for something else: `prior_coefficient_var[atom]` records the
*rational* factor the atom's coefficients were divided by (their gcd), and
`LA_mp_conflict_proof` multiplies it back into every coefficient it writes, because `la_generic`'s
coefficients are stated against the literals as the user wrote them. So veriT tracks one kind of
scaling for proofs and deliberately does not track the other — and `LA_mp_conflict_proof` is then
a direct transcription of the simplex conflict: literals, coefficients, done.

**cvc5** derives instead of overwriting. `TheoryArithPrivate::assertionCases` takes
`constraint->getFloor()` — a *different* `Constraint` object — calls
`floorConstraint->impliedByIntTighten(constraint, …)`, and asserts *that* to simplex. The call
records an edge in the constraint database's derivation graph tagged `IntTightenAP`, and
`Constraint::externalExplain` reads the tag back to emit `INT_TIGHT_UB`/`LB`. The tag is not
proof-mode bookkeeping: the graph is what `explain` walks whether or not proofs are on. The
header says as much about the one thing that *is* extra — "If proofs are on, coefficients will be
logged. If proofs are off, coefficients will not be logged" — and says it about the Farkas
coefficients, not about the tightening.

**SMTInterpol** does both. `LinArSolve.generateConstraint` floors the bound of any new integer
atom, so the *atom itself* is the tightened one and no gap opens between a literal and its bound.
For derived bounds, `CompositeReason` stores `mExactBound` (the rational Farkas bound) beside
`mBound` (its floor or ceiling) and exposes `getExactBound()`.

One solver overwrites, two keep the derivation — and the two that keep it do so for reasons that
have nothing to do with proofs.

### What a producer would actually need to know: nothing

Carcara's `strengthen` is called from `process_disequality`, once per row, on the single negated
literal already scaled by *its own* coefficient; the gcd of the scaled-cut case is that row's gcd.
The tightening is therefore a pure function of `(literal, coefficient)` — of data that is, by
construction, already in the `la_generic` step. Whatever the split form needs can be recomputed
from the step the solver was going to write anyway.

SMTInterpol demonstrates this by construction. `ProofSimplifier.convertLALemma` is exactly the
translation from a flat Farkas certificate to the split form, and it consults nothing but the
literals: a positively-occurring `(<= t 0)` over `Int` is bridged by `totalInt(t, 0)`, the same
literal over `Real` by `total(t, 0)`, an equality by `symm`; the solver contributes only the
coefficients. `total` and `totalInt` are picked apart by sort, in the converter, after the fact.

So the honest form of the producer's argument is: `la_generic` saves veriT from *printing* a
rounding it performed in place. It does not save it from tracking one, because there is nothing
to track.

### The two designs are not equally legible, and the corpus says so

Because cvc5 emits `INT_TIGHT_UB`/`LB` as steps of their own, its Alethe output has two disjoint
kinds of `la_generic`. `alethe_post_processor.cpp` shows all three idioms:

- `ARITH_SUM_UB` → `la_generic` with every coefficient `1`;
- `MACRO_ARITH_SCALE_SUM_UB` → `la_generic` with the Farkas coefficients (equality premises
  negated, inequality premises absolute, since `la_generic` reads direction off the relation);
- `INT_TIGHT_UB`/`LB` → a **one-premise** `la_generic`, `(cl (not (< i c)) (<= i ⌊c⌋))` with args
  `(1 1)`, plus a resolution.

That third idiom *is* the tightening rule this note proposes, spelled as a degenerate
`la_generic`. It is already in the corpus.

Measured: every `la_generic` step in ~235 raw proofs per solver (`QF_LIA`, `QF_UFLIA`, `UFLIA`),
with its combination re-run once with `strengthen` switched off, to ask whether the step needs any
integer reasoning at all or merely happened to contain rows that could be rounded.

| | cvc5 | veriT |
| --- | --- | --- |
| `la_generic` steps | 48 075 | 13 910 |
| mean rows | 4.12 | 8.39 |
| `strengthen` fires, per step | 1.66 | 2.03 |
| steps that **need** integrality | 65.8% | 25.2% |
| two-row steps needing it | 31 613 / 31 613 — **100%** | 251 / 2 281 — 11% |
| steps with >2 rows needing it | **0 / 16 462 — 0%** | 3 258 / 11 629 — 28% |

Not one of cvc5's 16 462 multi-row `la_generic` steps needs integrality; every step that does is
one of its 31 613 two-row tightenings. The separation is exact, and it is exact because the
post-processor put it there. veriT's is not separable at all: a quarter of its steps need
integrality, and it is fused into general Farkas combinations eight rows wide.

This changes the cost estimate by solver. Under the directed rule, **cvc5's proofs cost nothing**:
each multi-row step becomes one `farkas`, each two-row step becomes one `la_tightening`, 48 075
steps in and 48 075 out. The +1.8% is a veriT figure. (These are raw solver proofs; the earlier
table counts the `core` rung's elaborated proofs, where the reductions emit `la_generic` about
twice as often as the solvers do.)

### Where the argument really bites, it bites the other way

The producer's argument is about *cuts* — Gomory cuts and branch-and-bound — and about those
`la_generic`'s built-in integrality does nothing at all. It is a Chvátal rounding of one row. It
cannot express a cut, and neither veriT nor cvc5 tries:

- veriT drops the branch literals (`LIT_BRANCH_Z`) from the clause and emits `lia_generic`, a rule
  whose entry in `proof-type.c` reads `"valid: not yet defined"`;
- cvc5 tags such a constraint `IntHoleAP` — "a catch-all for all integer specific reason" —
  and `Constraint::externalExplain` turns it into `mkTrustedNode(THEORY_INFERENCE_ARITH, …)`,
  which the Alethe post-processor prints as `hole`.

SMTInterpol has no hole here, and the reason is `total-int` itself. `CutCreator.generateCut`
does not derive the cut: it builds the bound literal and hands it to the DPLL engine as a
branching *suggestion* (`mSolver.mSuggestions.add(cut)`). The case split it opens is discharged
by the axiom — `total-int` is stated for an arbitrary integer *term*, so it splits on the cut's
whole linear combination — and each branch closes by ordinary Farkas. One axiom serves as the
tightening rule and as the cut rule.

That is worth stating as a fact about the ladder rather than about arithmetic. veriT's 2 993
`lia_generic` steps are the *entire* non-core residue at the `core-full` rung. They are holes
because Alethe has no integer case-split axiom — not because `la_generic` is too weak, and not
because veriT withheld anything. The split form, `la_int_totality`, is exactly the axiom that
would make them provable in principle, and the directed `la_tightening` is one Farkas step from
it. That is the concrete reason, missing when the naming section was written, to want both.

### The answer

- **For veriT, yes, but the saving is smaller than the argument claims.** `la_generic` lets it
  transcribe a simplex conflict without mentioning an in-place rounding. It saves a printing
  decision, not solver bookkeeping: the rounding is a function of the step's own literals and
  coefficients, and SMTInterpol recovers it from exactly that.
- **For cvc5 and SMTInterpol, no — it costs them.** Both keep the derivation for their own
  reasons, and cvc5 has to *fuse* what it already had separate in order to write Alethe: three
  distinct proof rules go out as one, and one of them goes out as a one-premise instance of a
  rule built for many.
- **For cuts, the argument inverts.** Fusing buys no cut strength; both cvc5 and veriT fall back
  to holes there. The rule that would buy it is the split axiom.

### Addendum: `lia_generic` is not a totality axiom, and cannot be la_generic in disguise

A natural follow-up: if the missing rule is a case split, is veriT's `lia_generic` perhaps just
that split — or, weaker, could some of its instances be converted to `la_generic`
heuristically? No, structurally, and the measurement agrees.

`LA_mp_solve_z_aux` is a recursive branch-and-bound; `LA_mp_conflict_proof_z` emits the
accumulated conflict literals of the *whole search tree*, dropping the internal branch bounds
(`LIT_BRANCH_Z` is a sentinel with no term). A `lia_generic` step is the root of a branch tree
with its interior discarded — not one split, and not one combination.

And the conversion cannot work: veriT enters branch-and-bound only when its rational simplex is
SAT over the *already-tightened* bounds (`LA_constraint_push2` rounds every integer atom's bound
at registration). Rationally feasible over tightened rows means, by Farkas, that no
per-row-tightened combination refutes them — and that is exactly the certificate shape
`la_generic` checks. `la_generic` rounds each row *before* summing; a cut rounds a combination
*after*. Branching is veriT's own signal that it is on the wrong side of that gap.

Measured: all 2 993 `lia_generic` instances in the corpus dumped as SMT problems (the negated
clause as assertions, via the `--smt-solver` hook), then asked for refutability under each
budget. Over the rationals — the plain-Farkas budget — **0 of 1 677** tested instances are
refutable (all SAT, none timed out; the untested rest are size-sampled duplicates of the same
proofs). With `la_generic`'s per-row tightening applied first (integer rows strengthened
`t > b` to `t ≥ ⌊b⌋+1` before dropping to the rationals): **2 of 1 677** (0.12%) — both
instances whose arithmetic sits under uninterpreted functions (`x_count`, `s_count`), where
veriT's slack variables are plausibly not marked integer and it branched where a tightened
refutation existed. So the heuristic is real but worth one step in a thousand; the other 99.9%
genuinely need the case split, which is to say they need `la_int_totality`.
