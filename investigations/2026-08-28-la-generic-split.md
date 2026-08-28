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
