# Taking the `core-taut` rewrite residue to zero

*2026-08-25*

The `core-taut` regime reduces the whole rewrite vocabulary — `*_simplify`, `evaluate`,
`rare_rewrite` — to the core plus the two term-`ite` selection axioms. It left a residue: **839
steps for veriT and 8 174 for cvc5** per regime. This note is what that residue actually was, and
what it took to remove it.

## The residue, taken apart

Splitting it by *why* each step was left alone gives four groups, and only one of them was a gap in
the recipes:

| | veriT | cvc5 |
|---|---|---|
| blocked by the context guard, under identity-only assignments | 839 | 8 144 |
| blocked by the context guard, under a real assignment | 0 | 30 |
| `rare_rewrite` at depth 0: premised integer-rounding RARE rules | 0 | 111 |
| `evaluate` at depth 0: `to_int`/`to_real` folding | 0 | 156 |

### 1. The guard was asking the wrong question

Every recipe bottoms out in `refl` steps over subterms of the conclusion — including inside the
excluded-middle helper, which is `refl` plus `equiv_pos2` and one resolution, so `refl` is the only
context-sensitive rule they emit. At elaborated granularity `refl` is `strict_refl`, which checks
`context.apply(left) == right`, not `left == right`. Under an anchor that carries a substitution the
two come apart, and a step the recipe means as reflexivity is read as "the right-hand side is the
left after substituting". The recipes therefore skipped any conclusion with a free variable that an
anchor in scope *assigns*.

But solvers emit identity assignments constantly. veriT's `bind` anchors look like

```
(anchor :step t185 :args ((veriT_vr582 Int) (:= (veriT_vr582 Int) veriT_vr582)))
```

— the variable is assigned to itself. For those the substitution *is* the identity and `refl` checks
exactly as it does at depth 0. Measured over the corpus, **8 983 of the 9 013 blocked steps** are
under identity-only assignments.

The guard now asks whether the cumulative substitution moves the conclusion
(`context.apply(pool, t) == t`), keeping the cheap name test as a prefilter so the substitution is
only ever built for a term some anchor really touches.

The same reading fixed a latent bug next door: `core::equality::eq_reflexive` renamed `eq_reflexive`
to `refl` *unconditionally*. `eq_reflexive` reads no context and states plain reflexivity, so inside
a genuinely-assigning anchor the renamed step would state something else and be rejected. It is now
guarded by the same predicate.

### 2. The integer-rounding rewrites needed no axiom at all

cvc5's residual `rare_rewrite` steps are `arith-int-geq-tighten` (56), `arith-int-eq-conflict` (54)
and one `bool-eq-false`. The first two are RARE rules with *side conditions*, discharged by
`:premises`, which is why the trace replay skipped them:

```
(step t137 (cl (= (= (to_real (to_int -3/2)) -3/2) false)) :rule evaluate)
(step t138 (cl (= (+ (to_int -3/2) 1) -1)) :rule evaluate)
(step t139 (cl (= -1 (+ (to_int -3/2) 1))) :rule symm :premises (t138))
(step t140 (cl (= (>= (to_real T) -3/2) (>= T -1))) :rule rare_rewrite
      :premises (t137 t139) :args ("arith-int-geq-tighten" T -3/2 -1))
```

The premises witness that `-3/2` is not an integer and that `-1` is `⌊-3/2⌋ + 1`. But the
*equivalence* they license is unconditional, and both directions are single `la_generic` steps —
`T ≥ -3/2` with `T` an integer gives `T ≥ -1`, and `T ≥ -1` gives `T ≥ -3/2` because `-1 ≥ -3/2`.
The existing `atom_equiv` recipe does exactly that. So the only change needed was to stop bailing
out on premise-carrying RARE steps: the premises are dropped, and every arithmetic recipe validates
its own Farkas certificate before emitting, so a step whose premises really are load-bearing makes
the recipe fail rather than produce something that does not check.

`arith-int-eq-conflict` — `(= (= (to_real t) c) false)` for a non-integer `c` — needed one new
recipe, but again no new axiom: `la_rw_eq` turns the equality into the two bounds, `and_pos` splits
them, and `la_generic` closes `(cl ¬(t ≤ c) ¬(c ≤ t))` because an integer cannot sit strictly between
two consecutive integers. Eight steps, constant size.

**This only works because `la_generic`'s strengthening was fixed first.** It used to round *real*
rows as well, which made it unsound; see
[the strengthening note](./2026-08-25-la-generic-strengthening.md). The correctly-gated version is
still strong enough for all of the above.

### 3. `to_int` is the one place an axiom was genuinely needed

`(= (+ (to_int -3/2) 1) -1)` says `to_int(-3/2) = -2`. The ring normalization behind `poly_simp`
treats `(to_int -3/2)` as an opaque atom, and `la_generic` likewise, so nothing in the core knows
what the value is. Two new rules supply the floor characterization:

```
to_int_lower:  ▷ (to_real (to_int t)) ≤ t
to_int_upper:  ▷ t < (to_real (to_int t)) + 1
```

They pin `to_int t` to the unique integer in `(t − 1, t]`. From them the value follows with no
evaluator: `la_generic`'s integer strengthening turns each bound into the corresponding bound on the
candidate, and `la_disequality` closes the two bounds into the equality. The evaluation recipe folds
every ground `(to_int c)` subterm to its value this way, carrying the folding through the
surrounding term by congruence, and then proceeds as before.

These are the `to_int` half of the definitional `*_intro` family the classification already called
for; `div` and `mod` would need the same treatment and do not appear in this corpus.

## Result

With the guard refined, the premise bail-out removed, the `arith-int-eq-conflict` recipe added and
the `to_int` axioms in, `core-taut` leaves

| | rare_rewrite | evaluate | `*_simplify` |
|---|---|---|---|
| veriT | **0** | **0** | **0** |
| cvc5 | *(see report)* | | |

Regression coverage is in `core_taut_reduces_the_rewrite_vocabulary`, which now includes the two
integer-rounding rewrites (with their premises) and two `to_int` evaluations, and in the new
`to_int_lower` / `to_int_upper` / `to_int_axioms_determine_the_value` rule tests.
