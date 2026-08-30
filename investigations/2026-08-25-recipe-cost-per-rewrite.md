# Which rewrites are too costly to expand

*2026-08-25*

`core-taut` reduces the whole rewrite vocabulary — `*_simplify`, `evaluate`, `rare_rewrite` — to the
core, with zero residue. The question this note answers is the other one: *given that it can be
done, which rewrites should stay rules anyway, because their derivation is too expensive?*

## How it was measured

The recipes are instrumented (`CARCARA_RECIPE_COST=1`): for each rewrite — a RARE rule name, or a
`*_simplify` rewrite label — the elaborator records how many core steps that instance's recipe
emitted, and prints `RECIPE_COST <name> instances=N steps=S mean=M` per run. Collected over the
whole evaluation corpus, both producers, through the `core-taut` pipeline.

**176 453 instances of 53 distinct rewrites, 1 571 972 core steps.** Mean 8.9 steps per rewrite.

## The table

| rewrite | instances | steps | mean |
|---|---:|---:|---:|
| `ite-else-false` | 2 | 38 | 19.0 |
| `or-not-refl` | 50 | 928 | **18.6** (8–32) |
| `or-false-elim` | 1 | 18 | 18.0 |
| `ite-then-true` | 10 | 180 | 18.0 |
| `bool-impl-elim` | 2 393 | 38 288 | 16.0 |
| `bool-eq-false` | 21 886 | 262 634 | 12.0 (12–14) |
| `bool-eq-true` | 4 486 | 53 832 | 12.0 |
| `ite-not-cond` | 666 | 7 992 | 12.0 |
| `arith-int-eq-conflict` | 54 | 648 | 12.0 |
| `ite-eq` | 311 | 3 421 | 11.0 |
| `arith-geq-ite-lift` | 11 | 121 | 11.0 |
| `distinct-false` | 26 | 286 | 11.0 |
| `bool-double-not-elim` | 21 545 | 215 450 | 10.0 |
| `bool-impl-false1` | 24 230 | 242 300 | 10.0 |
| `bool-impl-true2` | 356 | 3 560 | 10.0 |
| *(twenty rewrites at 8.0)* — `arith-elim-lt` 22 637, `eq-symm` 23 355, `arith-leq-norm` 4 462, `arith-eq-elim-real` 3 530, `arith-eq-elim-int` 3 491, `arith-elim-gt` 1 850, `bool-and-de-morgan` 1 204, `comp-gt-elim` 1 073, `implies-contra` 622, `bool-implies-uncurry` 504, `comp-lt-elim` 415, `bool-implies-or-distrib` 165, `bool-implies-de-morgan` 156, `bool-or-de-morgan` 102, `bool-implies-peirce` 79, `bool-or-and-distrib` 72, `and-true-elim` 25, `equiv-neg-both` 13, `bool-and-mp-r` 13 | | | 8.0 |
| *(twelve rewrites at 7.0)* — `bool-and-conf` 8 004, `arith-elim-leq` 7 625, `bool-and-conf2` 5 601, `comp-geq-flip` 3 976, `arith-geq-tighten` 1 799, `bool-or-taut2` 842, `and-false` 514, `or-true` 335, `arith-geq-norm1-int` 107, `arith-geq-norm1-real` 100, `arith-int-geq-tighten` 56, `bool-or-taut` 29 | | | 7.0 |
| `eq-refl`, `comp-leq-refl` | 3 003 | 15 015 | 5.0 |
| `ite-false-cond`, `ite-true-cond`, `ite-eq-branch` | 4 617 | 13 851 | **3.0** |

## What the shape of it says

**Nothing here is expensive in the tier's sense.** The spread is 3 to 19 steps, and the mean is 8.9.
For comparison, the reductions the classification *does* call expensive cost an anchor plus a body
per instance — `sko_ex` measured at ~35 steps *per binding*, an ~8× local blowup. No rewrite recipe
is within reach of that.

**Only two rewrites have a cost that is not constant**, and both are mild:

- `or-not-refl` — removing `¬(t = t)` from a disjunction — ranges 8 to 32 steps across files,
  because the recipe is linear in the number of disjuncts it has to carry past. This is the one
  rewrite whose recipe grows with the *instance*, and the only genuine candidate for "keep the rule".
  It fires 50 times in the whole corpus.
- `bool-eq-false` ranges 12 to 14, from the degenerate-instance fallback (`(= (= false false)
  (not false))` takes the ground-evaluation route).

Everything else is a fixed template. The three cheapest — the `ite` condition rewrites at 3 steps —
are the term-`ite` selection axioms doing exactly the job they were added for.

**Where the total cost actually is, is arity, not the recipes.** The four largest contributors are
`bool-eq-false` (262 k steps), `bool-impl-false1` (242 k), `bool-double-not-elim` (215 k) and
`eq-symm` (187 k) — all constant-cost templates that simply fire tens of thousands of times. Halving
any of those templates would save more than eliminating every rewrite above 15 steps put together.

**And the `*_simplify` chains are short.** A `*_simplify` step's cost is (trace length) × (per-link
recipe), and the measured mean trace is **2.3 links**. The feared multiplication does not happen:
the fixpoints solvers actually emit are one or two rewrites deep.

## The answer

On this corpus, **no rewrite earns a rule on cost grounds**. If one had to be named, it is
`or-not-refl`, the only recipe that grows with its instance — and it fires 50 times.

Two caveats worth stating rather than hiding:

1. **This is a corpus argument, not a worst-case one.** The `:list` rules are linear in the arity of
   the `and`/`or` they act on, and this corpus does not exercise wide instances of them. The rule
   that *did* blow up on arity — `and_simplify`/`or_simplify` over hundred-argument conjunctions —
   was fixed by the `aci_simp` rename, not by keeping a rewrite, which is the pattern to prefer:
   reach for a computational primitive the core already has before reaching for a new rule.
2. **The cost that matters for the vocabulary is not the recipe's.** The reason to keep
   `rare_rewrite` would be trust-anchor economy (one rule instead of 53), and the earlier finding
   stands against it: a `rare_rewrite` check costs ~1.9 µs against ~0.07 µs for a `refl`, so the
   engine is the most expensive thing in the vocabulary per checked step, and the frozen-set
   analysis showed the whole vocabulary reduces for 1.2% of aggregate size on veriT and 17% on cvc5.
