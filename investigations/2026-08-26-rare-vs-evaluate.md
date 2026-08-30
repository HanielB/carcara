# Splitting the rewrite-removal cost: `rare_rewrite` versus `evaluate`

*2026-08-26.* Corpus: `~/benchmarks/alethecore-eval`, 983 proofs (489 veriT, 494 cvc5) over
QF_UF, QF_UFLIA, QF_LIA, QF_LRA, UF, UFLIA.

## The question

`core-taut` removes three things at once — the `*_simplify` rules, `rare_rewrite`, and
`evaluate` — and the evaluation could only report their combined cost: cvc5's aggregate step
ratio moves 0.95 → 1.10 (+16%) and veriT's 1.69 → 1.74. That conflates two very different
decisions. Removing `rare_rewrite` means giving up the RARE rewrite engine as a proof-checking
primitive; removing `evaluate` means giving up *constant folding*. There is no reason to expect
them to cost the same, and the classification treats them as separate axioms, so the evaluation
should too.

## The fifth rung

`core-no-rare` (`RewriteReduction::ToCoreKeepEval`) reduces `*_simplify` and `rare_rewrite` to
the core but keeps `evaluate`. It differs from `core-taut` in exactly one place — `single_lemma`
emits an `evaluate` step rather than expanding the constant fold through its recipe — so the
difference between the two configurations *is* the cost of removing `evaluate`, with nothing
else moving.

With the original proof and the base `core` configuration this makes a five-rung ladder, each
rung removing one more piece of the rewrite vocabulary:

| | `core` | −`*_simplify` | −`rare_rewrite` | −`evaluate` |
|---|---|---|---|---|
| veriT aggregate step ratio | 1.72 | 1.69 | 1.74 | 1.74 |
| veriT total steps | 5.71 M | 5.62 M | 5.79 M | 5.79 M |
| veriT median checking ratio | 1.02 | 1.07 | 1.08 | 1.10 |
| cvc5 aggregate step ratio | 0.95 | 0.95 | 1.10 | 1.10 |
| cvc5 total steps | 9.05 M | 9.05 M | 10.54 M | 10.56 M |
| cvc5 median checking ratio | 0.92 | 0.91 | 1.02 | 0.96 |
| `rare_rewrite` steps (veriT / cvc5) | 4 568 / 98 370 | 25 751 / 149 231 | 0 / 0 | 0 / 0 |
| `evaluate` steps (veriT / cvc5) | 0 / 26 010 | 181 / 26 010 | 181 / 25 947 | 0 / 0 |

## The answer: it is all `rare_rewrite`

- Removing `rare_rewrite` costs cvc5 **+16.5%** of its steps (9.05 M → 10.54 M) and veriT
  **+2.9%** (5.62 M → 5.79 M).
- Removing `evaluate` on top of that costs cvc5 **+0.26%** (10.54 M → 10.56 M) and veriT
  **+0.02%** (5 787 819 → 5 788 889). The aggregate ratio is unchanged to two decimals for both.

The per-rule instrumentation says the same thing from the other side: `evaluate`'s reduction
emits **2.09 new commands per instance** (26 099 instances, 54 427 emitted, net +28 328, cvc5
only — veriT emits no `evaluate` at all). Two commands times twenty-six thousand instances is not
a number that can move a ten-million-step corpus.

**So the 16% is the price of the RARE vocabulary, not of constant folding.** A classification
that wanted to keep one computational primitive and drop the other should keep `evaluate`: it is
the one that is nearly free to remove, which is the same as saying it buys nearly nothing.

## And removing `evaluate` makes checking *faster*

cvc5's median checking ratio goes 1.02 → 0.96 across that last rung, and its total 7.7 s → 7.6 s,
on a marginally *larger* proof. `evaluate` is one of the most expensive primitives per step —
median 1.85 µs on cvc5's `core-no-rare` proofs, against 0.05 µs for `and_pos` and 0.33 µs for
`resolution` — so trading each of its 25 947 steps for roughly two cheap core steps is a net win.

This is the clearest instance in the evaluation of a pattern worth stating plainly: **a coarse
rule is not cheaper to check merely because it is one step.** The checker's cost is per *work
done*, not per command, and a primitive that runs an evaluator or a normalizer inside itself
charges for it. The same effect shows up for `poly_simp` (5.85 µs), `aci_simp` (6.77 µs) and
`rare_rewrite` (2.90 µs) — every rule at the expensive end of the per-step distribution is a
computational primitive rather than an axiom.

The one place this does not hold is where the reduction is *large*: `rare_rewrite`'s removal adds
1.5 M commands to cvc5's corpus, and 16% more proof is not paid for by 2.9 µs a step.

## Reproducing

```
scripts/run-eval.sh <logic> {verit,cvc5}-norare 6     # elaborate + bench the fifth rung
scripts/analyze.py                                     # summary.csv / rules.csv / aggregate.csv
scripts/plots.py                                       # figures/fig-configs.png (report Figure 3)
CARCARA_RULE_GROWTH=1 scripts/rule-growth.sh <config>  # per-rule growth records
scripts/growth-table.py [--md] [--top N]               # the report's growth table
```

Figure `figures/fig-configs.png` shows the ladder directly: four panels (checking cost per rule
and rule usage, one column per producer), one series per rung. The `evaluate` and `rare_rewrite`
rows are the ones to look at — each has a marker in the rungs that keep it and none in the rungs
that do not.
