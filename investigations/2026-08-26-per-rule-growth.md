# Per-rule elaboration growth over the corpus

*2026-08-26.* Instrumentation: `CARCARA_RULE_GROWTH=1` (`carcara/src/elaborator/growth.rs`).
Corpus: `~/benchmarks/alethecore-eval`, base `core` pipeline
(`hoist polyeq core local core reordering prune`), 489 veriT and 494 cvc5 proofs.
Aggregation: `scripts/rule-growth.sh <config>`, table by `scripts/growth-table.py`.

## What is measured, and why the obvious number is the wrong one

The pipeline-level measurement (`scripts/pass-sizes.sh`) says *where along the pipeline* the proof
grows. This one says *which input rule* it grows for, which is the unit a classification decision
is actually about.

- **instances** — steps of that rule the pass reduced. A step it left alone is not counted.
- **emitted** — *newly built* commands, counting a subproof's body and its anchor. The step's own
  premises and everything below them are excluded: they were in the proof already. The first
  version of this instrumentation charged them, and reported `and` at 44 commands per instance
  instead of 2 — the boundary set (`step.premises ∪ discharge ∪ previous_step`) is what fixes it.
- **net** = emitted − instances. A rename has net 0 by construction.
- **share** — net against the *gross* growth (the sum of the positive nets), not the algebraic
  total, because a rule can have a negative net and normalizing by the total would push everyone
  else past 100%.

Sharing is charged to the reduction that *first built* a derivation (a global `COUNTED` set of
node pointers). A later reduction whose output the sharing pass replaces by an earlier identical
one is charged nothing — which is what actually happened to the proof.

## The two producers have opposite shapes

Gross growth: veriT 1 879 640 commands, cvc5 2 189 094.

| veriT | inst. | net | /inst | share | | cvc5 | inst. | net | /inst | share |
|---|---|---|---|---|---|---|---|---|---|---|
| `la_rw_eq` | 40 258 | 885 676 | 22.00 | 47.1% | | `or` | 754 247 | 678 615 | 0.90 | 31.0% |
| `ac_simp` | 48 111 | 775 546 | 16.12 | 41.3% | | `poly_simp_rel` | 41 166 | 568 734 | 13.82 | 26.0% |
| `and_simplify` | 26 849 | 82 248 | 3.06 | 4.4% | | `la_mult_neg` | 11 190 | 267 422 | 23.90 | 12.2% |
| `ite_intro` | 99 | 67 028 | 677.05 | 3.6% | | `and_intro` | 172 580 | 172 580 | 1.00 | 7.9% |
| `and` | 30 624 | 30 624 | 1.00 | 1.6% | | `implies` | 171 460 | 171 460 | 1.00 | 7.8% |
| `or` | 12 694 | 12 694 | 1.00 | 0.7% | | `la_mult_pos` | 4 618 | 114 833 | 24.87 | 5.2% |
| `eq_congruent_pred` | 4 734 | 9 468 | 2.00 | 0.5% | | `and` | 106 238 | 106 238 | 1.00 | 4.9% |
| `or_simplify` | 2 042 | 6 222 | 3.05 | 0.3% | | `equiv1` | 53 803 | 43 806 | 0.81 | 2.0% |
| `not_and` | 3 846 | 3 846 | 1.00 | 0.2% | | `not_and` | 28 317 | 28 317 | 1.00 | 1.3% |
| `qnt_cnf` | 143 | 2 757 | 19.28 | 0.1% | | `equiv2` | 12 481 | 12 481 | 1.00 | 0.6% |
| `equiv2` | 436 334 | −323 409 | −0.74 | −17.2% | | `not_symm` | 1 770 | 7 080 | 4.00 | 0.3% |
| `equiv1` | 31 433 | −13 311 | −0.42 | −0.7% | | `onepoint` | 61 | 4 076 | 66.82 | 0.2% |

**veriT is concentrated: two rules are 88% of its growth.** `la_rw_eq` and `ac_simp`, both
*constant-size* templates. The cost is the instance count, not the recipe, so optimizing either
recipe buys proportionally little and the only real lever is not emitting the steps.

**cvc5 is broad.** Its largest contributor, `or`, costs 0.90 commands per instance — below 1
because sharing folds some of them — and gets to 31.0% purely on 754 247 instances. The whole
clausification family is **45.1%** of cvc5's growth against 2.6% of veriT's; identical two-step
recipe, entirely different corpus impact, because the producers emit wildly different numbers of
these steps.

## Per-instance cost and corpus impact are different questions

`ite_intro` is by far the most expensive reduction in the pass at **677 commands per instance** —
and contributes 3.6%, because there are 99 of them. Same pattern on cvc5: `onepoint` at 66.8 each
is 0.2%, `miniscope_distribute` at 48.0 each is 0.1%. A 40-step recipe used twice matters less
than a 2-step one used a hundred thousand times. Ranking a growth table by per-instance cost
would put exactly the wrong rules at the top.

## Renames are free, and the table proves it

Eight veriT rules report net **exactly 0** over 897 292 instances: `th_resolution` (887 961),
`eq_reflexive` (3 370), the arithmetic bundle `prod`/`sum`/`minus`/`unary_minus`/`div_simplify`
(5 952 together), and `la_tautology`. `th_resolution` alone is 888 k steps reduced for zero
commands added.

This is the quantitative content of the rename criterion — *a one-step move onto a computational
primitive the core already has* — and it is why the promotions of `shuffle`, `nary_elim`,
`and_simplify`/`or_simplify` and the arithmetic bundle to *reducible* cost nothing in size. cvc5
emits almost none of these rules, which is why its net-zero list is 2 rules and 62 instances.

## Sharing can make a reduction negative

veriT's `equiv2` has net **−323 409** over 436 334 instances (−0.74 each), `equiv1` −13 311 over
31 433. Their two-step derivations are so repetitive that the sharing pass folds them into far
fewer distinct nodes than the steps they replace. Together they cancel **18%** of veriT's gross
growth — the reason shares are normalized by the gross rather than the algebraic total.

The same mechanism, weaker, is visible in cvc5's `or` (0.90 instead of 1.00) and `equiv1` (0.81):
partial folding rather than a net saving, because cvc5's instances are less uniform.

## What this is for

The immediate use is the SMT-LIB-wide run: the per-file output is one line per rule, so a sweep
over tens of thousands of proofs concatenates and aggregates in a single pass over a flat file
without re-parsing anything. The table then answers, directly, which reductions are worth
optimizing and which classification decisions are actually paying for themselves.
