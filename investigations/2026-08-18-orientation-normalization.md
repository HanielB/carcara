# Orientation normalization: feasible, sound, and not worth building

**Branch:** `inv/orientation-normalization` (commit `168ede40`, prototype + analysis tooling).
**Verdict:** the global pass **works** — the constraint system is a parity union-find that can
never be contradictory, the prototype's output re-checks on 489 proofs — but 96.7–98.8% of the
orientation variables are *pinned*, so the net yield beyond a three-line peephole is ~930 steps on
veriT and 0.26% of the DAG on cvc5. The investigation's real finding is what those 175 000
removable steps actually are: **two elaboration passes undoing each other**, which should be fixed
at the source.

## The opportunity, measured

| | total rule steps | `symm` | `trans` | `cong` | `eq_symmetric` |
|---|---|---|---|---|---|
| veriT, **input** | 3 779 178 | **0** | 38 116 | 611 601 | 0 |
| veriT, elaborated | 7 011 372 | **856 457 (12.2%)** | 473 039 | 930 010 | 0 |
| veriT-eq_cl, elaborated | 7 000 940 | 192 335 (2.8%) | 271 666 | 872 922 | **563 193 (8.1%)** |
| cvc5, **input** | 9 387 134 | 300 488 (3.2%) | 525 160 | 681 657 | 0 |
| cvc5, elaborated | 12 303 478 | 302 416 (2.5%) | 524 516 | 674 326 | 0 |

- **On veriT proofs every `symm` is elaboration-introduced**: the inputs contain none, the output
  856 457 — one step in eight. This is precisely the local-bridging tax the idea targets.
- **On cvc5 proofs there is almost nothing to win**: 300 488 of 302 416 are already in the input.
- **The eq_cl configuration relabels the tax rather than removing it**: `symm` falls to 2.8% while
  `eq_symmetric` rises to 8.1%, for an unchanged ~10.8% combined.

For calibration, the existing global `reordering` elimination deletes 300 725 steps from cvc5
inputs — 3.2% of them.

**The cost is size, not checking time.** `symm` is the cheapest rule there is: those 856 457 steps
are **0.43% of checking time** (57.5 ms of 13.48 s), i.e. 0.06% of wall time, since parsing is
~87% of the cost. The case for the idea is proof size and the parsing it implies.

**There is no transitive multiplier.** A `trans` that consumes a `symm` still needs the `trans`
(115 038 veriT `symm` steps feed a `trans`, 105 834 feed a `cong`, and none of those consumers
disappear). The one construct that glues a `symm` into a `trans` fires 4 936 times in eq_cl and
zero times elsewhere. Budget exactly one step per `symm`.

## The constraint system

Every step concluding a unit `(cl (= a b))` with `a ≠ b` gets a boolean "is this conclusion
reversed?"; a step concluding `(= t t)` is self-dual and carries no variable (60 328 of them in
veriT). `trans` forces its conclusion's variable equal to every premise's and reverses the premise
order; `cong` likewise, positionally, without reordering. `symm` is not a constraint at all — it is
the *objective*: the step vanishes exactly when its variable and its premise's differ.

Everything else is **pinned**: `strict_refl` (it applies the context to the left side only, and
`Γ ▷ t ≈ u` means `σΓ(t) ≈ u`, which is not symmetric), `assume` (exact set membership in the
problem's premises at elaborated granularity — no polyeq fallback), every rule whose own check
fixes which side is which (`rare_rewrite`, `evaluate`, `poly_simp`, the `*_simplify` family,
`aci_simp`, `connective_def`, `bind`, `onepoint`, `sko_*`, `let`, …), and any equality consumed as
a *clause literal* by `resolution`, `equiv1/2`, `eq_mp`, a discharge, or a subproof's closing step.
Forest roots are *not* pinned: `ProofNodeForest` makes every top-level command a root, the real
conclusion is the empty clause, and an unconsumed step can be flipped harmlessly.

All hard constraints are equalities between variables, so the system is a **parity union-find, not
2-SAT** — and since the input proof is already valid, the all-zero assignment satisfies every hard
constraint, so **it can never be contradictory** (confirmed: 0 conflicts over 1 401 proofs and
5.2 M hard edges). What is left is MAX-2-LIN(2) over the free components, NP-hard in general and
trivial here: the components are singletons and pairs, the largest having 39 variables.

**The boundaries are where it dies.** Pinned variables: **96.7%** (veriT), 94.7% (eq_cl), **98.8%**
(cvc5). Of veriT's 330 225 unremovable `symm` steps, **328 046 (99.3%) have a discharge-subproof
`assume` as their premise** — the `eq_transitive`/`eq_congruent` reduction assumes each clause
literal and then needs some of them the other way round, and the assumption's orientation is the
literal's orientation in the enclosing clause. Lifting the analysis to clause literals would not
rescue it: for **92.3%** of those equalities (100% in cvc5) the same equality also occurs as a
*proper subterm* of another term that traces back to the problem's assertions, so flipping the
literal would desynchronize it from a term the pass cannot rewrite. That is the "equalities are
terms" obstruction, quantified. For cvc5 separately, 57.4% of all `symm` steps are consumed by
`resolution`, i.e. rigid by construction.

## What the prototype found

`carcara/src/elaborator/orientation.rs` — parity union-find, local search over free components,
rewrite plan — behind a hidden `carcara orientation [--breakdown] [--apply]` subcommand and a
pipeline pass. Over 1 401 proofs:

| config | `symm` | removable | pinned | DAG nodes before → after |
|---|---|---|---|---|
| veriT | 506 052 | **175 016 (34.6%)** | 330 225 | 5 670 408 → 5 495 392 (−3.09%) |
| veriT-eq_cl | 177 221 | **175 016 (98.8%)** | 2 184 | 4 045 724 → 3 870 708 (−4.33%) |
| cvc5 | 302 810 | 34 644 (11.4%) | 265 348 | 13 514 248 → 13 479 604 (−0.26%) |

**But the veriT win is not orientation normalization.** Of the 175 016: 87 358 are a `symm` over a
`refl` and 86 728 a `symm` over a `symm` — **174 086 (99.5%) are one redundant round trip**, and
only ~930 are genuine global flips. The round trip has a precise cause, two passes undoing each
other:

```
(step t9.t1.t1 (cl (= ?v_0 @p_1)) :rule refl)                       ; polyeq/reflexivity.rs
(step t9.t1    (cl (= @p_1 ?v_0)) :rule symm :premises (t9.t1.t1))  ; polyeq/reflexivity.rs
(step t9.t2.t1 (cl (= ?v_0 @p_1)) :rule symm :premises (t9.t1))     ; local/congruence.rs
(step t9.t2    (cl (= (= e0 ?v_0) (= e0 @p_1))) :rule cong :premises (t9.t2.t1))
```

`strict_refl` substitutes only on the left, so the polyeq elaboration reaches the
right-substituting orientation via `symm` over a flipped `refl`; the congruence elaboration then
needs the original orientation back and adds a second `symm`, restating the first step verbatim.

The cvc5 gain (34 644, no round trips) *is* genuine global flipping — chains whose only consumers
are `trans`/`cong` — and is worth 0.26% of the DAG.

## The pass holds up, for what it is worth

`--pipeline … orientation` replaces a satisfied `symm` by its premise and reverses flipped
`trans`/`cong` conclusions (reversing `trans` premise order so the chain still reads left to
right). Validation: 351 already-elaborated proofs across all six logics and three configs re-check
(347 valid, 4 holey, 0 invalid); 138 end-to-end runs with the pass appended re-check (135 valid, 3
holey, 0 invalid; six further files fail identically *without* the pass, a pre-existing QF_LRA
parser error). Three unit tests cover the round-trip collapse, an assumption-pinned `symm` that
must survive, and a chain pinned by a resolution pivot.

Size and time on 60 veriT proofs, full pipeline plus the pass: 513 885 → 491 369 commands
(−4.38%), 93.6 → 91.8 MB, total time −6.9% — noisy, and a parsing win. Full-pipeline step deltas:
veriT −3.10%, eq_cl −4.19%, cvc5 −0.18%.

**One honesty caveat.** `Γ ▷ t ≈ u` reads as `σΓ(t) ≈ u` and is not symmetric, so flipping a step
under a substitution-carrying anchor changes what it asserts even though the syntactic
`trans`/`cong` checkers cannot tell. Textual diffing shows the pass never changes the conclusion of
any surviving step in a veriT proof — it only drops dead round-trip nodes and rewires consumers to
a node concluding the identical term, which is sound regardless of context — and every conclusion
it does reverse is in a cvc5 proof, none under a substitution anchor. Safe as measured; a
production version should make the distinction explicit rather than rely on that coincidence.

## Recommendation

1. **Land the round-trip fix at its source, not the global pass.** 99.5% of the achievable veriT
   and eq_cl gain is `symm(symm(X)) → X`, caused by the polyeq reflexivity elaboration emitting
   `symm` over a flipped `refl` (because `strict_refl` substitutes only on the left) and the
   congruence elaboration immediately flipping it back. Teaching the congruence elaborator to
   reach past a `symm` to its premise — or the reflexivity elaboration to keep both orientations
   available — removes ~175 000 steps with no new pass and no soundness argument beyond "these two
   steps conclude the same term".
2. **Do not build the global pass.** It is feasible and validated, but worth ~930 steps on veriT
   and 0.26% of the DAG on cvc5 beyond the peephole — not worth ~450 lines of elaborator carrying
   a caveat about contextual symmetry.
3. **The other 65% of veriT `symm` steps cannot be removed at this level.** They sit between a
   discharge subproof's `assume` and a `trans`/`cong`, pinned by the enclosing clause literal, and
   92.3% of those equalities also occur as proper subterms of assertion-derived terms. The lever
   is the *shape of the `eq_transitive`/`eq_congruent` reduction* — reorienting the discharge
   subproof's assumptions to match the chain and paying once in the closing clause — not a
   downstream rewrite.
4. **Keep the analysis tooling.** `carcara orientation --breakdown` runs 458 proofs in 5 s and
   answers "how much of this rule is structurally forced?", which generalizes to other questions.
5. **Two incidental findings worth their own fixes.** `Rc<ProofNode>::traverse` allocates a fresh
   visited set per call, so any analysis walking a forest root-by-root is quadratic in the shared
   subgraph — one 23 MB proof took 54 s instead of 0.76 s. And the `core` pass's degenerate
   one-link `eq_transitive` materializes its step by flipping twice, where a single one-premise
   `trans` would do.
