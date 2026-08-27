# Should `evaluate` be a core primitive? What the corpus says

**Branch:** `coreAlethe` (measurement only, no code change).
**Question:** a proposed reclassification would put `poly_simp` and `aci_simp` at *expensive*
(kept, not eliminated) and ask whether `evaluate` should be *core* rather than *reducible*. The
justification offered for making it core: eliminating `evaluate` when `poly_simp`/`aci_simp` are
not available as targets would be terrible.
**Verdict:** the premise does not hold. Eliminating `evaluate` without `poly_simp` costs about
**+1% of steps and +1% of checking time**, and `aci_simp` is not involved at all. If `evaluate`
becomes core, the honest argument is the one for the other computational schemas (a concise
per-operator statement, and a cheap check) — not the cost of its reduction. Its price is
**585 lines of trusted code, the largest single computational primitive in the core**.

The same measurements do support classifying `aci_simp` as *expensive* — the ACI reduction is
where veriT's post-elaboration checking time goes — and show that demoting `poly_simp` would cost
steps rather than reach, since every use the corpus exercises is linear.

## What `evaluate`'s reduction actually consumes

`core-no-rare` keeps `evaluate`; `core-taut` reduces it. The corpus-wide delta between the two
configurations is exactly the reduction's cost (`results/rules.csv`):

| | cvc5 | veriT |
|---|---:|---:|
| `evaluate` instances removed | 25 947 | 181 |
| total steps | +27 209 (+0.26%) | +1 070 (+0.02%) |
| of which `poly_simp` | +21 171 | +8 |
| of which `resolution` | +13 451 | +535 |
| of which `la_generic` | +4 462 | +60 |
| of which `true`/`false` | +6 659 | +295 |
| of which `equiv_neg1`/`equiv_neg2` | +6 060 | +181 |
| of which **`aci_simp`** | **0** | **0** |

So the recipe averages 1.05 net new steps per instance, and its only non-clausal targets are
`poly_simp` (0.82 per instance — the ground *numeric* path) and `la_generic` (0.17 — constant
relational atoms). `aci_simp` never appears: ACI normalization plays no part in evaluation.

## Without `poly_simp`: six core steps instead of one

Each `poly_simp` step the recipe emits proves a ground identity `(= t v)`. The core proves the
same thing without it, through the antisymmetry axiom:

```
(step s1 (cl (<= t v)) :rule la_generic :args (1))
(step s2 (cl (<= v t)) :rule la_generic :args (1))
(step s3 (cl (or (= t v) (not (<= t v)) (not (<= v t)))) :rule la_disequality)
(step s4 (cl (not (or …)) (= t v) (not (<= t v)) (not (<= v t))) :rule or_pos)
(step s5 (cl (= t v) (not (<= t v)) (not (<= v t))) :rule resolution :premises (s4 s3) …)
(step s6 (cl (= t v)) :rule resolution :premises (s5 s1 s2) …)
```

Six steps for one, checked at elaborated granularity. **Reach**: on the sampled instances the two
routes agree exactly.

- 10/10 numeric `evaluate` instances extracted from cvc5 proofs (`parse -v`, sharing expanded):
  both routes prove all of them.
- 13 synthetic ground identities covering the operator space: `poly_simp` proves 8, the
  `la_generic` pair proves the *same* 8. Both fail on `(* 2 3 4)` (n-ary product), `(to_int 3.7)`,
  `(div 7 2)`, `(mod 7 2)`, `(abs (- 5))` — so dropping `poly_simp` opens no new gap. (`to_int`
  has its own route through the `to_int_lower`/`to_int_upper` axioms; integer `div`/`mod` is the
  documented gap either way.)
- 75/75 real `poly_simp` conclusions sampled from five cvc5 QF_LIA/QF_LRA/QF_UFLIA proofs are
  provable by the `la_generic` pair, because ground and linear identities are all this corpus
  exercises.

**Cost of the poly_simp-free route**: +5 steps on each of the 21 171 numeric instances =
**+105 855 steps, ~+1.0%** of cvc5's 10.56 M-step elaborated corpus, and about +3.4 µs per
instance ≈ **+0.07 s on 7.6 s of checking (+0.9%)**. For comparison, eliminating `evaluate`
*with* `poly_simp` costs +0.26% of steps and is checking-neutral: 7.663 s (`core-no-rare`) vs
7.561 s (`core-taut`) over 486 proofs, a 1.3% difference that is inside run-to-run noise.

## Where `poly_simp` is genuinely irreplaceable

The `la_generic` pair only reaches *linear* identities. It fails, while `poly_simp` succeeds, on:

```
(= (* x y) (* y x))
(= (* (+ x 1) (+ x 1)) (+ (* x x) (* 2 x) 1))
(= (* 2 x 3) (* 6 x))
(= (* a (- c b)) (- (* a c) (* a b)))        ; distributivity
```

The last one is the step the `la_mult_pos`/`la_mult_neg` recipe hands to `poly_simp`, over
**116 615 cvc5 instances** (36 620 + 79 995) — the reduction of

```
(step t25 (cl (=> (and (< -1 0) (>= TaskOnDisk 24)) (<= (* -1 TaskOnDisk) (* -1 24))))
    :rule la_mult_neg)
```

emits exactly

```
(step t25.c3 (cl (= (* (- -1) (- TaskOnDisk 24)) (- (* -1 24) (* -1 TaskOnDisk))))
    :rule poly_simp)
```

**But on this corpus that identity is linear**, because every `la_mult_*` multiplier cvc5 emits
is a *numeral*: all 40 `poly_simp` identities the `la_mult_*` reductions produce in two
arithmetic-heavy proofs are provable by the `la_generic` bound pair, like every other sampled
identity. So `poly_simp` is not load-bearing here either — it becomes so only for a *symbolic*
multiplier, which the specification allows (`t1` is an arbitrary term) and this corpus never
exercises.

If `poly_simp` did leave the core, the tautology that would have to replace it for `la_mult_*` is
distributivity over subtraction, stated premise-free in the style of `mult_pos`:

```
(cl (= (* x (- y z)) (- (* x y) (* x z))))
```

`la_mult_neg` additionally negates the multiplier, so it needs either the product-negation rule
`(cl (= (* (- x) y) (- (* x y))))` — after which the remaining rearrangement is linear — or a
`mult_neg` companion axiom `(cl ¬(< x 0) ¬(> y 0) (< (* x y) 0))`, which removes the `m → -m`
bridge and lets the negative case use the same distributivity instance as the positive one.

## The checking-cost picture

Per-rule checking time in the elaborated proofs (`results/*-elab-steps.csv`):

| | steps | share of steps | share of check time | mean |
|---|---:|---:|---:|---:|
| veriT `aci_simp` | 301 970 | 5.2% | **46.0%** (7.22 s of 15.69 s) | 23.9 µs |
| veriT `la_generic` | 138 126 | 2.4% | 5.6% | 6.4 µs |
| cvc5 `poly_simp` | 52 305 | 0.56% | 11.2% | 12.0 µs |
| cvc5 `aci_simp` | 55 699 | 0.60% | 9.6% | 9.7 µs |
| cvc5 `evaluate` | 26 010 | 0.28% | 1.2% | 2.6 µs |

And in the *original* proofs: `evaluate` 0.95 µs/step (248 964 instances, 0.236 s), `poly_simp`
6.27 µs, `aci_simp` 8.83 µs, `ac_simp` **54.3 µs** (47 745 instances, 2.591 s).

Two readings follow.

**`aci_simp` as expensive — the strongest case in the data.** veriT emits no `aci_simp` at all;
the core pass *creates* 301 970 of them, from `ac_simp` (47 745), `and_simplify` (26 764),
`or_simplify` (1 841), `shuffle` and `nary_elim`. Checking those sources in the original proof
costs 2.61 s; checking the `aci_simp` steps they become costs **7.22 s** — the reduction makes
this reasoning 2.8× more expensive to check and 6× more numerous, which is precisely the
"check-power upgrade" that the *expensive* level exists to name. It is also why veriT's
post-elaboration checking time is dominated by a rule its proofs never contained.

**`poly_simp` as expensive — defensible, and cheaper than it looks on this corpus.** 12 µs/step,
11% of cvc5's checking time for 0.56% of its steps, and its own elimination is the aggressive
exemplar (RARE chains, with the Boolean-ANF blowup documented in the algebraic-hierarchy note).
Every one of its uses that the corpus exercises — ground evaluation, `poly_simp_rel`, `la_mult_*`
— is linear and has a core route through `la_generic` + `la_disequality` at about six steps a
piece. What demoting it would cost is therefore *steps*, plus one new tautology (distributivity)
to keep `la_mult_*` reducible for symbolic multipliers.

**`sko_ex`** already sits at *expensive* on a measured argument
(`investigations/2026-08-18-sko-ex-cost.md`): corpus cost only +0.71% of steps, but an ~8× local
blowup per instance.

## What this says about `evaluate`

Against making it core:

- Its reduction is cheap with `poly_simp` (+0.26% steps) and still cheap without it (+1.0%), so
  the cost criterion does not protect it.
- It is **585 lines of trusted code** (a 5-line rule plus the 580-line `ast/evaluate.rs`
  interpreter — rational arithmetic, every comparison operator, the Boolean connectives, `ite`,
  the division conventions), against 149 for `poly_simp` and 144 for `aci_simp`. Promoting
  `evaluate` while demoting those two would *raise* the trusted base by ~290 lines net, and
  `evaluate` is the largest single item the core could shed.
- 89.6% of its instances are duplicates that the `hoist` pass removes anyway (248 964 → 26 010),
  so the rule's frequency overstates how much reasoning it actually carries.

For making it core:

- Per-step it is the cheapest of the computational primitives to check (0.95 µs in the originals,
  against 6.3 for `poly_simp` and 8.8 for `aci_simp`), so keeping it is close to free for a
  checker that implements it.
- The logical argument stands on its own: constant evaluation has a concise statement per
  SMT-LIB operator, which is the same justification the core already accepts for `bitblast_*`
  and `distinct_elim` — definitional computational schemas. That argument is about what belongs
  in a core, not about what its elimination costs.

The two are not in tension: the classification can make `evaluate` core on the definitional
argument while recording that its reduction is cheap and its TCB cost is the largest — which is
what the current text already says ("the first candidate to demote if the TCB is ever the binding
constraint"). What the data does *not* support is justifying the promotion by the cost of
eliminating it.

## Method

- Corpus deltas from `results/rules.csv` (configurations `*-norare` vs `*-taut`), per-rule
  checking times from `results/*-elab-steps.csv` and `results/*-orig-steps.csv`, totals from
  `results/*-runs.csv`.
- Instances extracted with `carcara parse -v` (sharing expanded) and replayed as one-step probe
  proofs against their own problem file; scripts in the session scratchpad
  (`test-nopoly.py`, `test-poly-la.py`).
- Line counts from the TCB table in `docs/src/core.md` ("The trusted computing base, measured").
