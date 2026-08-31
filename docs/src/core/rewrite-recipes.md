# Recipes for eliminating the RARE rewrites

The [previous chapter](./rare-rules.md) catalogues the RARE rules the rewrite *routes* need — the
regime that keeps `rare_rewrite` as the core's rewrite primitive and expresses each `*_simplify`
step as a chain of RARE lemmas. This chapter is the other regime: **`rare_rewrite` is not in the
core at all**, and every rewrite has to be *derived*. It gives the derivation — the recipe — for
each rewrite the evaluation corpus exercises, whether it comes from `rewrites.eo` or from a
`*_simplify` trace.

All of these are implemented (`carcara/src/elaborator/core/rewrites/recipes.rs`, dispatched by
`rewrite_lemma`) and run by the `core-taut` pass. Every recipe concludes the unit clause
`(cl (= lhs rhs))` for one rewrite instance; the chain machinery glues the links with `trans` and
lifts an inner rewrite to the root with `cong`.

**Measured cost.** 176 453 instances of 53 distinct rewrites over the corpus, 1 571 972 core steps,
**mean 8.9 steps per rewrite**; per-rewrite figures appear in each section below and in full in
`investigations/2026-08-25-recipe-cost-per-rewrite.md`. Only one recipe's cost grows with its
instance.

The step counts below are *measured* for the rewrites the corpus exercises. Twenty of the recipes
have no corpus instance and their counts are the template size read off the recipe rather than an
observation: `and-flatten`, `or-flatten`, `and-dup-elim`, `or-dup-elim`, `arith-elim-int-lt`
(and `-int-gt`), `arith-leq-ite-lift`, `bool-eq-nrefl`, `bool-not-eq-false`, `equiv-true-l`,
`equiv-false-l`, `equiv-neg-l`, `implies-refl`, `implies-neg` (and `-l`/`-r`),
`ite-then-lookahead`, `ite-else-lookahead`, `ite-then-false`, `ite-else-true`,
`ite-then-true-else-false`, `ite-then-false-else-true`. They are implemented and unit-tested, not
exercised at scale.

## `evaluate`: the structural recursion

`evaluate` is not a rewrite rule but a *computational primitive* — its check is the 580-line
interpreter in `ast/evaluate.rs`. The `core-taut` regime removes it all the same, and this is where
that happens, so it belongs here even though it is not a RARE rule. Two entry points reach the same
code (`core/rewrites/ground.rs`):

- an `evaluate` **step of the input**, via `elaborate_evaluate`;
- a constant-folding **link of a `*_simplify` trace**, which the checkers label `"evaluate"` rather
  than with a RARE rule name; `core_lemma` routes that label here instead of to `rewrite_lemma`.

`evaluation(term, value)` first re-runs the checker's own evaluator and refuses if the two disagree,
then splits on what the value is:

| the value is | derivation |
|---|---|
| `true` | derive the literal `(cl term)` by the recursion below, then `bridge_true` |
| `false` | derive `(cl ¬term)`, then `bridge_false` |
| a number | the conclusion is a ring identity: **one `poly_simp` step** |
| a branch of a term-`ite` | the selection axiom picks the branch, the branch's own evaluation closes by `trans` |

The Boolean case is the recursion, `literal(t, want)`, deriving the unit clause `(cl t)` or
`(cl ¬t)` for a ground `t`. It is a *guided descent*: at each node it asks the evaluator what the
subterms are worth and emits only the CNF axiom instances that case needs.

| shape | derivation |
|---|---|
| `true` / `false` | the `true` / `false` axiom |
| `¬u` | recurse on `u` with the polarity flipped; for the negative direction, `nn_intro` + one resolution |
| `(and …)` true | `and_neg` resolved against each conjunct's literal |
| `(and …)` false | `and_pos` at the first false conjunct |
| `(or …)`, `(=>)`, `(xor)`, `(ite)` | dually, by the corresponding `*_pos`/`*_neg` axioms at the deciding argument |
| `(= x y)` at `Bool` | the four `equiv_pos`/`equiv_neg` cases, by the two sides' truth values |
| `(= x y)` numeric, true | a ring identity: one `poly_simp` |
| `(= x y)` numeric, false | one `la_generic` unit clause |
| `<`, `≤`, `>`, `≥` | one `la_generic` unit clause, positive or negated |

**Ground `to_int` is folded first.** Both the ring normalization and `la_generic` treat
`(to_int c)` as an opaque atom, so a term mixing it with arithmetic — cvc5 emits
`(= (+ (to_int -3/2) 1) -1)` — is not a ring identity until the application is gone. `fold_to_int`
replaces every such subterm by its value, carrying the replacement through the surrounding term by
`cong`, and the value itself comes from the two floor axioms:

```
(step f1 (cl (<= (to_real (to_int c)) c)))         :rule to_int_lower
(step f2 (cl (< c (+ (to_real (to_int c)) 1))))    :rule to_int_upper
(step f3 (cl ¬f1 (<= (to_int c) k)))               :rule la_generic   ; k = ⌊c⌋
(step f4 (cl ¬f2 (<= k (to_int c))))               :rule la_generic
(step f5 (cl (or (= (to_int c) k) ¬… ¬…)))         :rule la_disequality
… or + resolutions …                               → (cl (= (to_int c) k))
```

This is the only place the core needs to know what `to_int` *is*, and it needs no evaluator to do
it: the two bounds pin the value to a half-open unit interval and `la_generic`'s integer
strengthening picks the integer out of it.

**Cost.** Measured over the corpus in the `core-taut` regime, `evaluate` reduces at **2.09 new
commands per instance** — 26 099 instances, 54 427 emitted, net +28 328 — the bridge plus a
handful of axiom instances, and after the sharing pass has folded the repeated ones. (veriT emits
no `evaluate` at all, so the whole figure is cvc5's.) `div` and `mod` at a symbolic divisor are the
one shape with no recipe; they need the `div_intro` definitional axioms and do not occur in this
corpus.

## The four shared closures

Almost every recipe below is one of four shapes, so they are stated once.

### `bridge_true` / `bridge_false` — from a literal to an equality with a constant

A rewrite whose right-hand side is `true` or `false` is proved by deriving the *literal* and then
bridging. From `(cl A)` to `(cl (= A true))`:

```
(step b1 (cl (= A true) ¬A ¬true))  :rule equiv_neg1
(step b2 (cl true))                 :rule true
(step b3 (cl (= A true) ¬A))        :rule resolution :premises (b1 b2)
(step b4 (cl (= A true)))           :rule resolution :premises (b3 <A>)
```

and dually with `equiv_neg2` + the `false` axiom for `(cl (= A false))` from `(cl ¬A)`. **4 steps.**

### `equiv_intro` — from two directions to an equivalence

Given `right = (cl ¬a b)` and `left = (cl a ¬b)`:

```
(step e1 (cl (= a b) a b))    :rule equiv_neg2
(step e2 (cl (= a b) ¬a ¬b))  :rule equiv_neg1
(step e3 (cl (= a b) b))      :rule resolution :premises (e1 right)
(step e4 (cl (= a b) ¬b))     :rule resolution :premises (e2 left)
(step e5 (cl (= a b) (= a b))):rule resolution :premises (e3 e4)
(step e6 (cl (= a b)))        :rule contraction :premises (e5)
```

**6 steps.** `equiv_collapsed` is the variant for literals already in collapsed-negation form,
which is what `la_generic` produces.

### Excluded middle and double negation

`em(x) = (cl ¬x x)` is `refl` + `equiv_pos2` + one resolution (**3 steps**); `nn_intro(x)` is `em`
at `¬x`, giving `(cl ¬x ¬¬x)`. The `not_not` axiom `(cl ¬¬¬p p)` is what discharges a `¬¬` literal
that `and_neg` produces on a negated conjunct. These are the reason the Boolean recipes cost 10–16
steps rather than 6.

### `atom_equiv` — an equivalence between two arithmetic atoms

One `la_generic` Farkas certificate per direction, closed by `equiv_collapsed`:

```
(step a1 (cl ¬̃A B)) :rule la_generic :args (…)
(step a2 (cl A ¬̃B)) :rule la_generic :args (…)
… equiv_collapsed …
```

The coefficients are searched over a few sign choices and **validated by `la_generic`'s own checker
before emission**, so a shape the recipe did not anticipate fails the reduction rather than
producing a step that does not check. **8 steps** (7 when one direction collapses).

## Arithmetic atoms — `atom_equiv`

| rewrite | statement | steps |
|---|---|---:|
| `arith-elim-lt` | `(< t s) ≈ ¬(≥ t s)` | 8 |
| `arith-elim-gt` | `(> t s) ≈ ¬(≤ t s)` | 8 |
| `arith-elim-leq` | `(≤ t s) ≈ ¬(> t s)` | 7 |
| `arith-elim-int-lt` / `-int-gt` | the integer forms | 8 |
| `arith-leq-norm` | `(≤ t s) ≈ ¬(≥ t (+ s 1))` | 8 |
| `arith-geq-tighten` | `¬(≥ t s) ≈ (≥ s (+ t 1))` | 7 |
| `arith-int-geq-tighten` | `(≥ (to_real t) c) ≈ (≥ t ⌈c⌉)` | 7 |
| `arith-geq-norm1-int` / `-real` | `(≥ t s) ≈ (≥ (- t s) 0)` | 7 |
| `comp-lt-elim`, `comp-gt-elim`, `comp-geq-flip` | the `comp_simplify` orientations | 7–8 |

Each is one Farkas certificate per direction: the negations of the two atoms are the same linear
constraint up to sign and a unit shift, so the sum is contradictory with coefficients `±1`. The
*integer* variants need nothing extra — `la_generic`'s strengthening does the rounding, once it is
correctly gated on the row being integer-valued.

**`comp-lt-irrefl`** (`(< t t) ≈ ⊥`) and **`comp-leq-refl`** (`(≤ t t) ≈ ⊤`) are a single
`la_generic` unit clause plus a bridge: **5 steps**.

## Arithmetic equalities

**`arith-eq-elim-int` / `arith-eq-elim-real`** — `(= t s) ≈ (and (≥ t s) (≤ t s))`, **8 steps**:
`la_rw_eq` states exactly this equality as a core axiom, so the recipe is a rename plus the
`and`-orientation glue.

**`arith-int-eq-conflict`** — `(= (to_real t) c) ≈ ⊥` for integer-valued `t` and non-integer `c`,
**12 steps**. No rounding axiom is needed:

```
(step c1 (cl (= (= t c) (and (≤ t c) (≤ c t)))))  :rule la_rw_eq
(step c2 (cl ¬(= t c) (and …)))                   :rule equiv1 :premises (c1)
(step c3 (cl ¬(and …) (≤ t c)))                   :rule and_pos :args (0)
(step c4 (cl ¬(and …) (≤ c t)))                   :rule and_pos :args (1)
(step c5 (cl ¬(≤ t c) ¬(≤ c t)))                  :rule la_generic :args (1 1)
… resolutions …                                    → (cl ¬(= t c))
… bridge_false …
```

`c5` is where the integrality lives: an integer cannot sit strictly between two consecutive
integers, which the strengthening knows.

**`arith-geq-ite-lift`, `arith-leq-ite-lift`, `eq-ite-lift`** — `(⋈ (ite C t s) r) ≈ (ite C (⋈ t r)
(⋈ s r))`, **11 steps**: a case split on `C` using the `ite_pos`/`ite_neg` axioms on both sides.

## Equality and the `ite` term axioms

| rewrite | statement | recipe | steps |
|---|---|---|---:|
| `eq-refl` | `(= t t) ≈ ⊤` | `refl` + `bridge_true` | 5 |
| `eq-symm` | `(= t s) ≈ (= s t)` | two `symm` directions + `equiv_intro` | 8 |
| `ite-true-cond` | `(ite ⊤ x y) ≈ x` | one `ite_then_intro` + the `true` axiom | **3** |
| `ite-false-cond` | `(ite ⊥ x y) ≈ y` | one `ite_else_intro` + the `false` axiom | **3** |
| `ite-eq-branch` | `(ite c x x) ≈ x` | both selection axioms + `em(c)` | **3** |
| `ite-eq` | `(ite C (I ≈ t₁) (I ≈ t₂)) ≈ ⊤` where `I = (ite C t₁ t₂)` | the two selection axioms, case split on `C` | 11 |
| `ite-not-cond` | `(ite ¬c x y) ≈ (ite c y x)` | four selection-axiom instances crossed | 12 |
| `ite-then-lookahead`, `ite-else-lookahead` | `(ite c (ite c x y) z) ≈ (ite c x z)` | selection axioms on the nested `ite` | 8 |
| `ite-then-true`, `ite-else-false`, `ite-then-false`, `ite-else-true` | e.g. `(ite c ⊤ p) ≈ (or c p)` | selection axioms + the `or`/`and` axioms | 18–19 |
| `ite-then-true-else-false` | `(ite p ⊤ ⊥) ≈ p` | selection axioms + both constants | 8 |
| `ite-then-false-else-true` | `(ite p ⊥ ⊤) ≈ ¬p` | ditto, with `not_not` | 8 |

The three-step `ite` recipes are the **term-`ite` selection axioms** `ite_then_intro` /
`ite_else_intro` (`▷ ¬c, (ite c t s) ≈ t` and `▷ c, (ite c t s) ≈ s`) doing exactly the job they
were proposed for: they are the only core rules that characterize `ite` at a non-Boolean sort.

## Boolean connectives

All of these follow the same plan: derive `(cl ¬lhs rhs)` and `(cl lhs ¬rhs)` from the CNF axioms of
the two sides, then `equiv_intro`. They differ only in which axioms and how many double-negation
bridges are needed.

| rewrite | statement | steps |
|---|---|---:|
| `bool-double-not-elim` | `¬¬p ≈ p` | 10 |
| `bool-eq-true`, `equiv-true-l` | `(= p ⊤) ≈ p` | 12 |
| `bool-eq-false`, `equiv-false-l` | `(= p ⊥) ≈ ¬p` | 12 |
| `bool-eq-nrefl`, `equiv-neg-l` | `(= p ¬p) ≈ ⊥` | 8 |
| `bool-not-eq-false` | `¬(= p ⊥) ≈ p` | 8 |
| `equiv-neg-both` | `(= ¬a ¬b) ≈ (= a b)` | 8 |
| `bool-impl-elim` | `(=> t s) ≈ (or ¬t s)` | 16 |
| `bool-impl-true1/2`, `bool-impl-false1/2` | the constant implications | 7–10 |
| `implies-refl` | `(=> p p) ≈ ⊤` | 8 |
| `implies-neg`, `implies-neg-l`, `implies-neg-r` | the negated implications | 8 |
| `implies-contra` | `(=> ¬a ¬b) ≈ (=> b a)` | 8 |
| `bool-implies-peirce` | `(=> (=> a b) b) ≈ (or a b)` | 8 |
| `bool-implies-uncurry` | `(=> a (=> b c)) ≈ (=> (and a b) c)` | 8 |
| `bool-and-mp-l/r` | `(and a (=> a b)) ≈ (and a b)` | 8 |
| `bool-implies-de-morgan` | `¬(=> p q) ≈ (and p ¬q)` | 8 |
| `bool-or-de-morgan` | `¬(or x rest…) ≈ (and ¬x ¬(or rest…))` | 8 |
| `bool-and-de-morgan` | `¬(and x rest…) ≈ (or ¬x ¬(and rest…))` | 8 |
| `bool-implies-or-distrib` | `(=> (or y rest…) z) ≈ (and (=> y z) (=> (or rest…) z))` | 8 |
| `bool-or-and-distrib` | `(or (and y rest…) z zs…) ≈ (and (or y z zs…) (or (and rest…) z zs…))` | 8 |

**Two recurring traps**, both worth naming because both produced bugs:

1. `and_neg` on a conjunct whose argument is `¬a` carries the literal `¬¬a`, whose complement is
   `¬¬¬a` — *not* `¬a`. The `not_not` axiom is what discharges it. Reaching for `nn_intro` instead
   gives a clause that looks right and does not resolve.
2. When a `cong`-style recipe cites the same premise for two argument pairs, resolution's **set
   semantics** removes every copy of the literal at the first resolution; the second has no pivot.
   A repeated premise must be skipped, not resolved twice.

## n-ary structure

| rewrite | statement | recipe | steps |
|---|---|---|---:|
| `and-true-elim`, `or-false-elim` | `(and xs ⊤ ys) ≈ (and xs ys)` | one `and_pos` per surviving conjunct + `and_neg` on the result; the neutral element discharged by its constant axiom | 8 / 18 |
| `and-dup-elim`, `or-dup-elim` | remove one repeated argument | ditto, with the duplicate resolved once (set semantics) | 8 |
| `and-flatten`, `or-flatten` | `(op (op args…)) ≈ (op args…)` | one positive and one negative axiom close the equivalence | 8 |
| `and-false` | `(and xs ⊥ ys) ≈ ⊥` | `and_pos` at the constant + `bridge_false` | 7 |
| `or-true` | `(or xs ⊤ ys) ≈ ⊤` | `or_pos` at the constant + `bridge_true` | 7 |
| `bool-and-conf`, `bool-and-conf2` | `(and xs w ys ¬w zs) ≈ ⊥` | `and_pos` at the complementary pair + `bridge_false` | 7 |
| `bool-or-taut`, `bool-or-taut2` | `(or xs w ys ¬w zs) ≈ ⊤` | dual | 7 |
| **`or-not-refl`** | `(or ¬(t ≈ t) xs…) ≈ (or xs…)` | `refl` kills the reflexive disequality; the surviving disjuncts are carried past one `or_neg`+resolution each | **8–32** |
| `distinct-false` | `(distinct xs t ys t zs) ≈ ⊥` | `distinct_elim` as the definitional rule + `refl` on the repeated element + CNF axioms | 11 |

**`or-not-refl` is the one recipe whose cost grows with the instance**, being linear in the number
of disjuncts it carries past. It fires 50 times in the whole corpus. If any rewrite were to be kept
as a rule on cost grounds, it would be this one — and on this evidence it does not earn it.

## What the catalogue shows

- **No rewrite is expensive in the tier's sense.** The spread is 3 to 32 steps, against the ~35
  steps *per binding* plus an anchor that `sko_ex` costs. Every recipe here is constant-size except
  `or-not-refl`.
- **The total is frequency, not recipe size.** `bool-eq-false` (262 k steps), `bool-impl-false1`
  (242 k), `bool-double-not-elim` (215 k) and `eq-symm` (187 k) dominate, and all four are
  constant-cost templates that simply fire tens of thousands of times.
- **The `*_simplify` chains are short**: 2.3 links on average, so the trace-length multiplication
  the aggressive tier worries about does not materialize.
- **Four axioms carry the whole catalogue** beyond the CNF base: the term-`ite` selection pair
  (`ite_then_intro`/`ite_else_intro`), `la_rw_eq` and `la_disequality` for the arithmetic
  equalities, `distinct_elim` for `distinct`, and the `to_int` floor pair for the rounding rewrites.
  Nothing else was needed to bring the rewrite residue to zero for both producers.
