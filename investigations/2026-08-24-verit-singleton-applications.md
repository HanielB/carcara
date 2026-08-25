# veriT emits singleton applications of `and`/`or`

**Branch:** `coreAlethe`.
**Verdict:** a solver-side defect, not a limitation of RARE or of the core fragment. veriT writes
`(or x)` — a one-argument application of an n-ary connective — where the term is just `x`. The
Alethe specification does not allow such terms. **1 666 occurrences over 71 of veriT's 489 corpus
proofs**, concentrated in QF_LRA (1 275), then QF_LIA (241), UFLIA (106), QF_UF (32), UF (12);
**cvc5 emits none**.

## Where they come from

`or_simplify`/`and_simplify` remove disjuncts until one is left, and veriT writes the result as a
one-argument application rather than as the argument. From
`UFLIA/verit/simplify2__front_end_suite__javafe.reader.SrcReader.004`:

```
(! (and @p_75 @p_39 @p_40) :named @p_324)
(! (or @p_324) :named @p_326)
(step t49 (cl (= @p_326 @p_324)) :rule or_simplify)
```

The step says `(or A) ≈ A`, with `(or A)` a term of the proof.

## Why it went unnoticed

Carcara's parser accepts them, and the two `*_simplify` checkers compare *argument lists*
(`generic_and_or_simplify`), so a singleton application reads as the one-element list and the
step checks. The `and_simplify` checker even documents the neighbouring shape: "Sometimes, the
`and_simplify` and `or_simplify` rules are used on a nested application of the rule operator,
where the outer operation only has one argument, e.g. `(and (and p q r))`."

## What it cost, and what it does *not* mean

Elaborating those steps needs a derivation for links of the form `(or x) ≈ x`. No RARE rule can
state one: RARE's meta-level normalizes `(or x)` to `x` (`rare/mod.rs`: `(Or x) ~> x`), so a rule
declaring the collapse instantiates to `(= x x)` and proves reflexivity instead — pinned by the
existing test `rules::rare::rare_rewrite_meta_skip_guard`:

```
"(step t1 (cl (= p p)) :rule rare_rewrite :args (\"or-singleton\" p))": true,
"(step t1 (cl (= (or p) p)) :rule rare_rewrite :args (\"or-singleton\" p))": false,
```

An earlier version of the evaluation reported this as "two rewrites are not expressible in RARE",
which was the wrong conclusion: RARE is right, and so is its normalization. The terms are simply
not well-formed Alethe. The elaboration keeps a two-step core derivation (`or_pos`/`or_neg`, or
`and_pos`/`and_neg`) for those links purely as robustness against out-of-spec input.

## Recommendation

1. **veriT**: emit `x`, not `(or x)`.
2. **Carcara** (optional, independent): normalize singleton applications of n-ary operators away
   at parse time. That would fix every downstream consumer at once and let
   `generic_and_or_simplify` drop its argument-list special cases — but it changes what the
   checker accepts, so it is a deliberate decision rather than a cleanup.
