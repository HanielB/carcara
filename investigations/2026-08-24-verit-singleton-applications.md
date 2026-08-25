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

## Where they come from in veriT (2026-08-25)

`src/pre/simplify.c` simplifies an `and`/`or` node in three stages, each of which pushes its own
proof step:

```c
dest = simplify_neutral_proof(new_src, DAG_FALSE);   /* drop the neutral element */
...
dest = simplify_ACidem_proof(new_src);               /* drop duplicate arguments */
...
dest = simplify_or_proof(new_src);                   /* short-circuit, and arity-1 collapse */
```

The first two build their result with `DAG_new_stack(DAG_symb(src), DAGs)` and
`DAG_new(DAG_symb(src), j, PDAG)` respectively, **with no case for a single surviving argument**
(`src/pre/simp-node-proof.c:52`, `:97`). So removing the last `false` from `(or a false)` yields
`(or a)`. The third stage then has an explicit arity-1 branch that collapses `(or a)` to `a` and
emits an `or_simplify` step for it — which is the step Carcara sees.

The singleton is therefore transient *inside* veriT, but because every stage records a step, the
ill-formed intermediate is written into the proof both as a `:named` term and as the left-hand side
of the collapsing step. The corpus bears this out exactly: **1 666 singleton terms are introduced
(1 483 `or`, 183 `and`) and exactly 1 666 `and`/`or_simplify` steps collapse one** — a one-to-one
correspondence, so none of them is ever used for anything else.

The idiom for avoiding this is already in the codebase elsewhere, e.g.
`instantiation/inst-pre.c:519`: `stack_size(tmp) > 1 ? DAG_new_stack(CONNECTOR_OR, tmp) : ...`.

## The fix, applied and tested

Two lines, in `src/pre/simp-node-proof.c`:

```c
/* simplify_neutral_proof */
dest.DAG = stack_size(DAGs) == 1 ? DAG_dup(stack_get(DAGs, 0))
                                 : DAG_dup(DAG_new_stack(DAG_symb(src), DAGs));

/* simplify_ACidem_proof */
dest.DAG = j == 1 ? DAG_dup(PDAG[0]) : DAG_dup(DAG_new(DAG_symb(src), j, PDAG));
```

The driver in `simplify.c` already copes with a collapsed result: after the neutral stage it does
`if (DAG_symb(new_src) != CONNECTOR_OR) continue;`, which re-enters the loop on the new node. The
arity-1 branches of `simplify_and_proof`/`simplify_or_proof` become dead code.

Rebuilt veriT 2026.05 with the patch and regenerated the 71 affected proofs with the corpus's own
options (`--proof-with-sharing --proof-prune --proof-merge`): **71/71 still solve, and 0 singleton
applications remain**.

## One Carcara change the fix requires

Collapsing in the *first* stage changes the shape of the resulting `or_simplify` step. Where veriT
used to emit two steps

```
(= (or false B) (or B))     then     (= (or B) B)
```

it now emits one, `(= (or false B) B)`. When `B` is itself a disjunction, Carcara's
`generic_and_or_simplify` mis-read that: it takes the right-hand side to be the *list* of surviving
arguments, so `B = (or b1 b2)` was read as two survivors rather than one, and the step was rejected.
23 of the 71 regenerated proofs failed for this reason.

The checker now keeps both readings — the right-hand side as an argument list, and as a single
surviving argument — and accepts either. This is the dual of the special case it already had for a
singleton *left*-hand side (`(and (and p q r))`). With it, **63 of the 71 check**; the other 8 do
not parse in Carcara either before or after the patch, for an unrelated Int/Real sort mismatch in
veriT's QF_LRA output, and are not part of the evaluation set.

The patch, with a submission-ready header, is saved as
`investigations/patches/verit-2026.05-no-singleton-and-or.patch`.

## Recommendation

1. **veriT**: apply the two-line patch above. It is contained, it makes the emitted proofs shorter
   by 1 666 steps on this corpus, and it removes the out-of-spec terms entirely.
2. **Carcara**: the `generic_and_or_simplify` relaxation is already in, and is needed to consume
   the fixed output.
3. **Carcara** (optional, independent): normalize singleton applications of n-ary operators away
   at parse time. That would fix every downstream consumer at once and let
   `generic_and_or_simplify` drop its argument-list special cases — but it changes what the
   checker accepts, so it is a deliberate decision rather than a cleanup.
