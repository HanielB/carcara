# `rare_rewrite`: skipping the meta-rewriting sweep

**Branch:** `inv/rare-meta-skip` (commit `d4ca1284`) — **merged into `coreAlethe`**.
**Verdict:** `rare_rewrite`'s median cost per step falls from **6.6 µs to 1.9 µs**, and whole-proof
checking by **21–33%** on arithmetic proofs, with verdicts unchanged on 979 corpus proofs.

## Why it was expensive

`check_rare` instantiated the RARE rule and then ran `rewrite_meta_terms` over each instantiated
term — a full recursive walk trying ~40 meta-rules at every operator node. Those rules exist only
to normalize the n-ary/`rare-list` constructs that a `:list` parameter introduces. **16 of the 119
rules** in cvc5's `rewrites.eo` declare one, and the four most frequent rules in the corpus
declare none: `arith-elim-lt` (74 228 steps), `eq-symm` (24 285), `arith-elim-leq` (23 436),
`bool-double-not-elim` (22 590). For those the sweep was a pure no-op traversal — and it made
`rare_rewrite` the most expensive frequent rule in the corpus (median 7.96 µs, against 0.07 µs for
`refl` and 0.35 µs for `resolution`).

## The correctness argument

The sweep is *exactly* the identity on a term where no meta-rule matches anywhere: every node is
rebuilt from unchanged children, and hash consing returns the original `Rc`. So the property to
detect is "no meta-rule can match at any node".

Whether a rule can match at a node depends, besides its children, only on the node's **operator
and arity**. `MetaShapes` (in `carcara/src/rare/mod.rs`) derives those root shapes *from the rule
list itself* — `ManyEq(op, _)` admits any arity of `op`, `OperatorEq(op, ps)` admits `op` at arity
`ps.len()`, and a `VarEqual`/`Const` root would match non-operator terms and makes the analysis
give up — so the predicate cannot drift from `build_rules`. For the standard set it collapses to
"an `Op(RareList, …)`, or one of the 14 n-ary operators applied to ≤ 1 argument". The
approximation is one-sided: over-reporting costs a no-op sweep, under-reporting would falsely
reject a valid step.

What can put such a node into an *instantiated* term is exactly two things:

1. **the rule's own conclusion/premises** — `Substitution::apply` rebuilds each non-variable node
   with the same operator and the same number of arguments, never splicing, so arity is preserved
   and any node originating in the pattern keeps the pattern's shape;
2. **the substituted argument values**, which are inserted verbatim (capture-avoidance renames
   binders in the *pattern*, not inside values).

Nothing else: `pool.add` is pure hash consing with no normalization, and binder renaming only
creates `Var` nodes. So the guard is
`needs_meta_rewriting = rule_has_meta_construct ∨ any_argument_value_has_meta_construct`, and both
halves are load-bearing (verified by disabling each and watching a test fail).

The argument scan is deliberately *not* narrowed to `:list` rules: a `rare-list` reaching a rule
that declares none must be normalized, not rejected. Argument values can indeed be `rare-list`
terms — e.g. `:args ("or-not-refl" nil$ (rare-list @p_62 @p_64))` occurs in the corpus.

**Worth recording:** on today's `rewrites.eo` the naive guard "the rule declares `:list`" happens
to be correct, because the one rule whose own terms contain a meta-construct (`or-not-refl`, whose
conclusion is the singleton `(or xs)`) also declares `:list`. That is a property of the file, not
of the guard — a rule with a unary `(or x)` and no `:list` parameter would break it. The
`or-singleton` regression test pins that case.

## What was implemented

- `carcara/src/rare/mod.rs`: `MetaShapes` with `contains_redex`/`any_contains_redex`, the shapes
  of the fixed rule set cached in a `OnceLock`, and a `PtrHasher` for the traversal's visited set
  (hashing term pointers through SipHash was measurable). `rewrite_meta_terms` also returns early
  when the term has no redex, as a backstop independent of its callers.
- `carcara/src/ast/rare_rules.rs` and `carcara/src/parser/rare/mod.rs`:
  `RuleDefinition::has_meta_construct`, computed once when the rule set is parsed — the per-rule
  half belongs there, not per step. Also `TypeParameter::variable`, built once at parse time from
  the same pool and sort as its occurrences, instead of being reconstructed (string clone plus
  re-intern) on every step.
- `carcara/src/checker/rules/rare.rs`: the guard, and the substitution map moved into
  `Substitution::new` instead of cloned. The second premise loop — which re-checks that the actual
  premises are meta-normal — is skipped along with the sweep, since when no sweep is needed the
  first loop has already equated each premise with a term the shape argument shows admits no
  match.

## Measurements

Alternating runs, two each:

| proof | `rare_rewrite` median | their total | whole-proof checking |
|---|---|---|---|
| `rings_…2exp10_4vars_3ite` (20 796 steps) | 6.62 → **1.88 µs** | 264 → **51 ms** | 878 → **682 ms** (−21%) |
| `rings_…2exp6_4vars_2ite` (20 322) | 5.10 → **1.63 µs** | 243 → **48 ms** | 829 → **624 ms** (−25%) |
| `mathsat__EufLaArithmetic__hard__hard20` (6 150) | 17.32 → **2.65 µs** | 97 → **17 ms** | 265 → **178 ms** (−33%) |
| `Averest__parallel_prefix_sum…blmc004` (5 625) | 8.56 → **3.41 µs** | 78 → **21 ms** | 412 → **338 ms** (−14%) |

Where the remaining ~1.9 µs goes, by ablation on the reference file: the argument redex scan
~26 ms/run, `subst.apply` of the conclusion ~23 ms, building the substitution map ~10 ms,
everything else ~1 ms.

## Validation

- **979 distinct proofs, 0 mismatches** against a baseline binary from the branch point, comparing
  full stdout and stderr: all of `proofs/` and `elab/` for the six logics under `cvc5/`, plus the
  157 files that use one of the 16 `:list` rules. Outcomes identical on both binaries: 901 valid,
  70 holey, 7 invalid, 1 pre-existing stack overflow.
- `cargo test --release` (257 tests) green; `cargo fmt`, `cargo clippy --release --all-targets`
  and `cargo doc` clean. New tests: `rare::tests::test_meta_shapes_agree_with_rewriting` and
  `rules::rare::rare_rewrite_meta_skip_guard`, the latter with a new `or-singleton` rule.

## Left on the table

The argument scan is not memoized: the same hash-consed argument terms are rescanned at every step
that mentions them, and a cache alongside `sorts_cache`/`free_vars_cache` in the pool would mostly
erase it — that needs a new `TermPool` method implemented in `PrimitivePool`, `ContextPool` and
`LocalPool`. `Substitution::apply`'s memoization cache is pure overhead for patterns this small,
but replacing it means duplicating capture-avoiding instantiation. And the second premise loop is
redundant whenever the first one passes, not only when the sweep is skipped — but that rests on
idempotence of the sweep rather than on the shape argument, so it was kept.
