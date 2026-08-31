# Carcara performance on the alethe-bv corpus: parsing, rare_rewrite, ac_simp

**Date:** 2026-08-31.
**Context:** follow-up to [2026-08-30-alethe-bv-eval.md](2026-08-30-alethe-bv-eval.md).
The cluster run (28,500 unsat QF_BV+QF_UFBV; cvc5 600s, carcara 1200s) finished
with 24,204 valid / 0 holey / 0 proof rejections. This note localizes where
carcara's time goes and what to do about it. Profiles: callgrind on three
representative benchmarks; corpus numbers from the run's `--stats` output.

## Where the time goes

Over the 24,204 valid checks: **parsing 147,391s (78.8%), checking 39,603s**.
Within checking, rule totals (count x mean): rare_rewrite 29,169s (75%),
resolution 3,871s, ac_simp 2,981s, evaluate 1,890s, poly_simp 376s. The new BV
rules are negligible in aggregate (all bitblast steps together < 70s;
absorb/bv_repeat_elim free).

## Parsing (the dominant cost) — two distinct problems

**1. Quadratic let expansion (the pathological tail).** With
`--expand-let-bindings`, `parse_let_term` expands each let by running
`Substitution::apply` over the already-expanded body. On problems with deeply
nested lets the cost is quadratic in nesting depth x expanded-DAG size:

- sage/app11/bench_17: 2,886 nested lets in a 1.2MB assert -> **61.7s to parse
  a 1.7MB proof, 6ms to check it** (~28KB/s). Callgrind: `parse_problem` 94%
  inclusive, of which `parse_let_term -> Substitution::apply` 91.8%.
- Sage2/bench_3507: 8,258 nested lets — its 1200s cluster "check timeout"
  (20MB proof) is really this, in parsing. bench_4827 is the same shape.
- Counter-example: bench_11381 has 47k *shallow* lets and parses in 0.4s;
  float/e3.c (no lets, similar proof size to bench_17) parses at 48MB/s.

*Fix:* expand lets environment-style during parsing — bind the let variable in
the parser's scope table and resolve occurrences to the bound `Rc<Term>` while
parsing the body. No substitution pass at all, linear, equivalent under
hash-consing. Alternatives that also help: port the coreAlethe substitution
commits
([7728a9f7](https://github.com/HanielB/carcara/commit/7728a9f7af1b177543e0d09656e7557fa137ecc5)
"Improve performance of substitutions",
[63f9e344](https://github.com/HanielB/carcara/commit/63f9e34450b68d8aa4394418aeb24dc02dae46c4)
"Defer the invalidation of substitution application caches"), and swap the
substitution cache's default SipHash for rapidhash (~18% of the pathological
profile is SipHash).

**2. Lexer throughput (the bulk cost).** On a normal 20MB proof parse,
`Lexer::next_token` is 44.6% inclusive of the whole run: `current()` clones the
`Chars` iterator on every peek (each character decoded twice),
`read_chars_while` builds every token `String` char by char, ~20% of the
profile is malloc/free. *Fix:* byte-slice cursor with zero-copy token slices
(`&source[start..end]`), a byte classification table for
`is_symbol_character`, and String allocation only at storage points. The
corpus produced 242GB of proofs; at the observed ~1.6MB/s average, lexer +
allocator work is most of the 147k s.

(Related, not this corpus's bottleneck: coreAlethe
[b6d0beb9](https://github.com/HanielB/carcara/commit/b6d0beb9c6fdb5529b84221e50872f365655c180)
makes HashMapStack lookups O(1) in subproof nesting depth — BV proofs have no
anchors, but the port is worthwhile; note wt-diff's version diverged to
RapidHashMap.)

## rare_rewrite (75% of rule time)

Callgrind on jain_6_true.c.21 (3,481 rare steps, ~965µs/step locally, check
essentially all rare_rewrite): **~60% of the entire check run is the
meta-rewrite matching machinery** — `match_meta_terms` 29.2% (self),
`check_rewrites` and its inlined map/alloc work ~30%, SipHash ~5%. For every
node visited, `check_rewrites` linearly tries all ~40 meta-rules, allocating a
fresh `IndexMap` (SipHash `RandomState`, thread-local lazy init visible in the
profile) per attempted rule, and `match_meta_terms` allocates a `String` key
per variable binding.

Fixes, in expected-impact order:
1. **Dispatch on the LHS root operator**: index the meta-rules by `Operator`;
   most nodes match nothing and should cost one branch, not 40 match attempts.
2. **No allocation until a rule matches**: the rules bind at most a couple of
   variables — a `SmallVec<(&'static str, Trace)>` replaces the per-attempt
   `IndexMap` and the String keys.
3. **Reuse the RewriteContext cache** across the premises and conclusion of one
   `check_rare` call (it is currently rebuilt per `rewrite_meta_terms` call),
   and ideally across steps (sound: terms are hash-consed, rewriting is pure).
4. `check_rare` rewrites every premise **twice**: the first loop compares the
   premise against the normalized instantiated rule premise; the second loop
   re-normalizes the proof premise and requires it to be a fixpoint. If the
   first comparison passed, the premise equals a normal form, so the second
   loop looks redundant — verify on the corpus, then drop it.
5. Done (ported from coreAlethe
   [61c65719](https://github.com/HanielB/carcara/commit/61c65719ab34db875981384a3f47fe016cf53c6c)):
   build the meta-rule set once behind
   a OnceLock. Measured no median change (it fixed a first-step timing
   outlier), kept for merge parity.

## ac_simp (100µs/step median, 3.3M steps)

`apply_ac_simp` re-traverses the conclusion's whole DAG with a cache that
lives only for the one step. BV proofs apply it repeatedly to overlapping
giant and/or terms. *Fix:* checker-lifetime memo (sound: hash-consed terms,
pure function). Same recipe applies to `aci_simp`.

## poly_simp (worst-case outlier)

`Polynomial::add_term` deliberately traverses without a cache (each occurrence
carries a different coefficient), which is exponential on DAG-shared terms:
Sage2/bench_11381 has a single poly_simp step of **8.4s** (203ms mean, 867ms
std). *Fix:* memoize node -> Polynomial (computed with coefficient 1) and
scale/merge per occurrence.

## Also fixed in this pass

- Huge indexed-op arguments: `assert_indexed_op_args_value` range-checked
  through `Integer::to_usize()`, so `(_ bvN w)` with N >= 2^64 was rejected
  ("expected argument value to be greater than at least 0..."). Now compared as
  rug Integers (`Range::contains_integer`). Recovers 7 of the 9 corpus parse
  errors (float/e3.c, qurt.c.{5,10,15}, smulov3bw0128, two Sydr predicates);
  e3.c verified end-to-end valid. Example kept in
  `~/exp/results/alethe-bv/all-bv/examples/huge-indexed-op-args/`.
- The remaining 2 errors are the non-standard `choice` binder (out of scope for
  now, per Haniel).
- `~/exp/alethe-lag/rule-boxplots.py` and `~/exp/alethe-bv/rule-boxplots.py`:
  `--stats` "by rule" runs names longer than the column into the value with no
  space; the old regex silently dropped every `bv_bitblast_step_*` row. Both
  scripts now use `^    (.+?)\s*([\d.]+)(unit) ± `.

## Round-2 outcome (2026-08-31, job all-bv2)

The fixes above (coreAlethe-upstream merge, environment-style let expansion,
memoized poly_simp, lexer token slicing, huge indexed-op arguments) plus the
cvc5 change (Boolean ABSORB -> dedicated `absorb` rule, option
`proof-alethe-absorb`, default on; cvc5 alethebv@33a825c5fe, carcara
bv-fixes@00670e05) were re-run over the 24,218 benchmarks round 1 produced
proofs for.

Results: 24,218/24,218 unsat reproduced; **24,214 valid, 0 holey, 0 check
timeouts**; the only non-valid are 2 borderline cvc5 no-proofs (600.4s) and
the 2 `choice`-binder files. The 7 huge-indexed-op benchmarks now check valid.

On the 24,202 benchmarks valid in both rounds:

| | round 1 | round 2 | speedup |
|---|---|---|---|
| parsing | 147,374s | 9,328s | **15.8x** |
| checking | 39,584s | 12,205s | 3.2x |
| carcara total | 186,958s | 21,533s | **8.7x** |
| median / worst | 148ms / 289s | 36ms / 73s | |

carcara is now **cheaper than cvc5 on 100% of benchmarks** (the scatter cloud
sits entirely below the diagonal; every round-1 above-diagonal streak is gone).
Rule totals: rare_rewrite 29,169s -> 4,645s (rare-meta-skip); ac_simp
(2,981s) **eliminated** — its replacement `absorb` checks 7.4M steps in 2.1s;
poly_simp 376s -> 190s; grand rule total 38.6k s -> 11.6k s. Remaining top
costs are rare_rewrite and resolution (~4.6k s each), then evaluate (1.7k s).
Plots in `~/exp/alethe-bv/plots2/`.
