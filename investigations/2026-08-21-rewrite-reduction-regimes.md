# The rewrite-reduction regimes: `core-taut` and `core-simp-rare`

**Branch:** `coreAlethe` (commit `8ca3808d`).
**Verdict:** both regimes of the frozen-RARE analysis are implemented and validated: the
aggressive tier's `*_simplify` rules reduce — to `rare_rewrite`/`evaluate` chains
(`core-simp-rare`) or all the way to the core plus one new axiom pair (`core-taut`), which also
reduces every `evaluate` and `rare_rewrite` step. **Eliminating the whole rewrite vocabulary
costs 1.9% of aggregate proof size on veriT's proofs (2.49 → 2.53) and 15% on cvc5's
(0.93 → 1.08, still smaller than the input), with checking within 3% and 12% of the base
configuration**; `rare_rewrite` goes 98 692 → 8 285 steps on cvc5 and to zero on veriT, and
`evaluate` 26 084 → 156, the remainder being the `to_int`/floor family that needs a
`to_int_intro` axiom. The `aci_simp` rename of the aci-compatible `and`/`or_simplify` instances
(297 020 steps of veriT's output) is what makes it this cheap. Keeping the RARE engine buys
nothing: `core-simp-rare` produces base-sized proofs that check in the same time as
`core-taut`'s — and before the rename its rewrite chains checked *slower* than `core-taut`'s
32%-larger output (17.1 s vs 15.4 s), a `rare_rewrite` step costing ~1.9 µs against ~0.07 µs
for a `refl`.
Full numbers in the evaluation report; the design analysis is the "trusted computing base"
section of `docs/src/core.md`.

## What was built

- **Labeled simplify checkers.** The `simplify!` arms of the seven `generic_simplify_rule`-based
  checkers (`ite`/`eq`/`not`/`implies`/`equiv`/`bool`/`comp_simplify`) return the name of the
  rewrite they apply along with the result. One source of truth: the elaborator's traces iterate
  the checker's own step functions, so the replay cannot drift from the check
  (`checker/rules/simplification.rs`).
- **Trace producers** (`elaborator/core/rewrites/trace.rs`). Root-rewrite iteration mirroring
  `generic_simplify_rule` (early goal stop, cycle detection, flipped orientation → closing
  `symm`); a phase mirror for `and`/`or_simplify` (constant removal, duplicate removal,
  short-circuit detection, with per-argument double-negation parity normalization lifted by
  `cong`); argument-list comparison checker-style, so singleton applications (`(or x)`) and bare
  terms are both handled.
- **The chain builder** (`rewrites/mod.rs`): one lemma per link, `trans` glue, with the lemma
  provider chosen by regime. In `ToRare`, a lemma is a single `rare_rewrite` step whose
  instantiation is computed and validated by mirroring `check_rare` (substitution +
  meta-normalization), or an `evaluate` step for constant folds — falling back to the core
  recipe when the rule file lacks the rule or the meta-level list semantics make the instance
  differ from the term as written. In `ToCore`, every lemma is a core recipe.
- **The recipe library** (`rewrites/recipes.rs`, ~1600 lines): the 36 corpus RARE rules and
  every trace label. Families: arithmetic atom equivalences by one validated `la_generic` per
  direction, assembled against the `equiv_neg` axioms exploiting that `¬c`/`c` and `¬¬c`/`¬c`
  are syntactic resolution complements (no `not_not` bridges needed); propositional
  equivalences by discharge subproofs over the CNF axioms; n-ary `and`/`or` rules by the
  pos/neg axioms with set-semantics-aware packing (a duplicated literal is gone after its first
  resolution — `Builder::and_intro` now resolves each distinct conjunct once); term-`ite` rules
  from the new selection axioms by case-splitting on the condition (excluded middle is `refl` +
  `equiv_pos2` + resolution, 3 steps; double-negation *introduction* is excluded middle at
  `¬x`); `distinct-false` through `distinct_elim` as the definitional rule.
- **The `evaluate` recipe** (`rewrites/ground.rs`): structural recursion driven by the
  checker's own `Rc<Term>::evaluate` — `poly_simp` for ring identities, `la_generic` for
  constant relational atoms, the CNF axioms selecting each connective's decided branch, the
  selection axioms for term-`ite`, and an `equiv_neg` bridge to `(= t true/false)` at the top.
- **The axiom pair `ite_then_intro`/`ite_else_intro`** (`checker/rules/tautology.rs`):
  `(cl (not c) (= (ite c t s) t))` and `(cl c (= (ite c t s) s))` — the definitional
  characterization of term-`ite` the analysis identified as the one genuine gap.
- **`rare-tests/rare/simplify-rules.eo`**: the rewrite rules the traces need beyond
  `rewrites.eo` (`rewrites-ext.eo` in the eval dir is the concatenation). `and`/`or-flatten`
  are deliberately absent, and *not* because RARE is lacking: those links equate a singleton
  application of an n-ary connective with its argument, which is not a well-formed Alethe term,
  so there is nothing for a rule to state — RARE's normalization of `(or x)` to `x` is right.
  veriT emits such terms anyway (1 666 occurrences over 71 of its 489 corpus proofs; cvc5: none),
  so those links keep a two-step core derivation as a robustness measure for out-of-spec input.
- **Guard refinement**: `ContextStack` now tracks anchor-*assigned* names separately from
  merely declared ones (`assigns`/`assigns_nothing`); recipes are skipped only when the
  conclusion mentions an assigned variable, since only those change under the context
  substitution.

## Traps found while validating

1. **Resolution's set semantics vs duplicated literals.** `(and true true)`, `(or false false
   false)`, duplicated conjuncts in `and_intro` — after one resolution on a literal, its other
   copies are gone from the resolvent; packing or resolving again on it fails. Fixed by
   resolving once per *distinct* literal everywhere (`and_intro`, `pack_or`, the ground
   recursion, `guarded`'s assumptions — a lookahead's inner `ite` can *be* the right-hand side,
   making two case equalities identical).
2. **Singleton applications, which should not exist.** The `and`/`or_simplify` checkers compare
   argument lists, so `(= (or x) x)` and `(= (or false x) (or x))` are both accepted — the
   right-hand side can be a singleton application or a bare term. Alethe has no singleton
   application of an n-ary connective, so these steps are out of spec; **veriT emits them anyway**
   — 1 666 occurrences over 71 of its 489 corpus proofs, none from cvc5, concentrated in QF_LRA
   (1 275). Carcara's parser accepts them and the checkers tolerate them, so the elaboration has
   to as well: the trace compares argument lists checker-style and gives the final link the right
   side exactly as written, and the `ToRare` lemma emission validates each instantiation against
   the exact target, falling back to the core derivation when the meta-normalized instance
   differs. **The fix belongs upstream** — veriT should write `x` rather than `(or x)`, or
   Carcara should normalize singleton applications at parse time, which would also let the two
   checkers drop their argument-list special cases.
4. **`la_generic` takes single negations only** (`negate_disequality` uses `remove_negation`),
   so direction clauses use collapsed literals (`c` for `¬c`) and the equivalence assembly
   resolves on the complement pairs directly.

## The rename survey: what else a computational primitive subsumes

The `and/or_simplify` → `aci_simp` move (2026-08-24, now *reducible*) prompted a systematic
check: which rewrites are single-step instances of a computational primitive already in the
core? The criterion is the one that promoted `shuffle` and `nary_elim`: a one-step rename onto
a core primitive, check coarsening accepted, validated by the primitive's own checker before
emission.

| primitive | subsumes | status |
|---|---|---|
| `aci_simp` | `shuffle`; `nary_elim` (AC operators); `ac_simp` (per layer); **`and_simplify`/`or_simplify`** (every non-short-circuiting instance) | all implemented; the last two now *reducible* |
| `poly_simp` | `prod_simplify`, `sum_simplify`, `minus_simplify`, `unary_minus_simplify` (whole rules); `div_simplify`'s real-division cases | implemented in the regimes as renames; the rules sit in the *expensive* tier ("check-power upgrade") — by the criterion that just moved `and`/`or` they are reclassification candidates, and the measurement below says what that would cost |
| `evaluate` | `mod_simplify` (its whole check *is* constant evaluation; zero corpus instances); `div_simplify`'s **integer** cases (closing the one `poly_simp` gap — `Rc<Term>::evaluate` covers `div`, `mod` and `to_int`); the constant-folding instances of `eq`/`not`/`comp`/`ite_simplify` | implemented: whole-step renames in the regimes that keep `evaluate`, the evaluation recipe in `core-taut` |
| `la_generic` | `la_tautology`, `la_totality` (plus `or_intro` packaging) | long done, *reducible* |

**What the `poly_simp` rename actually costs.** The tier's objection to it is that the rule's own
check (fold the constants of an n-ary product, O(n)) is replaced by ring normalization. Measured
on `clock_synchro__clocksynchro_9clocks` (QF_LRA/veriT, the corpus's most
`prod_simplify`-dense proof), full pipeline, three runs:

| | steps/run | median | total/run | share of the file's checking |
|---|---:|---:|---:|---:|
| original `prod`/`sum`/`minus_simplify` | 572 | 0.37 µs | 0.23 ms | 0.14% |
| renamed `poly_simp` | 580 | 3.95 µs | 2.73 ms | 1.7% |

So the upgrade is real — **12× per step** — but it is 1.5 percentage points of that file's
164.8 ms check, and corpus-wide the four rules are only ~4 000 steps. For calibration, the
`and`/`or` → `aci_simp` rename that was just accepted costs the same order (0.44 µs → ~3 µs
median, ~7×), over 27 000 steps. The honest distinction is not the constant factor but the
worst case: ACI normalization is near-linear in the arguments, while ring normalization
distributes over nested products and can blow up on terms no `prod_simplify` instance would have
strained. Nothing in the corpus exhibits that (p99 of the renamed steps is 14 µs), so the
decision rests on how much weight the classification gives an unexercised worst case —
a tier judgement, left to the maintainer rather than taken here.

Checked and *not* subsumable by any single core rule: `eq-symm` (an equivalence between the two
orientations — needs the two-subproof recipe), the De Morgan and implication/equivalence
shapes, the `distinct` rules (the definitional gap), and the arithmetic atom flips (Farkas
pairs, two steps by construction). The pattern that remains is the one the classification
already states: a rewrite reduces to a *check* when some core primitive's normalization is the
rewrite's own semantics, and to a *derivation* otherwise.

## Sizing the frozen set

The `core-simp-rare` outputs answer the question the analysis left open: **53 distinct rewrite
rules** over the corpus — 40 of the 101 active non-BV/array rules of `rewrites.eo` plus 13 of
`simplify-rules.eo`; veriT's proofs need 28, cvc5's 45 (before the `aci_simp` renames the
counts were 55/32/45, the difference being the duplicate-removal rules the renames absorb). Two links of the `*_simplify` chains have no rule at
all, because they equate a singleton application of `and`/`or` with its argument — not a
well-formed Alethe term (see the singleton note below).

The one blow-up found — QF_LIA/veriT at 10.58 aggregate under `core-taut` (from 4.07), entirely
from two `Averest` proofs with ~18 000 `and_simplify` steps over hundred-argument conjunctions,
where the n-ary recipes are linear in the arity — is **fixed by renaming the aci-compatible
`and_simplify`/`or_simplify` instances to `aci_simp`** (Haniel's suggestion): the
non-short-circuiting part of those rules is exactly the `aci_simp` computational check, so the
step is a rename like `shuffle`/`nary_elim`, validated by `aci_simp_equal` before emission. The
Averest file drops from 1.88 M steps back to ~551 k, the base pipeline's size (commit
`049aa322`).

## Validation

- Corpus sweep (`scripts/sweep-variants.sh`): every proof of the corpus elaborated with both
  regimes and rechecked at elaborated granularity — verdicts match the base pipeline's
  everywhere (the only ELABFAIL/holey rows are the pre-existing timeout, empty-proof and
  `lia_generic` cases), with zero kept-step warnings outside the anchor-assigned residue.
- 269 unit/integration tests including `tests/test_rewrite_elaboration.rs`: ~50 shapes per
  regime elaborated and rechecked, vocabulary asserted clean.
- The `hoist` pre-filter (same commit): duplicate-conclusion digests collected in the existing
  pre-scan; unique conclusions skip the memo, the derivation walk and the context check, and
  duplication-free proofs skip the rebuild — −20% pass time on the largest QF_UF/veriT proof,
  no verdict changes.
