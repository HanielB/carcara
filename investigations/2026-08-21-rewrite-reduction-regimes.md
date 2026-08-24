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
- **`rare-tests/rare/simplify-rules.eo`**: the 27 rewrite rules the traces need beyond
  `rewrites.eo` (`rewrites-ext.eo` in the eval dir is the concatenation). `and`/`or-flatten`
  are deliberately absent — the RARE list semantics normalize `(and (and xs))` to `(and xs)` in
  the rule's own instantiation, so the singleton unwrap is not RARE-expressible; those links are
  emitted as their two-step core derivation in both regimes.
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
2. **Singleton applications.** The `and`/`or_simplify` checkers compare argument lists, so
   `(= (or x) x)` and `(= (or false x) (or x))` are both accepted — the right-hand side can be a
   singleton application `form` would collapse or a bare term. The trace compares lists
   checker-style and gives the final link the right side exactly as written.
3. **RARE cannot say everything the checkers do.** Besides the flatten/unit rules, an
   instantiated right-hand side `(or ys)` meta-normalizes to `ys` while the proof's term keeps
   the singleton — the `ToRare` lemma emission validates the instantiation against the exact
   target and falls back to the core recipe on mismatch.
4. **`la_generic` takes single negations only** (`negate_disequality` uses `remove_negation`),
   so direction clauses use collapsed literals (`c` for `¬c`) and the equivalence assembly
   resolves on the complement pairs directly.

## Sizing the frozen set

The `core-simp-rare` outputs answer the question the analysis left open: **53 distinct rewrite
rules** over the corpus — 40 of the 101 active non-BV/array rules of `rewrites.eo` plus 13 of
`simplify-rules.eo`; veriT's proofs need 28, cvc5's 45 (before the `aci_simp` renames the
counts were 55/32/45, the difference being the duplicate-removal rules the renames absorb). Two rewrites of the `*_simplify`
fixpoint systems are not expressible in RARE at all (the singleton collapse and the flatten),
since the list semantics normalize the rule's own left-hand side away.

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
