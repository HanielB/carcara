# Merging the core-Alethe work onto `parsing-subst-fixes`

**Date:** 2026-08-30. **Branch:** `coreAlethe-upstream` = `parsing-subst-fixes` (f230a608)
+ a single merge commit bringing in all of `coreAlethe` (ad5cfc55; 149 commits since the
common base 86f4e1f1, all from August 2026 — the core-fragment project).

## Shape of the merge

`parsing-subst-fixes` had restructured the repository (crate moved to the root, `cli`
merged into `src/bin/cli/`) and reworked the AST: sorts are a separate `Rc<Sort>`
representation (`Term::Sort` is gone, `pool.sort` returns `Rc<Sort>`), `match_term!`
auto-checks repeated names, `free_vars` returns a `Cow`, configs are setter-based
(`GenerateSetters`), parser errors carry the source filename, and elaboration errors are
located to a file and pass (`ElaborationErrorAtStep::at(filename, pass)`).

Git's rename detection placed all our added files (`src/elaborator/core/**`, `hoist.rs`,
`prune.rs`, `scopes.rs`, `growth.rs`, the test suites) into the new layout on its own.
15 files had content conflicts; three files upstream had deleted (`ast/mod.rs`,
`ast/pool/mod.rs`, `cli/main.rs`) had our small changes ported to their successors by
hand. After the textual merge, ~110 compile errors were the actual port: mechanical
`as_sort()`→`as_ref()`, `Term::Sort`-arm removal, `match_term!` pattern dedup, `Cow`
adaptations, and `Source`-typed parser entry points.

## Files where one side was taken wholesale

Two files were competing rewrites of the same mechanism, where interleaving hunks would
have produced incoherent code. In both, **our version won**, because the elaborator's
correctness depends on its semantics; upstream's independent improvements were re-ported
on top:

- **`ast/substitution.rs`** — ours: generation-tagged lazy cache invalidation,
  the `captured` set, and shadow-without-renaming (a binder that merely shadows a
  substituted variable is *not* α-renamed — the reductions rely on terms continuing to
  match what the solver wrote). Upstream's competing design (scoped `HashMapStack` cache
  + `renaming_shadow` multiset) was dropped. Re-ported from upstream: `SortSubstitution`
  (needed by the sort/term split), the generic `rename_binding_list<V: BindingValue>`,
  the `MatchCase`/`MatchPattern` handling, and `is_compatible`-based sort checks.
  `apply_uncached` (upstream's context-building heuristic entry point) is kept as an
  alias for `apply`: with the lazy cache, `insert` no longer scans the cache, which is
  the overhead that entry point existed to avoid.
- **`utils.rs` (`HashMapStack`)** — ours: O(1) scoped-shadowing lookups (upstream kept
  per-scope maps searched innermost-first, only swapping in rapidhash). Upstream's
  `get_top`/`retain_top` extensions existed only for their replaced substitution design
  and were dropped; `Extend` was reimplemented for our structure.

Similarly, `checker/rules/simplification.rs` and `parser/rare/mod.rs` are our versions
(the named-rewrite step functions that the recipe machinery replays, and the
`TypeParameter.variable` construction), adapted to the new sort API. The rare `:list`
parameter no longer gets a `(rare-list S)` sort — upstream removed `Sort::RareList`, and
the parameter's variable is typed at the element sort directly, which is what our
checker/elaborator used via `.variable` anyway (`TypeParameter` now carries upstream's
`sort: Rc<Sort>` plus our `attribute` and `variable`; only `Display` consumed the old
`term` field).

## Semantic decisions worth knowing about

- **`Substitution::new` takes `impl IntoIterator`** and collects into an `IndexMap`, so
  both our (IndexMap) and upstream's (RapidHashMap) call sites work. Iteration order of
  the map affects renaming determinism; upstream call sites hand over hash-ordered maps,
  as they did upstream.
- **`aci_simp` on `str.++`**: upstream added `StrConcat` to the aci operators but let it
  reach the argument-*multiset* comparison, which treats it as commutative — unsound for
  string concatenation. The port keeps the `str.++` support (flattening + identity
  elimination) but excludes it from the shuffle branch, like `bvconcat`.
- **`set_replay_valid`** (our chain-replay validation of greedy pivot inference) now
  accepts the checker's special case of a resolution concluding the empty clause with a
  bare `false` left implicitly eliminated — `greedy_resolution` already accepted it, and
  upstream's new `infer_pivots` integration test exercises it.
- **Our elaborator passes** return `ElaborationErrorAtStep` and are dispatched through
  upstream's located-error scheme, so core/hoist failures now also report file and pass.
- **checker `Config`** gained `get_allowed_rules()` (the hoist test builds the elaborator
  config from the checker's allowed rules, and the field is private under the setter
  convention).
- The pool's `sort_with_priorities` keeps our fallback (compute the sort of a term built
  in another pool rather than panic), and `free_vars` keeps our fix for `let`: the free
  variables of binding *values* are free in the `let` term.

## Validation

- `cargo check --all-targets` clean (a handful of pre-existing upstream warnings
  remain silenced with `#[allow(dead_code)]` where the method is a utility kept for API
  completeness).
- Full test suite: **388 tests, all pass** — upstream's 123 lib + 217 rule + 16
  elaboration tests, and our 14 core-elaboration + 13 hoist + 3 rewrite-elaboration
  suites (ported to `Source`-typed parsing, setter-based configs, and the
  filename-threaded `elaborate`).
- Corpus sample, 2 proofs × 5 logics × both solvers (sizes 30–258k steps): old and new
  binaries agree on all 20 input verdicts (including the one holey QF_LIA/veriT input);
  every arm-A output (`hoist polyeq local core core reordering`) re-checks at elaborated
  granularity under both binaries, and every arm-B output (`core core`, new binary) at
  default granularity. Arm-A step counts are identical old-vs-new on 18 of 20 proofs;
  the two QF_UFLIA/veriT proofs come out slightly larger under the new binary
  (7095→7130, 9691→9705, ≈0.3%) — both valid, presumably a different chain choice
  somewhere in the merged resolution machinery.

## Follow-ups

- The eval scripts point `CARC` at `wt-corealethe`; benchmarking under this branch means
  rebuilding there or repointing. Upstream's performance work (substitutions, resolution
  elaboration, rapidhash, context cache heuristic) shifts absolute times, so ladder
  numbers are not comparable across the merge without a resweep.
