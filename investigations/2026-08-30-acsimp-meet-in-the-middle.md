# `ac_simp` at SMT-LIB scale: the silent keeps, and the meet-in-the-middle completion

**Date:** 2026-08-30. **Commits:** 16862ede (the completion), 1d25acf6 (warnings on
the aci renames). **Trigger:** the SMT-LIB cluster evaluation (`alethe-core`):
nine veriT QF\_LRA `clock_synchro` proofs kept one `ac_simp` step each after the
`core` pass — silently, with no reduction warning.

## Why it was silent

The `ac_simp` reduction had three keep paths that returned the original step
without logging (malformed premise, computed-normal-form mismatch, unchekable
layer), and the cluster runner only captured carcara's stderr on a non-zero
exit — so even the paths that did warn were invisible on success. Both are
fixed: every keep path in `simplification.rs` now warns (the `shuffle` /
`nary_elim` renames included), and the runner reports a `warns=` count plus a
deduplicated warning digest per configuration.

## The actual gap

The decomposition computed a normal form of the conclusion's *left-hand side*
and required it to equal the right-hand side literally. Premise rewrites were
applied in **both orientations** (veriT sometimes writes a premise equality
reversed), and normalization **stopped** at each premise's replacement term.
Two consequences at scale:

- an undirected entry can fire *backward*, replacing an already-normal subterm
  by the premise's nested side and stopping there — the computed form is then
  *less* normal than the conclusion's right-hand side;
- a replacement term that is itself not in normal form is propagated verbatim,
  while the checker — whose `ac_simp` reading is structural and normalizes
  **both** sides — accepts the step.

The `clock_synchro` instances hit the first case: the probe showed the computed
form holding a nested `and`-chain of one repeated literal exactly where the
conclusion had the collapsed literal.

## The completion

Two routes, in order:

1. **Legacy** (unchanged, tried first): both-orientation premise map,
   normalization stopping at replacements, conclusion reached directly. Every
   instance it covers decomposes byte-identically to before — verified on the
   ac\_simp-heavy local corpus proofs (6/6 identical outputs).
2. **Meet in the middle** (new): normalize **both** sides of the conclusion,
   with **forward-only** premise rewrites and normalization **continuing past**
   each replacement (the map is skipped at the replacement's own root, which is
   what lets a converse premise pair terminate). Derive each side down to the
   common normal form with the same per-layer `aci_simp`/`cong`/`trans`
   machinery — the premise node glued to its replacement's own normalization by
   `trans` — and close with `trans(d_lhs, symm(d_rhs))`. This mirrors the
   checker's structural reading, so everything the checker accepts in the
   binder-free fragment is now derivable.

Directionality note: forward-only entries suffice in the meet route even when a
premise is used "backward", because the side that contains the redex rewrites
to the replacement and the other side already contains it — both descents meet.

## Validation

- All 388 tests pass.
- The nine failing SMT-LIB instances: `clocksynchro_{7,8,9}clocks` (and family)
  reduce to **0** `ac_simp` steps, no warnings, and the arm-A output re-checks
  at the elaborated granularity.
- No regression: previously-covered instances produce byte-identical outputs
  (legacy route first).

The static binary for the follow-up cluster rerun is built
(`carcara 1.1.0 [git 1d25acf6 coreAlethe-upstream]`); the first run's results
stay on the submitted binary (1f562e59) for provenance, with these instances
documented in coverage.
