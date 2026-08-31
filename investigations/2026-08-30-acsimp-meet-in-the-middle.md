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

## Addendum (same day): the other two at-scale defects, fixed

The full SMT-LIB sweep surfaced two more, both in the `core-expensive` rung and
both concentrated where the local corpus had no instances:

- **Deep outbound premises (ac012f21).** `mutate_impl` recorded only a returned
  root's *direct* outbound premises into the enclosing scope's frame, so a
  pass-built derivation whose interior references nodes outside the scope (a
  replayed `bind` body keeping its premises, a shared depth-0 derivation) left
  the scope's `outbound_premises` incomplete — 292 cvc5 tasks (UF-heavy)
  panicked on the printer's invariant. The frame extension now walks the
  returned derivation (stopping at already-collected nodes, so linear), the two
  invariant assertions name the offending scope, and `CARCARA_VALIDATE_FOREST=1`
  re-checks every scope's outbound list after each pass.
- **Non-closure anchor variables in the closure replay (23cac212).** A
  generalized bind's anchor may bind more variables than the closed literal
  quantifies; the body may still reference them (cvc5's LRA Monniaux-QE proofs
  emit `forall_inst` steps instantiating an anchor variable *at itself*). The
  closure replay substituted only the closed literal's variables, so those
  references escaped the eliminated anchor unbound: 619 LRA `core-full` outputs
  failed to re-parse, and the same family accounts for 924\,780 of the 926\,058
  `bind` steps cvc5's `core-full` rung left standing. Each such variable is now
  substituted by a closed dummy witness of its sort (`(choice ((v S)) true)`),
  sound because the closing clause cannot mention it.

Validated: 388 tests pass; the LRA family now elaborates to 0 `bind` steps and
re-checks strictly; the UF panic benchmark completes and re-checks; the veriT
UF full-rung invalid sampled locally re-checks valid; full-pipeline outputs are
byte-identical to the pre-fix binary on the ac\_simp- and bind-heavy local
corpus proofs (6/6). Residual defect classes left for triage (small, recorded
in the SMT-LIB report's coverage): a broken `trans` inside a discharge-scope
reduction on 4 QF\_UFIDL/uclid veriT proofs at `core-full`, ~27 veriT
"pivot was not found" at the same rung, and a handful of pivot-inference and
`rare_rewrite`-reduction warnings.

The rerun binary is `carcara 1.1.0 [git 23cac212 coreAlethe-upstream]`.

## Addendum (2026-08-31): the `onepoint` replay guard, removed

Round 2 of the SMT-LIB evaluation localized the remaining `bind` incompleteness
to a single guard: the replay refused any nested scope closed by `onepoint`
("its side condition is recomputed from the substituted body"). The refusal was
conservative, not necessary: the body's point equations and the anchor's
assigned values are transported by the *same* substitution, and the eliminated
variables are never substituted (the shadows guard), so the substituted scope
offers exactly the substituted points its transported anchor assigns — the
side condition commutes. Removed in `3cbabbcb`; the `onepoint` scope now flows
through the generic nested-scope path.

Validated on every guard-hitting class the round-2 warning digest named:
LIA/tptp (`NUM915/916/918`), UF (`stream_processor`), and the LRA Monniaux-QE
family — all reduce to **zero** `bind` steps and re-check at the elaborated
granularity, with `CARCARA_VALIDATE_FOREST` clean; 388 tests pass; covered
local-corpus instances elaborate byte-identically (6/6). Since `onepoint` was
the *only* bind-failure class in the digest, the next round should take cvc5's
kept `bind` residue from 926k to (near) zero. Static rerun binary:
`carcara 1.1.0 [git 3cbabbcb coreAlethe-upstream]`.
