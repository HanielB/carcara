# Core elaboration

The `core` pass is the elaboration counterpart of the [core Alethe fragment](../core.md): it
rewrites every step whose rule sits in the *reducible* tier of the
[classification](../core/classification.md) into a derivation over core rules only. The recipes
implemented are exactly the ones documented there; this page records what the pass covers, how it
behaves, and what it leaves alone.

## Usage

The pass is opt-in (it is not part of the default pipeline). The recommended pipeline runs it
*twice*, sandwiching the `local` pass:

```
carcara elaborate example.smt2.alethe example.smt2 --pipeline polyeq core local core reordering
```

The first `core` runs after `polyeq` (which normalizes the implicit reorderings the recipes rely
on) and eliminates the reducible tier — in particular the `eq_*` family, before `local`'s
canonicalize-but-keep handling of it would introduce `weakening` scaffolding. `local` then infers
resolution pivots, and in canonicalizing `cong`/`trans` steps may itself emit a few
`eq_symmetric`/`equiv2` steps — which the second `core` reduces. `reordering` finally removes
the reordering bookkeeping (the `uncrowd` pass, which splits crowding resolutions into
resolution/`contraction` pairs, composes with this pipeline but is not needed for
elaborated-granularity checking, whose resolution checker works set-wise). With this pipeline
the elaborated output of veriT proofs in the quantifier-free and quantified UF/LIA/LRA logics
is entirely within the core vocabulary (plus `contraction`, which the chain pipeline
deliberately uses), apart from the unreduced expensive/aggressive-tier steps present in the
input.

The output can then be checked in elaborated (strict) mode — with the RARE rule set when the
input contained `ite_intro` steps, whose reduction emits `rare_rewrite` instances:

```
carcara check --check-granularity elaborated --rare-file rare-tests/rare/ite-intro.rare example.elab.alethe example.smt2
```

There used to be a variant, `core-keep-eq-cl`, that skipped the clausal equality reductions — a
vocabulary point between the original rule set and the full core, motivated entirely by the
discharge-subproof blowup those reductions caused. It is gone, because that is now what the *single*
pass does: `eq_transitive`, `eq_congruent`, `eq_symmetric` and `not_symm` are classified
**expensive**, exactly as `sko_ex` is — the reduction is complete and implemented, but each instance
costs a discharge subproof and buys no checking power, so the pass leaves the steps alone by
default. Re-enabling any of them is one entry in `get_elaboration_function`.

## The rewrite-reduction regimes

Two variants of the pass extend it over the rewrite vocabulary (the `*_simplify` rules,
`evaluate`, `rare_rewrite`):

- **`core-simp-rare`** replays each `*_simplify` step as the chain of rewrites its checker
  applies, one `rare_rewrite` lemma per rewrite (an `evaluate` lemma for the constant folds),
  glued by `trans`. `evaluate` and `rare_rewrite` are kept: they are the computational
  vocabulary this regime deliberately retains. The chains use rewrite rules beyond cvc5's
  `rewrites.eo`, shipped in `rare-tests/rare/simplify-rules.eo`; give the checker the
  concatenation of both files (`--rare-file`). Two links have no rule and are emitted as their
  core derivation instead: they equate a *singleton application* of `and`/`or` with its argument,
  which is not a well-formed Alethe term, so there is nothing for a rule to state (RARE agrees,
  normalizing `(or x)` to `x`). veriT nevertheless emits such terms — 1 666 occurrences over 71
  of its corpus proofs, none from cvc5 — so the pass keeps the derivation as a robustness
  measure for out-of-spec input.
- **`core-taut`** reduces the whole vocabulary to the core: the chains' lemmas, and every
  `evaluate` and `rare_rewrite` step of the input, become core derivations, using the recipes
  the "frozen RARE set" analysis of the classification proposes (the `poly_simp_rel` template
  for the arithmetic atom equivalences, discharge subproofs over the CNF axioms for the
  propositional ones, the term-`ite` selection axioms `ite_then_intro`/`ite_else_intro` for the
  `ite` rules) and, for `evaluate`, a structural recursion following the checker's own
  evaluation function. The `prod`/`sum`/`minus`/`unary_minus`/`div_simplify` rules rename to
  `poly_simp` in both regimes (their integer-`div` instances excepted).

The traces are read off the checkers themselves: the `*_simplify` step functions return the
name of the rewrite they apply, so the replay cannot drift from what the check accepts. Steps
whose conclusion mentions an anchor-*assigned* variable are kept unreduced (the recipes' `refl`
and excluded-middle steps would change meaning under the context substitution), as are
`rare_rewrite` steps of rules outside the recipe set — both logged, both counted by the
evaluation.

## What a recipe is written against

A recipe is derived from **the semantics of its rule as implemented by Carcara's checker**, not
from the shapes any particular solver emits. The checker function defines the space the recipe
must cover; proofs from veriT and cvc5 are validation data. Where the checker's own decision
procedure is reusable, the recipe reuses it rather than reimplementing it — `qnt_cnf`'s descent
is guided by the checker's `negation_normal_form`/`prenex_forall`/`conjunctive_normal_form`,
`bfun_elim` follows the checker's assignment enumeration, `onepoint`'s guards come from the
`extract_points` grammar — so that the two cannot drift apart.

This matters because a recipe written against one producer's idioms silently fails on another's
equally valid output: the *checker*, for instance, discovers `onepoint` guards by a
polarity-driven traversal that accepts equalities in either orientation anywhere in the
`and`/`or`/`=>` structure, so a recipe that pattern-matches one producer's layout is
under-covering by construction, not by necessity.

Consequently, coverage below is stated in terms of the checker's accepted space, and an
uncovered case is one that is genuinely hard to *derive*, not merely one that a given solver
does not happen to produce.

## Covered rules

**Clausal.** `th_resolution` (rename to `resolution`), `tautology` (→ `true`, dropping the
premise), the 19 premise clausification rules (`and`, `or`, `not_and`, `not_or`, `xor1/2`,
`not_xor1/2`, `implies`, `not_implies1/2`, `equiv1/2`, `not_equiv1/2`, `ite1/2`, `not_ite1/2` —
each becomes its paired CNF axiom plus one resolution on the premise formula), and the extra
rules `and_intro` (→ `and_neg` + resolution) and `eq_mp` (→ `equiv_pos2` + resolution, shared
with the `local` pass).

**Equality.** `eq_reflexive` (→ `refl`, a rename) and `eq_congruent_pred` (→ `eq_congruent` plus
one `equiv_pos` axiom and a resolution: the predicate rule is the function rule read through an
equivalence). The other clausal equality rules — `eq_transitive`, `eq_congruent`, `eq_symmetric`,
`not_symm` — are *expensive* and left alone: their discharge-subproof reductions live in
`core/equality.rs`, complete and tested, but unregistered.

**Arithmetic.** `la_totality` and the binary form of `la_tautology` (→ `la_generic` + the
`or_intro` packing pattern; the unit form is a coefficient-`[1]` `la_generic` rename), and
`la_rw_eq` (→ discharge subproof with two `la_generic` steps for the → direction, the
`la_disequality` axiom unpacked by `or_pos` and crossed with `and_pos` for ←).

**ACI.** `shuffle` (rename to `aci_simp`), `nary_elim` for the associative-commutative operators
(also a rename to `aci_simp` — both sides flatten to the same argument multiset),
`and_simplify`/`or_simplify` (an `aci_simp` rename whenever the instance is aci-compatible —
flattening, neutral-element removal, duplicate removal, which the pass decides by running the
`aci_simp` check itself — and a constant-size chain over the CNF axioms for the short-circuits
to a constant), and the legacy `ac_simp` (decomposed into one `aci_simp` step per connective layer, glued by `cong`/`trans`,
memoized over the term DAG so shared subterms are derived once). veriT emits `ac_simp` in two
forms: the specification's premise-free flattening, and a premise-carrying form — congruence
over previously derived flattenings of subterms, which is how rewrites *under a binder* reach
the conclusion (packaged as `bind` subproofs among the premises; note that the premises are
outside the specification's premise-free rule statement, and that Carcara's checker implements
a strictly stronger reading that ignores them and normalizes through binders). The
decomposition consumes the premises as ready-made equalities for those subterms — `cong` over
the premise equalities plus `aci_simp` on the binder-free layers — so no binder congruence
needs to be derived, and both forms reduce completely.

**Binder.** The six quantifier rewrites `qnt_simplify`, `qnt_rm_unused`, `qnt_join`,
`miniscope_distribute`, `miniscope_split`, `miniscope_ite`, in their `forall` forms, via the
**generalized `bind`** (divergence 8 of the core proposal, in its no-substitutions instance):
each direction of the equivalence eliminates the quantifier with `forall_inst` *at the anchor's
own variables* and reintroduces it with a closing `bind` step over a declared subset of the
anchor variables. Carcara's `bind` checker accepts this generalized form: under an anchor
declaring only fresh variables, the previous step may conclude an arbitrary clause, and the
conclusion closes exactly one literal as a `forall` over a subset of the anchor variables (in
anchor order), the remaining literals passing through unchanged.

`onepoint` reduces by the classification's case-split template, in both `forall` and (through
the `connective_def` duality) `exists` forms: the guard equalities are extracted from the body
(from the antecedent's `and`-spine, or from a negated consequent), oriented toward the point
values, and *transported* through the body by deep `cong` — with an `eq_symmetry` bridge when
veriT wrote a guard equality in the flipped orientation — while the reverse direction re-derives
the body from the substituted formula by refuting the trivialized guards (`refl` on `(= t t)`).
The whole equivalence lives inside the now-vacuous anchor and closes with the generalized
`bind`.

`ite_intro` derives each ite-subterm's
selection tautology `(ite c (= s r₁) (= s r₂))` by a two-branch discharge over the condition:
under the assumed (negated) condition, `equiv_neg1/2` and the `true`/`false` axioms give
`(= c ⊤)`/`(= c ⊥)`, `cong` lifts that into `s = (ite c r₁ r₂)`, and the term-level branch
selection is the `rare_rewrite` rule `ite-true-cond`/`ite-false-cond` of the alethe-toolkit
rule set (shipped as `rare-tests/rare/ite-intro.rare`); the branches are crossed with the
`ite_neg1/2` axioms and the equivalence is packed by `and_neg`/`and_pos` and the
iff-introduction pattern.

Since the convenience rules `equiv_intro` and `or_intro` are proposals not yet checked by
Carcara, the pass emits their *expansions* (`equiv_neg1/2` + resolutions, `or_neg` × n +
resolutions + `contraction`) rather than the named rules.

## Behavior on uncovered shapes

The pass is best-effort and never rejects a proof: a step whose shape a recipe does not cover
(e.g. an `exists`-form quantifier rewrite, a `nary_elim` over a chainable operator, a
`bfun_elim` whose Boolean arguments sit below uninterpreted functions), or whose reduction
fails, is kept unchanged and a warning is logged. In particular the following stay untouched,
by design:

- `sko_ex`, which is classified *expensive*: its reduction (through the quantifier duality, with
  the ∃-shaped witnesses bridged to the ¬∀¬-shaped ones by a `bind` over the `choice` binder) is
  complete and lives in `core/skolem.rs`, and every emitted step is a cheap core rule — but it
  costs ~35 steps per binding, an ~8× local blowup, which the classification is not willing to
  pay by default. Re-enabling it is one entry in `get_elaboration_function`; the measurements are
  in `investigations/2026-08-18-sko-ex-cost.md`;
- the rest of the *expensive* tier (`weakening` and `contraction` — reducible only under
  `resolution`'s RUP reading, which the elaborated granularity does not use — the `la_mult_*`
  family, the arithmetic `*_simplify` renames) and the *aggressive* tier (Boolean `*_simplify`, `distinct_elim`,
  `comp_simplify`) — `aci_simp` and `evaluate` are core computational primitives and need no
  reduction;
- `lia_generic`, which is the `hole` pass's job and is deliberately excluded here.

## Step ids

New steps are generated in a `.c<n>` id namespace (`t1.c1`, `t1.c2.c1`, …), disjoint from the
`.t<n>` namespace used by the other passes, so the pass composes with `polyeq` and `uncrowd`
without id collisions. The step being elaborated keeps its id and conclusion, so all references
to it remain valid.
