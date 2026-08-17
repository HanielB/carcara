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
carcara elaborate example.smt2.alethe example.smt2 --pipeline polyeq core local core uncrowd reordering
```

The first `core` runs after `polyeq` (which normalizes the implicit reorderings the recipes rely
on) and eliminates the reducible tier — in particular the `eq_*` family, before `local`'s
canonicalize-but-keep handling of it would introduce `weakening` scaffolding. `local` then infers
resolution pivots, and in canonicalizing `cong`/`trans` steps may itself emit a few
`eq_symmetric`/`equiv2` steps — which the second `core` reduces. `uncrowd` finally splits the
crowding resolutions the reductions emit, and `reordering` removes the reordering bookkeeping.
With this pipeline the elaborated output of veriT proofs in the quantifier-free and quantified
UF/LIA/LRA logics is entirely within the core vocabulary (plus `contraction`, which the chain
pipeline deliberately uses), apart from the unreduced expensive/aggressive-tier steps present in
the input.

The output can then be checked in elaborated (strict) mode:

```
carcara check --check-granularity elaborated example.elab.alethe example.smt2
```

## Covered rules

**Clausal.** `th_resolution` (rename to `resolution`), `tautology` (→ `true`, dropping the
premise), the 19 premise clausification rules (`and`, `or`, `not_and`, `not_or`, `xor1/2`,
`not_xor1/2`, `implies`, `not_implies1/2`, `equiv1/2`, `not_equiv1/2`, `ite1/2`, `not_ite1/2` —
each becomes its paired CNF axiom plus one resolution on the premise formula), and the extra
rules `and_intro` (→ `and_neg` + resolution) and `eq_mp` (→ `equiv_pos2` + resolution, shared
with the `local` pass).

**Equality.** `eq_reflexive` (→ `refl`), and the clausal repackagings `eq_transitive`,
`eq_congruent`, `eq_congruent_pred`, `eq_symmetric`, `not_symm` — each derived under a discharge
subproof that assumes the negated literals and closes with `trans`/`cong`/`symm` (and, for
`eq_congruent_pred`, the `eq_mp` pattern; for `eq_symmetric`, both directions glued by the
iff-introduction pattern).

**Arithmetic.** `la_totality` and the binary form of `la_tautology` (→ `la_generic` + the
`or_intro` packing pattern; the unit form is a coefficient-`[1]` `la_generic` rename), and
`la_rw_eq` (→ discharge subproof with two `la_generic` steps for the → direction, the
`la_disequality` axiom unpacked by `or_pos` and crossed with `and_pos` for ←).

**ACI.** `shuffle` (rename to `aci_simp`), `nary_elim` for the associative-commutative operators
(also a rename to `aci_simp` — both sides flatten to the same argument multiset), and the legacy
`ac_simp` (decomposed into one `aci_simp` step per connective layer, glued by `cong`/`trans`,
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

**Legacy quantifier rules.** `qnt_cnf` reduces by a guided clausal descent: the conclusion
`(cl (or ¬(∀x̄.φ) (∀x̄ₖ.C)))` is derived by instantiating the left quantifier under an anchor
over `x̄ₖ` (dropped variables at dummy `choice` witnesses) and then decomposing `φ` one
connective at a time with the CNF axioms (`and_pos`/`or_neg`/`implies_neg1/2`/`equiv_*`/
`ite_*`/`not_not`, plus the `connective_def` duality for `¬∃`), each branch choice guided by an
oracle that mirrors the checker's NNF/prenexing/CNF computation; the derivation is a linear
resolution chain, subproof-free except for the closing `bind`. `bfun_elim`, in its top-level
form, expands the Boolean-quantified premise into the conjunction of its `2^k` instances
(`forall_inst` per assignment, in the checker's enumeration order, `and_neg` to repack, a
closing `bind` over the non-Boolean variables).

Since the convenience rules `equiv_intro` and `or_intro` are proposals not yet checked by
Carcara, the pass emits their *expansions* (`equiv_neg1/2` + resolutions, `or_neg` × n +
resolutions + `contraction`) rather than the named rules.

## Behavior on uncovered shapes

The pass is best-effort and never rejects a proof: a step whose shape a recipe does not cover
(e.g. an `exists`-form quantifier rewrite, a `nary_elim` over a chainable operator, a
`bfun_elim` whose Boolean arguments sit below uninterpreted functions), or whose reduction
fails, is kept unchanged and a warning is logged. In particular the following stay untouched,
by design:

- `sko_ex`: reducible on paper via the `sko_forall` duality, but elaborating *existing* steps
  is blocked on choice-binder congruence (divergence 5): the duality route produces the witness
  `(choice ((x S)) ¬¬φ)` where the step's conclusion uses `(choice ((x S)) φ)`, and no core
  rule can rewrite under a `choice` binder today;
- the *expensive* tier (`weakening`, `contraction`, the `la_mult_*` family, the arithmetic
  `*_simplify` renames) and the *aggressive* tier (Boolean `*_simplify`, `aci_simp` itself,
  `distinct_elim`, `comp_simplify`);
- `lia_generic` (the `hole` pass's job, deliberately excluded here) and `ite_intro` (awaits
  veriT-side removal: its conclusion nests the term-level ite constants inside the very formula
  being defined, and reducing it needs a term-level ite selection axiom the core does not
  have).

## Step ids

New steps are generated in a `.c<n>` id namespace (`t1.c1`, `t1.c2.c1`, …), disjoint from the
`.t<n>` namespace used by the other passes, so the pass composes with `polyeq` and `uncrowd`
without id collisions. The step being elaborated keeps its id and conclusion, so all references
to it remain valid.
