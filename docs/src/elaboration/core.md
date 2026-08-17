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
memoized over the term DAG so shared subterms are derived once). The decomposition covers the
binder-free fragment of `ac_simp`: instances whose rewrite reaches *under a binder* (the
checker's normalization descends into binders and `let`s) would additionally need a
binder-congruence (`bind`) wrapper around the recursive derivation, and are kept unchanged for
now — in practice a handful of premise-carrying `ac_simp` steps in quantified-logic proofs.

**Binder.** The six quantifier rewrites `qnt_simplify`, `qnt_rm_unused`, `qnt_join`,
`miniscope_distribute`, `miniscope_split`, `miniscope_ite`, in their `forall` forms, via the
**generalized `bind`** (divergence 8 of the core proposal, in its no-substitutions instance):
each direction of the equivalence eliminates the quantifier with `forall_inst` *at the anchor's
own variables* and reintroduces it with a closing `bind` step over a declared subset of the
anchor variables. Carcara's `bind` checker accepts this generalized form: under an anchor
declaring only fresh variables, the previous step may conclude an arbitrary clause, and the
conclusion closes exactly one literal as a `forall` over a subset of the anchor variables (in
anchor order), the remaining literals passing through unchanged.

Since the convenience rules `equiv_intro` and `or_intro` are proposals not yet checked by
Carcara, the pass emits their *expansions* (`equiv_neg1/2` + resolutions, `or_neg` × n +
resolutions + `contraction`) rather than the named rules.

## Behavior on uncovered shapes

The pass is best-effort and never rejects a proof: a step whose shape a recipe does not cover
(e.g. an `exists`-form quantifier rewrite, a `nary_elim` over a chainable operator), or whose
reduction fails, is kept unchanged and a warning is logged. In particular the following stay
untouched, by design:

- `onepoint` and `sko_ex` (reducible, but their elaborations need the `onepoint` grammar
  template and choice-binder congruence respectively — planned);
- the *expensive* tier (`weakening`, `contraction`, the `la_mult_*` family, the arithmetic
  `*_simplify` renames) and the *aggressive* tier (Boolean `*_simplify`, `aci_simp` itself,
  `distinct_elim`, `comp_simplify`);
- the legacy rules other than `ac_simp` and the ones other passes already handle (`lia_generic`
  is the `hole` pass's job and is deliberately excluded here; `qnt_cnf` has no defined semantics
  to reduce; `ite_intro` and `bfun_elim` await removal), plus the `ac_simp` instances that
  rewrite under a binder (see above).

## Step ids

New steps are generated in a `.c<n>` id namespace (`t1.c1`, `t1.c2.c1`, …), disjoint from the
`.t<n>` namespace used by the other passes, so the pass composes with `polyeq` and `uncrowd`
without id collisions. The step being elaborated keeps its id and conclusion, so all references
to it remain valid.
