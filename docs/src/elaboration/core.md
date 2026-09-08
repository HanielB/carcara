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

The output can then be checked in elaborated (strict) mode:

```
carcara check --check-granularity elaborated example.elab.alethe example.smt2
```

There used to be a variant, `core-keep-eq-cl`, that skipped the clausal equality reductions — a
vocabulary point between the original rule set and the full core, motivated entirely by the
discharge-subproof blowup those reductions caused. It is gone, because that is now what the *single*
pass does: `eq_transitive`, `eq_congruent`, `eq_symmetric` and `not_symm` are classified
**expensive**, exactly as `sko_ex` is — the reduction is complete and implemented, but each instance
costs a discharge subproof and buys no checking power, so the pass leaves the steps alone by
default. Re-enabling any of them is one entry in `get_elaboration_function`.

## The rewrite-reduction regimes

Three variants of the pass extend it over the rewrite vocabulary (the `*_simplify` rules,
`evaluate`, `rare_rewrite`), each removing one more piece of it:

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
- **`core-no-rare`** goes one rung further: the chains' lemmas and every `rare_rewrite` step of
  the input become core derivations, but `evaluate` is kept. Constant folding stays one
  computational primitive instead of a derivation over the `to_int` bounds and the Boolean
  axioms. This rung exists to isolate what removing `evaluate` alone costs — it is the only
  difference between this regime and the next.
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

**Equality.** `eq_reflexive` (→ `refl`, a rename), `eq_congruent_pred` (→ `eq_congruent` plus
one `equiv_pos` axiom and a resolution: the predicate rule is the function rule read through an
equivalence), `eq_symmetric` (→ `refl` + `cong`, the flip being a congruence instance since
`cong`'s checker tries all four orientations of a two-argument equality pair) and `not_symm` (the
contraposition of that equivalence). `eq_transitive` and `eq_congruent` are *variants* and left
alone: Carcara checks them with the very functions `trans` and `cong` call, so eliminating them
would trade steps for nothing. Their discharge-subproof reductions live in `core/equality.rs`,
complete and tested, but registered by no regime.

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

**Legacy.** `qnt_cnf` instantiates the premise's quantifier under the conclusion's anchor and
descends to the conclusion's clause by one CNF-axiom step per connective on the path from the body
to the clause's literals, the branch choices guided by the checker's own CNF — a linear resolution
chain, subproof-free but for the closing `bind`.

`bfun_elim` reduces both of the transformations its checker applies, wherever in the premise they
happen, and in the same order.

The *second step* — an application with a non-constant Boolean argument becoming an `ite` over
that argument — is an equivalence, derived per `ite` node of the conclusion's tree by two
subproof-free branches: `equiv_neg1`/`equiv_neg2` and the `true`/`false` axioms give the
conditional literal `(cl (= c ⊤) ¬c)`, the clausal `eq_congruent` carries it into the application,
`ite_then_intro`/`ite_else_intro` select the branch out of the `ite`, `eq_transitive` chains the
two, and the branches resolve on the condition.

The *first step* — a quantifier over Boolean variables becoming the conjunction (or disjunction)
of its `2^k` instances — comes in two derivations, because what a position needs differs. At the
**top of the premise** an implication suffices, and that is the cheap one: `forall_inst` at each
Boolean assignment, `and_neg` to repack, a closing `bind` over the remaining variables. At **any
other position** a congruence has to carry it, and a congruence only carries an equivalence, so
the ← direction is derived too: under an anchor over the quantifier's variables, each instance is
taken out of the packing (`and_pos`) and turned back into the body by a case split on the Boolean
variables, after which the `2^k` branches resolve on those variables and close with the
generalized `bind`. That case split *assumes* its hypotheses, in a discharge subproof: it is a
split on the anchor's own variables, so nothing in it is context-free and the subproof costs no
sharing, and the unit hypotheses `(= x ⊤)` are what let plain `cong` carry the rewriting up the
body and the vanilla `bind` carry it through a binder of the body — which the literal-based route
cannot cross, since neither form of `bind` carries a conditional equality through a quantifier.

An `exists` goes through the quantifier duality: `(∃X.φ)` is `¬(∀X.¬φ)`, and its expansion is the
same equivalence with the instances packed as `(not (or φ[σ]))` — the shape that turns back into
`(∃ȳ. (or φ[σ]))` under the duality, with no De Morgan step in between. The packing then reads
`or_pos`/`or_neg` where the plain case reads `and_neg`/`and_pos`, and nothing else changes.

`cong` carries the equalities to the positions they sit at, `bind` takes them under a quantifier,
and `equiv_pos2` crosses the whole rewriting with the top-level implication. For one Boolean
variable, and counting only the steps the reduction adds: **8** for the top-level implication,
**41** where the equivalence is needed, **60** for an `exists` — which is why the cheap derivation
is kept for the position that can use it.

What is kept: expansions under a `let` or a `choice`/`lambda` binder — `bind` over the `choice`
binder is what the core deliberately leaves out — and a conclusion only *polyeq*-equal to the
expansion, which the `polyeq` pass normalizes upstream. Both are refused explicitly, so the log
names the reason.

The repeated leaves of a reduction — `refl` on one term, the conditional literal for one
condition, the `true`/`false` axioms — are built once per step (`Builder::leaf`), at the step's
own depth where every scope the reduction opens can see them. On a three-argument application,
whose expansion is a tree of seven `ite`s, that takes the reduction from 147 steps to 99.

The clausal equality rules are what keep those branches subproof-free, and the choice is forced.
The hypothesis a branch reasons under is available only as a *literal* — `cong` and `trans` take
their hypotheses as unit premises, so using them would mean assuming the condition and discharging
it, once per `ite` node. `eq_congruent` and `eq_transitive` state the same judgments as
premise-free clauses, so the hypothesis stays a literal; and they cost nothing in the
classification, being *variants* that Carcara checks with the functions `cong`/`trans` call.
Staying subproof-free is also what makes a *ground* branch shareable at all, since both the `core`
pass's memo and the `hoist` pass refuse a derivation that reaches an assumption or a subproof.
Neither picks these up as things stand — the memo is keyed by the *elaborated step's* conclusion,
and `hoist` runs before `core` in the default pipelines — so collecting them is a matter of a
`hoist` stage after `core`.

`ite_intro` derives each ite-subterm's selection tautology `(ite c (= s r₁) (= s r₂))` from the
term-`ite` selection axioms: `ite_then_intro` is `(cl ¬c (= s r₁))` and `ite_else_intro` is
`(cl c (= s r₂))` outright, and `ite_neg1/2` cross them into the tautology — five steps and no
subproof, plus `refl` + `cong` (the flip of an equality is a congruence instance) and `equiv_pos2`
for an equality the rule wrote the other way round, which is veriT's usual orientation. The
equivalence is then packed by `and_neg`/`and_pos` and the iff-introduction pattern. The earlier
derivation assumed the condition and selected the branch with the `rare_rewrite` rules
`ite-true-cond`/`ite-false-cond`, so checking its output needed the RARE file; it does not any
more, and each tautology went from ~31 steps to 13–20.

Since the convenience rules `equiv_intro` and `or_intro` are proposals not yet checked by
Carcara, the pass emits their *expansions* (`equiv_neg1/2` + resolutions, `or_neg` × n +
resolutions + `contraction`) rather than the named rules.

## The `core-expensive` pass

The *expensive* tier is the last elimination stage: rules whose reduction is complete but buys no
checking power, so the other regimes keep them. `--pipeline … core-expensive` applies them:

| rule | becomes |
|---|---|
| `poly_simp` | two `la_generic` bounds closed by `la_disequality` (linear identities only — a nonlinear one keeps the step) |
| `aci_simp` | the two clausal directions of the equivalence, over `and_pos`/`and_neg`/`or_pos`/`or_neg`, closed by the iff-introduction pattern |

Those two are the whole regime (`get_expensive_elaboration_function`), and the rest of the tier is
deliberately not in it. `eq_transitive` and `eq_congruent` are *variants* rather than reducible
rules — checked by the very functions `trans` and `cong` call, so eliminating them would trade
steps for nothing — and `eq_symmetric`/`not_symm` are reduced by the default pass instead, on the
cheap `cong` route. `sko_ex` is *expensive* but its recipe is complete and lives in
`core/skolem.rs`; re-enabling it is an entry in `get_elaboration_function`, not a regime of its
own (see below).

It runs after the regime that handles the other tiers, e.g.

```
carcara elaborate example.smt2.alethe example.smt2 \
    --pipeline hoist polyeq core-taut local core-taut core-expensive reordering prune
```

which leaves a proof over the core vocabulary alone. What each stage costs, in proof size and in
checking time, is measured in the evaluation report.

## Behavior on uncovered shapes

The pass is best-effort and never rejects a proof: a step whose shape a recipe does not cover
(e.g. an `exists`-form quantifier rewrite, a `nary_elim` over a chainable operator, a
`bfun_elim` whose case split would have to cross a binder), or whose reduction
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
