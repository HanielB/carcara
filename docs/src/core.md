# The core Alethe fragment

This chapter defines a *core* set of Alethe rules that is the intended target of Carcara's
elaboration: after the full elaboration pipeline runs, every step of the resulting proof should use
only core rules (or rules whose reduction has deliberately not been applied — see the reducibility
ladder below). This gives elaboration a precise specification, and it shrinks the rule vocabulary
that consumers of elaborated proofs — strict re-checking, and the translation backends to other
formats — have to support.

The classification covers all 120 rules of the Alethe specification, plus the extra rules Carcara
supports beyond the specification. The full rule-by-rule table is in the
[classification](./core/classification.md) subchapter. This chapter explains the criterion behind
the classification, the reduction recipes, and the borderline decisions.

## The reducibility ladder

Every rule sits on a four-level ladder, ordered by how costly it is to push the rule down into the
core:

- **Core**: logical primitives that elaboration targets. Elaborated proofs may freely use them.
- **Reducible**: rules with a reduction meeting the cost criterion R1–R4 below, applied by
  default. Elaboration eliminates all of them from its output.
- **Rare/simplify**: the rewrite vocabulary — the `*_simplify` rules and `rare_rewrite`, whose
  reduction replays a rewrite chain the checker itself computes. Complete and implemented,
  applied only in the regimes that ask for it, since what it removes is a *rewrite interface*
  rather than a rule.
- **Expensive**: rules whose reduction is complete and implemented (the `core-expensive` pass)
  but buys no checking power and costs a discharge subproof or a handful of steps per instance:
  the computational primitives `poly_simp` and `aci_simp`, binder congruence `bind`, and
  `sko_ex`. These are the rules a consumer keeps if it implements their checks, and drops if it
  does not.
- **Variant**: `eq_transitive` and `eq_congruent`, the premise-free clausal forms of `trans` and
  `cong`. Carcara checks them with the very functions those rules call, so they add nothing to
  the trusted base and eliminating them would trade steps for nothing: they are neither counted
  towards the core nor eliminated.

The three non-core levels are *nested elimination stages*: reading a proof from the solver's
output toward the core, elaboration removes the reducible tier first, the rewrite vocabulary
second, and the expensive tier last — each stage paying in proof size and checking time for a
smaller vocabulary and trusted base, and the evaluation prices the stages separately. The one
rule outside every stage is `lia_generic`, which carries no certificate at all: **oracle**.

Orthogonally to the tiers, the classification organizes the rules into *concern categories*:
**structural** (proof structure: `assume`, `subproof`, `hole`), **clausal** (resolution and the
CNF layer), **binder** (quantifiers and binders), **equality & rewriting** (congruence closure and
term rewriting), **arithmetic**, **bitvector**, and **legacy**. The legacy category collects rules that are
placeholders, solver-implementation artifacts, or superseded by more general rules (`lia_generic`,
`qnt_cnf`, `ite_intro`, `bfun_elim`, and `ac_simp`, which is superseded by `aci_simp`); for these
the long-term recommendation remains *removal* — solvers should stop emitting them, or the
specification should replace them with principled counterparts — but four of the five are
meanwhile reducible (only `lia_generic` is not).

Of the 120 specification rules, this classification yields **52 core**, **52 reducible**,
**7 rare/simplify**, **6 expensive**, **2 variants**, and **1 oracle** rule, distributed as
follows:

| category | total | core | reducible | rare/simplify | expensive | variant | oracle |
|---|---|---|---|---|---|---|---|
| structural | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| clausal | 47 | 23 | 22 | 0 | 0 | 2 | 0 |
| binder | 13 | 4 | 7 | 0 | 2 | 0 | 0 |
| equality & rewriting | 25 | 6 | 10 | 6 | 3 | 0 | 0 |
| arithmetic | 13 (+1) | 2 (+1) | 9 | 1 | 1 | 0 | 0 |
| bitvector | 14 | 14 | 0 | 0 | 0 | 0 | 0 |
| legacy | 5 | 0 | 4 | 0 | 0 | 0 | 1 |

The extra rule `evaluate` (constant evaluation of interpreted operators) is part of the core as a
computational primitive: each interpreted SMT-LIB operator gives it a concise definitional
statement, the same justification the core accepts for `bitblast_*` and `distinct_elim`, and it
is the cheapest of the computational checks. The other two computational primitives sit at
*expensive* instead: `poly_simp` reduces (for the linear identities, which is every instance
solvers emit) to two Farkas bounds closed by `la_disequality`, and `aci_simp` to the two clausal
directions of its equivalence. What made this split possible is the adopted axiom triple
`mult_pos`/`mult_neg`/`mult_distrib` — the product sign rules and distributivity over
subtraction — which carries the `la_mult_*` reductions that used to be `poly_simp`'s
load-bearing use (see the arithmetic section below). For every rare/simplify and expensive rule
the [classification](./core/classification.md) records the concrete *reduction scheme* and its
measured cost, so the distance of each rule from the core is visible. The classification also
opens each category with the *proof system* it embodies, first abstractly and then as
concretized by that category's core rules.

The core property is defined *post-pipeline*: intermediate passes may emit non-core rules (e.g.
`reordering` steps, which the final pass of the default pipeline removes); only the output of the
full pipeline must be within core ∪ (whatever elimination stages were not applied). Proofs containing
`hole` or `lia_generic` (without an external solver) can only ever be "core modulo holes".
(`qnt_cnf` was in this class as long as only its spec-side reading — which has no semantics —
was considered; the `core` pass now reduces it against Carcara's implemented semantics.)

## The cost criterion

A rule is classified as reducible only if it has a reduction satisfying all of:

- **R1 (linear)**: the reduction produces O(n) new steps, where n is the size of the step (clause
  length plus premise count), with a small constant;
- **R2 (syntactic)**: every emitted step is checkable by purely syntactic matching — no search, no
  polyequality reasoning, and all resolution pivots explicit;
- **R3 (local)**: the reduction replaces a single proof node without rewriting any of its consumers;
- **R4 (non-circular)**: for each pair of interderivable rules, exactly one side is kept as the
  axiom.

A rule that fails any of R1–R4 stays in the core (if it is a logical primitive) or lands on a
later elimination stage: the *rare/simplify* level if its reduction is a rewrite-chain replay,
the *expensive* level if the reduction is per-instance costly without buying checking power. The
point of R1–R2 is that reducing a rule by default must not make proofs meaningfully larger or
harder to check; the later stages are exactly the reductions that do, priced rather than
forbidden.

## The subproof-discharge vehicle

The main tension in the equality fragment is that the clausal tautologies (`eq_transitive`,
`eq_congruent`, ...) are premise-free clauses usable directly in resolution, while their natural
primitives (`trans`, `cong`, `symm`) take premises. The bridge is the `subproof` rule: a subproof

```
(anchor :step tN)
(assume tN.a0 φ1)
...
(assume tN.ak φk)
... inner steps concluding ψ ...
(step tN (cl (not φ1) ... (not φk) ψ) :rule subproof :discharge (tN.a0 ... tN.ak))
```

discharges its assumptions into exactly the clause shape of the clausal tautologies. This makes the
whole clausal `eq_*` family reducible with linear-size, syntactically-checkable output. It also
dissolves the specification's stated reason for keeping `eq_symmetric` as a primitive (that deriving
it from `symm` "would require a long and tedious use of subproof"): since `eq_symmetric` concludes
an equivalence, the derivation needs one three-step `symm` subproof per direction plus
iff-introduction (`equiv_intro`) — about nine steps, constant and entirely mechanical.

### Worked example: `eq_transitive`

```
(step t1 (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)
```

becomes

```
(anchor :step t1)
(assume t1.a0 (= a b))
(assume t1.a1 (= b c))
(step t1.t1 (cl (= a c)) :rule trans :premises (t1.a0 t1.a1))
(step t1 (cl (not (= a b)) (not (= b c)) (= a c)) :rule subproof :discharge (t1.a0 t1.a1))
```

If a clause literal is flipped with respect to the chain (e.g. `(not (= c b))` where the chain needs
`(= b c)`), a `symm` step over the corresponding assumption is inserted before `trans`, exactly as
the current local elaboration of `trans` does. The reduction is at most 2n steps for a clause of n
literals.

### Worked example: `eq_congruent` and `eq_congruent_pred`

`eq_congruent` follows the same pattern with `cong` as the inner step:

```
(step t1 (cl (not (= a b)) (not (= c d)) (= (f a c) (f b d))) :rule eq_congruent)
```

becomes

```
(anchor :step t1)
(assume t1.a0 (= a b))
(assume t1.a1 (= c d))
(step t1.t1 (cl (= (f a c) (f b d))) :rule cong :premises (t1.a0 t1.a1))
(step t1 (cl (not (= a b)) (not (= c d)) (= (f a c) (f b d))) :rule subproof :discharge (t1.a0 t1.a1))
```

For `eq_congruent_pred` there is a divergence between the specification and practice (see
[divergences](#divergences-from-the-specification) below). In the form veriT produces and Carcara
checks, the step ends in two literals `(not (P t̄)) (P ū)` rather than the single equality
`(= (P t̄) (P ū))` of the specification. The reduction additionally assumes `(P t̄)` and applies
`eq_mp` (an extra reducible rule, itself elaborated to `equiv_pos2` + `resolution`):

```
(step t1 (cl (not (= a b)) (not (= c d)) (not (P a c)) (P b d)) :rule eq_congruent_pred)
```

becomes

```
(anchor :step t1)
(assume t1.a0 (= a b))
(assume t1.a1 (= c d))
(assume t1.a2 (P a c))
(step t1.t1 (cl (= (P a c) (P b d))) :rule cong :premises (t1.a0 t1.a1))
(step t1.t2 (cl (P b d)) :rule eq_mp :premises (t1.a2 t1.t1))
(step t1 (cl (not (= a b)) (not (= c d)) (not (P a c)) (P b d)) :rule subproof
    :discharge (t1.a0 t1.a1 t1.a2))
```

The specification form reduces with just the `cong` inner step, like `eq_congruent`. Either way the
reduction is at most 2n + 4 steps.

## Premise clausification rules: axiom + resolution

The 19 premise-taking clausification rules (`and`, `or`, `not_and`, `not_or`, `xor1/2`,
`not_xor1/2`, `implies`, `not_implies1/2`, `equiv1/2`, `not_equiv1/2`, `ite1/2`, `not_ite1/2`) each
reduce to their premise-free `*_pos`/`*_neg` axiom twin plus one `resolution` step with an explicit
pivot (the premise formula). For example:

```
(step t2 (cl φk) :rule and :premises (t1))          ; t1: (cl (and φ0 ... φn))
```

becomes

```
(step t2.t1 (cl (not (and φ0 ... φn)) φk) :rule and_pos :args (k))
(step t2 (cl φk) :rule resolution :premises (t2.t1 t1) :args ((and φ0 ... φn) false))
```

The exact pairings, derived from the specification's rule statements, are:

| premise rule | axiom | | premise rule | axiom |
|---|---|---|---|---|
| `and` (k) | `and_pos` (k) | | `implies` | `implies_pos` |
| `not_and` | `and_neg` | | `not_implies1` | `implies_neg1` |
| `or` | `or_pos` | | `not_implies2` | `implies_neg2` |
| `not_or` (k) | `or_neg` (k) | | `equiv1` | `equiv_pos2` |
| `xor1` | `xor_pos1` | | `equiv2` | `equiv_pos1` |
| `xor2` | `xor_pos2` | | `not_equiv1` | `equiv_neg2` |
| `not_xor1` | `xor_neg1` | | `not_equiv2` | `equiv_neg1` |
| `not_xor2` | `xor_neg2` | | `ite1` | `ite_pos1` |
| `ite2` | `ite_pos2` | | `not_ite1` | `ite_neg1` |
| `not_ite2` | `ite_neg2` | | | |

Note that the `equiv` family crosses indices: `equiv1` pairs with `equiv_pos2`, `equiv2` with
`equiv_pos1`, `not_equiv1` with `equiv_neg2`, and `not_equiv2` with `equiv_neg1`.

This direction of reduction (premise rule → axiom, rather than the reverse) is forced by R4: each
axiom is interderivable with its premise-taking twin via a subproof, but one side must be primitive.
The premise-free side is the right choice — it has an O(1) syntactic check, and it is usable inside
resolution chains without subproof wrappers.

## The CNF axioms are kept whole

All 19 CNF axioms are core: they are the [def] clauses of the clausal proof system — one
Tseitin-defining clause per connective — with O(1) syntactic checks, and the natural target of
the premise clausification reductions above.

The `xor`, `ite`, and (under a `connective_def` extension with `(φ₁ → φ₂) ≈ (¬φ₁ ∨ φ₂)`)
`implies` families *would* be derivable through `connective_def`: unpack the definition with
`equiv1`/`equiv2` and re-clausify through the `and`/`or` axioms (+ `not_not`), a constant
template of at most ~9 steps per axiom. For `xor_pos1` (`¬X ∨ φ₁ ∨ φ₂`, with `X = (xor φ₁ φ₂)`
and the definition `X ≈ D` where `D = (¬φ₁ ∧ φ₂) ∨ (φ₁ ∧ ¬φ₂)`):

```
t1. (cl (= X D))                 connective_def
t2. (cl ¬X D)                    equiv1 t1
t3. (cl ¬D (¬φ₁∧φ₂) (φ₁∧¬φ₂))    or_pos
t4. (cl ¬(¬φ₁∧φ₂) φ₂)            and_pos (index 1)
t5. (cl ¬(φ₁∧¬φ₂) φ₁)            and_pos (index 0)
t6. (cl ¬X φ₂ φ₁)                resolution t2 t3 t4 t5
```

The classification nevertheless keeps the whole axiom base primitive, for three reasons. First,
uniformity: the 19 axioms are one concept — the [def] clauses — and cutting the base at the
`and`/`or`/`equiv` boundary trades a uniform O(1)-checkable family for derivations whose only
yield is a smaller rule *count* (the checks were already syntactic; R1–R4 measure checking
power, and none is gained). Second, the `implies` derivations would additionally depend on the
proposed `connective_def` `→` extension (divergence item 6) — an adopted-rule dependency the
core should not carry. Third, the elaboration targets these axioms directly: the premise
clausification reductions emit them, so removing them from the core would force every emitted
axiom to be expanded into its `connective_def` derivation, inflating exactly the proofs the core
is meant to keep small.

Within the base, the `equiv` family plays a special structural role: it is the *bootstrap* —
unpacking any `connective_def` equivalence requires `equiv_pos1`/`equiv_pos2` — and the
`and`/`or` families are the Tseitin base every clausification re-clausifies into. The
derivability of the `xor`/`ite`/`implies` families through the definitions remains a useful
*lemma* (the definitions and the axioms agree), not a reduction the elaboration performs.

## Resolution's dual semantics, `weakening`, and `contraction`

The core `resolution` rule carries *two* semantics, both first-class: the **chain** reading — a
chain of binary resolutions with explicit pivots (`:args`), checkable by pure syntactic matching,
which is what the elaboration pipeline produces (pivot inference + uncrowding) and strict mode
checks — and the **RUP** reading — the conclusion is a reverse-unit-propagation consequence of
the premises, checkable by unit propagation (Carcara's `prefer_rup` mode).

Under the RUP reading, `weakening` and `contraction` are *degenerate instances* of `resolution`:
negating the conclusion immediately falsifies the premise clause (same literal set, or a
superset), so the conflict appears before any propagation happens. Both therefore reduce to
`resolution` by a pure rename, zero new steps, and both sit at the *reducible* level: RUP is one
of `resolution`'s two core semantics, so the target of the rename is a core rule as it stands.

What the rename does cost is a change of *which* semantics checks the step — a linear syntactic
scan (containment / dedup) becomes a unit-propagation check — and it is unavailable to a pipeline
targeting the chain reading, under which `weakening` is not derivable at all, since chain
resolution never introduces literals. The two readings pull in opposite directions here:
uncrowding *introduces* explicit `contraction` steps precisely to make the chain reading's
implicit duplicate merging syntactically checkable, while the RUP reading absorbs them silently.
So an elaboration targeting the chain core keeps both rules in its output (as Carcara's does, and
as its elaborated granularity requires, since `resolution` is checked there with explicit
pivots); one targeting the RUP core renames them away.

## Arithmetic: `la_generic` as the computational core

The core's designated *computational* primitive for arithmetic — a rule whose checking is not
syntactic matching but a decision procedure with a fixed, well-understood algorithm — is
`la_generic`: linear consequence, checked by verifying a Farkas certificate. Expanding it into
rewrite chains would blow up unboundedly.

The *ring* axis has two realizations, on opposite sides of the core boundary. Inside the core sits
the `mult_distrib` axiom, distributivity over subtraction — the one ring *law* any reduction
needs, since scaling a comparison relates the scaled difference to the product of multiplier and
original difference. Outside it, at the *expensive* level, sits `poly_simp` (an extra rule, not
among the 120 specification rules): a unit equality between polynomial terms, checked by
ring-normalizing both sides. Nothing in the core depends on it any more — the `la_mult_*`
reductions go through `mult_distrib` — and its own instances reduce (`core-expensive`) to two
Farkas bounds closed by `la_disequality` whenever the identity is linear, which is every instance
the corpus contains. What keeps a consumer implementing its 149-line check is proof size, not
reach: six steps per identity, plus the loss of the genuinely nonlinear instances (a commuted
product, a binomial expansion), which no core rule states.

For consumers that want `rare_rewrite` as the sole rewrite trust anchor, `poly_simp` also admits
an elaboration into rewrite chains (distributivity, associativity/commutativity, constant
folding, cancellation glued by `trans`/`cong`, meeting in the shared normal form) — worst-case
exponential (a product of k binomials expands to 2^k monomials), though benign for the
polynomials solvers emit; the elementary ring rules it needs are listed in
[RARE rules for the rewrite routes](./core/rare-rules.md).

Two LA rules reduce to `la_generic` alone:

- `la_tautology`, first form (a single trivially-unsatisfiable-when-negated inequality literal):
  `la_generic` with coefficient `[1]`.
- `la_tautology`, second form, and `la_totality`: both conclude a *unit clause containing a
  disjunction term* (a historical quirk noted in the specification). `la_generic` concludes a proper
  clause, so the reduction needs a constant-size repackaging from `(cl φ1 φ2)` to
  `(cl (or φ1 φ2))`: two `or_neg` steps and two resolutions plus a `contraction` — six steps total,
  still O(1), and exactly one application of the proposed `or_intro` (see the convenience rules
  below).

`la_disequality` stays **core**, as the category's one non-computational axiom: the negation of
its positive equality literal is a *disequality*, which a Farkas combination cannot consume, and
no other core rule can introduce a positive arithmetic equality at all — the rule *is* order
antisymmetry ([antisym]), the exact counterpart of cvc5's dedicated `ARITH_TRICHOTOMY` rule (see
"Lemmas, not axioms" in the [RARE chapter](./core/rare-rules.md), which also records the
two-coefficient-vector generalization of `la_generic` that would make it derivable).
`la_rw_eq` then reduces to it: the ← direction from `la_disequality`, the → direction by two
Farkas steps, closed by `equiv_intro` (worked example in the classification). `lia_generic` is
special: it is not checkable at all without an external solver, and is classified as
*oracle-reducible* — the existing hole elaboration pass replaces it with a full sub-proof produced
by an external solver.

### Nonlinear multiplication: reducing the `la_mult_*` family

The nonlinear multiplication rules are *reducible*, on an adopted axiom triple stated as
premise-free clauses in `la_disequality`'s style (`mult_pos` first implemented 2026-08-25, the
other two 2026-08-27):

```
(cl ¬(> x 0) ¬(> y 0) (> (* x y) 0))              ; mult_pos  — the positive cone
(cl ¬(< x 0) ¬(> y 0) (< (* x y) 0))              ; mult_neg  — its negative companion
(cl (= (* x (- y z)) (- (* x y) (* x z))))        ; mult_distrib — distributivity over −
```

Each check is O(1) syntactic matching. `mult_pos` is exactly the overlap of the existing
schemas: the binary all-positive instance of `la_mult_sign` (see the extras table below), and
the (`⋈` = `>`, `t3` = `0`) instance of `la_mult_pos`. `mult_neg` exists so that the reduction
scales by the multiplier the step *names*: bridging `(< m 0)` to `(> (- m) 0)` and reusing
`mult_pos` would make the ring identity underneath speak about `(- m)`, which `mult_distrib`
alone no longer closes. And `mult_distrib` is the one ring law the core needs beyond
`la_generic`'s linear reasoning — the identity relating the scaled sides' difference to the
product of multiplier and original difference is nonlinear whenever the multiplier is symbolic.
This triple is what freed `poly_simp` to leave the core: no reduction delegates to ring
normalization any more.

The reductions, all using subproof-discharge plus the implication-term repackaging
(`implies_neg1/2` + two resolutions + `contraction`, the dual of the `la_totality` or-packaging):

- **`la_mult_pos`/`la_mult_neg`, strict forms** — constant template: `la_generic` turns
  `t2 ⋈ t3` into a sign fact about the difference (`(- t2 t3) > 0`), the sign axiom applies to
  `(* t1 (- t2 t3))`, `mult_distrib` distributes it — the step that previously went to
  `poly_simp` — and `la_generic` converts back to `(* t1 t2) ⋈' (* t1 t3)`, the residual
  rearrangement being linear in the products.
- **`≈` form** — no axiom needed at all: `cong` on the multiplication.
- **`≤`/`≥` and disequality forms** — one bounded case split each (`t2 - t3 < 0 ∨ t2 - t3 = 0`
  via `la_generic`/`la_disequality`-style totality), combining the strict and `cong` branches.
- **`la_mult_sign`** (extra rule, `alethe-toolkit` branch) — O(n) fold over the monomial: one
  sign-axiom instance plus one `mult_distrib` distribution per factor, even-exponent factors
  (`v ≠ 0`) costing one bounded case split each.
- **`la_mult_abs_comparison`** (extra rule, `alethe-toolkit` branch) — reduces to the same base
  only once `abs` is handled by a definitional rewrite (`(abs t) ≈ (ite (>= t 0) t (- t))`, e.g. as
  a RARE rule): then each factor costs a bounded case split and the product comparisons chain
  through the axiom. O(n) with a larger constant; contingent on the `abs` rewrite, so it stays
  outside the implemented stages until that primitive is chosen.

The trade is the usual one: elaborated proofs get O(n) scaffolding where solvers emitted one macro
step, and the checker must trust ring normalization (`poly_simp`) as a second computational
primitive alongside Farkas checking.

### Comparison with RESOLUTE's `farkas`

The [RESOLUTE format](https://ultimate.informatik.uni-freiburg.de/smtinterpol/proof-format.html)
concentrates its linear arithmetic in one axiom,
`(farkas c1 (<=? a1 b1) … cn (<=? an bn))`, proving the clause of *negated* atoms
`(cl ¬(a1 <=? b1) … ¬(an <=? bn))` when the positive integer combination
`Σ ci·(ai − bi)` is a constant `c ≥ 0` (strict somewhere if `c = 0`). Since `<=?` ranges over
`<`, `≤`, *and* `=`, the comparison with `la_generic` splits cleanly:

- **On the shared fragment they are the same rule.** Both are "one positive Farkas combination
  refutes the negated clause literals," equation rows included: a `farkas` `=`-row appears in
  the conclusion as a negated equality, exactly `la_generic`'s equation rows. `la_generic`
  allows signed rational coefficients on equations where `farkas` requires positive integers,
  but the sign is recovered by swapping the equation's arguments and the rationals by clearing
  denominators. Alethe keeps all four order operators in both polarities; RESOLUTE normalizes a
  positive `(≤ a b)` literal to `¬(< b a)` — a representational flip over the total order, not
  a power difference.
- **Positive equality literals are the delta — and RESOLUTE's answer is `trichotomy`, not a
  stronger `farkas`.** A `farkas` conclusion contains only negated atoms, so a clause with a
  positive equality literal is not even expressible by it: the extension of
  [spec issue #72](https://github.com/alethe-proofs/specification/issues/72) is strictly
  stronger *as a single rule*. But RESOLUTE never needed that strength in the certificate rule,
  because `(trichotomy a b) ▷ (< a b), (= a b), (< b a)` is its designated positive-equality
  introducer, and `farkas` + `trichotomy` + resolution is complete for clause validity in the
  convex linear fragment: `trichotomy` introduces the equality and one `farkas` step cuts each
  strict branch against the available bounds. That composition covers both the issue-72 case
  (~3 glue steps) *and* antisymmetry — which the extended `la_generic` cannot reach. As single
  rules: `farkas` ≈ base `la_generic` < issue-72 `la_generic`; as systems:
  `farkas`+`trichotomy` ≡ `la_generic`+`la_disequality` ≡ the two-vector generalization (see
  the [RARE chapter](./core/rare-rules.md)), all strictly above issue-72 alone.
- **`la_disequality` *is* `trichotomy`**, literally, modulo the atom flip
  `¬(t1 ≤ t2) ↔ (t2 < t1)`. RESOLUTE independently arrived at the architecture chosen here:
  keep the Farkas engine minimal and put the bounds-to-equality crossing in a dedicated
  premise-free axiom — corroborating [antisym] as a core axiom.
- **Integer packaging is inverted.** `la_generic` tightens strict integer bounds inside the
  rule; `farkas` carries *zero* integrality (mixed Int/Real rows convert to Real) and all of it
  lives in the separate axiom `(total-int a c) ▷ (a ≤ c), (c+1 ≤ a)` — notably applicable to an
  arbitrary integer *term* `a`, making it the split form of a cutting plane (next section).
  Net single-cut power is the same.

The surrounding ecosystems mirror each other too: RESOLUTE's `poly+`/`poly*` play `poly_simp`'s
ring-normalization role, and its `div-low`/`div-high`/`mod-def`/`to_int-low`/`to_int-high`
axioms are exactly the `alethe-toolkit` `*_intro` definitional characterizations (see the
extras table below).

### Completeness for linear arithmetic

Measured against clause validity, the core's arithmetic —
`la_generic` (with integer tightening) + `la_disequality` + `resolution` — is **refutation-complete
for pure-integer LIA**, and the gaps that remain are of a different nature than missing axioms.

Farkas combinations alone are incomplete over the integers — for
`3x + 3y ≥ 1 ∧ 3x + 3y ≤ 2` the LP relaxation is satisfiable, so no single combination refutes
it. Completeness requires Gomory–Chvátal rounding: from derived `t ≥ b` (integer term `t`,
fractional `b`) conclude `t ≥ ⌈b⌉`. `la_generic` derives exactly that, one cut per step, because
a cut is just a clause whose literals the rule already accepts:
`(cl ¬row₁ … ¬rowₘ (>= t ⌈b⌉))` checks by negating the cut literal to `t < ⌈b⌉`,
*integer-tightening* it to `t ≤ ⌈b⌉ − 1 = ⌊b⌋`, and combining against the rows implying
`t ≥ b > ⌊b⌋`. The per-row strict-to-nonstrict tightening `la_generic` already performs is
precisely one rounding application, and emitting the cut as a conclusion literal lets
`resolution` chain rounds. The instance above falls in two steps:

```
(step t1 (cl (not (>= (+ (* 3 x) (* 3 y)) 1)) (>= (+ x y) 1)) :rule la_generic :args ...)
(step t2 (cl (not (<= (+ (* 3 x) (* 3 y)) 2)) (not (>= (+ x y) 1))) :rule la_generic :args ...)
```

plus resolutions. Since every rational polyhedron reaches its integer hull in finitely many
Chvátal rounds (Schrijver), every infeasible pure-LIA system has a *finite* refutation in this
vocabulary. RESOLUTE composes the same power differently: `total-int` on the integer term is
the split form of the cut — branch `t ≤ k ∨ t ≥ k+1`, refute the far branch by `farkas`.

What is genuinely missing:

1. **Efficiency and proof production, not expressiveness.** Chvátal rank can be exponential in
   the encoding (knapsack-style instances), and solvers do not proof-log their
   branch-and-bound/cut reasoning as cut steps. This is the honest status of `lia_generic`: a
   *practicality* hole — nobody produces the cut proofs — not an expressiveness hole in the
   core, which sharpens its classification as removal/oracle.
2. **The mixed Int/Real fragment.** Rounding is sound only when every variable in the row is
   integer-sorted (`la_generic`'s tightening and `total-int` both correctly require this). For
   genuinely mixed constraints one needs splits on the integer subterms only, and there finite
   convergence breaks down (Cook–Kannan–Schrijver: split closures need not converge finitely on
   mixed sets). LIRA is where a real completeness frontier lies, for both formats equally.
3. **`div`/`mod`/`to_int`.** Completeness over full SMT-LIB LIA requires their definitional
   characterizations to reduce to pure inequalities — the toolkit's `*_intro` family, mirrored
   by RESOLUTE's `div`/`mod`/`to_int` axioms.

## The computational primitives, algebraically

The core's non-arithmetic computational primitive is `aci_simp`, and it is natural to ask whether it
and `poly_simp` are two faces of one rule — normalize in whatever algebraic structure the operator
generates — and could be presented, or implemented, hierarchically. They can be *organized* that
way, and the classification below does so. They should not be *merged*.

`aci_simp` picks the top-level operator of each side, flattens nested applications of that same
operator, drops duplicates and the operator's unit, and compares the argument lists as multisets;
anything that is not an application of the top operator is an opaque atom. That is normalization in
a single-operator structure. `poly_simp` builds a linear combination of monomials — a pointer-sorted
multiset of atoms per monomial, a rational coefficient each, reduced mod 2^w for bitvector sorts —
recursing through `+`, `-`, `*`, `to_real` and constant division, and distributing. That is
normalization in a commutative ring. Arranged by the laws each operator obeys:

| level | laws | operators | primitive |
| --- | --- | --- | --- |
| semigroup | A | `concat` | `aci_simp` (compared by equality, not as a multiset) |
| commutative monoid | A, C, unit | — | the shared floor of both primitives |
| bounded semilattice | + idempotence | `and`, `or`, `bvand`, `bvor` | `aci_simp` |
| abelian group of exponent 2 | + self-inverse | `bvxor` | `aci_simp` (A, C, unit only) |
| commutative ring | + distributivity, inverses | `+`, `*`, `bvadd`, `bvmul` | `poly_simp` |
| ℤ/2^w | + quotient by 2^w | the bitvector ring operators | `poly_simp` |

The two meet at the commutative-monoid line and diverge above it in different directions, so neither
subsumes the other. On the ring operators the containment is strict and in `poly_simp`'s favour:
every associativity, commutativity and unit-removal case `aci_simp` accepts for `+`, `*`, `bvadd`
and `bvmul` is a polynomial identity, and `poly_simp` additionally sees through `-`, `to_real` and
constant division, recurses through *mixed* operators where `aci_simp` halts at the first change of
operator, and distributes. Those four operators could therefore be dropped from `aci_simp` with no
loss of proving power. Conversely `poly_simp` rejects every `bvand`/`bvor`/`bvxor` case, which are
atoms to it.

**Why one rule would be the wrong unification.** A merged `alg_simp` would still have to recover the
law set from the operator before normalizing — the operator match the two rules already are — so it
moves a dispatch entry without removing code, and the [TCB measurement](#the-trusted-computing-base-measured)
is unchanged. It would also be expensive: `aci_simp` is the target of the `shuffle`, `nary_elim` and
`and_simplify`/`or_simplify` renames and accounts for 1.35M steps of the elaborated corpus, whose
Boolean path is a flatten, a set dedup and a multiset compare, against a polynomial path that
allocates a monomial per term and does rational arithmetic.

The decisive reason is that the embedding is exponential. Putting `and`/`or` into the ring engine
means the Boolean-ring (algebraic normal form) encoding over 𝔽₂, where `x ∧ y = xy`, `x ⊕ y = x + y`
and `¬x = 1 + x`, so that

```
x₁ ∨ … ∨ xₙ  =  1 + (1 + x₁)(1 + x₂) ⋯ (1 + xₙ)
```

expands to 2ⁿ monomials, which the polynomial normalizer would genuinely build. A check that is
linear in the term size today would become exponential in the arity of a disjunction — on a corpus
where wide disjunctions are precisely what `aci_simp` is used for. What one would buy is a *complete*
decision procedure for the propositional fragment, far more than the coarse ACI check the core
wants, at a price the core should not pay. The semilattice level is not a degenerate case of the
ring level; it is a quotient the ring cannot represent compactly, and that is the substantive content
of the hierarchy.

The hierarchy earns its keep in the checker rather than in the rule set. Idempotence is a semilattice
law and not a monoid law, and applying it uniformly across the associative operators lets `aci_simp`
prove `(= (+ x x) x)` and `(= (bvxor a a) a)` — a soundness bug that was present until the split was
written down explicitly as `is_idempotent` in `carcara/src/checker/rules/simplification.rs`. The
same reading suggests one cheap extension, not adopted here: `bvxor`'s law is self-inversion,
`x ⊕ x = 0`, so keeping occurrence counts mod 2 instead of deduplicating would let `aci_simp` prove
`(= (bvxor a b a) b)`. The full analysis is recorded in
`investigations/2026-08-25-aci-poly-algebraic-hierarchy.md`.

## Other reductions

- `eq_reflexive` is `refl` with an empty context: a rename, one step.
- `eq_symmetric` concludes an equivalence, so it reduces to two `symm` subproofs (one per
  direction) closed by `equiv_intro` — about nine steps.
- `not_symm` needs only one direction: a `symm` subproof plus one resolution against the
  premise — four steps.
- `tautology` concludes exactly `⊤`, so it reduces to a premise-free `true` step. Note this drops
  the premise from the proof DAG (relevant for slicing).
- `th_resolution` is, per the specification, the same rule as `resolution`; elaboration normalizes
  the name.
- `shuffle` is subsumed by `aci_simp`: multiset equality of arguments under a commutative operator
  is a special case of ACI equivalence, `shuffle`'s operators (`+`, `*`, `and`, `or`) are all in
  `aci_simp`'s operator list, and the conclusion shape is identical — so the reduction is a pure
  rename, zero new steps, and `shuffle` sits at the *reducible* level with `aci_simp` as its
  target. The check does coarsen — `aci_simp` also collapses idempotent duplicates and identity
  elements, so the renamed step admits conclusions the multiset check would reject — but the
  admitted conclusions are all sound, and `aci_simp` is the designated ACI primitive the step
  lands on anyway.
- `nary_elim` also reduces to `aci_simp` by a rename, for the associative-commutative operators:
  the n-ary application and its binary nesting flatten to the same argument multiset, so ACI
  normalization proves the equality directly. Only the chainable (`=`, comparisons) and
  non-commutative (`→`, `-`) cases stay outside this route — those keep the
  binary-associativity `rare_rewrite` chain as their scheme.
- `reordering` is already eliminated by the reordering elaboration pass, which recomputes downstream
  conclusions instead.
- `multi_rare_rewrite` reduces to a chain of `rare_rewrite` steps glued with `trans`/`cong`
  scaffolding (the exact recipe depends on the rule-position semantics and should be validated when
  implemented).

## Proposed convenience rules: `equiv_intro` and `or_intro`

Two derivation patterns recur throughout the reductions of this chapter, and are worth naming as
explicit rules — *proposed* additions that are themselves **reducible**, so they enlarge the
vocabulary only as compact abbreviations, never the trust base:

- **`equiv_intro`** — iff-introduction: from `(cl ¬A B)` and `(cl A ¬B)`, conclude
  `(cl (= A B))`. Reducible via the clausal derivation used throughout this chapter: resolve the
  premises against `equiv_neg2` (`(cl (= A B) A B)`) and `equiv_neg1` (`(cl (= A B) ¬A ¬B)`) with
  two contractions — ~7 steps, all syntactic. Every two-implication template (the quantifier
  rewrites, `onepoint`, the `xor`/`ite`/`implies` axiom derivations) ends in exactly this
  pattern, so naming it shrinks elaborated proofs by a constant factor at their most repetitive
  point.
- **`or_intro`** — packing a clause into its disjunction term: from `(cl l₁ … lₙ)`, conclude
  `(cl (or l₁ … lₙ))` — the inverse of the `or` rule's deconstruction. Reducible via `or_neg` on
  each literal + n resolutions + `contraction`, O(n) and syntactic. This is the packaging step of
  the `la_totality`/`la_tautology` reductions, of the implication-term packaging, and of the
  generalized `bind`'s unit-closure discipline (packing a multi-literal conclusion before closing
  over the anchor). The name parallels the existing extra `and_intro`.

Both sit at the reducible level: an elaboration may emit them freely (consumers reduce them on
demand by the recipes above), or expand them inline when targeting the strict core.

## Skolemization: one rule suffices

`sko_ex` and `sko_forall` are duals through the quantifier duality that `connective_def` already
provides (`∃x̄.φ ≈ ¬∀x̄.¬φ` and vice versa), so only one needs to be primitive. The
classification keeps `sko_forall` and reduces `sko_ex` by a constant template, independent of the
number of variables:

1. from `sko_ex`'s premise `Γ, ctx ▷ φ ≈ ψ`, derive `¬φ ≈ ¬ψ` by `cong`;
2. apply `sko_forall` to `∀x̄.¬φ`, concluding `∀x̄.¬φ ≈ ¬ψ`;
3. `cong` (¬) gives `¬∀x̄.¬φ ≈ ¬¬ψ`;
4. chain with `connective_def` (`∃x̄.φ ≈ ¬∀x̄.¬φ`) and a `¬¬ψ ≈ ψ` rewrite through `trans`.

Six steps for any n. The direction is conventional — the symmetric template reduces `sko_forall`
to `sko_ex` — and R4 just requires picking one.

Two prerequisites make this exact, both worth raising with the specification:

- **The spec's statement of `sko_forall` is erroneous for n > 1.** It maps every
  `xᵢ ↦ εxᵢ.¬φ` over the bare body, leaving the later variables `x_{i+1}…xₙ` free in the choice
  term with nothing to bind them. Implementations use the well-formed sequential form: Carcara's
  checker (`checker/rules/subproof.rs`) expects `εxᵢ.¬(∀x_{i+1}…xₙ.φ')`, remaining variables
  re-quantified and earlier skolemizations substituted — the exact dual of `sko_ex`'s
  `εxᵢ.(∃x_{i+1}…xₙ.φ')`. The spec text should be fixed to the sequential form.
- **Binder congruence for `choice` is part of `bind`** — if the `sko_ex` reduction is wanted at
  all. The witnesses of a `sko_ex` step (`εxᵢ.(∃…φ)`) and those produced by the dual route
  (`εxᵢ.¬(∀…¬φ)`) differ by a duality rewrite *under* `ε`, so bridging them needs congruence
  under the choice binder. This is the *only* thing that needs it: solvers never write a `bind`
  over `choice`, so a core that keeps `sko_ex` never reshapes a witness and never asks the
  question. Rather than a separate
  primitive (the earlier divergence-5 proposal), the `bind` rule is read as *binder-generic*:
  from `Γ, x↦y ▷ φ ≈ ψ` conclude `Γ ▷ εx.φ ≈ εy.ψ`, with exactly the mechanics it already has
  for `∀`/`∃` — which is in fact how Carcara's `bind` checker is implemented, so no new rule is
  involved. With it, the `¬∀¬`/`∃`-shaped witnesses of existing proofs are bridged by
  `connective_def` + `not-not` reasoning under the binder, and the reduction applies to
  already-produced steps, not just to new proofs that take the duality detour from the start —
  the `core` pass implements exactly this (all corpus instances reduce; see the elaboration
  chapter).

## Deriving the quantifier rewrites from Skolemization

The quantifier rewrites (`qnt_simplify`, `qnt_join`, `qnt_rm_unused`, the miniscope rules) do not
need binder-pattern RARE after all. The route is inspired by SMTInterpol's
[RESOLUTE proof format](https://ultimate.informatik.uni-freiburg.de/smtinterpol/proof-format.html),
whose entire quantifier fragment is four premise-free clausal axioms over the choice operator —
`forall-` being exactly Alethe's `forall_inst`, and the introduction forms being ε-critical
axioms with `choose`-witnesses. The key observation is that the ε-critical clause is
*Skolemization in clausal form* — the → direction of `sko_forall`'s equivalence — and therefore
needs no new primitive: keeping Skolemization in the core, the clause is a constant derived
template. For any `φ`, with witness `c = (choice ((x S)) (not φ))`:

```
(anchor :step tk :args ((:= (x S) c)))
(step tk.t1 (cl (= φ φ[c])) :rule refl)                          ; refl applies the context
(step tk (cl (= (forall ((x S)) φ) φ[c])) :rule sko_forall)
(step tk' (cl (forall ((x S)) φ) (not φ[c])) :rule equiv2 :premises (tk))
```

Four steps, and the **∀-ε-clause** `(cl ∀x.φ, ¬φ[c])` is available for resolution reasoning at
any witness. (`equiv1` instead of `equiv2` yields the elimination direction
`(cl ¬∀x.φ, φ[c])`, though `forall_inst` already provides it at arbitrary terms. The n-ary form
works the same way with `sko_forall`'s sequential witnesses; the ∃-variants derive through the
quantifier-duality instance of `connective_def`, which stays axiomatic as the R4 orientation —
it bootstraps all ∃-reasoning, including `sko_ex`'s reduction.)

With the ε-clause template in hand, each quantifier rewrite falls to a two-implication derivation
closed by iff-introduction (the proposed `equiv_intro`, itself reducible), using only
`forall_inst`, the CNF axioms, and resolution:

- **`qnt_rm_unused`** (`∀xy.φ ≈ ∀x.φ`, `y` unused): → is the ε-clause of the small quantifier
  resolved against `forall_inst` of the large one at `(c, d)`; ← symmetric. Constant.
- **`qnt_join`**: same shape with nested ε-clauses for the merged prefix. Constant.
- **`qnt_simplify`** (`∀x̄.⊤ ≈ ⊤`): ε-clause + `true`, three steps.
- **`miniscope_distribute`/`miniscope_ite`**: the pattern threaded through `and_pos`/`and_neg`
  (resp. the `ite` axioms), one block per conjunct/branch — see the worked example below.
- **`miniscope_split`**: ditto per disjunct; its variable partitioning, program-like as a static
  RARE pattern, is unproblematic here — the clausal route instantiates witnesses per instance and
  needs no pattern.

Three remarks on cost and style. Every derived step is a syntactic instance check (the checker
performs the substitution directly, as for `forall_inst`, rather than stepwise through a context).
The witness terms embed copies of the bodies, so proof *text* grows quadratically without
`let`-sharing — RESOLUTE's mitigation, and the reason the `sko_*` subproof forms (which confine
witnesses to the context) remain the compact packaging for Skolemization itself. And the
derivations are clausal where the binder category is otherwise equational: the equivalences are
derived as clauses and injected into rewriting chains via iff-introduction — the same benign
context-mixing as the `onepoint` template.

### Generalizing `bind` (proposed)

The witness blowup disappears entirely under one further proposal (divergence 8): generalize
`bind` so that ∀-introduction is one of its instances. The anchor takes *both* fresh variables
and substitution entries (capture-avoiding), and the inner derivation may conclude *any* clause:

```
(anchor :step t :args ((y1 S1) ... (yk Sk) (:= (x1 T1) u1) ... (:= (xm Tm) um)))
... steps concluding (cl l1 ... ln) ...
(step t (cl L1 ... Ln') :rule bind)
```

The conclusion is computed literal-wise, in two forms:

- **Transformation literals** — equalities `(= a b)` whose left side mentions substituted
  variables — close as today: `(= (Q x̄ₐ ȳₐ. a) (Q ȳᵦ. b))`, with each binder set *miniscoped*
  to the variables actually free on that side (unused variables may be dropped — `qnt_rm_unused`
  built into the rule; binding the full declared sets remains legal, so every current `bind`
  instance is unchanged).
- **The generalization literal** — at most *one* non-equality literal closes as `∀Ȳ.l`, with `Ȳ`
  a declared subset of the fresh variables; the remaining literals pass through untouched, and are
  therefore `ȳ`-free by scoping. Miniscoping thus applies only to binder *sets* (the equality
  sides above, and the closure's declared subset), never to clause structure. This restriction
  loses no generality: a multi-literal conclusion is packed into its disjunction *term* before
  closing (`or_neg` + resolutions + `contraction`, O(n) — i.e. one `or_intro`), and side
  hypotheses are assumed *outside* the anchor — which is how the elaboration templates are
  structured anyway, so in practice the closure applies to a unit conclusion, exactly like the
  spec's existing binder subproofs. ∀-introduction is the no-substitutions instance.

Vanilla `bind` is the instance with renaming substitutions and a single equality literal — the
conclusion coincides syntactically with today's rule, with zero extra steps. Checking stays
syntactic and linear (see "Checking without free-variable computation" below). The
capture story is carried entirely by the side conditions: the substitution must be
capture-avoiding, fresh names distinct under nesting.

**Where arbitrariness must stop.** For a transformation literal, the *equivalence* conclusion is
sound only under a discipline on the substituted terms `ū`: with arbitrary `ū`, only the ←
direction holds (`Qȳ.b` covers just the instances `a[ū]`, not all `x̄`). The disciplines are
exactly the existing binder rules:

| discipline on `ū` | rule |
|---|---|
| renamings into the fresh variables | `bind` (vanilla instance) |
| ε-witnesses of the sequential shape | `sko_forall` / `sko_ex` |
| points justified by the guarded-occurrence grammar | `onepoint` |

So the generalization recasts the binder category as **one anchor-closing scheme parameterized by
the substitution discipline** — [α/congr-bind], [ε], and [qe-point] are the three justifications
for the same closing step, and [gen] is the discipline-free case. Congruence under `choice` is
handled by `bind` itself, read as binder-generic (the α/congruence discipline over `ε`; formerly
the separate divergence-5 proposal): `ε` has no elimination/introduction rules, so this
congruence-only instance is all the choice binder ever needs.

#### Checking without free-variable computation

Restricting miniscoping to binder sets makes checking free of free-variable computation: only the
*shapes* of the arguments and of the subproof's conclusion are inspected, and the quantifier
prefixes are *built* from them.

- **Declared binder sets, positional construction**: the closure's prefix `Ȳ` and each
  transformation literal's binder sets are declared (in the conclusion as written); the checker
  verifies each is a subset of the corresponding anchor sets *in anchor order* — pure list checks
  — and compares the positionally built conclusion with the written one syntactically.
- **Scoping does the rest, for free.** With anchor variable names required to be *fresh for the
  ambient scope* — a symbol-table membership test at anchor time, not a term traversal — the
  parser's ordinary well-scopedness discipline enforces every remaining condition: a pass-through
  literal that uses a fresh variable has it *unbound*, and is rejected before the rule checker
  runs; a *dropped* binder variable that was actually used is caught the same way; and a declared
  variable a literal does not use is a vacuous binder, hence harmless (the checker is
  deliberately permissive about it — `qnt_rm_unused`-flavored slack).
- **The unsound shape is inexpressible.** With grouping, the one shape scoping cannot reject is
  the split of `∀` over `∨` — `(cl (∀y.l₁) (∀y.l₂))` from `(cl l₁(y) l₂(y))`. With a single
  closure literal there is nothing to split: a second `∀y` would have to introduce a shadowing
  name (rejected by freshness), and any stray use of the real `y` is unbound.

Free-variable computation thus moves entirely to the *producer*, which chooses tight prefixes at
elaboration time (and knows the free variables anyway); the checker's work is subset checks,
positional construction, and syntactic comparison — plus the scope enforcement its parser already
performs incrementally. The one assumption to state explicitly: a checker whose parser is lax
about unbound variables would inherit that obligation in the rule checker.

#### What the generalization buys

First, what it does *not* buy: proving power. Apart from choice congruence (the binder-generic
`bind` over `ε`),
**every instance of the generalized `bind` is derivable from the core** — the rule is
*admissible*, with `sko_forall` and `forall_inst` carrying exactly the two directions of its
closure. Per instance — anchor variables `x̄` with substitution entries, inner subproof deriving
`φ ≈ ψ`, closure `(∀x̄_φ. φ) ≈ (∀x̄_ψ. ψ)`:

- **→** Skolemize the target `∀x̄_ψ. ψ` by the ∀-ε-clause template (`refl` under the witness
  context + `sko_forall` + `equiv2`), reducing it to `ψ` at the sequential ε-witnesses; obtain
  `φ` at the corresponding points by `forall_inst` on the premise quantifier (the witness images
  under the anchor's substitution); *replay* the inner derivation with the witnesses substituted
  for `x̄`; cross with `eq_mp`. Substitution entries `x ↦ t` are transported by the
  `extract_points`-style `symm`/`cong`/`eq_mp` steps of the `onepoint` elaboration;
  declared-but-vanished variables take dummy `choose` witnesses.
- **←** Symmetric, and `equiv_intro` closes the equivalence; existential instances route through
  the `sko_ex`-via-duality reduction first.

The one load-bearing assumption is that the inner derivation *can* be replayed: every core rule
is schematic, so its instances remain valid under uniform substitution of closed terms (the
ε-witnesses) for the fresh anchor variables, including under nested binders since the witnesses
are closed — the same stability fact the worked example below exercises. The residue is exactly
choice congruence: `sko_forall` speaks only about `∀` (and `∃` through duality), so a context
used to rewrite under a `choice` binder has no Skolemization to route through — which is why the
binder-generic reading of `bind` (formerly the separate divergence-5 proposal) carries genuine
content there, outside both the generalization's closing step and this fallback.

Admissibility settles the proposal's status in the strongest possible way: divergence 8 is a
pure *proof-engineering* proposal — the safest kind to adopt, since a checker can always fall
back to expansion — and the binder category's core is closed as it stands, with nothing in the
reducible tier secretly depending on the generalization being accepted.

The value is therefore proof-theoretic, and sharper than "shorter proofs":

1. **It closes a symbolic derivation instead of replaying it.** The generalization adds *one
   step* on top of a derivation carried out at a symbolic variable; the Skolemization fallback
   cannot close anything symbolic — it must run the entire inner derivation substituted at the
   witness, pushing `x := c` through every step (compounding for nested closures).
2. **ε-free proofs of ε-free facts.** The fallback smuggles choice terms into elaborations of
   statements that mention no choice at all; the generalization keeps the quantifier rewrites
   inside the choice-free fragment — which matters for reconstruction targets without Hilbert
   choice, and reserves `sko_*` for genuine Skolemization content.
3. **Linear checking, not just linear text.** The fallback's `forall_inst`/`sko_forall` steps are
   substitution-instance checks over terms embedding body copies, so checking *time* scales with
   witness size; the generalization's closures are positional shape comparisons, independent of
   body size.

Side by side, on the inner closure of the worked example below — the generalized `bind` (left
column of steps) versus the fallback for the very same conclusion:

```
; generalized bind: three symbolic steps, one closing step
(anchor :step s :args ((x S)))
(step s.t1 (cl (not (forall ((x S)) (and P Q))) (and P Q)) :rule forall_inst :args (x))
(step s.t2 (cl (and P Q)) :rule resolution :premises (h s.t1))
(step s.t3 (cl P)         :rule and :premises (s.t2) :args (0))
(step s (cl (forall ((x S)) P)) :rule bind)                  ; unit closure over {x}
```

```
; fallback: the same three steps REPLAYED at c = (choice ((x S)) (not P)),
; plus the epsilon-clause of the target quantifier
(step s.t1 (cl (not (forall ((x S)) (and P Q))) (and P[c] Q[c])) :rule forall_inst :args (c))
(step s.t2 (cl (and P[c] Q[c])) :rule resolution :premises (h s.t1))
(step s.t3 (cl P[c])            :rule and :premises (s.t2) :args (0))
(anchor :step s.t4 :args ((:= (x S) c)))
(step s.t4.t1 (cl (= P P[c])) :rule refl)
(step s.t4 (cl (= (forall ((x S)) P) P[c])) :rule sko_forall)
(step s.t5 (cl (forall ((x S)) P) (not P[c])) :rule equiv2 :premises (s.t4))
(step s.t6 (cl (forall ((x S)) P)) :rule resolution :premises (s.t5 s.t3))
```

Four steps against seven — but more importantly, on the left the three inner steps are untouched
by the closure and mention no witness, while on the right *the same three steps* reappear with
`P[c]`, `Q[c]` spelled out (each a copy of the body inside `c`), and two further steps carry the
witness again. Scale `P` and `Q` up, or nest closures, and the two routes diverge quadratically
in both text and checking time, while the left column's cost is unchanged.

Further consequences:

- the quantifier-rewrite elaborations become **witness-free and linear** — quantifiers are
  eliminated by `forall_inst` *at the anchor variable itself* and reintroduced by the generalized
  `bind`'s closure (worked example below); the Skolemization route remains the proposal-free
  fallback;
- `qnt_simplify` is four steps: `anchor x`; `true`; close by generalization; iff-introduction —
  no `ε` anywhere — and `qnt_rm_unused` instances are absorbed into the rule itself;
- `onepoint`'s inner-quantifier case becomes direct generalization, dropping its `∀ȳ.⊤ ≈ ⊤`
  detour;
- mixed instances add genuinely new expressive power: an equality literal *plus* `ȳ`-free side
  literals concludes a conditional rewrite under a binder, `(cl (= (Qx̄.φ) (Qȳ.ψ)) ¬p)` — today
  inexpressible without detours;
- the abstract proof system reads: [inst] and [gen] as the ∀-elimination/introduction pair, with
  [α/congr-bind], [ε], [qe-point] as the three substitution disciplines of the same closing
  scheme, and `choice` congruence as the residue.

### Worked example: elaborating `miniscope_distribute`

The instance to elaborate, written out in full (with `P`, `Q` schematic bodies that may mention
`x`):

```
(step t (cl (= (forall ((x S)) (and P Q))
               (and (forall ((x S)) P) (forall ((x S)) Q)))) :rule miniscope_distribute)
```

With the generalized `bind`, the derivation is organized entirely by the anchor mechanism — two
assume/discharge subproofs, one per direction, each using variables-only anchors whose closing
steps are generalized-`bind` instances: no substitutions, a *unit* inner conclusion, and the
closure prefix `{x}` declared in the concluded quantifier. Auxiliary patterns appear only through
their named rules (`and`, `and_intro`, `equiv_intro`), never inline-expanded — reductions
compose. No choice term appears anywhere:

```
; direction →: assume the left-hand side; each conjunct's quantifier by unit closure
(anchor :step t.p1)
(assume t.p1.h (forall ((x S)) (and P Q)))
(anchor :step t.p1.t1 :args ((x S)))
(step t.p1.t1.t1 (cl (not (forall ((x S)) (and P Q))) (and P Q))
    :rule forall_inst :args (x))
(step t.p1.t1.t2 (cl (and P Q)) :rule resolution :premises (t.p1.h t.p1.t1.t1))
(step t.p1.t1.t3 (cl P) :rule and :premises (t.p1.t1.t2) :args (0))
(step t.p1.t1 (cl (forall ((x S)) P)) :rule bind)            ; unit closure over {x}
(anchor :step t.p1.t2 :args ((x S)))
(step t.p1.t2.t1 (cl (not (forall ((x S)) (and P Q))) (and P Q))
    :rule forall_inst :args (x))
(step t.p1.t2.t2 (cl (and P Q)) :rule resolution :premises (t.p1.h t.p1.t2.t1))
(step t.p1.t2.t3 (cl Q) :rule and :premises (t.p1.t2.t2) :args (1))
(step t.p1.t2 (cl (forall ((x S)) Q)) :rule bind)            ; unit closure over {x}
(step t.p1.t3 (cl (and (forall ((x S)) P) (forall ((x S)) Q)))
    :rule and_intro :premises (t.p1.t1 t.p1.t2))
(step t.p1 (cl (not (forall ((x S)) (and P Q)))
               (and (forall ((x S)) P) (forall ((x S)) Q)))
    :rule subproof :discharge (t.p1.h))

; direction ←: assume the right-hand side; rebuild the body under one anchor
(anchor :step t.p2)
(assume t.p2.h (and (forall ((x S)) P) (forall ((x S)) Q)))
(anchor :step t.p2.t1 :args ((x S)))
(step t.p2.t1.t1 (cl (forall ((x S)) P)) :rule and :premises (t.p2.h) :args (0))
(step t.p2.t1.t2 (cl (not (forall ((x S)) P)) P) :rule forall_inst :args (x))
(step t.p2.t1.t3 (cl P) :rule resolution :premises (t.p2.t1.t1 t.p2.t1.t2))
(step t.p2.t1.t4 (cl (forall ((x S)) Q)) :rule and :premises (t.p2.h) :args (1))
(step t.p2.t1.t5 (cl (not (forall ((x S)) Q)) Q) :rule forall_inst :args (x))
(step t.p2.t1.t6 (cl Q) :rule resolution :premises (t.p2.t1.t4 t.p2.t1.t5))
(step t.p2.t1.t7 (cl (and P Q)) :rule and_intro :premises (t.p2.t1.t3 t.p2.t1.t6))
(step t.p2.t1 (cl (forall ((x S)) (and P Q))) :rule bind)    ; unit closure over {x}
(step t.p2 (cl (not (and (forall ((x S)) P) (forall ((x S)) Q)))
               (forall ((x S)) (and P Q)))
    :rule subproof :discharge (t.p2.h))

; close with the proposed convenience rule
(step t (cl (= (forall ((x S)) (and P Q))
               (and (forall ((x S)) P) (forall ((x S)) Q))))
    :rule equiv_intro :premises (t.p1 t.p2))
```

Twenty steps, all unit-clause reasoning under the hypotheses, linear in the original step —
the anchors carry all the binding structure, `forall_inst :args (x)` at the anchor's own variable
does the elimination (note that `P` and `Q` appear *unchanged* throughout: instantiating at the
anchor variable is a no-op substitution), and each closure is the single-literal case of the
generalized `bind`, so its checking is exactly the positional shape comparison of the previous
subsection. Without the generalization, the same derivation runs through the Skolemization
fallback: each variables-only anchor is replaced by explicit reasoning at the counterexample
witness of the quantifier being introduced (`sko_forall`'s equivalence at `c = εx.¬φ` via `refl`
+ `equiv2`), which is what makes that route's proof text quadratic — the two directions need
*different* witnesses, since `(forall ((x S)) P) ≈ P[c₃]` is not valid, so the clausal glue is
intrinsic either way. The n-ary and multi-variable cases iterate the same shape.

#### The same derivation in RESOLUTE

For contrast, the same equivalence in SMTInterpol's RESOLUTE format. There are no subproofs and
no anchors: the proof is a flat resolution DAG over clauses-as-*sets* (duplicate literals merge
silently), hypothetical reasoning rides along as extra literals, and the quantifiers are handled
by the `choose`-witness axioms. Write `P[c]` for `P` with `x` substituted by `c`, and abbreviate
the three witnesses (RESOLUTE's `let` mechanism):

```
cP  = (choose ((x S)) (not P))
cQ  = (choose ((x S)) (not Q))
cPQ = (choose ((x S)) (not (and P Q)))
```

Each line binds a named proof (`let-proof`) of the clause shown in the comment (`+`/`-` mark
literal polarity):

```
; direction →
c1 = (forall+ (forall ((x S)) P))                 ; ( +(forall ((x S)) P)  -P[cP] )
c2 = (forall- (cP) (forall ((x S)) (and P Q)))    ; ( -(forall ((x S)) (and P Q))  +(and P[cP] Q[cP]) )
c3 = (and- 0 (and P[cP] Q[cP]))                   ; ( -(and P[cP] Q[cP])  +P[cP] )
d1 = (res P[cP] (res (and P[cP] Q[cP]) c2 c3) c1) ; ( -(forall ((x S)) (and P Q))  +(forall ((x S)) P) )
c4 = (forall+ (forall ((x S)) Q))                 ; ( +(forall ((x S)) Q)  -Q[cQ] )
c5 = (forall- (cQ) (forall ((x S)) (and P Q)))    ; ( -(forall ((x S)) (and P Q))  +(and P[cQ] Q[cQ]) )
c6 = (and- 1 (and P[cQ] Q[cQ]))                   ; ( -(and P[cQ] Q[cQ])  +Q[cQ] )
d2 = (res Q[cQ] (res (and P[cQ] Q[cQ]) c5 c6) c4) ; ( -(forall ((x S)) (and P Q))  +(forall ((x S)) Q) )
c7 = (and+ (and (forall ((x S)) P) (forall ((x S)) Q)))
                                                  ; ( +(and (forall ((x S)) P) (forall ((x S)) Q))
                                                  ;   -(forall ((x S)) P)  -(forall ((x S)) Q) )
d3 = (res (forall ((x S)) Q) (res (forall ((x S)) P) c7 d1) d2)
                                                  ; ( -(forall ((x S)) (and P Q))
                                                  ;   +(and (forall ((x S)) P) (forall ((x S)) Q)) )
                                                  ; the duplicated negative literal merged: sets

; direction ←
c8  = (forall+ (forall ((x S)) (and P Q)))        ; ( +(forall ((x S)) (and P Q))  -(and P[cPQ] Q[cPQ]) )
c9  = (and- 0 (and (forall ((x S)) P) (forall ((x S)) Q)))
                                                  ; ( -(and (forall ((x S)) P) (forall ((x S)) Q))
                                                  ;   +(forall ((x S)) P) )
c10 = (forall- (cPQ) (forall ((x S)) P))          ; ( -(forall ((x S)) P)  +P[cPQ] )
c11 = (and- 1 (and (forall ((x S)) P) (forall ((x S)) Q)))
                                                  ; ( -(and (forall ((x S)) P) (forall ((x S)) Q))
                                                  ;   +(forall ((x S)) Q) )
c12 = (forall- (cPQ) (forall ((x S)) Q))          ; ( -(forall ((x S)) Q)  +Q[cPQ] )
c13 = (and+ (and P[cPQ] Q[cPQ]))                  ; ( +(and P[cPQ] Q[cPQ])  -P[cPQ]  -Q[cPQ] )
d4  = (res Q[cPQ] (res P[cPQ] c13 (res (forall ((x S)) P) c9 c10))
                  (res (forall ((x S)) Q) c11 c12))
                                                  ; ( -(and (forall ((x S)) P) (forall ((x S)) Q))
                                                  ;   +(and P[cPQ] Q[cPQ]) )
d5  = (res (and P[cPQ] Q[cPQ]) d4 c8)             ; ( +(forall ((x S)) (and P Q))
                                                  ;   -(and (forall ((x S)) P) (forall ((x S)) Q)) )

; equivalence introduction
e1 = (=+1 (= (forall ((x S)) (and P Q))
             (and (forall ((x S)) P) (forall ((x S)) Q))))
                                                  ; ( +(= …)  +(forall ((x S)) (and P Q))
                                                  ;           +(and (forall ((x S)) P) (forall ((x S)) Q)) )
e2 = (=+2 (= (forall ((x S)) (and P Q))
             (and (forall ((x S)) P) (forall ((x S)) Q))))
                                                  ; ( +(= …)  -(forall ((x S)) (and P Q))
                                                  ;           -(and (forall ((x S)) P) (forall ((x S)) Q)) )
s1 = (res (and (forall ((x S)) P) (forall ((x S)) Q)) e1 d5)
                                                  ; ( +(= …)  +(forall ((x S)) (and P Q)) )
s2 = (res (forall ((x S)) (and P Q)) e2 d3)       ; ( +(= …)  -(forall ((x S)) (and P Q)) )
     (res (forall ((x S)) (and P Q)) s1 s2)       ; ( +(= (forall ((x S)) (and P Q))
                                                  ;       (and (forall ((x S)) P) (forall ((x S)) Q))) )
```

The rule-by-rule correspondence is exact: `forall-` is `forall_inst`; `forall+` is the ∀-ε-clause
(an *axiom* in RESOLUTE, a four-step `sko_forall` derivation in Alethe); `and- i`/`and+` are
`and_pos`/`and_neg`; `or+ i`/`or-` are `or_neg`/`or_pos`; `=+1`/`=+2` are `equiv_neg2`/
`equiv_neg1`, so the closing block is `equiv_intro`'s expansion written inline. The structural
differences are equally visible: RESOLUTE's three `choose` witnesses each embed a copy of the
bodies (the quadratic-text cost the generalized `bind` avoids entirely), its set-clauses merge
duplicate literals silently where Alethe's chain reading demands explicit `contraction`, and the
absence of subproofs means the two hypotheses survive as carried literals through every
resolution instead of being discharged once at an anchor boundary.

### Instantiation is not Skolemization

A natural follow-up is whether `forall_inst` could itself be phrased via `sko_forall`. It cannot:
Skolemization provides `∀x.φ ≈ φ[c]` at the *one designated* witness `c = εx.¬φ`, and reaching
`φ[t]` for an arbitrary term requires `φ[c] → φ[t]` — contraposed, Hilbert's term-level critical
axiom `ψ[t] → ψ[εx.ψ]`. Within Alethe that axiom is interderivable with `forall_inst` *given* the
Skolemization equivalences (the triangle `forall_inst` ↔ ∃-introduction ↔ critical axiom), so
some arbitrary-term principle must be primitive no matter how the rules are arranged:
Skolemization says "one designated witness suffices", instantiation says "every term is a
candidate", and neither implies the other. This is why the abstract proof system of the
[classification](./core/classification.md) keeps [inst] and [ε] as separate rules — and why
RESOLUTE, too, keeps `forall-` primitive alongside its `choose`-based axioms.

Since the route needs no new primitive, it is part of the main classification: the six quantifier
rewrites are *reducible*. Binder congruence for `choice` — the binder-generic reading of `bind`,
divergence 5 — is not needed for these derivations, only for bridging witness shapes when
elaborating already-produced `sko_ex` steps.

## Elaborating `onepoint`

`onepoint` also admits an elaboration, built from two observations.

First, *iff-introduction is derivable*: Alethe has no rule concluding `A ≈ B` from the two
implications, but the clausal derivation exists — from `(cl ¬A B)` and `(cl A ¬B)`, resolving
against the axioms `equiv_neg2` (`(cl (= A B) A B)`) and `equiv_neg1` (`(cl (= A B) ¬A ¬B)`)
with two `contraction`s yields `(cl (= A B))` in about seven steps. This is the pattern the
proposed `equiv_intro` convenience rule names.

Second, the two implications of a `onepoint` step `(∀x̄.φ) ≈ (∀x_k̄.φ')` are derivable from core
rules:

- **→**: `forall_inst` instantiating the eliminated variables by their points `x_j := t_j` and
  the kept variables by themselves (`x_k := x_k`, under the enclosing anchor), then the step's own
  premise `φ ≈ φ'` (whose context performs exactly `x_j ↦ t_j`) via `equiv1` + `resolution`.
- **←**: for arbitrary `x̄` assuming `φ'`, a case split on each point equality `x_j ≈ t_j`
  (O(m) splits): the false branch satisfies the positive-polarity guard in `φ` directly, the true
  branch transports `φ'` to `φ` by `cong` with the point equality.

The existential case dualizes through `connective_def` + `forall_inst` on the negated body. The
whole scheme is O(points·|φ|) steps of core rules, wrapped in a subproof over the kept variables
and closed by the derived iff-introduction. Notably, it *discharges* the specification's admitted
gap in `onepoint`: the unproved mutual substitution into point terms becomes explicit
anchor-ordered case splits with `cong`/`trans` obligations.

Two caveats initially kept `onepoint` in the core; both are resolved:

- **The side condition is an inductive grammar, and the grammar is the template.** The
  specification's "positive polarity" prose underdetermines the rule (and naive polarity is
  unsound for `∀`: `∀x.(x≈t ∨ ψ)` must not one-point). Carcara's checker
  (`checker/rules/subproof.rs::extract_points`) implements the real condition: a polarity-tracking
  walk — positive start for `∃`, negative for `∀`, flipping through `¬` and `⇒`-antecedents —
  that collects equalities only at positive polarity, descending through `∧` on the positive side
  and `∨`/`⇒` on the negative side. Each production of this grammar maps one-to-one to a step of
  the `≠`-branch derivation (`implies_neg1` for guards, `or_neg`/`and_pos` + `resolution` for
  descent, `not_not` for flips), so the checker's recursion *is* the elaboration template — no
  exotic shape can pass the checker and escape the derivation. Points under an inner quantifier
  generalize directly with the generalized `bind`'s closure (divergence 8), or — without the
  proposal — via `bind` plus the `Qȳ.⊤ ≈ ⊤` schema (exactly `qnt_simplify`'s instance, itself
  derived via the Skolemization route). The spec should adopt the grammar as the rule's official
  side condition (divergence 7).
- **The context interaction is benign.** The derivation uses only premise-free tautologies plus
  the step's own premise, whose substituted variables never occur on its right-hand side — so the
  contextual and plain readings of every judgment involved coincide — and the replaced node keeps
  its exact conclusion clause and anchor position, leaving consumers untouched (R3).

`onepoint` is therefore classified reducible, conditional on divergence 7.

## Borderline rules kept in the core

- **`symm`** — kept *against* the specification's "technically superfluous" note. That note relies
  on the implicit reordering of equalities; the whole point of elaboration is to make implicit
  reasoning explicit, so elaborated output needs an explicit symmetry step. Dropping `symm` would
  push implicit reordering back onto every consumer.
- **`not_not`** — deriving it needs the rewrite `¬¬φ ≈ φ` (i.e. `not_simplify`) plus `equiv_pos2`
  and resolution, which pulls the rewrite tier into the propositional core. It is the primitive that
  makes the implicit merging of double negations in resolution explicit.
- **The 19 CNF axioms** (the `and`/`or`/`equiv`/`xor`/`ite`/`implies` families) — one side of
  the axiom/premise-rule pairs must be primitive (R4); the `equiv` family additionally bootstraps
  `connective_def` unpacking; and cross-reductions within a family (e.g. `equiv_pos1` from
  `equiv_pos2` via symmetry of the equivalence) fail R2. The `xor`/`ite`/`implies` families are
  kept even though `connective_def` derivations exist — see "The CNF axioms are kept whole"
  above. (`weakening` and `contraction` remain outside the core: under resolution's RUP reading
  they are zero-step renames, hence reducible — see "Resolution's dual semantics" above.)
- **`connective_def`** — kept whole. Its propositional instances are derivable at O(1) via
  `equiv_neg1/2` and the branch tautologies, but the quantifier-duality instance
  (`¬∀x̄.φ ≈ ∃x̄.¬φ`) is the R4-chosen axiom side that bootstraps all ∃-reasoning (`sko_ex`'s
  reduction, the ∃-variants of the quantifier rewrites), and the definition list is where the
  `xor`/`ite`/`implies` axiom-agreement lemmas and the proposed `→` extension (divergence 6)
  live.
- **`la_generic`** and **`rare_rewrite`** — the designated computational and rewrite primitives, as
  discussed above.
- **The binder rules** `let` and `bind_let` — primitives with no reduction candidates.
- **`bind`** — *expensive*, not core: the admissibility argument of "what the generalization
  buys" is now implemented (`core-expensive`), so a consumer can have a proof without binder
  congruence — the ∀-ε-clause Skolemizes one side, `forall_inst` instantiates the other at the
  same witnesses, and the subproof's body is replayed there. What it costs is a copy of the body
  per direction, which is why the default regimes keep the rule. The divergence-8 generalization
  still sits on top of it: anchors carry fresh variables and substitutions, the closing step
  additionally concludes a single ∀-closure literal, and vanilla `bind` is an instance with zero
  extra steps (see "Generalizing `bind`").
- **`sko_forall`** — the designated Skolemization primitive. Its dual `sko_ex` is reducible
  through the quantifier duality (see the Skolemization section above); by R4 exactly one of the
  pair is kept, and the choice is conventional.

## The rare/simplify and expensive levels: the later elimination stages

The **rare/simplify** level is the rewrite vocabulary: the Boolean/ite/equality/comparison
`*_simplify` rules and `rare_rewrite` itself. Each `*_simplify` is a composition of elementary
rewrites glued by `refl`/`trans`/`cong` — exactly what `rare_rewrite` chains express — and the
trace replay is implemented (the `core-simp-rare` and `core-taut` regimes), with the traces read
off the checkers' own labeled step functions rather than recovered by instrumentation. Two of
the eight left this level for *reducible*: `and_simplify` and `or_simplify`, whose
non-short-circuiting instances are `aci_simp` **renames** — the ACI normalization is precisely
what those rules do — and whose short-circuiting ones are constant-size CNF-axiom chains. The
same rename criterion promoted `shuffle` and `nary_elim`, and it gives the constant-folding
instances of the remaining six an `evaluate` route.

The quantifier-level rewrites (`qnt_simplify`, `qnt_join`, `qnt_rm_unused`, the miniscoping
rules) are *not* in this level: although they rewrite the binder itself — which `bind` +
`rare_rewrite` cannot express — they reduce through the generalized `bind` (divergence 8) or,
proposal-free, the Skolemization route (the derived ∀-ε-clause template; see "Deriving the
quantifier rewrites from Skolemization"), so no binder-aware RARE extension is a prerequisite
for any rule.

The **expensive** level is the last stage, and every rule on it has an implemented reduction,
applied by the `core-expensive` pass: `poly_simp` (linear identities → two Farkas bounds +
`la_disequality`), `aci_simp` (→ the two clausal directions of the equivalence), `bind` (→ for
an α-renaming, Skolemizing *both* sides at the same witnesses and joining them, four steps and
no look at the body; for a rewriting body, the ∀-ε-clause plus a replay at the witnesses — the
admissibility argument of "what the generalization buys", made executable), and `sko_ex` (→ the
duality route). What defines the level is not a missing prerequisite but a measured
price: `aci_simp` is where 46% of veriT's post-elaboration checking time went when the pass
created 300 000 of them, `poly_simp`'s six-steps-per-identity is pure growth, and `sko_ex`'s
recipe costs an ~8× local blowup — so the default regimes keep the rules, and the stage exists
for consumers who want the smaller vocabulary badly enough to pay for it.

The clausal equality rules are deliberately *not* on it. `eq_transitive` and `eq_congruent` are
**variants** of `trans` and `cong`, checked by the same functions, so eliminating them trades
steps for nothing — they are kept, uncounted, and the `deep-hoist` replay in fact targets them.
`eq_symmetric` went the other way: it states the equivalence `(= (= a b) (= b a))`, which `cong`
proves outright with one `refl` for its premise minimum, so it is *reducible* in two steps. The purely arithmetic simplifications —
`prod_simplify`, `sum_simplify`, `minus_simplify`, `unary_minus_simplify` — are *reducible* as
`poly_simp` renames (the check coarsens from per-schema folding to ring normalization, 12× per
step measured, the same trade as `shuffle` → `aci_simp`), and under `core-expensive` they end at
the Farkas bounds that `poly_simp`'s own reduction produces.

## The trusted computing base, measured

The point of reducing to a small core is that the *checker for the core* is all one has to
trust. That claim can be made quantitative against Carcara's implementation: how many lines of
Rust does the verdict on a core-fragment proof depend on, once every reducible rule has been
elaborated away? Counted on the `coreAlethe` branch, at function granularity for rule checkers
(a rule's entry function plus the helpers only its family uses) and at module granularity for
infrastructure; test modules, the printer, and error *formatting* are excluded.

**Fragment-independent infrastructure** — trusted no matter what the rule vocabulary is:

| component | lines |
|---|---:|
| lexer + parser (`parser/`, minus the RARE grammar) | 3 456 |
| terms, hash consing, proof AST (`ast/term, rc, pool, proof, problem, iter, macros`) | 2 726 |
| polyequality / alpha-equivalence (`ast/polyeq.rs` — `assume`, premise matching) | 823 |
| substitution + context (`ast/substitution.rs`, `ast/context.rs` — `refl`, the binder rules) | 895 |
| checker driver (`checker/mod.rs`, `checker/shared.rs`, `rules/mod.rs` helpers) | 917 |
| **subtotal** | **≈ 8 800** |

**Core rule checkers.** The syntactic rules are strikingly small — the 19 CNF axioms are 138
lines *in total*, `true`/`false`/`not_not` another 24 — and the bulk sits in exactly two places:
the resolution family and the computational primitives.

| group | lines |
|---|---:|
| resolution family (greedy + explicit-pivot + RUP; `rules/resolution.rs` part + `src/resolution.rs`) | 723 |
| CNF axioms + `true`/`false`/`not_not` | 162 |
| binder rules (`bind` incl. the generalized closure, `let`, `bind_let`, `subproof`, `sko_forall`, `forall_inst`) | 418 |
| equality (`refl`/`strict_refl`, `trans`, `cong`, `symm`, `connective_def`) | 273 |
| `la_disequality` | 11 |
| **syntactic subtotal** | **≈ 1 600** |
| `la_generic` (incl. `LinearComb`, strengthening, disequality splitting) | 267 |
| `mult_pos`/`mult_neg`/`mult_distrib` + `to_int_lower`/`to_int_upper` + `ite_*_intro` + `qnt_duality` (axiom checkers) | ≈ 110 |
| `evaluate` (5-line rule + `ast/evaluate.rs`) | 585 |
| `rare_rewrite` (`rules/rare.rs` + `src/rare/` matcher + RARE parser + `ast/rare_rules.rs`) | 1 233 |
| **computational subtotal** | **≈ 2 200** |
| *`poly_simp` (149) and `aci_simp` (144) — now* expensive*: kept by the default regimes, discharged by `core-expensive`* | *(293)* |

**Total: ≈ 12 600 lines** (12 900 while `poly_simp`/`aci_simp` are kept) — about 8 800 of them
the parser/AST skeleton any checker needs, and
about 4 000 rule-specific. For comparison, Carcara's *full* rule vocabulary is ≈ 11 100 lines of
rule code (the 8 510-line `checker/rules/` directory plus the resolution, RARE and evaluation
modules) before counting the out-of-fragment theories (strings, pseudo-Boolean and cutting-planes
add another 2 900). Elaborating to the core discharges roughly **two thirds of the rule-specific
code from the TCB** — and, more importantly, the ≈ 9 500-line elaborator itself is *not* in it:
its output is re-checked against the core vocabulary, so every reduction recipe, the sharing and
hoisting machinery, and every pipeline pass can be wrong without compromising a verdict.
(A fragment including bitblasting adds the 14 definitional `bitblast_*` schemas, ≈ 780 lines.)

Two entries dominate the computational half, and both are, in principle, removable.

### A frozen RARE set instead of a RARE engine

`rare_rewrite` is the single largest core primitive: 1 233 lines of Rust — instantiation,
`:list`/n-ary meta-normalization, its own parser — **plus the RARE rule file itself, which is
trusted data** (`rewrites.eo`: 119 declarations, 513 lines). The evaluation corpus exercises
**36 of the 119 rules** (184 334 steps over 494 cvc5 proofs; the elaborated outputs use the same
36, since the `core` pass's recipes emit only `ite-true-cond`/`ite-false-cond`, already among
them). They fall into three recipe families, each of which is machinery the `core` pass already
has:

| family | rules | steps | recipe in core terms |
|---|---|---:|---|
| arithmetic atom equivalences | `arith-elim-lt/leq/gt`, `arith-leq-norm`, `arith-eq-elim-int/real`, `arith-geq-tighten`, `arith-geq-norm1-int/real` | 122 939 (67%) | the `poly_simp_rel` template: each direction one `la_generic` Farkas certificate (through `la_disequality` when a positive equality is produced), glued by the `equiv_intro` pattern — 8 steps for atom↔atom, ~20 when an equality is eliminated |
| propositional equivalences | `bool-double-not-elim`, `eq-symm`, `eq-refl`, `bool-eq-false/true`, `bool-impl-*`, `bool-and/or-de-morgan`, `bool-implies-or-distrib`, `bool-or-and-distrib`, `bool-implies-de-morgan`, `or-not-refl`, `distinct-false`, `bool-or-taut`, `bool-and-conf` | 60 524 (33%) | two discharge subproofs over the CNF axioms closed by the `equiv_intro` pattern — the same shape as the `eq_*` reductions; constant-size for fixed-arity rules, linear in n for the 8 that declare `:list` |
| `ite` selection | `ite-not-cond`, `ite-eq`, `ite-then-true`, `ite-else-false`, `ite-true-cond`, `ite-false-cond`, `ite-eq-branch`, `arith-geq-ite-lift` | 871 (0.5%) | constant-size; the Boolean-sorted members via `ite_pos1/2` + `ite_neg1/2` + resolution, the term-level members via the proposed selection axiom pair (next subsection) |

So a **frozen** alternative exists: fix this rule set, give each member a recipe, and
`rare_rewrite` moves from core to *reducible* — deleting the entire RARE subsystem *and* the
trusted rule file from the TCB, with no new trusted code, since every recipe lands on rules
already in the core and the recipes themselves live in the untrusted elaborator. The volume is
real but concentrated: the top four rules (`arith-elim-lt`, `eq-symm`, `arith-elim-leq`,
`bool-double-not-elim`) are 78% of all instances, and 56% of instances are cross-subproof
duplicates the `hoist` pass would absorb. What the frozen set gives up is exactly its name: any
new producer rule requires a hand-written recipe rather than a declaration, and the aggressive
tier's designated reduction *target* changes meaning — the `*_simplify` rules are compositions
of elementary rewrites, i.e. `rare_rewrite` chains, so removing `rare_rewrite` forces the
question of whether the *whole* rewrite vocabulary reduces. That question is answered next; it
turns out to sharpen rather than kill the plan. The classification keeps `rare_rewrite` core —
it is the extensibility point — but the frozen set is the measured answer to "what does that
choice cost in trust": 1 233 lines of Rust plus 513 lines of trusted declarations, against 36
recipes. **Both regimes are implemented** as the `core-taut` and `core-simp-rare` variants of
the `core` pass (see the elaboration chapter), the former on the term-`ite` selection axioms
`ite_then_intro`/`ite_else_intro` proposed below.

#### Dropping the `*_simplify` rules too: the whole file

If the aggressive tier's `*_simplify` reductions are also to be carried out — each step
replayed as a chain of per-rewrite lemmas glued by `cong`/`trans` — then under a no-`rare_rewrite`
regime every rewrite those chains use needs a core recipe too, not just the 36 the corpus
emits directly. The relevant scope is **every rule of `rewrites.eo` outside the bitvector and
array theories: 101 active declarations** (of 107 active; the file also carries 12 commented-out
declarations, ten of them the `bv-*` set), together with the ~30 catalogue-only rewrites the
[`*_simplify` fixpoint systems](./core/rare-rules.md) need beyond the file (the n-ary
`and`/`or` list rules, the `equiv`/`implies` simplification sets, the ring rules, the constant
folds, the generic ACI rules). The catalogue extras add *no new recipe family* — a ring identity
is one `poly_simp` step, a constant fold is the `evaluate` recipe above, an ACI step is one
`aci_simp` — so the whole analysis is the classification of the 101 by recipe:

| family | rules | recipe | size per instance |
|---|---:|---|---|
| linear-atom equivalences (`arith-elim-*`, `arith-leq-norm`, `arith-geq-tighten`, `arith-geq-norm1-*`, `arith-eq-elim-*`, `arith-int-eq-conflict`, `arith-int-geq-tighten`) | 13 | the `poly_simp_rel` template: one `la_generic` per direction (`la_disequality` for positive equalities), `equiv_intro` glue; integer tightening is `la_generic`'s strengthening | 8–20 steps |
| propositional equivalences (`bool-*`) and equality logic (`eq-refl`, `eq-symm`, `eq-cond-deq`, `or-not-refl`) | 35 | two discharge subproofs over the CNF axioms closed by the `equiv_intro` pattern; `refl`/`trans`/`symm` for the equality ones; premise-carrying members (`bool-not-true/false`, `eq-cond-deq`) consume their premise via `cong` | constant; linear in *n* for the `:list` rules |
| Boolean-sorted `ite` (`ite-then-true`, `ite-else-false`, `ite-expand`, the `lookahead-self` group, `ite-neg-branch`, `bool-not-ite-elim`, …) | 11 | `ite_pos1/2` + `ite_neg1/2` + resolution + `equiv_intro` | constant |
| term-level `ite` (`ite-true-cond`, `ite-false-cond`, `ite-not-cond`, `ite-eq-branch`, the polymorphic lookaheads, `ite-eq`, `eq-ite-lift`) and its arithmetic lifts (`arith-*-ite-lift`, `arith-min-*`, `arith-max-*`) | 16 | **blocked** — see below; given the proposed selection axioms: excluded middle (3 core steps: `refl` + `equiv_pos2` + resolution) + `cong` + `trans`, plus `la_generic` for the min/max members | constant |
| `abs` (`abs-elim-*`, `arith-abs-eq`, `arith-abs-*-gt`) | 5 | `abs_intro` definitional axiom + the term-`ite` machinery + a 4-way sign case split in `la_generic` | constant (~40 steps) |
| `div`/`mod`/coercions (`arith-*-total*`, `arith-mod-over-mod*`, `mod-elim`, `arith-to-int-elim-to-real`, `arith-div-elim-to-real*`, `is_int-elim`) | 17 | the `*_intro` characterization axioms + `la_generic`/`poly_simp`; the division-by-zero rules are **axioms outright** — see below | constant *at literal divisors* (how cvc5 instantiates them); symbolic divisors would need nonlinear uniqueness arguments |
| `distinct` (`distinct-binary-elim`, `distinct-false`) | 2 | `distinct_elim` as definitional + `refl` + CNF axioms — see below | linear in arity |
| nonlinear tangent planes (`mult-tangent-lower/upper`) | 2 | the proposed `mult_pos` [pos-cone] axiom + `poly_simp` + a 4-quadrant `la_generic` case split | constant (~40 steps) |

Four families reduce today with no additions. The remaining four converge on a short list of
**genuinely new axioms** — the honest price of the whole program, and the answer to "which
rewrites deserve a rule instead of a recipe":

1. **Term-`ite` selection** — the one outright gap. No core rule characterizes `ite` at
   non-Boolean sorts: `ite_pos/neg` are formula-level, so `(= (ite true t s) t)` has *no
   derivation at all* (which is exactly why the `ite_intro` recipe reaches for
   `ite-true-cond`/`ite-false-cond` today). The fix is one definitional axiom pair in the
   premise-free-clause style of `la_disequality`:
   `▷ ¬c, (ite c t s) ≈ t` and `▷ c, (ite c t s) ≈ s`.
   Both RARE rules become 2-step lemmas (instantiate, resolve against the `true`/`false`
   axioms), the other fourteen term-`ite` rules derive by case split, and the `ite_intro`
   recipe sheds its RARE dependency. This pair is to `ite` what the `bitblast_*` schemas are to
   the bitvector operations.
2. **`distinct_elim` promoted to a definitional computational schema** (*adopted* 2026-08-25:
   the rule is now **core**). Its aggressive-tier blocker — an n-ary RARE rule needs an
   arity-dependent Eunoia program — was a RARE-*expressiveness* blocker, never a problem with
   the rule itself, and it dissolves under recipes, which can emit arity-dependent derivations
   freely. Something must still *define* `distinct`, since no core rule mentions it:
   `distinct_elim` itself is that definitional primitive (checked by recomputing the pairwise
   expansion, exactly like `bitblast_*`). The two RARE `distinct` rules reduce to it:
   `distinct-binary-elim` is one `distinct_elim` step plus Boolean glue, and `distinct-false` is
   `distinct_elim` + `refl` on the repeated element + CNF axioms.
3. **The `*_intro` definitional family**, most of it already proposed on the alethe-toolkit
   branch: `div_intro` (the Euclidean characterization `s ≠ 0 → t = s·(div t s) + (mod t s) ∧
   0 ≤ mod t s < |s|`), `to_int_intro` (floor bounds), an `abs_intro`, an `is_int` definition,
   and a `to_real` coercion-erasure principle (or a subtyping-aware `refl`, which
   `--allow-int-real-subtyping` already gestures at). On top of these, the four
   **division-by-zero rules** (`arith-div-total-zero-*`, `arith-int-div-total-zero`,
   `arith-int-mod-total-zero`) are not derivable from anything, even in principle: SMT-LIB
   leaves `t/0` unspecified and cvc5's rewrites *fix* it (`(/ t 0) = 0`, `(mod t 0) = t`), so
   adopting them is adopting the total semantics, and they can only enter as definitional
   axioms alongside `div_intro`. A caveat scoped precisely: with these characterizations the
   `div`/`mod` recipes are linear only when the divisor is a literal — which is how cvc5 emits
   every instance, discharging the `≠ 0` premises by evaluation. At a *symbolic* divisor,
   `arith-int-div-total-neg` and `arith-mod-over-mod` need the uniqueness of Euclidean division,
   a nonlinear argument; the frozen fragment should restrict those rules to literal divisors
   rather than buy the nonlinear machinery.
4. **`mult_pos`** — already the classification's proposed [pos-cone] axiom for the
   `la_mult_*` schemes; the two tangent-plane rules are its only other clients here, with
   constant-size recipes once it exists.

Nothing else earns a rule on cost grounds: the worst recipes in the derivable families are the
~40-step constant-size `abs`/tangent case splits, and the `:list` rules are linear with small
constants. One catalogue rule deserves a flag rather than an axiom: `eq-const-diff`
(`(= c₁ c₂) ≈ ⊥` for distinct literals) reduces via `la_generic` for *numeric* constants, but at
other value sorts the core has no disequality introducer — outside this fragment's theories,
which is where it should stay.

The combined regime — `rare_rewrite` frozen out *and* the eight `*_simplify` rules reduced —
would additionally delete most of `simplification.rs` (~750 of its 896 lines; `aci_simp` stays)
and retire `distinct_elim`'s Eunoia blocker, at the price of the axiom list above and of
`*_simplify` steps costing trace-length × recipe-size core steps, with the repeated
literal-instance lemmas being exactly what the `hoist` pass deduplicates. The
trace-instrumentation prerequisite of the aggressive tier (recording the fixpoint's rewrite
order) is unchanged — recipes replace the chain's *links*, not the need to know the chain.

### `evaluate` without the evaluator

The same question for `evaluate` has a sharper answer. Its checker is 5 lines of rule plus the
580-line `ast/evaluate.rs` interpreter — rational arithmetic, all the comparison operators,
Boolean connectives, `ite`, division conventions. The corpus's 248 964 instances (a sample of 36
proofs, ~24 800 instances, classified by the evaluated term's head) are: ring identities over
constants (`*` 33%, `+` 15%, `-`, `/`) — one `poly_simp` step each; constant relational atoms
(`>=`, `<=`, `<`, `>`, integer `=`) — one `la_generic` certificate each (via `la_disequality`
for a true equality), plus the ~7-step `equiv_intro` bridge from the proved atom `A` to the
conclusion `(= A true)` or `(= A false)`; and Boolean evaluations (`not` 10%, `and`, `or`,
`ite`) — CNF axioms and resolution, constant-size. Nothing in the corpus needs more; the one
genuine gap is integer `div`/`mod` (absent here), which no core rule characterizes — reducing
those needs the `div_intro`-style definitional axioms of the alethe-toolkit branch. So
`evaluate` too could move to reducible with **zero new trusted code**, deleting 585 lines from
the TCB — and the `core-taut` regime *does* reduce it, at about 7 new commands per instance; the
recipe is the structural recursion documented in [Recipes for eliminating the RARE
rewrites](./core/rewrite-recipes.md#evaluate-the-structural-recursion). It stays core in the
classification because the price is steps, not trust — ~90% of its instances are
duplicates (the `hoist` pass's best customer), and re-deriving what a 20-line interpreter case
decides in microseconds is the classification's cost criterion applied in reverse. Unlike
`rare_rewrite`, though, nothing structural depends on it: `evaluate` is the first candidate to
demote if the TCB is ever the binding constraint.

## Extra rules beyond the specification

Carcara checks several rules that are not among the 120 specification rules. Classified the same
way:

| rule | level | reduction |
|---|---|---|
| `eq_mp` | reducible (**done**) | `equiv_pos2` + `resolution` (local elaboration) |
| `equiv_intro` (proposed) | reducible | iff-introduction; `equiv_neg1/2` + resolutions + contractions (see the convenience rules section) |
| `or_intro` (proposed) | reducible | clause-to-`or`-term packing; `or_neg` ×n + resolutions + `contraction` |
| `bounded_farkas` | reducible (**done**) | `la_generic` with inferred coefficients (local elaboration) |
| `and_intro` | reducible | `and_neg` + one `resolution` with explicit pivots |
| `strict_resolution` | core variant | strict form of `resolution` used after elaboration |
| `poly_simp` | **expensive** (computational) | ring-normalization primitive; linear instances reduce to Farkas bounds + `la_disequality` (`core-expensive`); see the arithmetic section |
| `mult_pos`, `mult_neg`, `mult_distrib` | adopted core axioms | the product sign rules and distributivity over subtraction; base of the `la_mult_*` reductions |
| `la_mult_sign` (`alethe-toolkit` branch) | reducible in principle | O(n) fold of `mult_pos`/`mult_neg` + `mult_distrib` + `la_generic`; not implemented (branch not merged) |
| `la_mult_abs_comparison` (`alethe-toolkit` branch) | blocked | reducible to the same base once an `abs` definitional rewrite exists |
| `evaluate` | **core** (computational) | constant evaluation of interpreted operators: each interpreted operator gives it a concise definitional statement (the `bitblast_*`/`distinct_elim` justification), and it is the cheapest computational check |
| `mod_simplify`, `all_simplify` | rewrite tier | `all_simplify` already oracle-reducible via the hole pass |
| strings, PB, cutting-planes, arrays, DRUP, `sat_refutation` | theory extensions (out of scope) | `sat_refutation` oracle-reducible via its dedicated pass |

## Divergences from the specification

Points where this classification deliberately diverges from the specification, or proposes
extending it, all worth raising with the Alethe specification maintainers:

1. **`symm` vs `eq_symmetric`**: the specification calls `symm` superfluous and adds `eq_symmetric`
   deliberately; this classification keeps `symm` as the primitive and reduces `eq_symmetric` (and
   `not_symm`) to it, since subproof-discharge makes the reduction three steps.
2. **`eq_congruent_pred` conclusion shape**: the specification states the single-equality form
   `¬(t1 ≈ u1), ..., ¬(tn ≈ un), (P t̄) ≈ (P ū)` — identical in shape to `eq_congruent`, differing
   only in the co-domain sort condition. veriT produces, and Carcara checks
   (`checker/rules/congruence.rs`), the two-literal form ending in `¬(P t̄), (P ū)`. Both forms
   admit the O(n) reduction shown above, but the specification and the implementations should agree
   on one shape.
3. **`shuffle` vs `aci_simp`**: every `shuffle` instance is an `aci_simp` instance (see above), so
   the specification carries two rules for one judgment. The apparent reason to keep both is
   checking cost — a multiset comparison versus full ACI normalization — which is a performance
   distinction, not an expressiveness one; worth deciding whether that justifies a separate rule.
4. **`sko_forall`'s choice terms are ill-formed for n > 1**: the stated `εxᵢ.¬φ` leaves the later
   variables free; implementations (Carcara's checker, mirroring what solvers emit) use the
   sequential form `εxᵢ.¬(∀x_{i+1}…xₙ.φ')`. The spec text should be corrected to the sequential
   form.
5. **The Skolemization pair and choice-binder congruence**: only one of `sko_ex`/`sko_forall`
   needs to be primitive (see the Skolemization section); making that reduction applicable to
   *existing* proofs requires binder congruence for `choice`, for which the proposal is to state
   `bind` as *binder-generic* — the same rule, mechanics unchanged, over `∀`/`∃`/`ε` alike —
   rather than to add a separate rule; Carcara's `bind` checker already implements this reading.

   **The divergence is conditional on that reduction, and only on it.** Choice congruence is
   never needed to *check* a solver's proof: no corpus `bind` step is over a `choice` binder
   (0 of 12,893), and the only construction that emits one is the `sko_ex` reduction's own
   witness bridge. It is also the only thing standing between the `bind` reduction and complete
   coverage — with `sko_ex` core, every `bind` step the corpus contains reduces. Keeping `sko_ex` in the core instead — which is exactly what having both
   `∃`-introduction and `∃`-elimination primitive means, and what RESOLUTE does with its four
   quantifier axioms — leaves every witness in the shape the solver wrote it, and the choice
   binder then needs no rule at all. So the trade is: *derive `sko_ex` from `sko_forall` and pay
   for it with binder-generic `bind`, or keep both Skolemization rules and pay nothing.* The
   `bind` reduction, which needs the quantifier rules but never the choice one, is what makes
   the second option cheap: with `sko_ex` core, `bind` itself becomes eliminable.
6. **Extend `connective_def` with implication**: adding `(φ₁ → φ₂) ≈ (¬φ₁ ∨ φ₂)` to
   `connective_def`'s definition list lets the three `implies` CNF axioms reduce like the `xor`
   and `ite` families, shrinking the axiomatic CNF base to the `and`/`or`/`equiv` families.
7. **Adopt the inductive side condition for `onepoint`**: the spec's "positive polarity" prose
   underdetermines (and naively misstates) the rule's applicability; the guarded-occurrence
   grammar implemented by Carcara's `extract_points` should become the official side condition —
   it is simultaneously the induction structure of the rule's elaboration (see "Elaborating
   `onepoint`").
8. **Generalize `bind`** (see "Generalizing `bind`"): anchors carry fresh variables and
   capture-avoiding substitutions, and the closing step concludes transformation literals as
   quantified equivalences (miniscoped binder sets) plus at most one ∀-closure literal over a
   declared subset of the fresh variables — miniscoping only ever on binder sets, never on clause
   structure, which keeps checking free of free-variable computation. Vanilla `bind` is an
   instance with zero extra steps; ∀-introduction is the no-substitutions instance; `sko_*` and
   `onepoint` are the same closing scheme under their substitution disciplines; `qnt_rm_unused`
   is absorbed. Admissible given Skolemization, so no logical content is added. `choice`
   congruence is the binder-generic reading of `bind` itself (formerly the separate divergence-5
   proposal), orthogonal to this scheme.

## Validation

Each reduction recipe is validated by:

1. a hand-worked before/after example in this chapter or the classification table;
2. a minimal problem/proof pair exercising the rule, elaborated with the default pipeline and
   re-checked in elaborated (strict) mode, with a vocabulary check asserting that every output rule
   is core or an unapplied expensive/aggressive rule;
3. corpus-level measurement of elaborated-proof size and checking time using the benchmarking
   infrastructure, before any reduction is made default-on.
