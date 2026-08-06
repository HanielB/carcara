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
- **Reducible**: rules with a reduction meeting the cost criterion R1–R4 below. Elaboration should
  eventually eliminate all of them from its output.
- **Expensive**: rules with a concrete, small-step-count scheme that however *upgrades the checking
  power* the step requires — a fixed syntactic schema becomes a `poly_simp` ring check or an
  `aci_simp` ACI-normalization check (e.g. the `la_mult_*` family, `shuffle`, the arithmetic
  `*_simplify` renames) — or that depends on a proposed-but-not-yet-adopted rule.
- **Aggressive**: rules whose scheme is trace-replay or program-like, needs missing infrastructure
  (RARE under binders, evaluation operators, checker instrumentation), or has severe worst-case
  size. The exemplar is elaborating `poly_simp` *itself* into `rare_rewrite` chains — at this
  level one is no longer just reducing a rule but shrinking the trust base.

The last two levels are accepted in elaborated output today; the ladder records, per rule, exactly
what it would cost to go further. Legacy rules (below) sit outside the ladder at a fifth level,
**removal**.

Orthogonally to the tiers, the classification organizes the rules into *concern categories*:
**structural** (proof structure: `assume`, `subproof`, `hole`), **clausal** (resolution and the
CNF layer), **binder** (quantifiers and binders), **equality & rewriting** (congruence closure and
term rewriting), **arithmetic**, **bitvector**, and **legacy**. The legacy category collects rules that are
placeholders, solver-implementation artifacts, or superseded by more general rules (`lia_generic`,
`qnt_cnf`, `ite_intro`, `bfun_elim`, and `ac_simp`, which is superseded by `aci_simp`); for these
the long-term goal is not reduction but *removal* — solvers should stop emitting them, or the
specification should replace them with principled counterparts.

Of the 120 specification rules, this classification yields **41 core**, **44 reducible**,
**13 expensive**, **17 aggressive**, and **5 removal** rules, distributed as follows:

| category | total | core | reducible | expensive | aggressive | removal |
|---|---|---|---|---|---|---|
| structural | 3 | 3 | 0 | 0 | 0 | 0 |
| clausal | 47 | 12 | 33 | 2 | 0 | 0 |
| binder | 13 | 5 | 2 | 0 | 6 | 0 |
| equality & rewriting | 25 | 6 | 7 | 2 | 10 | 0 |
| arithmetic | 13 (+1) | 1 (+1) | 2 | 9 | 1 | 0 |
| bitvector | 14 | 14 | 0 | 0 | 0 | 0 |
| legacy | 5 | 0 | 0 | 0 | 0 | 5 |

The "+1" is the extra rule `poly_simp`, promoted into the core as a computational primitive; one
new axiom (`la_mult_pos_pos`) is also proposed — see the arithmetic section below. For every
expensive and aggressive rule, the [classification](./core/classification.md) records its
concrete *reduction scheme* — what the reduction would be, at what cost, and which prerequisite is
missing — so the distance of each rule from the core is visible. The classification also opens
each category with the *proof system* it embodies, first abstractly and then as concretized by
that category's core rules.

The core property is defined *post-pipeline*: intermediate passes may emit non-core rules (e.g.
`reordering` steps, which the final pass of the default pipeline removes); only the output of the
full pipeline must be within core ∪ (unapplied expensive/aggressive rules). Proofs containing
`hole`, `lia_generic` (without an external solver), or `qnt_cnf` can only ever be "core modulo
holes".

## The cost criterion

A rule is classified as reducible only if it has a reduction satisfying all of:

- **R1 (linear)**: the reduction produces O(n) new steps, where n is the size of the step (clause
  length plus premise count), with a small constant;
- **R2 (syntactic)**: every emitted step is checkable by purely syntactic matching — no search, no
  polyequality reasoning, and all resolution pivots explicit;
- **R3 (local)**: the reduction replaces a single proof node without rewriting any of its consumers;
- **R4 (non-circular)**: for each pair of interderivable rules, exactly one side is kept as the
  axiom.

A rule that fails any of R1–R4 stays in the core (if it is a logical primitive) or lands on the
*expensive* or *aggressive* level, depending on how it fails: a check-power upgrade or a
missing proposed rule is expensive; trace-replay, missing infrastructure, or bad worst-case size
is aggressive. The point of R1–R2 is that reducing a rule must not make proofs meaningfully larger
or harder to check — a reduction that needs many steps, or steps whose checking requires search,
defeats the purpose.

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
it from `symm` "would require a long and tedious use of subproof"): the subproof is three steps.

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
`(= (P t̄) (P ū))` of the specification. The reduction additionally assumes `(P t̄)` and applies the
`equiv_pos2` + `resolution` pattern already used by the `eq_mp` elaboration:

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
(step t1.t2 (cl (not (= (P a c) (P b d))) (not (P a c)) (P b d)) :rule equiv_pos2)
(step t1.t3 (cl (P b d)) :rule resolution :premises (t1.t2 t1.t1 t1.a2)
    :args ((= (P a c) (P b d)) false (P a c) false))
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

## Reducing within the CNF axioms

Not all 19 CNF axioms need to be primitive: the `xor` and `ite` families are derivable, because
`connective_def` provides definitions for exactly those connectives. The recipe unpacks the
definition and re-clausifies. For `xor_pos1` (`¬X ∨ φ₁ ∨ φ₂`, with `X = (xor φ₁ φ₂)` and the
definition `X ≈ D` where `D = (¬φ₁ ∧ φ₂) ∨ (φ₁ ∧ ¬φ₂)`):

```
t1. (cl (= X D))                 connective_def
t2. (cl ¬(= X D) ¬X D)           equiv_pos2
t3. (cl ¬X D)                    resolution t2 t1
t4. (cl ¬D (¬φ₁∧φ₂) (φ₁∧¬φ₂))    or_pos
t5. (cl ¬(¬φ₁∧φ₂) φ₂)            and_pos (index 2)
t6. (cl ¬(φ₁∧¬φ₂) φ₁)            and_pos (index 1)
t7. (cl ¬X φ₂ φ₁)                resolution t3 t4 t5 t6
```

Seven steps, all syntactic. The `neg` variants additionally use `equiv_pos1` (the other direction
of the definition), `and_neg`/`or_neg`, and `not_not` to strip the `¬¬φ` literals the definition
introduces; the four `ite` axioms follow the same pattern through `ite`'s definition
`(φ₁→φ₂) ∧ (¬φ₁→φ₃)` and the `implies` axioms. Every derivation is a constant template of at most
~10 steps.

The `implies` family reduces the same way under the **proposed extension of `connective_def`**
with the implication definition `(φ₁ → φ₂) ≈ (¬φ₁ ∨ φ₂)` (divergence item 6), which this
classification adopts: `implies_pos` unpacks the definition via `equiv_pos2` and re-clausifies
with `or_pos` (5 steps); `implies_neg2` uses `equiv_pos1` + `or_neg` (4 steps); `implies_neg1`
additionally needs `not_not` to strip the `¬¬φ₁` literal (6 steps). No circularity: the
derivations touch only the `equiv`, `and`/`or`, and `not_not` primitives.

The remaining 8 axioms are genuinely primitive: the `equiv` family is the *bootstrap* — unpacking
any `connective_def` equivalence requires `equiv_pos1`/`equiv_pos2`, so R4 keeps all four `equiv`
axioms — and the `and`/`or` families are the Tseitin base every derivation above re-clausifies
into (they have no definitions to unpack that would not themselves need `and`/`or`).

## Resolution's dual semantics, `weakening`, and `contraction`

The core `resolution` rule carries *two* semantics, both first-class: the **chain** reading — a
chain of binary resolutions with explicit pivots (`:args`), checkable by pure syntactic matching,
which is what the elaboration pipeline produces (pivot inference + uncrowding) and strict mode
checks — and the **RUP** reading — the conclusion is a reverse-unit-propagation consequence of
the premises, checkable by unit propagation (Carcara's `prefer_rup` mode).

Under the RUP reading, `weakening` and `contraction` are *degenerate instances* of `resolution`:
negating the conclusion immediately falsifies the premise clause (same literal set, or a
superset), so the conflict appears before any propagation happens. Both therefore reduce to
`resolution` by a pure rename. They sit at the *expensive* level rather than reducible because
the rename upgrades the check: a linear syntactic scan (containment / dedup) becomes unit
propagation, and the chain reading — under which `weakening` is not derivable at all, since chain
resolution never introduces literals — loses them from its vocabulary. The two readings pull in
opposite directions here: uncrowding *introduces* explicit `contraction` steps precisely to make
the chain reading's implicit duplicate merging syntactically checkable, while the RUP reading
absorbs them silently. An elaboration targeting the chain core keeps both rules in its output; one
targeting the RUP core renames them away.

## Arithmetic: `la_generic` and `poly_simp` as the computational core

The core has two designated *computational* primitives for arithmetic, i.e. rules whose checking is
not syntactic matching but a decision procedure with a fixed, well-understood algorithm:

- `la_generic`: linear consequence, checked by verifying a Farkas certificate. Expanding it into
  rewrite chains would blow up unboundedly.
- `poly_simp` (an extra rule, not among the 120 specification rules): a unit equality between
  polynomial terms, checked by ring-normalizing both sides. This is the *nonlinear normalization*
  primitive: it justifies distribution, flattening, and constant folding of products — steps that
  `la_generic` cannot express, since it treats distinct monomials as unrelated atoms.

For consumers that do not want to trust the ring check, `poly_simp` itself admits an elaboration
into rewrites: replay the normalization of both sides as chains of elementary RARE arithmetic
rewrites (distributivity, associativity/commutativity, constant folding, cancellation) glued by
`trans`/`cong`, meeting in the shared normal form. This makes `rare_rewrite` the sole rewrite
trust anchor, at a cost: the proof grows with the size of the *distributed* normal form, which is
worst-case exponential in the step (a product of k binomials expands to 2^k monomials), though
benign for the polynomials solvers typically emit. The classification therefore keeps `poly_simp`
core, with the rewrite elaboration recorded as an optional trust-reduction path rather than the
default. The elementary ring rules this route needs are listed in
[RARE rules for the rewrite routes](./core/rare-rules.md).

Two LA rules reduce to `la_generic` alone:

- `la_tautology`, first form (a single trivially-unsatisfiable-when-negated inequality literal):
  `la_generic` with coefficient `[1]`.
- `la_tautology`, second form, and `la_totality`: both conclude a *unit clause containing a
  disjunction term* (a historical quirk noted in the specification). `la_generic` concludes a proper
  clause, so the reduction needs a constant-size repackaging from `(cl φ1 φ2)` to
  `(cl (or φ1 φ2))`: two `or_neg` steps and two resolutions plus a `contraction` — six steps total,
  still O(1).

`la_disequality` is expensive: the negation of its positive equality literal is a *disequality*,
which a Farkas combination cannot consume — its scheme goes through `la_rw_eq` as the
order-antisymmetry axiom instead (see the classification). `lia_generic` is
special: it is not checkable at all without an external solver, and is classified as
*oracle-reducible* — the existing hole elaboration pass replaces it with a full sub-proof produced
by an external solver.

### Nonlinear multiplication: reducing the `la_mult_*` family

With `poly_simp` in the core, the nonlinear multiplication rules stop being leaves. The proposed
common base is a single new axiom — the ordered-ring fact that the positive cone is closed under
multiplication:

```
(cl (=> (and (> x 0) (> y 0)) (> (* x y) 0)))     ; la_mult_pos_pos
```

Its check is O(1) syntactic matching. It is exactly the overlap of the existing schemas: the binary
all-positive instance of `la_mult_sign` (see the extras table below), and the (`⋈` = `>`,
`t3` = `0`) instance of `la_mult_pos` modulo one `poly_simp` step (`(* t1 0) ≈ 0`). No negative
variant is needed: mixed- and negative-sign cases route through `la_generic` sign-flips
(`t < 0 → -t > 0`) plus `poly_simp` (`(* (- x) (- y)) ≈ (* x y)`).

The reductions, all using subproof-discharge plus the implication-term repackaging
(`implies_neg1/2` + two resolutions + `contraction`, the dual of the `la_totality` or-packaging):

- **`la_mult_pos`/`la_mult_neg`, strict forms** — constant template: `la_generic` turns
  `t2 ⋈ t3` into a sign fact about the difference (`(- t2 t3) > 0`), the axiom applies to
  `(* t1 (- t2 t3))`, and `poly_simp` justifies the distribution
  `(* t1 (- t2 t3)) ≈ (- (* t1 t2) (* t1 t3))` — the step that previously blocked this reduction —
  before `la_generic` converts back to `(* t1 t2) ⋈ (* t1 t3)`.
- **`≈` form** — no axiom needed at all: `cong` on the multiplication.
- **`≤`/`≥` and disequality forms** — one bounded case split each (`t2 - t3 < 0 ∨ t2 - t3 = 0`
  via `la_generic`/`la_disequality`-style totality), combining the strict and `cong` branches.
- **`la_mult_sign`** (extra rule, `alethe-toolkit` branch) — O(n) fold over the monomial: one axiom
  instance plus one `poly_simp` normalization per factor, negative factors pre-flipped through
  `la_generic`, even-exponent factors (`v ≠ 0`) costing one bounded case split each.
- **`la_mult_abs_comparison`** (extra rule, `alethe-toolkit` branch) — reduces to the same base
  only once `abs` is handled by a definitional rewrite (`(abs t) ≈ (ite (>= t 0) t (- t))`, e.g. as
  a RARE rule): then each factor costs a bounded case split and the product comparisons chain
  through the axiom. O(n) with a larger constant; contingent on the `abs` rewrite, so it stays at
  the aggressive level until that primitive is chosen.

The trade is the usual one: elaborated proofs get O(n) scaffolding where solvers emitted one macro
step, and the checker must trust ring normalization (`poly_simp`) as a second computational
primitive alongside Farkas checking.

## Other reducible rules

- `eq_reflexive` is `refl` with an empty context: a rename, one step.
- `eq_symmetric` reduces to `subproof { assume (= t1 t2); symm; discharge }` — three steps.
- `not_symm` reduces to the same subproof plus one resolution against the premise — four steps.
- `tautology` concludes exactly `⊤`, so it reduces to a premise-free `true` step. Note this drops
  the premise from the proof DAG (relevant for slicing).
- `th_resolution` is, per the specification, the same rule as `resolution`; elaboration normalizes
  the name.
- `shuffle` is subsumed by `aci_simp`: multiset equality of arguments under a commutative operator
  is a special case of ACI equivalence, `shuffle`'s operators (`+`, `*`, `and`, `or`) are all in
  `aci_simp`'s operator list, and the conclusion shape is identical — so the reduction is a pure
  rename, zero new steps — though the check coarsens: `aci_simp` also collapses idempotent
  duplicates and identity elements, so the renamed step admits conclusions the multiset check
  would reject. That check-power upgrade is what places `shuffle` at the *expensive* level rather
  than among the strictly reducible rules.
- `reordering` is already eliminated by the reordering elaboration pass, which recomputes downstream
  conclusions instead.
- `multi_rare_rewrite` reduces to a chain of `rare_rewrite` steps glued with `trans`/`cong`
  scaffolding (the exact recipe depends on the rule-position semantics and should be validated when
  implemented).

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
- **`bind` must be generalized to the choice binder.** The witnesses of a `sko_ex` step
  (`εxᵢ.(∃…φ)`) and those produced by the dual route (`εxᵢ.¬(∀…¬φ)`) differ by a duality rewrite
  *under* `ε`, and no current rule reasons under choice binders — `bind` covers only `∀`/`∃`.
  Extending `bind`'s binder set to `choice` (from `Γ, x↦y ▷ φ ≈ ψ` conclude
  `Γ ▷ εx.φ ≈ εy.ψ`) closes exactly this gap: with it, the `¬∀¬`/`∃`-shaped witnesses of
  existing proofs can be bridged by `connective_def` + `not-not` reasoning under the binder, and
  the reduction applies to already-produced steps, not just to new proofs that take the duality
  detour from the start.

## Elaborating `onepoint`

`onepoint` also admits an elaboration, built from two observations.

First, *iff-introduction is derivable*: Alethe has no rule concluding `A ≈ B` from the two
implications, but the clausal derivation exists — from `(cl ¬A B)` and `(cl A ¬B)`, resolving
against the axioms `equiv_neg2` (`(cl (= A B) A B)`) and `equiv_neg1` (`(cl (= A B) ¬A ¬B)`)
with two `contraction`s yields `(cl (= A B))` in about seven steps.

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
  need one extra ingredient: generalizing the branch through the binder uses `bind` plus the
  `Qȳ.⊤ ≈ ⊤` schema (exactly `qnt_simplify`'s instance, the minimal binder-pattern axiom). The
  spec should adopt the grammar as the rule's official side condition (divergence 7).
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
- **The 8 retained CNF axioms** (the `and`/`or`/`equiv` families) — one side of the
  axiom/premise-rule pairs must be primitive (R4); the `equiv` family additionally bootstraps
  `connective_def` unpacking; and cross-reductions within a family (e.g. `equiv_pos1` from
  `equiv_pos2` via symmetry of the equivalence) fail R2. The `xor`, `ite`, and (via the proposed
  `connective_def` extension) `implies` families are *not* kept — see "Reducing within the CNF
  axioms" above. (`weakening` and `contraction` are likewise no longer borderline keeps: under
  resolution's RUP reading they are expensive-level renames — see "Resolution's dual semantics"
  above.)
- **`connective_def`** — its propositional instances are derivable at O(1) via `equiv_neg1/2` and
  the branch tautologies, but the quantifier-duality instance (`¬∀x̄.φ ≈ ∃x̄.¬φ`) requires reasoning
  under binders that no core rule provides. Kept whole for uniformity.
- **`la_generic`** and **`rare_rewrite`** — the designated computational and rewrite primitives, as
  discussed above.
- **The binder rules** `bind`, `let`, `bind_let` — primitives with no reduction candidates.
- **`sko_forall`** — the designated Skolemization primitive. Its dual `sko_ex` is reducible
  through the quantifier duality (see the Skolemization section below); by R4 exactly one of the
  pair is kept, and the choice is conventional.

## The expensive and aggressive levels, and their trajectory

The aggressive level is dominated by the **rewrite equalities**: the Boolean/ite/equality
`*_simplify` rules and `aci_simp`. Each is in principle a composition of elementary rewrites
glued by `refl`/`trans`/`cong`/`bind` — exactly what `rare_rewrite` chains express. Reducing them
requires either an external oracle (as the hole elaboration already does for `all_simplify` and
`rare_rewrite`) or instrumenting the deterministic simplification checkers to record rewrite
traces. Deterministic, no search — but a large engineering effort, hence deferred.

The quantifier-level rewrites (`qnt_simplify`, `qnt_join`, `qnt_rm_unused`, the miniscoping
rules) are aggressive for a different reason: not engineering volume, but a missing primitive.
Rewriting *below* a binder already works today (`bind` + `rare_rewrite`); these rules rewrite the
binder itself — eliminating, shrinking, merging, or duplicating the quantifier — which `bind`
cannot express, so they wait on *binder-pattern* RARE rules (variable-list parameters in binding
position; see the RARE chapter).

The expensive level collects the schemes that are cheap in steps but upgrade the required
checking power: the `la_mult_*` family and the arithmetic `*_simplify` members through
`poly_simp` (the purely arithmetic simplifications — `prod_simplify`, `sum_simplify`,
`minus_simplify`, `unary_minus_simplify` — have both routes: rename to `poly_simp` with a ring
check and zero new steps, or a RARE trace with syntactic checks at trace-length cost),
`shuffle` and `la_disequality` through `aci_simp`/`la_rw_eq`, and `nary_elim` (a promotion
candidate instead: the polyequality elaboration itself emits it).

## Extra rules beyond the specification

Carcara checks several rules that are not among the 120 specification rules. Classified the same
way:

| rule | level | reduction |
|---|---|---|
| `eq_mp` | reducible (**done**) | `equiv_pos2` + `resolution` (local elaboration) |
| `bounded_farkas` | reducible (**done**) | `la_generic` with inferred coefficients (local elaboration) |
| `and_intro` | reducible | `and_neg` + one `resolution` with explicit pivots |
| `strict_resolution` | core variant | strict form of `resolution` used after elaboration |
| `poly_simp` | **core** (computational) | ring-normalization primitive; see the arithmetic section |
| `la_mult_pos_pos` | proposed core axiom | `(> x 0) ∧ (> y 0) → (> (* x y) 0)`; base of the `la_mult_*` reductions |
| `la_mult_sign` (`alethe-toolkit` branch) | expensive | O(n) fold of `la_mult_pos_pos` + `poly_simp` + `la_generic` |
| `la_mult_abs_comparison` (`alethe-toolkit` branch) | aggressive | reducible to the same base once an `abs` definitional rewrite exists |
| `evaluate`, `mod_simplify`, `all_simplify` | aggressive (rewrite tier) | `all_simplify` already oracle-reducible via the hole pass |
| strings, PB, cutting-planes, arrays, DRUP, `sat_refutation` | aggressive (theory extensions) | `sat_refutation` oracle-reducible via its dedicated pass |

## Divergences from the specification

Two points where this classification deliberately diverges, worth raising with the Alethe
specification maintainers:

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
   needs to be primitive (see the Skolemization section); making the reduction applicable to
   existing proofs requires generalizing `bind` to the choice binder, which is proposed as a spec
   extension.
6. **Extend `connective_def` with implication**: adding `(φ₁ → φ₂) ≈ (¬φ₁ ∨ φ₂)` to
   `connective_def`'s definition list lets the three `implies` CNF axioms reduce like the `xor`
   and `ite` families, shrinking the axiomatic CNF base to the `and`/`or`/`equiv` families.
7. **Adopt the inductive side condition for `onepoint`**: the spec's "positive polarity" prose
   underdetermines (and naively misstates) the rule's applicability; the guarded-occurrence
   grammar implemented by Carcara's `extract_points` should become the official side condition —
   it is simultaneously the induction structure of the rule's elaboration (see "Elaborating
   `onepoint`").

## Validation

Each reduction recipe is validated by:

1. a hand-worked before/after example in this chapter or the classification table;
2. a minimal problem/proof pair exercising the rule, elaborated with the default pipeline and
   re-checked in elaborated (strict) mode, with a vocabulary check asserting that every output rule
   is core or an unapplied expensive/aggressive rule;
3. corpus-level measurement of elaborated-proof size and checking time using the benchmarking
   infrastructure, before any reduction is made default-on.
