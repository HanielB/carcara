# The core Alethe fragment

This chapter defines a *core* set of Alethe rules that is the intended target of Carcara's
elaboration: after the full elaboration pipeline runs, every step of the resulting proof should use
only core rules (or *leaf* rules, see below). This gives elaboration a precise specification, and it
shrinks the rule vocabulary that consumers of elaborated proofs — strict re-checking, and the
translation backends to other formats — have to support.

The classification covers all 120 rules of the Alethe specification, plus the extra rules Carcara
supports beyond the specification. The full rule-by-rule table is in the
[classification](./core/classification.md) subchapter. This chapter explains the criterion behind
the classification, the reduction recipes, and the borderline decisions.

## The three tiers

- **Core**: logical primitives that elaboration targets. Elaborated proofs may freely use them.
- **Reducible**: rules with a known, cheap reduction into core rules. Elaboration should eventually
  eliminate all of them from its output.
- **Leaf**: theory- or rewrite-level axiom schemas (bitblasting, the `*_simplify` family, etc.) with
  no cheap reduction today. They are accepted in elaborated output, but each has a documented
  long-term reduction trajectory (mostly towards `rare_rewrite`).

Of the 120 specification rules, this classification yields **42 core**, **32 reducible**, and
**46 leaf** rules.

The core property is defined *post-pipeline*: intermediate passes may emit non-core rules (e.g.
`reordering` steps, which the final pass of the default pipeline removes); only the output of the
full pipeline must be within core ∪ leaf. Proofs containing `hole`, `lia_generic` (without an
external solver), or `qnt_cnf` can only ever be "core modulo holes".

## The cost criterion

A rule is classified as reducible only if it has a reduction satisfying all of:

- **R1 (linear)**: the reduction produces O(n) new steps, where n is the size of the step (clause
  length plus premise count), with a small constant;
- **R2 (syntactic)**: every emitted step is checkable by purely syntactic matching — no search, no
  polyequality reasoning, and all resolution pivots explicit;
- **R3 (local)**: the reduction replaces a single proof node without rewriting any of its consumers;
- **R4 (non-circular)**: for each pair of interderivable rules, exactly one side is kept as the
  axiom.

A rule that fails any of R1–R4 stays in the core (if it is a logical primitive) or in the leaf tier
(if it is a theory/rewrite schema). The point of R1–R2 is that reducing a rule must not make proofs
meaningfully larger or harder to check — a reduction that needs many steps, or steps whose checking
requires search, defeats the purpose.

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

## Linear arithmetic: `la_generic` as the computational core

`la_generic` is kept core: checking it requires verifying a Farkas certificate, which is arithmetic
rather than syntactic matching, but expanding it into rewrite chains would blow up unboundedly. Two
LA rules reduce to it:

- `la_tautology`, first form (a single trivially-unsatisfiable-when-negated inequality literal):
  `la_generic` with coefficient `[1]`.
- `la_tautology`, second form, and `la_totality`: both conclude a *unit clause containing a
  disjunction term* (a historical quirk noted in the specification). `la_generic` concludes a proper
  clause, so the reduction needs a constant-size repackaging from `(cl φ1 φ2)` to
  `(cl (or φ1 φ2))`: two `or_neg` steps and two resolutions plus a `contraction` — six steps total,
  still O(1).

`la_disequality` stays leaf: the negation of its positive equality literal is a *disequality*, which
a Farkas combination cannot consume; reducing it would need case-split machinery. `la_mult_pos` and
`la_mult_neg` involve nonlinear multiplication and also stay leaf. `lia_generic` is special: it is
not checkable at all without an external solver, and is classified as *oracle-reducible* — the
existing hole elaboration pass replaces it with a full sub-proof produced by an external solver.

## Other reducible rules

- `eq_reflexive` is `refl` with an empty context: a rename, one step.
- `eq_symmetric` reduces to `subproof { assume (= t1 t2); symm; discharge }` — three steps.
- `not_symm` reduces to the same subproof plus one resolution against the premise — four steps.
- `tautology` concludes exactly `⊤`, so it reduces to a premise-free `true` step. Note this drops
  the premise from the proof DAG (relevant for slicing).
- `th_resolution` is, per the specification, the same rule as `resolution`; elaboration normalizes
  the name.
- `reordering` is already eliminated by the reordering elaboration pass, which recomputes downstream
  conclusions instead.
- `multi_rare_rewrite` reduces to a chain of `rare_rewrite` steps glued with `trans`/`cong`
  scaffolding (the exact recipe depends on the rule-position semantics and should be validated when
  implemented).

## Borderline rules kept in the core

- **`symm`** — kept *against* the specification's "technically superfluous" note. That note relies
  on the implicit reordering of equalities; the whole point of elaboration is to make implicit
  reasoning explicit, so elaborated output needs an explicit symmetry step. Dropping `symm` would
  push implicit reordering back onto every consumer.
- **`weakening`** — not derivable: resolution cannot introduce arbitrary literals, and the only
  elimination is rewriting all consumers, which violates R3. The elaborator itself emits it
  (uncrowding).
- **`not_not`** — deriving it needs the rewrite `¬¬φ ≈ φ` (i.e. `not_simplify`) plus `equiv_pos2`
  and resolution, which pulls the rewrite tier into the propositional core. It is the primitive that
  makes the implicit merging of double negations in resolution explicit.
- **The 19 `*_pos`/`*_neg` axioms** — one side of the axiom/premise-rule pairs must be primitive
  (R4), and cross-reductions within the family (e.g. `equiv_pos1` from `equiv_pos2` via symmetry of
  the equivalence) fail R2.
- **`connective_def`** — its propositional instances are derivable at O(1) via `equiv_neg1/2` and
  the branch tautologies, but the quantifier-duality instance (`¬∀x̄.φ ≈ ∃x̄.¬φ`) requires reasoning
  under binders that no core rule provides. Kept whole for uniformity.
- **`la_generic`** and **`rare_rewrite`** — the designated computational and rewrite primitives, as
  discussed above.
- **The binder rules** (`bind`, `let`, `bind_let`, `onepoint`, `sko_ex`, `sko_forall`) — primitives
  with no reduction candidates. `onepoint` additionally has a specification-acknowledged gap (the
  substitution into the point terms is unproved).

## The leaf tier and its trajectory

The leaf tier is dominated by two families:

- **Rewrite equalities (17 rules)**: the `*_simplify` family, `ac_simp`, `aci_simp`. Each is in
  principle a composition of elementary rewrites glued by `refl`/`trans`/`cong`/`bind` — exactly
  what `rare_rewrite` chains express. Reducing them requires either an external oracle (as the hole
  elaboration already does for `all_simplify` and `rare_rewrite`) or instrumenting the deterministic
  simplification checkers to record rewrite traces. Deterministic, no search — but a large
  engineering effort, hence deferred.
- **Bitblasting (14 rules)**: reducible in principle to Boolean reasoning of size quadratic in the
  bit-width; low payoff, since consumers prefer the leaves.

The remaining leaves are structural transformations (`distinct_elim`, `nary_elim`, `bfun_elim`,
`ite_intro`, `la_rw_eq`, `shuffle`, `qnt_join`, `qnt_rm_unused`), the miniscoping rules, and
`qnt_cnf`, which the specification itself declares a placeholder (treated as hole-like). `shuffle`
fails R1: expressing an arbitrary permutation via commutativity/associativity rewrites is O(n²) in
the worst case. `nary_elim` is a promotion candidate: the polyequality elaboration itself emits it.

## Extra rules beyond the specification

Carcara checks several rules that are not among the 120 specification rules. Classified the same
way:

| rule | class | reduction |
|---|---|---|
| `eq_mp` | reducible (**done**) | `equiv_pos2` + `resolution` (local elaboration) |
| `bounded_farkas` | reducible (**done**) | `la_generic` with inferred coefficients (local elaboration) |
| `and_intro` | reducible | `and_neg` + one `resolution` with explicit pivots |
| `strict_resolution` | core variant | strict form of `resolution` used after elaboration |
| `evaluate`, `mod_simplify`, `poly_simp`, `all_simplify` | leaf (rewrite tier) | `all_simplify` already oracle-reducible via the hole pass |
| strings, PB, cutting-planes, arrays, DRUP, `sat_refutation` | leaf (theory extensions) | `sat_refutation` oracle-reducible via its dedicated pass |

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

## Validation

Each reduction recipe is validated by:

1. a hand-worked before/after example in this chapter or the classification table;
2. a minimal problem/proof pair exercising the rule, elaborated with the default pipeline and
   re-checked in elaborated (strict) mode, with a vocabulary check asserting that every output rule
   is core or leaf;
3. corpus-level measurement of elaborated-proof size and checking time using the benchmarking
   infrastructure, before any reduction is made default-on.
