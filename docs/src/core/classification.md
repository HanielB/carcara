# Rule classification

The full classification of the 120 Alethe specification rules, in specification order. Tiers are
**core** (elaboration target), **reducible** (cheap reduction into core exists — recipe given), and
**leaf** (theory/rewrite schema, accepted in elaborated output for now). See the
[parent chapter](../core.md) for the cost criterion (R1–R4) and the worked-out recipes.

The *check* column states the checking complexity of the steps a reduction emits: *syntactic* (pure
matching), *Farkas* (arithmetic certificate checking, via `la_generic`), or *oracle* (external
solver). The *status* column tracks Carcara's elaboration: *done* (the reduction is implemented),
*planned*, *—* (core, nothing to reduce), or *accepted* (leaf).

Tally: 42 core, 32 reducible, 46 leaf.

## Special and structural rules

| rule | tier | reduces to | steps | check | status / notes |
|---|---|---|---|---|---|
| `assume` | core | — | | | polyeq elaboration already makes non-syntactic matches explicit |
| `hole` | core | — | | | terminal; taints validity ("core modulo holes") |
| `true` | core | — | | | |
| `false` | core | — | | | |
| `not_not` | core | — | | | primitive for explicit double-negation merging; deriving it would pull in the rewrite tier |
| `th_resolution` | reducible | `resolution` | 0 | syntactic | planned; same rule per the spec, normalize the name |
| `resolution` | core | — | | | local elaboration already adds explicit pivots |
| `tautology` | reducible | `true` | 1 | syntactic | planned; conclusion is literally `⊤`; drops the premise from the DAG |
| `contraction` | core | — | | | |
| `subproof` | core | — | | | the discharge vehicle for all clausal-tautology reductions |

## Linear arithmetic

| rule | tier | reduces to | steps | check | status / notes |
|---|---|---|---|---|---|
| `la_generic` | core | — | | | the computational LA core (Farkas certificates) |
| `lia_generic` | reducible (oracle) | full subproof | — | oracle | done — hole elaboration pass, requires external solver |
| `la_disequality` | leaf | — | | | negated literal is a disequality; not a Farkas consequence |
| `la_totality` | reducible | `la_generic` + `or_neg` ×2 + `resolution` ×2 + `contraction` | 6 | Farkas + syntactic | planned; unit-clause-with-`or` packaging |
| `la_tautology` | reducible | `la_generic` (coeff `[1]`, or `[1,1]` + `or` packaging) | 1–6 | Farkas + syntactic | planned; the spec itself states the equivalence |
| `la_mult_pos` | leaf | — | | | nonlinear multiplication |
| `la_mult_neg` | leaf | — | | | nonlinear multiplication |

## Binders and quantifiers

| rule | tier | reduces to | steps | check | status / notes |
|---|---|---|---|---|---|
| `bind` | core | — | | | |
| `sko_ex` | core | — | | | binder primitive (nested choice terms) |
| `sko_forall` | core | — | | | binder primitive |
| `forall_inst` | core | — | | | polyeq elaboration already normalizes it |
| `qnt_cnf` | leaf | — | | | spec-declared placeholder; treated as hole-like |
| `onepoint` | core | — | | | binder primitive; spec-acknowledged proof gap |
| `qnt_join` | leaf | — | | | |
| `qnt_rm_unused` | leaf | — | | | |
| `miniscope_distribute` | leaf | — | | | |
| `miniscope_split` | leaf | — | | | |
| `miniscope_ite` | leaf | — | | | |
| `let` | core | — | | | |
| `bind_let` | core | — | | | |

## Equality

| rule | tier | reduces to | steps | check | status / notes |
|---|---|---|---|---|---|
| `refl` | core | — | | | the only rule applying the context |
| `trans` | core | — | | | |
| `cong` | core | — | | | |
| `eq_reflexive` | reducible | `refl` (empty context) | 1 | syntactic | planned |
| `eq_transitive` | reducible | subproof + `trans` (+ `symm`) | ≤ 2n | syntactic | planned; current local elaboration canonicalizes flips but keeps the rule |
| `eq_congruent` | reducible | subproof + `cong` (+ `symm`) | ≤ 2n+2 | syntactic | planned; ditto |
| `eq_congruent_pred` | reducible | subproof + `cong` + `equiv_pos2` + `resolution` | ≤ 2n+4 | syntactic | planned; see the spec-divergence note on its conclusion shape |
| `symm` | core | — | | | kept against the spec's "superfluous" note: explicit symmetry for elaborated output |
| `not_symm` | reducible | subproof + `symm` + `resolution` | 4 | syntactic | planned |
| `eq_symmetric` | reducible | subproof + `symm` | 3 | syntactic | planned |

## Premise clausification rules

All reduce by the axiom + `resolution` pattern (2 steps each, syntactic, explicit pivot = the
premise formula); all planned. The `equiv` family crosses indices.

| rule | axiom | | rule | axiom |
|---|---|---|---|---|
| `and` (k) | `and_pos` (k) | | `equiv1` | `equiv_pos2` |
| `not_or` (k) | `or_neg` (k) | | `equiv2` | `equiv_pos1` |
| `or` | `or_pos` | | `not_equiv1` | `equiv_neg2` |
| `not_and` | `and_neg` | | `not_equiv2` | `equiv_neg1` |
| `xor1` | `xor_pos1` | | `ite1` | `ite_pos1` |
| `xor2` | `xor_pos2` | | `ite2` | `ite_pos2` |
| `not_xor1` | `xor_neg1` | | `not_ite1` | `ite_neg1` |
| `not_xor2` | `xor_neg2` | | `not_ite2` | `ite_neg2` |
| `implies` | `implies_pos` | | `not_implies1` | `implies_neg1` |
| `not_implies2` | `implies_neg2` | | | |

## Clausal CNF axioms (all core)

`and_pos`, `and_neg`, `or_pos`, `or_neg`, `xor_pos1`, `xor_pos2`, `xor_neg1`, `xor_neg2`,
`implies_pos`, `implies_neg1`, `implies_neg2`, `equiv_pos1`, `equiv_pos2`, `equiv_neg1`,
`equiv_neg2`, `ite_pos1`, `ite_pos2`, `ite_neg1`, `ite_neg2` — 19 rules. One side of each
axiom/premise-rule pair must be primitive (R4); the premise-free side wins (O(1) syntactic check,
usable in resolution chains without subproof wrappers).

## Structural clause rules

| rule | tier | reduces to | steps | check | status / notes |
|---|---|---|---|---|---|
| `weakening` | core | — | | | not derivable without rewriting consumers (R3) |
| `reordering` | reducible | (eliminated) | 0 | — | done — reordering pass recomputes downstream conclusions |
| `shuffle` | leaf | — | | | term-level permutation; comm/assoc rewrite expansion is O(n²), fails R1 |

## Definitional

| rule | tier | reduces to | steps | check | status / notes |
|---|---|---|---|---|---|
| `connective_def` | core | — | | | propositional instances O(1)-derivable, quantifier-duality instance is not; kept whole |

## Rewrite equalities (all leaf)

`and_simplify`, `or_simplify`, `not_simplify`, `implies_simplify`, `equiv_simplify`,
`bool_simplify`, `ac_simp`, `aci_simp`, `ite_simplify`, `qnt_simplify`, `eq_simplify`,
`div_simplify`, `prod_simplify`, `unary_minus_simplify`, `minus_simplify`, `sum_simplify`,
`comp_simplify` — 17 rules. Long-term trajectory: `rare_rewrite` chains, via oracle (extending the
hole pass) or by instrumenting the simplification checkers to record rewrite traces.

## Structural transformations (all leaf)

| rule | notes |
|---|---|
| `distinct_elim` | |
| `la_rw_eq` | fixed schema `(t ≈ u) ≈ (t ≤ u ∧ u ≤ t)`; rewrite-tier candidate |
| `nary_elim` | promotion candidate: the polyeq elaboration itself emits it |
| `bfun_elim` | polyeq elaboration normalizes but keeps it |
| `ite_intro` | veriT implementation artifact (spec's own remark) |

## Bitblasting (all leaf)

`bitblast_extract`, `bitblast_concat`, `bitblast_sext`, `bitblast_eq`, `bitblast_ult`,
`bitblast_slt`, `bitblast_add`, `bitblast_neg`, `bitblast_mult`, `bitblast_and`, `bitblast_or`,
`bitblast_xor`, `bitblast_xnor`, `bitblast_not` — 14 rules. Reducible in principle to Boolean
reasoning of size O(width²); low payoff.

## RARE

| rule | tier | reduces to | steps | check | status / notes |
|---|---|---|---|---|---|
| `rare_rewrite` | core | — | | | the designated rewrite primitive; oracle-checkable today |
| `multi_rare_rewrite` | reducible | `rare_rewrite` chain + `trans`/`cong` | O(k·depth) | syntactic | planned; validate rule-position semantics first |
