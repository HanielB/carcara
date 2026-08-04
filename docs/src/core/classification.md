# Rule classification

The full classification of the 120 Alethe specification rules, organized by *concern category*
(structural, clausal, binder, equality & rewriting, arithmetic, bitvector, legacy). Within each
category, rules are listed by tier: **core** (elaboration target), **reducible** (cheap reduction
into core exists — recipe given), and **leaf** (axiom schema accepted in elaborated output for
now). See the [parent chapter](../core.md) for the cost criterion (R1–R4) and the worked-out
recipes.

The *check* column states the checking complexity of the steps a reduction emits: *syntactic* (pure
matching), *Farkas* (arithmetic certificate checking, via `la_generic`), *ring* (polynomial
normalization, via `poly_simp`), or *oracle* (external solver). The *status* column tracks
Carcara's elaboration: *done* (the reduction is implemented), *planned*, *—* (core, nothing to
reduce), or *accepted* (leaf).

## Summary

| category | total | core | reducible | leaf |
|---|---|---|---|---|
| structural | 3 | 3 | 0 | 0 |
| clausal | 47 | 25 | 22 | 0 |
| binder | 13 | 7 | 0 | 6 |
| equality & rewriting | 25 | 6 | 8 | 11 |
| arithmetic | 13 (+1) | 1 (+1) | 4 | 8 |
| bitvector | 14 | 0 | 0 | 14 |
| legacy | 5 | 0 | 1 | 4 |
| **total** | **120** | **42** | **35** | **43** |

The "+1" in the arithmetic row is the extra (non-specification) rule `poly_simp`, promoted into
the core as the ring-normalization primitive; totals count specification rules only. The new axiom
`la_mult_pos_pos` is proposed as the base of the nonlinear multiplication reductions (see the
arithmetic category and the [extras](#extra-rules-beyond-the-specification) section).

For every **leaf** rule, the tables below also give a *reduction scheme*: the hypothetical
reduction it would have if the named prerequisite existed, with its cost. This makes visible *why*
each leaf is a leaf — which primitive is missing, or which cost bound (R1–R4) the reduction
violates — and how far each rule is from becoming reducible.

## Structural

The proof-structure rules: 3 rules, all core.

| rule | tier | notes |
|---|---|---|
| `assume` | core | polyeq elaboration already makes non-syntactic matches explicit |
| `subproof` | core | the discharge vehicle for all clausal-tautology reductions |
| `hole` | core | terminal; taints validity ("core modulo holes") |

## Clausal

The propositional/CNF layer: resolution and its bookkeeping, the premise-free CNF axioms, and the
premise-taking clausification rules. 47 rules: 25 core, 22 reducible.

### Core (25)

| rule | notes |
|---|---|
| `resolution` | local elaboration already adds explicit pivots |
| `contraction` | |
| `weakening` | not derivable without rewriting consumers (R3) |
| `true` | |
| `false` | |
| `not_not` | primitive for explicit double-negation merging; deriving it would pull in the rewrite tier |
| `and_pos` (k), `and_neg`, `or_pos`, `or_neg` (k), `xor_pos1/2`, `xor_neg1/2`, `implies_pos`, `implies_neg1/2`, `equiv_pos1/2`, `equiv_neg1/2`, `ite_pos1/2`, `ite_neg1/2` | the 19 CNF axioms. One side of each axiom/premise-rule pair must be primitive (R4); the premise-free side wins (O(1) syntactic check, usable in resolution chains without subproof wrappers) |

### Reducible (22)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `th_resolution` | `resolution` | 0 | syntactic | planned; same rule per the spec, normalize the name |
| `tautology` | `true` | 1 | syntactic | planned; conclusion is literally `⊤`; drops the premise from the DAG |
| `reordering` | (eliminated) | 0 | — | done — reordering pass recomputes downstream conclusions |
| 19 premise clausification rules | matching CNF axiom + `resolution` | 2 each | syntactic | planned; pivot = the premise formula |

The exact axiom pairings for the premise clausification rules (the `equiv` family crosses indices):

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

## Binder

Quantifier and binder handling. 13 rules: 7 core, 6 leaf.

### Core (7)

| rule | notes |
|---|---|
| `bind` | |
| `let` | |
| `bind_let` | emitted by the polyeq elaboration itself |
| `onepoint` | spec-acknowledged proof gap (substitution into the point terms) |
| `sko_ex` | binder primitive (nested choice terms) |
| `sko_forall` | binder primitive |
| `forall_inst` | polyeq elaboration already normalizes it |

### Leaf (6)

All six are quantifier-level rewrites blocked on the same missing prerequisite: a rewrite
primitive that works under binders (binder-aware RARE rules applied through `bind`).

| rule | reduction scheme | cost | missing prerequisite |
|---|---|---|---|
| `qnt_simplify` | binder-aware `rare_rewrite` chain + `bind`/`trans` | O(trace) | RARE under binders |
| `qnt_join` | single binder-aware rewrite schema + `bind` | O(1) | RARE under binders |
| `qnt_rm_unused` | single binder-aware rewrite schema + `bind` | O(1) | RARE under binders |
| `miniscope_distribute` | per-connective distribution schema + `bind`/`cong` scaffolding | O(n) | RARE under binders |
| `miniscope_split` | same | O(n) | RARE under binders |
| `miniscope_ite` | same | O(n) | RARE under binders |

## Equality and rewriting

The congruence-closure primitives, their clausal derivatives, and the term-rewriting schemas.
25 rules: 6 core, 8 reducible, 11 leaf.

### Core (6)

| rule | notes |
|---|---|
| `refl` | the only rule applying the context |
| `trans` | |
| `cong` | |
| `symm` | kept against the spec's "superfluous" note: explicit symmetry for elaborated output |
| `connective_def` | propositional instances O(1)-derivable, quantifier-duality instance is not; kept whole |
| `rare_rewrite` | the designated rewrite primitive; oracle-checkable today |

### Reducible (8)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `eq_reflexive` | `refl` (empty context) | 1 | syntactic | planned |
| `eq_transitive` | subproof + `trans` (+ `symm`) | ≤ 2n | syntactic | planned; current local elaboration canonicalizes flips but keeps the rule |
| `eq_congruent` | subproof + `cong` (+ `symm`) | ≤ 2n+2 | syntactic | planned; ditto |
| `eq_congruent_pred` | subproof + `cong` + `equiv_pos2` + `resolution` | ≤ 2n+4 | syntactic | planned; see the spec-divergence note on its conclusion shape |
| `eq_symmetric` | subproof + `symm` | 3 | syntactic | planned |
| `not_symm` | subproof + `symm` + `resolution` | 4 | syntactic | planned |
| `shuffle` | `aci_simp` (rename) | 0 | ACI normalization | planned; subsumption into a leaf — coarsens the check from multiset comparison to ACI equivalence |
| `multi_rare_rewrite` | `rare_rewrite` chain + `trans`/`cong` | O(k·depth) | syntactic | planned; validate rule-position semantics first |

### Leaf (11)

| rule | reduction scheme | cost | missing prerequisite / blocker |
|---|---|---|---|
| `and_simplify`, `or_simplify`, `not_simplify`, `implies_simplify`, `equiv_simplify`, `bool_simplify`, `ite_simplify`, `eq_simplify` | `rare_rewrite` chain glued by `trans`/`cong`, replaying the rewrite trace of the fixpoint | O(trace) | instrumenting the simplification checkers to record traces (or oracle via the hole pass); RARE coverage of each rewrite |
| `aci_simp` | elementary assoc/comm/identity/idempotence rewrites | O(n²) worst case | fails R1; no canonical ACI normal form (spec's own remark) — kept as the designated ACI primitive |
| `distinct_elim` | single `rare_rewrite` instance | 1 | an n-ary RARE rule for `distinct`, including the Bool special case (> 2 Bool arguments → ⊥) |
| `nary_elim` | chain of binary-associativity `rare_rewrite` steps | O(n) | the polyeq elaboration itself emits it (near-circular); promotion-to-core candidate instead |

## Arithmetic

13 specification rules (1 core, 4 reducible, 8 leaf) plus the extra rule `poly_simp` in the core.
The proposed axiom `la_mult_pos_pos` is the base of the nonlinear multiplication reductions — see
the
[arithmetic section](../core.md#arithmetic-la_generic-and-poly_simp-as-the-computational-core) of
the parent chapter.

### Core (1 + 1 extra)

| rule | notes |
|---|---|
| `la_generic` | the linear computational primitive (Farkas certificates) |
| `poly_simp` (extra) | the nonlinear computational primitive: unit polynomial equality, checked by ring-normalizing both sides. Itself admits an elaboration into `rare_rewrite` chains for consumers that do not trust the ring check — see the parent chapter |

### Reducible (4)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `la_totality` | `la_generic` + `or_neg` ×2 + `resolution` ×2 + `contraction` | 6 | Farkas + syntactic | planned; unit-clause-with-`or` packaging |
| `la_tautology` | `la_generic` (coeff `[1]`, or `[1,1]` + `or` packaging) | 1–6 | Farkas + syntactic | planned; the spec itself states the equivalence |
| `la_mult_pos` | `la_mult_pos_pos` + `poly_simp` + `la_generic` (+ `cong`, case splits for non-strict forms) | O(1) template | syntactic + Farkas + ring | planned; needs `poly_simp` core promotion and the `la_mult_pos_pos` axiom |
| `la_mult_neg` | same, with `la_generic` sign-flip preprocessing | O(1) template | syntactic + Farkas + ring | planned; ditto |

### Leaf (8)

| rule | reduction scheme | cost | missing prerequisite / blocker |
|---|---|---|---|
| `la_disequality` | subproof + `la_rw_eq` + `and_neg` + `equiv_pos1` + `resolution`: assume both inequalities, build the conjunction, and use `la_rw_eq` as the order-antisymmetry axiom to conclude the equality | ~7 (O(1)) | relies on `la_rw_eq` staying in the vocabulary — **promotion candidate to reducible** |
| `la_rw_eq` | single `rare_rewrite` instance | 1 | a RARE rule for `(t ≈ u) ≈ (t ≤ u ∧ u ≤ t)` |
| `prod_simplify`, `sum_simplify`, `minus_simplify`, `unary_minus_simplify` | rename to `poly_simp` — each instance is a unit polynomial equality; *alternative*: `rare_rewrite` chain over the RARE arithmetic rules, glued by `trans`/`cong` | 0, or O(trace) via RARE | none (given `poly_simp` in the core) — **promotion candidates to reducible**; the `poly_simp` path trades per-schema syntactic checking for the ring check, the RARE path keeps checking syntactic at the cost of trace-length proofs |
| `div_simplify` | `poly_simp` for real division by constants; `evaluate`/RARE for the integer `div`/`mod` cases | O(1) | integer division semantics are outside the ring primitive |
| `comp_simplify` | `rare_rewrite` chain for the relational rewrites | O(trace) | RARE coverage of the comparison rewrites |

## Bitvector

14 rules, all leaf: `bitblast_extract`, `bitblast_concat`, `bitblast_sext`, `bitblast_eq`,
`bitblast_ult`, `bitblast_slt`, `bitblast_add`, `bitblast_neg`, `bitblast_mult`, `bitblast_and`,
`bitblast_or`, `bitblast_xor`, `bitblast_xnor`, `bitblast_not`.

Shared reduction scheme: unfold the bit-level definition via `cong` plus the Boolean CNF axioms,
after expanding the `bbterm` machinery definitionally (the spec itself notes `bbterm` is
expressible with standard SMT-LIB functions). Cost: O(n) in the conclusion, but the conclusion is
already O(width) to O(width²) large, so the constants are big. Missing prerequisite: `bbterm`
definitional expansion; and the payoff is low, since consumers prefer the leaves.

## Legacy

Rules the specification itself flags as placeholders or solver-implementation artifacts. Unlike the
other categories, the long-term goal here is not reduction but *removal*: solvers should stop
emitting them, or the specification should replace them with principled counterparts. 5 rules:
1 reducible (via oracle), 4 leaf.

| rule | tier | reduction scheme | notes |
|---|---|---|---|
| `lia_generic` | reducible (oracle) | full sub-proof from an external solver | done — hole elaboration pass; not checkable at all without the oracle |
| `qnt_cnf` | leaf | oracle only | spec-declared "placeholder rule" for the whole quantifier clausification — there is no defined semantics to reduce; treated as hole-like |
| `ite_intro` | leaf | removal (veriT-side): with the internal ite constants gone, the step degenerates to `refl` | artifact of veriT's internal ite constants (the spec's own remark); source of the ite-reordering polyeq quirk |
| `bfun_elim` | leaf | case expansion over Boolean arguments via ite/equiv tautologies | O(2^k) in the number of Boolean arguments — fails R1; removal preferred. veriT preprocessing artifact; polyeq elaboration normalizes but keeps it |
| `ac_simp` | leaf | decompose into one `aci_simp` step per single-connective layer, glued by `cong`/`trans` through the alternating `∧`/`∨` structure (O(d), d = alternation depth) | superseded by the more general `aci_simp`, which however normalizes a single connective at a time where `ac_simp` handles `∧` and `∨` simultaneously; removal in favor of `aci_simp` preferred over reduction |

## Extra rules beyond the specification

Carcara checks several rules that are not among the 120 specification rules. Classified the same
way, with their concern category noted:

| rule | category | tier | reduction |
|---|---|---|---|
| `eq_mp` | clausal | reducible (**done**) | `equiv_pos2` + `resolution` (local elaboration) |
| `and_intro` | clausal | reducible | `and_neg` + one `resolution` with explicit pivots |
| `strict_resolution` | clausal | core variant | strict form of `resolution` used after elaboration |
| `bounded_farkas` | arithmetic | reducible (**done**) | `la_generic` with inferred coefficients (local elaboration) |
| `poly_simp` | arithmetic | **core** (computational) | ring-normalization primitive; listed in the arithmetic core table above |
| `la_mult_pos_pos` | arithmetic | proposed core axiom | `(> x 0) ∧ (> y 0) → (> (* x y) 0)`; base of the `la_mult_*` reductions |
| `la_mult_sign` (`alethe-toolkit` branch) | arithmetic | reducible | O(n) fold of `la_mult_pos_pos` + `poly_simp` + `la_generic` |
| `la_mult_abs_comparison` (`alethe-toolkit` branch) | arithmetic | leaf | reducible to the same base once an `abs` definitional rewrite exists |
| `evaluate`, `mod_simplify`, `all_simplify` | equality & rewriting | leaf | `all_simplify` already oracle-reducible via the hole pass |
| strings, PB, cutting-planes, arrays, DRUP, `sat_refutation` | theory extensions | leaf | `sat_refutation` oracle-reducible via its dedicated pass |
