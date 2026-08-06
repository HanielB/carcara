# Rule classification

The full classification of the 120 Alethe specification rules, organized by *concern category*
(structural, clausal, binder, equality & rewriting, arithmetic, bitvector, legacy). Each category
section opens with the *proof system* it embodies — first abstractly, then as concretized by the
category's core rules — followed by its rules grouped by *reducibility level*:

- **core** — the elaboration target;
- **reducible** — a reduction meeting the criteria R1–R4 exists (linear size, checks staying
  within syntactic matching plus what the step already required, local, non-circular);
- **expensive** — a concrete, small-step-count scheme exists, but it *upgrades the checking
  power* the step requires (e.g. a syntactic schema becomes a `poly_simp` ring check or an
  `aci_simp` ACI-normalization check) or depends on a proposed-but-not-yet-adopted rule;
- **aggressive** — a scheme exists in principle but is trace-replay or program-like, needs
  missing infrastructure (RARE under binders, `bbterm` expansion, evaluation operators, checker
  instrumentation), or has severe worst-case size. The exemplar is elaborating `poly_simp` itself
  into `rare_rewrite` chains — reducing not just a rule but the trust base.

Legacy rules sit outside the ladder: their level is **removal** (solvers should stop emitting
them, or the specification should replace them). See the [parent chapter](../core.md) for the
criteria and the worked-out recipes; the RARE rules required by the rewrite-based schemes are
catalogued in [RARE rules for the rewrite routes](./rare-rules.md).

The *check* column states the checking complexity of the steps a scheme emits: *syntactic* (pure
matching), *Farkas* (arithmetic certificate checking, via `la_generic`), *ring* (polynomial
normalization, via `poly_simp`), or *oracle* (external solver). The *status* column tracks
Carcara's elaboration: *done*, *planned*, or *—* (core, nothing to reduce).

## Summary

| category | total | core | reducible | expensive | aggressive | removal |
|---|---|---|---|---|---|---|
| structural | 3 | 3 | 0 | 0 | 0 | 0 |
| clausal | 47 | 25 | 22 | 0 | 0 | 0 |
| binder | 13 | 6 | 1 | 0 | 6 | 0 |
| equality & rewriting | 25 | 6 | 7 | 2 | 10 | 0 |
| arithmetic | 13 (+1) | 1 (+1) | 2 | 9 | 1 | 0 |
| bitvector | 14 | 0 | 0 | 0 | 14 | 0 |
| legacy | 5 | 0 | 0 | 0 | 0 | 5 |
| **total** | **120** | **41** | **32** | **11** | **31** | **5** |

The "+1" in the arithmetic row is the extra (non-specification) rule `poly_simp`, promoted into
the core as the ring-normalization primitive; totals count specification rules only. The new
axiom `la_mult_pos_pos` is proposed as the base of the nonlinear multiplication schemes.

## Structural

**Proof system.** The judgment structure of the calculus: clauses as sequents, hypothetical
reasoning by assumption introduction and discharge, and a marked escape hatch for unverified
reasoning. Concretely: `assume` introduces hypotheses, `subproof` discharges them into a clause
(implication introduction in clausal form — the vehicle for all clausal-tautology reductions),
and `hole` marks trust failures.

3 rules, all core.

| rule | level | notes |
|---|---|---|
| `assume` | core | polyeq elaboration already makes non-syntactic matches explicit |
| `subproof` | core | the discharge vehicle for all clausal-tautology reductions |
| `hole` | core | terminal; taints validity ("core modulo holes") |

## Clausal

**Proof system.** Ground resolution over a Tseitin-style CNF encoding: a refutationally complete
propositional calculus consisting of binary resolution with factoring and weakening, applied to
*defining clauses* that relate each connective to its arguments. Concretely: `resolution` (with
explicit pivots), `contraction` (factoring), `weakening`, the polarity units `true`/`false`,
`not_not` for explicit double-negation merging, and the 19 `*_pos`/`*_neg` axioms as the defining
clauses of `and`, `or`, `xor`, `=>`, Boolean `=`, and `ite`.

47 rules: 25 core, 22 reducible.

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

**Proof system.** First-order binder handling in the tradition of Hilbert's ε-calculus:
α-conversion and congruence under binders, universal instantiation, Skolemization via the choice
operator, definition unfolding, and guarded quantifier elimination. Concretely: `bind`
(α-renaming and congruence under `∀`/`∃` — proposed to be generalized to `choice`),
`forall_inst` (∀-elimination), `sko_forall` (the ε-axiom; `sko_ex` derived through the duality),
`let`/`bind_let` (definition unfolding), and `onepoint` (guarded quantifier elimination —
candidate for derivation).

13 rules: 6 core, 1 reducible, 6 aggressive.

### Core (6)

| rule | notes |
|---|---|
| `bind` | proposed to be generalized to the `choice` binder (see parent chapter) — needed to reason under Skolem witnesses |
| `let` | |
| `bind_let` | emitted by the polyeq elaboration itself |
| `onepoint` | elaboration scheme identified (two implications + derivable iff-introduction; see parent chapter) — promotion candidate pending validation; would discharge the spec-acknowledged proof gap |
| `sko_forall` | the designated Skolemization primitive; the spec's n-ary statement is erroneous (divergence 4) and must be fixed to the sequential choice-term form implementations already use |
| `forall_inst` | polyeq elaboration already normalizes it |

### Reducible (1)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `sko_ex` | `connective_def` (duality) + `sko_forall` + `cong` ×2 + `not-not` rewrite + `trans` | 6 (any n) | syntactic | planned; mutually dual with `sko_forall` — either could be the primitive (R4 picks one). Elaborating *existing* steps additionally needs `bind` generalized to `choice` to bridge the `∃`-shaped vs `¬∀¬`-shaped witnesses |

### Aggressive (6)

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

**Proof system.** Equational logic in Birkhoff's sense — reflexivity, symmetry, transitivity,
congruence, and closure under contexts — extended by an axiom-schema layer of oriented rewrite
rules. Concretely: `refl` (which also applies the context substitution), `symm`, `trans`, and
`cong` form the equational base; `connective_def` contributes the definitional axioms of the
connectives; and `rare_rewrite` is the generic interface through which arbitrary equational
axiom schemas (RARE rules) enter the system. The clausal `eq_*` forms are the same system
repackaged as premise-free clauses through `subproof` discharge.

25 rules: 6 core, 7 reducible, 2 expensive, 10 aggressive.

### Core (6)

| rule | notes |
|---|---|
| `refl` | the only rule applying the context |
| `trans` | |
| `cong` | |
| `symm` | kept against the spec's "superfluous" note: explicit symmetry for elaborated output |
| `connective_def` | propositional instances O(1)-derivable, quantifier-duality instance is not; kept whole |
| `rare_rewrite` | the designated rewrite primitive; oracle-checkable today |

### Reducible (7)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `eq_reflexive` | `refl` (empty context) | 1 | syntactic | planned |
| `eq_transitive` | subproof + `trans` (+ `symm`) | ≤ 2n | syntactic | planned; current local elaboration canonicalizes flips but keeps the rule |
| `eq_congruent` | subproof + `cong` (+ `symm`) | ≤ 2n+2 | syntactic | planned; ditto |
| `eq_congruent_pred` | subproof + `cong` + `equiv_pos2` + `resolution` | ≤ 2n+4 | syntactic | planned; see the spec-divergence note on its conclusion shape |
| `eq_symmetric` | subproof + `symm` | 3 | syntactic | planned |
| `not_symm` | subproof + `symm` + `resolution` | 4 | syntactic | planned |
| `multi_rare_rewrite` | `rare_rewrite` chain + `trans`/`cong` | O(k·depth) | syntactic | planned; validate rule-position semantics first |

### Expensive (2)

| rule | reduction scheme | cost | what makes it expensive |
|---|---|---|---|
| `shuffle` | `aci_simp` (rename) | 0 | the check coarsens from multiset comparison to full ACI normalization |
| `nary_elim` | chain of binary-associativity `rare_rewrite` steps | O(n) | the polyeq elaboration itself emits it (near-circular); promotion-to-core candidate instead |

### Aggressive (10)

| rule | reduction scheme | cost | missing prerequisite / blocker |
|---|---|---|---|
| `and_simplify`, `or_simplify`, `not_simplify`, `implies_simplify`, `equiv_simplify`, `bool_simplify`, `ite_simplify`, `eq_simplify` | `rare_rewrite` chain glued by `trans`/`cong`, replaying the rewrite trace of the fixpoint | O(trace) | instrumenting the simplification checkers to record traces (or oracle via the hole pass); RARE coverage of each rewrite |
| `aci_simp` | elementary assoc/comm/identity/idempotence rewrites | O(n²) worst case | fails R1; no canonical ACI normal form (spec's own remark) — kept as the designated ACI primitive |
| `distinct_elim` | single `rare_rewrite` instance | 1 | an n-ary RARE rule for `distinct` needs a recursive Eunoia *program* (arity-dependent output), including the Bool special case (> 2 Bool arguments → ⊥) |

## Arithmetic

**Proof system.** Certificate checking for ordered-ring reasoning along three axes: Farkas'-lemma
combinations for *linear order* consequences, polynomial identity (ring normalization) for the
*equational* part, and positivity of products for the *nonlinear order* part. Concretely:
`la_generic` (Farkas certificates), `poly_simp` (ring normalization; the extra rule promoted into
the core), and the proposed axiom `la_mult_pos_pos` (`(> x 0) ∧ (> y 0) → (> (* x y) 0)`, the
positive cone closed under multiplication).

13 specification rules (1 core, 2 reducible, 9 expensive, 1 aggressive) plus the extra rule
`poly_simp` in the core. See the
[arithmetic section](../core.md#arithmetic-la_generic-and-poly_simp-as-the-computational-core) of
the parent chapter for the recipes.

### Core (1 + 1 extra)

| rule | notes |
|---|---|
| `la_generic` | the linear computational primitive (Farkas certificates) |
| `poly_simp` (extra) | the nonlinear computational primitive: unit polynomial equality, checked by ring-normalizing both sides. Its own elaboration into `rare_rewrite` chains is the *aggressive* exemplar — see the parent chapter |

### Reducible (2)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `la_totality` | `la_generic` + `or_neg` ×2 + `resolution` ×2 + `contraction` | 6 | Farkas + syntactic | planned; unit-clause-with-`or` packaging |
| `la_tautology` | `la_generic` (coeff `[1]`, or `[1,1]` + `or` packaging) | 1–6 | Farkas + syntactic | planned; the spec itself states the equivalence |

### Expensive (9)

| rule | reduction scheme | cost | what makes it expensive |
|---|---|---|---|
| `la_mult_pos` | `la_mult_pos_pos` + `poly_simp` + `la_generic` (+ `cong`, case splits for non-strict forms) | O(1) template | a syntactic schema becomes ring + Farkas checking; needs the proposed `la_mult_pos_pos` axiom |
| `la_mult_neg` | same, with `la_generic` sign-flip preprocessing | O(1) template | ditto |
| `la_disequality` | subproof + `la_rw_eq` + `and_neg` + `equiv_pos1` + `resolution` (order antisymmetry via `la_rw_eq`) | ~7 (O(1)) | relies on `la_rw_eq` staying in the vocabulary |
| `la_rw_eq` | single `rare_rewrite` instance | 1 | needs the `(t ≈ u) ≈ (t ≤ u ∧ u ≤ t)` RARE rule adopted |
| `prod_simplify`, `sum_simplify`, `minus_simplify`, `unary_minus_simplify` | rename to `poly_simp`; *alternative*: `rare_rewrite` chain over the RARE arithmetic rules | 0, or O(trace) via RARE | per-schema syntactic checking becomes the ring check (the RARE path keeps checks syntactic at trace-length cost) |
| `div_simplify` | `poly_simp` for real division by constants; `evaluate`/RARE for the integer `div`/`mod` cases | O(1) | integer division semantics are outside the ring primitive |

### Aggressive (1)

| rule | reduction scheme | cost | missing prerequisite / blocker |
|---|---|---|---|
| `comp_simplify` | `rare_rewrite` chain for the relational rewrites | O(trace) | RARE coverage of the comparison rewrites, including evaluation operators for constant folding |

## Bitvector

**Proof system.** Bit-blasting semantics: bitvector terms interpreted as tuples of Booleans, each
operation defined bit-wise. There are no core rules in this category — the 14 `bitblast_*` axioms
are per-operation definitional schemas, and abstractly the whole category compiles down to the
*clausal* system over `bbterm` definitions (which the spec itself notes are expressible with
standard SMT-LIB functions).

14 rules, all aggressive: `bitblast_extract`, `bitblast_concat`, `bitblast_sext`, `bitblast_eq`,
`bitblast_ult`, `bitblast_slt`, `bitblast_add`, `bitblast_neg`, `bitblast_mult`, `bitblast_and`,
`bitblast_or`, `bitblast_xor`, `bitblast_xnor`, `bitblast_not`.

Shared reduction scheme: unfold the bit-level definition via `cong` plus the Boolean CNF axioms,
after expanding the `bbterm` machinery definitionally. Cost: O(n) in the conclusion, but the
conclusion is already O(width) to O(width²) large, so the constants are big. Missing
prerequisite: `bbterm` definitional expansion; and the payoff is low, since consumers prefer the
schemas.

## Legacy

No proof system — placeholders and solver-implementation artifacts. Unlike the other categories,
the long-term goal here is not reduction but *removal*: solvers should stop emitting them, or the
specification should replace them with principled counterparts. 5 rules, all at level "removal".

| rule | fallback scheme | notes |
|---|---|---|
| `lia_generic` | full sub-proof from an external solver (oracle) | done — hole elaboration pass; not checkable at all without the oracle |
| `qnt_cnf` | oracle only | spec-declared "placeholder rule" for the whole quantifier clausification — there is no defined semantics to reduce; treated as hole-like |
| `ite_intro` | removal (veriT-side): with the internal ite constants gone, the step degenerates to `refl` | artifact of veriT's internal ite constants (the spec's own remark); source of the ite-reordering polyeq quirk |
| `bfun_elim` | case expansion over Boolean arguments via ite/equiv tautologies | O(2^k) in the number of Boolean arguments — fails R1; removal preferred. veriT preprocessing artifact; polyeq elaboration normalizes but keeps it |
| `ac_simp` | decompose into one `aci_simp` step per single-connective layer, glued by `cong`/`trans` (O(d), d = alternation depth) | superseded by the more general `aci_simp`, which however normalizes a single connective at a time where `ac_simp` handles `∧` and `∨` simultaneously; removal in favor of `aci_simp` preferred over reduction |

## Extra rules beyond the specification

Carcara checks several rules that are not among the 120 specification rules. Classified the same
way, with their concern category noted:

| rule | category | level | reduction |
|---|---|---|---|
| `eq_mp` | clausal | reducible (**done**) | `equiv_pos2` + `resolution` (local elaboration) |
| `and_intro` | clausal | reducible | `and_neg` + one `resolution` with explicit pivots |
| `strict_resolution` | clausal | core variant | strict form of `resolution` used after elaboration |
| `bounded_farkas` | arithmetic | reducible (**done**) | `la_generic` with inferred coefficients (local elaboration) |
| `poly_simp` | arithmetic | **core** (computational) | ring-normalization primitive; listed in the arithmetic core table above |
| `la_mult_pos_pos` | arithmetic | proposed core axiom | `(> x 0) ∧ (> y 0) → (> (* x y) 0)`; base of the `la_mult_*` schemes |
| `la_mult_sign` (`alethe-toolkit` branch) | arithmetic | expensive | O(n) fold of `la_mult_pos_pos` + `poly_simp` + `la_generic` |
| `la_mult_abs_comparison` (`alethe-toolkit` branch) | arithmetic | aggressive | reducible to the same base once an `abs` definitional rewrite exists |
| `evaluate`, `mod_simplify`, `all_simplify` | equality & rewriting | aggressive | `all_simplify` already oracle-reducible via the hole pass |
| strings, PB, cutting-planes, arrays, DRUP, `sat_refutation` | theory extensions | aggressive | `sat_refutation` oracle-reducible via its dedicated pass |
