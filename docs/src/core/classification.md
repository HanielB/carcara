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
  missing infrastructure (RARE under binders, evaluation operators, checker instrumentation), or
  has severe worst-case size. The exemplar is elaborating `poly_simp` itself into `rare_rewrite`
  chains — reducing not just a rule but the trust base.

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
| clausal | 47 | 12 | 33 | 2 | 0 | 0 |
| binder | 13 | 5 | 8 | 0 | 0 | 0 |
| equality & rewriting | 25 | 6 | 7 | 2 | 10 | 0 |
| arithmetic | 13 (+1) | 1 (+1) | 2 | 9 | 1 | 0 |
| bitvector | 14 | 14 | 0 | 0 | 0 | 0 |
| legacy | 5 | 0 | 0 | 0 | 0 | 5 |
| **total** | **120** | **41** | **50** | **13** | **11** | **5** |

The "+1" in the arithmetic row is the extra (non-specification) rule `poly_simp`, promoted into
the core as the ring-normalization primitive; totals count specification rules only. The new
axiom `la_mult_pos_pos` is proposed as the base of the nonlinear multiplication schemes.

## The judgment forms

Two judgment forms underlie all of the categories, and every proof-system description below is
phrased in terms of them:

- the **clause judgment** `▷ l₁, …, lₙ` — a sequent asserting the disjunction of the literals;
- the **contextual equality judgment** `Γ ▷ t ≈ u`, where the context `Γ` carries bound variables
  and substitution entries `x ↦ s`; semantically it asserts `σΓ(t) ≈ u`, which is why the topmost
  equality is *not* symmetric.

The structural category connects the two: subproofs let a derivation of one judgment under
hypotheses be discharged into a clause, and anchors let equality reasoning proceed under a
context. Each category below states its abstract inference rules over these judgments, then names
the core rules that concretize them.

## Structural

**Proof system.** Abstractly, the hypothetical-reasoning skeleton of natural deduction, over
clause judgments:

- **[hyp]** — introduce a hypothesis `φ`;
- **[discharge]** — from a derivation of `ψ` under hypotheses `φ₁, …, φₖ`, conclude the clause
  `▷ ¬φ₁, …, ¬φₖ, ψ` (implication introduction, in clausal form);
- **[oracle]** — assert any clause, marked as unverified.

Concretely: `assume` is [hyp], `subproof` with its `:discharge` annotation is [discharge] — the
vehicle for all clausal-tautology reductions — and `hole` is [oracle] (terminal, taints
validity).

3 rules, all core.

| rule | level | notes |
|---|---|---|
| `assume` | core | polyeq elaboration already makes non-syntactic matches explicit |
| `subproof` | core | the discharge vehicle for all clausal-tautology reductions |
| `hole` | core | terminal; taints validity ("core modulo holes") |

## Clausal

**Proof system.** Abstractly, ground resolution over a Tseitin-style CNF encoding — a
refutationally complete propositional calculus over clause judgments, with two consequence
readings:

- **[res]** — from `▷ C₁, l` and `▷ C₂, ¬l`, conclude `▷ C₁, C₂` (chained; pivot `l` explicit);
- **[rup]** — conclude `▷ C` whenever unit-propagating `¬C` over the premises yields a conflict
  (subsumes [res] chains, and absorbs the structural rules below);
- **[fact]** / **[weak]** — the structural rules of factoring (merge duplicate literals) and
  weakening (append literals);
- **[def]** — for each connective `∘`, its *defining clauses*: the CNF of `x ↔ ∘(x̄)` relating a
  formula to its immediate subformulas.

Concretely: `resolution` carries both [res] (the chain reading, explicit pivots, syntactic check
— what elaboration produces and strict mode checks) and [rup] (`rup_resolution`, unit
propagation); `true`/`false` are the polarity units and `not_not` normalizes literals with
stacked negations; the 8 retained CNF axioms are [def] for `and`, `or`, and Boolean `=`.
[fact]/[weak] are `contraction`/`weakening` — bookkeeping absorbed by the [rup] reading (hence
expensive, below); the [def] clauses for `xor`, `ite`, and `implies` are derived through
`connective_def` (the `implies` case via its proposed extension with `(φ₁→φ₂) ≈ (¬φ₁ ∨ φ₂)`,
divergence item 6).

47 rules: 12 core, 33 reducible, 2 expensive.

### Core (12)

| rule | notes |
|---|---|
| `resolution` | dual semantics, both core: chain-with-explicit-pivots (`resolution_with_args`, syntactic) and RUP consequence (`rup_resolution`, unit propagation) |
| `true` | |
| `false` | |
| `not_not` | primitive for explicit double-negation merging; deriving it would pull in the rewrite tier |
| `and_pos` (k), `and_neg`, `or_pos`, `or_neg` (k), `equiv_pos1/2`, `equiv_neg1/2` | the 8 retained CNF axioms. One side of each axiom/premise-rule pair must be primitive (R4); the `equiv` family is the bootstrap for unpacking `connective_def` equivalences; `and`/`or` are the Tseitin base every derivation re-clausifies into |

### Reducible (33)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `th_resolution` | `resolution` | 0 | syntactic | planned; same rule per the spec, normalize the name |
| `tautology` | `true` | 1 | syntactic | planned; conclusion is literally `⊤`; drops the premise from the DAG |
| `reordering` | (eliminated) | 0 | — | done — reordering pass recomputes downstream conclusions |
| `xor_pos1/2`, `xor_neg1/2`, `ite_pos1/2`, `ite_neg1/2` | `connective_def` + `equiv_pos1/2` + `and`/`or`/`implies` axioms (+ `not_not`) + `resolution` | ≤ ~10 each | syntactic | planned; unpack the connective's definition and re-clausify (worked example in the parent chapter) |
| `implies_pos`, `implies_neg1`, `implies_neg2` | `connective_def` (proposed `→` extension) + `equiv_pos1/2` + `or_pos`/`or_neg` (+ `not_not`) + `resolution` | 4–6 each | syntactic | planned; requires divergence item 6 (extend `connective_def` with `(φ₁→φ₂) ≈ (¬φ₁ ∨ φ₂)`) |
| 19 premise clausification rules | matching CNF axiom + `resolution` | 2 each | syntactic | planned; pivot = the premise formula. The `xor`/`ite` targets are themselves reducible — reductions compose |

### Expensive (2)

| rule | reduction scheme | cost | what makes it expensive |
|---|---|---|---|
| `weakening` | rename to `resolution` (RUP reading): negating the conclusion falsifies the premise before any propagation | 0 | a linear syntactic containment scan becomes a unit-propagation check; not derivable at all under the chain reading (chain resolution never introduces literals) |
| `contraction` | rename to `resolution` (RUP reading): same degenerate-RUP argument | 0 | ditto — and the chain-targeting pipeline *introduces* explicit `contraction` steps (uncrowding) precisely to avoid implicit duplicate merging; the two readings pull in opposite directions here |

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

**Proof system.** Abstractly, first-order binder handling in the tradition of Hilbert's
ε-calculus, over contextual equality judgments:

- **[α/congr-bind]** — congruence under a binder: from `Γ, ȳ, x̄↦ȳ ▷ φ ≈ ψ`, conclude
  `Γ ▷ Qx̄.φ ≈ Qȳ.ψ` (α-renaming as the special case);
- **[inst]** — universal instantiation, `∀x̄.φ → φ[x̄↦t̄]`;
- **[gen]** — generalization: from a derivation of `φ` at a fresh `x̄`, conclude `∀x̄.φ`
  (admissible via [ε]; realized by the proposed generalization of `bind`, divergence 8);
- **[ε]** — the critical axiom of the ε-calculus: `Qx̄.φ ≈ φ[x̄ ↦ ε-witnesses]`, where the
  witness for each variable is a choice term over the remaining prefix;
- **[unfold]** — definition/let expansion, replacing defined variables by their definientia;
- **[qe-point]** — guarded one-point quantifier elimination: a variable forced to equal a term by
  a positive-polarity equality is instantiated to it.

Concretely: `bind` is [α/congr-bind] — kept primitive for the sake of its `choice` instance
(divergence 5), though its `∀`/`∃` instances are derivable from [gen] (see parent chapter);
`forall_inst` is [inst]; the proposed generalization of `bind` realizes [gen], and recasts
[α/congr-bind] *derives* — `bind` becomes a reducible rule, with binder congruence for `choice`
as the one primitive residue (divergence 5, needed to reason under ε-witnesses); `sko_forall` is
the designated [ε] axiom, with `sko_ex` derived through the quantifier duality; `let`/`bind_let`
are [unfold]; and `onepoint` is [qe-point] — derived, see below.

The quantifier rewrites reduce through the **Skolemization route** (RESOLUTE-inspired, documented
in the parent chapter): since `refl` under a witness context + `sko_forall` + `equiv_pos1` derive
the clausal ∀-ε-form `(cl ∀x.φ, ¬φ[c])` in a constant template, each quantifier rewrite falls to
a two-implication derivation with `forall_inst` and the CNF axioms — no binder-pattern RARE
needed. Under the proposed generalization of `bind` (divergence 8) the same derivations become
witness-free and linear: quantifiers are eliminated by `forall_inst` at a variables-only anchor's
own variable and reintroduced by generalization.

13 rules: 5 core, 8 reducible.

### Core (5)

| rule | notes |
|---|---|
| `bind` | binder congruence; divergence 8 proposes generalizing it so that anchors carry fresh variables and substitutions, and the closing step additionally concludes a single ∀-closure literal (unit in practice; miniscoping only on binder *sets*, clause structure untouched) — ∀-introduction becomes the no-substitutions instance, vanilla `bind` an instance with zero extra steps, `sko_*`/`onepoint` the same closing scheme under their substitution disciplines, and `qnt_rm_unused` is absorbed. Checking stays free-variable-free: declared binder subsets verified positionally, scoping enforced by the parser (see parent chapter). The `choice` instance (divergence 5) stays outside. Together with `rare_rewrite` it covers rewriting *below* a binder |
| `let` | |
| `bind_let` | emitted by the polyeq elaboration itself |
| `sko_forall` | the designated Skolemization primitive; the spec's n-ary statement is erroneous (divergence 4) and must be fixed to the sequential choice-term form implementations already use |
| `forall_inst` | polyeq elaboration already normalizes it; independent of Skolemization — some arbitrary-term principle must be primitive (see parent chapter) |

### Reducible (8)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `sko_ex` | `connective_def` (duality) + `sko_forall` + `cong` ×2 + `not-not` rewrite + `trans` | 6 (any n) | syntactic | planned; mutually dual with `sko_forall` — either could be the primitive (R4 picks one). Elaborating *existing* steps additionally needs binder congruence for `choice` to bridge the `∃`-shaped vs `¬∀¬`-shaped witnesses |
| `onepoint` | case-split template driven by the guarded-occurrence grammar: `=`-branches transport `φ'` by deep `cong` with the point equalities; `≠`-branches derive `φ` by one CNF-axiom step per grammar production (`implies_neg1` for guards, `or_neg`/`and_pos` + `resolution` for descent, `not_not` for flips); assembled by the derivable iff-introduction and `bind` | O(points·\|φ\|) | syntactic | planned; requires the spec to adopt the inductive side condition (divergence 7). Points under inner quantifiers generalize directly with the generalized `bind` (divergence 8), or via the derived `∀ȳ.⊤ ≈ ⊤`. Discharges the spec-acknowledged mutual-points gap via anchor-ordered case splits |
| `qnt_simplify` | generalized `bind` + `true` + iff-intro | 4 | syntactic | planned; witness-free with divergence 8, else ∀-ε-clause template |
| `qnt_rm_unused` | absorbed by the generalized `bind`'s miniscoped closure; standalone steps via `forall_inst` + closure + iff-intro | O(1) | syntactic | planned; ditto |
| `qnt_join` | same, nested for the merged prefix | O(1) | syntactic | planned; ditto |
| `miniscope_distribute` | `forall_inst` at the anchor variable + `and_pos`/`and_neg` + generalized `bind` + iff-intro (worked example in the parent chapter) | O(conjuncts) | syntactic | planned; ditto. ∃/∨ form via the axiomatic duality instance of `connective_def` |
| `miniscope_split` | same, per disjunct | O(disjuncts) | syntactic | planned; ditto |
| `miniscope_ite` | same, through the `ite` axioms | O(1) | syntactic | planned; ditto |

All six quantifier rewrites have two routes: witness-free and linear via the proposed
the generalized `bind` (divergence 8), or the proposal-free Skolemization fallback (∀-ε-clause template),
whose ε-witness terms embed copies of the bodies and make proof *text* quadratic without
`let`-sharing.

## Equality and rewriting

**Proof system.** Abstractly, equational logic in Birkhoff's sense, over contextual equality
judgments:

- **[refl]**, **[sym]**, **[trans]** — equivalence of `≈`;
- **[congr]** — compatibility with function application: from `tᵢ ≈ uᵢ`, conclude
  `f(t̄) ≈ f(ū)`;
- **[subst]** — closure of the axiom layer under substitution instances;
- **[axiom]** — an axiom-schema store: definitional equalities of the connectives, plus an open
  set of oriented rewrite rules (a rewrite system R) whose instances enter the derivation.

Concretely: `refl`, `symm`, `trans`, `cong` are the four Birkhoff rules ([subst] is realized by
the context mechanism — `refl` is the one rule that applies the context substitution);
`connective_def` contributes the fixed definitional [axiom]s of the connectives; and
`rare_rewrite` is the generic [axiom] interface through which arbitrary RARE rules enter the
system. The clausal `eq_*` forms are the same system repackaged as premise-free clauses through
`subproof` discharge.

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

**Proof system.** Abstractly, certificate checking for ordered-ring reasoning, along three axes:

- **[farkas]** — *linear order*: a clause of linear constraints is valid if a positive
  combination of the negated constraints (given by the certificate coefficients) is
  contradictory;
- **[ring]** — *equational*: `t ≈ u` whenever `t` and `u` normalize to the same polynomial;
- **[pos-cone]** — *nonlinear order*: the positive cone is closed under multiplication,
  `x > 0 ∧ y > 0 → x·y > 0`.

Concretely: `la_generic` is [farkas], `poly_simp` (the extra rule promoted into the core) is
[ring], and the proposed axiom `la_mult_pos_pos` is [pos-cone]. Everything else in the category
reduces to combinations of these three plus the clausal and equational cores.

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

**Proof system.** Abstractly, the definitional interpretation of bitvectors as tuples of
Booleans: one axiom scheme per operation,

- **[bv-def(∘)]** — `∘(x̄) ≈ ⟦∘⟧(bits(x̄))`, equating each bitvector operation applied to
  bit-tuples with its Boolean bit-level definition at the given width.

Concretely, the 14 `bitblast_*` axioms *are* [bv-def(∘)] for their respective operations — they
constitute the definitional core of the category, and consumers take them as such.

14 rules, all core: `bitblast_extract`, `bitblast_concat`, `bitblast_sext`, `bitblast_eq`,
`bitblast_ult`, `bitblast_slt`, `bitblast_add`, `bitblast_neg`, `bitblast_mult`, `bitblast_and`,
`bitblast_or`, `bitblast_xor`, `bitblast_xnor`, `bitblast_not`. Like `la_generic` and `poly_simp`,
they are computational schemas — checking one recomputes the bit-level definition at the given
width and compares — so they extend the computational core rather than the syntactic one.

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
| `equiv_intro` (proposed) | clausal | reducible | iff-introduction from the two implications; `equiv_neg1/2` + resolutions + contractions (~7 steps) — names the closing pattern of every two-implication template |
| `or_intro` (proposed) | clausal | reducible | packs `(cl l₁ … lₙ)` into `(cl (or l₁ … lₙ))`; `or_neg` ×n + resolutions + `contraction` — the packaging step of the LA reductions and the generalized `bind`'s unit closure |
| `and_intro` | clausal | reducible | `and_neg` + one `resolution` with explicit pivots |
| `strict_resolution` | clausal | core variant | strict form of `resolution` used after elaboration |
| `bounded_farkas` | arithmetic | reducible (**done**) | `la_generic` with inferred coefficients (local elaboration) |
| `poly_simp` | arithmetic | **core** (computational) | ring-normalization primitive; listed in the arithmetic core table above |
| `la_mult_pos_pos` | arithmetic | proposed core axiom | `(> x 0) ∧ (> y 0) → (> (* x y) 0)`; base of the `la_mult_*` schemes |
| `la_mult_sign` (`alethe-toolkit` branch) | arithmetic | expensive | O(n) fold of `la_mult_pos_pos` + `poly_simp` + `la_generic` |
| `la_mult_abs_comparison` (`alethe-toolkit` branch) | arithmetic | aggressive | reducible to the same base once an `abs` definitional rewrite exists |
| `evaluate`, `mod_simplify`, `all_simplify` | equality & rewriting | aggressive | `all_simplify` already oracle-reducible via the hole pass |
| strings, PB, cutting-planes, arrays, DRUP, `sat_refutation` | theory extensions | aggressive | `sat_refutation` oracle-reducible via its dedicated pass |
