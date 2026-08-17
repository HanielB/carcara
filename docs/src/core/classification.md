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
  missing infrastructure (evaluation operators, checker instrumentation), or has severe
  worst-case size. The exemplar is elaborating `poly_simp` itself into `rare_rewrite`
  chains — reducing not just a rule but the trust base.

Legacy rules sit outside the ladder: their level is **removal** (solvers should stop emitting
them, or the specification should replace them). See the [parent chapter](../core.md) for the
criteria and the worked-out recipes; the RARE rules required by the rewrite-based schemes are
catalogued in [RARE rules for the rewrite routes](./rare-rules.md).

For every non-trivial reduction, a collapsible **example** follows its table — click to expand.
The [reduction graph](./reduction-graph.md) shows the same content as an interactive picture:
its nodes link back to the sections and examples here.

The *check* column states the checking complexity of the steps a scheme emits: *syntactic* (pure
matching), *Farkas* (arithmetic certificate checking, via `la_generic`), *ring* (polynomial
normalization, via `poly_simp`), or *oracle* (external solver). The *status* column tracks
Carcara's elaboration: *done*, *planned*, or *—* (core, nothing to reduce).

## Summary

| category | total | core | reducible | expensive | aggressive | removal |
|---|---|---|---|---|---|---|
| structural | 3 | 3 | 0 | 0 | 0 | 0 |
| clausal | 47 | 23 | 22 | 2 | 0 | 0 |
| binder | 13 | 5 | 8 | 0 | 0 | 0 |
| equality & rewriting | 25 | 6 | 9 | 0 | 10 | 0 |
| arithmetic | 13 (+1) | 2 (+1) | 3 | 7 | 1 | 0 |
| bitvector | 14 | 14 | 0 | 0 | 0 | 0 |
| legacy | 5 | 0 | 0 | 0 | 0 | 5 |
| **total** | **120** | **53** | **42** | **9** | **11** | **5** |

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
stacked negations; the 19 CNF axioms are [def] for all six connectives (`and`, `or`, Boolean
`=`, `xor`, `ite`, `implies`). [fact]/[weak] are `contraction`/`weakening` — bookkeeping
absorbed by the [rup] reading (hence expensive, below). The `xor`/`ite`/`implies` axioms also
admit `connective_def` derivations (the `implies` case via the proposed extension with
`(φ₁→φ₂) ≈ (¬φ₁ ∨ φ₂)`, divergence item 6), recorded as agreement lemmas in the parent chapter
— the axioms stay primitive.

47 rules: 23 core, 22 reducible, 2 expensive.

### Core (23)

| rule | notes |
|---|---|
| `resolution` | dual semantics, both core: chain-with-explicit-pivots (`resolution_with_args`, syntactic) and RUP consequence (`rup_resolution`, unit propagation) |
| `true` | |
| `false` | |
| `not_not` | primitive for explicit double-negation merging; deriving it would pull in the rewrite tier |
| `and_pos` (k), `and_neg`, `or_pos`, `or_neg` (k), `equiv_pos1/2`, `equiv_neg1/2`, `xor_pos1/2`, `xor_neg1/2`, `ite_pos1/2`, `ite_neg1/2`, `implies_pos`, `implies_neg1/2` | the 19 CNF axioms — the whole [def] base is primitive. One side of each axiom/premise-rule pair must be primitive (R4); the `equiv` family is the bootstrap for unpacking `connective_def` equivalences; `and`/`or` are the Tseitin base every derivation re-clausifies into; the `xor`/`ite`/`implies` families are kept even though `connective_def` derivations exist (see the parent chapter) |

### Reducible (22)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `th_resolution` | `resolution` | 0 | syntactic | **done** (`core` pass); same rule per the spec, normalize the name |
| `tautology` | `true` | 1 | syntactic | **done** (`core` pass); conclusion is literally `⊤`; drops the premise from the DAG |
| `reordering` | (eliminated) | 0 | — | done — reordering pass recomputes downstream conclusions |
| 19 premise clausification rules | matching CNF axiom + `resolution` | 2 each | syntactic | **done** (`core` pass); pivot = the premise formula |

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

<details id="ex-clausification">
<summary>Example: a clausification rule (<code>and</code>)</summary>

```
(step t2 (cl q) :rule and :premises (t1) :args (1))     ; t1: (cl (and p q r))
```

becomes

```
(step t2.t1 (cl (not (and p q r)) q) :rule and_pos :args (1))
(step t2 (cl q) :rule resolution :premises (t2.t1 t1) :args ((and p q r) false))
```

The other 18 premise clausification rules follow the identical two-step shape with their paired
axiom from the table above — all 19 axioms are core, so every reduction lands directly in the
core fragment.

</details>

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

Concretely: `bind` is [α/congr-bind], and its proposed generalization (divergence 8) also
realizes [gen] — recasting [α/congr-bind], [ε], and [qe-point] as one anchor-closing scheme
under three substitution disciplines, with binder congruence for `choice` as the one primitive
residue (divergence 5, needed to reason under ε-witnesses); `forall_inst` is [inst], independent
of [ε] (see parent chapter); `sko_forall` is the designated [ε] axiom, with `sko_ex` derived
through the quantifier duality; `let`/`bind_let` are [unfold]; and `onepoint` is [qe-point] —
derived, see below.

The quantifier rewrites reduce through the **Skolemization route** (RESOLUTE-inspired, documented
in the parent chapter): since `refl` under a witness context + `sko_forall` + `equiv2` derive
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
| `onepoint` | case-split template driven by the guarded-occurrence grammar: `=`-branches transport `φ'` by deep `cong` with the point equalities; `≠`-branches derive `φ` by one CNF-axiom step per grammar production (`implies_neg1` for guards, `or_neg`/`and_pos` + `resolution` for descent, `not_not` for flips); assembled by `equiv_intro` (or its derivation) and `bind` | O(points·\|φ\|) | syntactic | planned; requires the spec to adopt the inductive side condition (divergence 7). Points under inner quantifiers generalize directly with the generalized `bind` (divergence 8), or via the derived `∀ȳ.⊤ ≈ ⊤`. Discharges the spec-acknowledged mutual-points gap via anchor-ordered case splits |
| `qnt_simplify` | generalized `bind` + `true` + iff-intro | 4 | syntactic | **done** (`core` pass, ∀ forms); witness-free with divergence 8, else ∀-ε-clause template |
| `qnt_rm_unused` | absorbed by the generalized `bind`'s miniscoped closure; standalone steps via `forall_inst` + closure + iff-intro | O(1) | syntactic | **done** (`core` pass, ∀ forms); ditto |
| `qnt_join` | same, nested for the merged prefix | O(1) | syntactic | **done** (`core` pass, ∀ forms); ditto |
| `miniscope_distribute` | `forall_inst` at the anchor variable + `and_pos`/`and_neg` + generalized `bind` + iff-intro (worked example in the parent chapter) | O(conjuncts) | syntactic | **done** (`core` pass, ∀ forms); ∃/∨ form via the axiomatic duality instance of `connective_def` |
| `miniscope_split` | same, per disjunct | O(disjuncts) | syntactic | **done** (`core` pass, ∀ forms) |
| `miniscope_ite` | same, through the `ite` axioms | O(1) | syntactic | **done** (`core` pass, ∀ forms) |

All six quantifier rewrites have two routes: witness-free and linear via the proposed
generalization of `bind` (divergence 8), or the proposal-free Skolemization fallback (∀-ε-clause
template),
whose ε-witness terms embed copies of the bodies and make proof *text* quadratic without
`let`-sharing.

<details id="ex-sko-fallback">
<summary>Example: the Skolemization fallback (<code>qnt_rm_unused</code> without divergence 8)</summary>

The same `qnt_rm_unused` instance as above, using only today's rules. Wherever the generalized
`bind` closed an anchor over a symbolic variable, the fallback derives the quantifier's
∀-ε-clause from `sko_forall` and reasons *at the witness term*. Abbreviate the witnesses
(each spelled once — note how `c2` embeds `c1`, the quadratic-text cost):

```
cB = (choice ((x S)) (not (P x)))                          ; for (forall ((x S)) (P x))
c1 = (choice ((x S)) (not (forall ((y S)) (P x))))         ; sequential witnesses
c2 = (choice ((y S)) (not (P (choice ((x S)) (not (forall ((y S)) (P x)))))))
                                                           ; = (choice ((y S)) (not (P c1)))
dy = (choice ((y S)) true)                                 ; dummy for the vanished y
```

Direction →, at `cB`:

```
(anchor :step t.k1 :args ((:= (x S) cB)))
(step t.k1.t1 (cl (= (P x) (P cB))) :rule refl)
(step t.k1 (cl (= (forall ((x S)) (P x)) (P cB))) :rule sko_forall)
(step t.k2 (cl (forall ((x S)) (P x)) (not (P cB))) :rule equiv2 :premises (t.k1))
(step t.k3 (cl (not (forall ((x S) (y S)) (P x))) (P cB))
    :rule forall_inst :args (cB dy))
(step t.k4 (cl (not (forall ((x S) (y S)) (P x))) (forall ((x S)) (P x)))
    :rule resolution :premises (t.k2 t.k3))
```

Direction ←, at the sequential witnesses `c1`, `c2`:

```
(anchor :step t.k5 :args ((:= (x S) c1) (:= (y S) c2)))
(step t.k5.t1 (cl (= (P x) (P c1))) :rule refl)
(step t.k5 (cl (= (forall ((x S) (y S)) (P x)) (P c1))) :rule sko_forall)
(step t.k6 (cl (forall ((x S) (y S)) (P x)) (not (P c1))) :rule equiv2 :premises (t.k5))
(step t.k7 (cl (not (forall ((x S)) (P x))) (P c1)) :rule forall_inst :args (c1))
(step t.k8 (cl (not (forall ((x S)) (P x))) (forall ((x S) (y S)) (P x)))
    :rule resolution :premises (t.k6 t.k7))

(step t (cl (= (forall ((x S) (y S)) (P x)) (forall ((x S)) (P x))))
    :rule equiv_intro :premises (t.k4 t.k8))
```

Compare with the generalized-`bind` example above: the shape is identical, but symbolic
variables became witness terms, the vanished `y` needs the dummy `dy`, and each subproof body
carries the choice terms textually. One degenerate delight: for `qnt_simplify` the body is
closed, so the fallback collapses — the `sko_forall` anchor with the vacuous witness context
yields `(cl (= (forall ((x S)) true) true))` directly in two steps.

</details>

<details id="ex-sko-ex">
<summary>Example: <code>sko_ex</code> via duality</summary>

For a step `(step t (cl (= (exists ((x S)) φ) ψ)) :rule sko_ex)` whose subproof's last step
`t.tk` concludes `(cl (= φ ψ))` under the witness context:

```
(step t.k1 (cl (= (not φ) (not ψ))) :rule cong :premises (t.tk))
(step t.k2 (cl (= (forall ((x S)) (not φ)) (not ψ))) :rule sko_forall)     ; closes the subproof
(step t.k3 (cl (= (exists ((x S)) φ) (not (forall ((x S)) (not φ))))) :rule connective_def)
(step t.k4 (cl (= (not (forall ((x S)) (not φ))) (not (not ψ)))) :rule cong :premises (t.k2))
(step t.k5 (cl (= (not (not ψ)) ψ)) :rule rare_rewrite :args ("not-not-elim" ψ))
(step t (cl (= (exists ((x S)) φ) ψ)) :rule trans :premises (t.k3 t.k4 t.k5))
```

For already-produced steps, aligning the `∃`-shaped witness of the original context with the
`¬∀¬`-shaped one `sko_forall` expects needs the choice-congruence rule (divergence 5).

</details>

<details id="ex-onepoint">
<summary>Example: <code>onepoint</code></summary>

The instance, with its premise subproof (the context performs `x ↦ t`, and `refl` proves the
substituted body):

```
(anchor :step s :args ((:= (x S) t)))
(step s.t1 (cl (= (=> (= x t) (P x)) (=> (= t t) (P t)))) :rule refl)
(step s (cl (= (forall ((x S)) (=> (= x t) (P x))) (=> (= t t) (P t)))) :rule onepoint)
```

The elaboration, in full. Direction →: `forall_inst` at the point `t` produces exactly the
right-hand side (with a non-trivial premise subproof, one extra `equiv1` + `resolution` bridges
`φ[t]` to `φ'`):

```
(anchor :step s.p1)
(assume s.p1.h (forall ((x S)) (=> (= x t) (P x))))
(step s.p1.t1 (cl (not (forall ((x S)) (=> (= x t) (P x)))) (=> (= t t) (P t)))
    :rule forall_inst :args (t))
(step s.p1.t2 (cl (=> (= t t) (P t))) :rule resolution :premises (s.p1.h s.p1.t1))
(step s.p1 (cl (not (forall ((x S)) (=> (= x t) (P x)))) (=> (= t t) (P t)))
    :rule subproof :discharge (s.p1.h))
```

Direction ←: derive `(P t)` from the hypothesis, transport it through the guard equality inside
an inner discharge subproof (the guarded-occurrence grammar's production for `⇒`-guards), package
the implication term, and close over `x`:

```
(anchor :step s.p2)
(assume s.p2.h (=> (= t t) (P t)))
(anchor :step s.p2.t1 :args ((x S)))
(step s.p2.t1.t1 (cl (= t t)) :rule eq_reflexive)
(step s.p2.t1.t2 (cl (not (= t t)) (P t)) :rule implies :premises (s.p2.h))
(step s.p2.t1.t3 (cl (P t)) :rule resolution :premises (s.p2.t1.t2 s.p2.t1.t1))
(anchor :step s.p2.t1.t4)
(assume s.p2.t1.t4.h (= x t))
(step s.p2.t1.t4.t1 (cl (= t x)) :rule symm :premises (s.p2.t1.t4.h))
(step s.p2.t1.t4.t2 (cl (= (P t) (P x))) :rule cong :premises (s.p2.t1.t4.t1))
(step s.p2.t1.t4.t3 (cl (P x)) :rule eq_mp :premises (s.p2.t1.t3 s.p2.t1.t4.t2))
(step s.p2.t1.t4 (cl (not (= x t)) (P x)) :rule subproof :discharge (s.p2.t1.t4.h))
(step s.p2.t1.t5 (cl (=> (= x t) (P x)) (= x t)) :rule implies_neg1)
(step s.p2.t1.t6 (cl (=> (= x t) (P x)) (not (P x))) :rule implies_neg2)
(step s.p2.t1.t7 (cl (not (= x t)) (=> (= x t) (P x)))
    :rule resolution :premises (s.p2.t1.t4 s.p2.t1.t6))
(step s.p2.t1.t8 (cl (=> (= x t) (P x)) (=> (= x t) (P x)))
    :rule resolution :premises (s.p2.t1.t7 s.p2.t1.t5))
(step s.p2.t1.t9 (cl (=> (= x t) (P x))) :rule contraction :premises (s.p2.t1.t8))
(step s.p2.t1 (cl (forall ((x S)) (=> (= x t) (P x)))) :rule bind)   ; unit closure over {x}
(step s.p2 (cl (not (=> (= t t) (P t))) (forall ((x S)) (=> (= x t) (P x))))
    :rule subproof :discharge (s.p2.h))
(step s (cl (= (forall ((x S)) (=> (= x t) (P x))) (=> (= t t) (P t))))
    :rule equiv_intro :premises (s.p1 s.p2))
```

Deeper guard shapes add one `or_neg`/`and_pos` step per grammar production; multiple points case
split in anchor order.

</details>

<details id="ex-qnt-simplify">
<summary>Example: <code>qnt_simplify</code></summary>

```
(anchor :step t.p :args ((x S)))
(step t.p.t1 (cl true) :rule true)
(step t.p (cl (forall ((x S)) true)) :rule bind)      ; unit closure (divergence 8)
(step t.t1 (cl true) :rule true)
(step t.t2 (cl (= (forall ((x S)) true) true)
              (not (forall ((x S)) true)) (not true)) :rule equiv_neg1)
(step t (cl (= (forall ((x S)) true) true)) :rule resolution :premises (t.t2 t.p t.t1))
```

</details>

<details id="ex-qnt-rm-unused">
<summary>Example: <code>qnt_rm_unused</code></summary>

For `(cl (= (forall ((x S) (y S)) (P x)) (forall ((x S)) (P x))))` (`y` unused in the body):

```
(anchor :step t.p1)
(assume t.p1.h (forall ((x S) (y S)) (P x)))
(anchor :step t.p1.t1 :args ((x S)))
(step t.p1.t1.t1 (cl (not (forall ((x S) (y S)) (P x))) (P x)) :rule forall_inst :args (x x))
(step t.p1.t1.t2 (cl (P x)) :rule resolution :premises (t.p1.h t.p1.t1.t1))
(step t.p1.t1 (cl (forall ((x S)) (P x))) :rule bind)        ; unit closure over {x}
(step t.p1 (cl (not (forall ((x S) (y S)) (P x))) (forall ((x S)) (P x)))
    :rule subproof :discharge (t.p1.h))

(anchor :step t.p2)
(assume t.p2.h (forall ((x S)) (P x)))
(anchor :step t.p2.t1 :args ((x S) (y S)))
(step t.p2.t1.t1 (cl (not (forall ((x S)) (P x))) (P x)) :rule forall_inst :args (x))
(step t.p2.t1.t2 (cl (P x)) :rule resolution :premises (t.p2.h t.p2.t1.t1))
(step t.p2.t1 (cl (forall ((x S) (y S)) (P x))) :rule bind)  ; closure over {x, y}, y vacuous
(step t.p2 (cl (not (forall ((x S)) (P x))) (forall ((x S) (y S)) (P x)))
    :rule subproof :discharge (t.p2.h))

(step t (cl (= (forall ((x S) (y S)) (P x)) (forall ((x S)) (P x))))
    :rule equiv_intro :premises (t.p1 t.p2))
```

In the → direction, `y` is instantiated at `x` (any term of `y`'s sort works, since `y` does not
occur in the body); in the ← direction, the vacuous `y` is simply part of the declared closure
prefix. The Skolemization fallback instead instantiates `y` at a dummy witness
`(choice ((y S)) true)`.

</details>

<details id="ex-qnt-join">
<summary>Example: <code>qnt_join</code></summary>

For `(cl (= (forall ((x S)) (forall ((y S)) P)) (forall ((x S) (y S)) P)))` (`P` may mention
both `x` and `y`):

```
(anchor :step t.p1)
(assume t.p1.h (forall ((x S)) (forall ((y S)) P)))
(anchor :step t.p1.t1 :args ((x S) (y S)))
(step t.p1.t1.t1 (cl (not (forall ((x S)) (forall ((y S)) P))) (forall ((y S)) P))
    :rule forall_inst :args (x))
(step t.p1.t1.t2 (cl (forall ((y S)) P)) :rule resolution :premises (t.p1.h t.p1.t1.t1))
(step t.p1.t1.t3 (cl (not (forall ((y S)) P)) P) :rule forall_inst :args (y))
(step t.p1.t1.t4 (cl P) :rule resolution :premises (t.p1.t1.t2 t.p1.t1.t3))
(step t.p1.t1 (cl (forall ((x S) (y S)) P)) :rule bind)      ; unit closure over {x, y}
(step t.p1 (cl (not (forall ((x S)) (forall ((y S)) P))) (forall ((x S) (y S)) P))
    :rule subproof :discharge (t.p1.h))

(anchor :step t.p2)
(assume t.p2.h (forall ((x S) (y S)) P))
(anchor :step t.p2.t1 :args ((x S)))
(anchor :step t.p2.t1.t1 :args ((y S)))
(step t.p2.t1.t1.t1 (cl (not (forall ((x S) (y S)) P)) P) :rule forall_inst :args (x y))
(step t.p2.t1.t1.t2 (cl P) :rule resolution :premises (t.p2.h t.p2.t1.t1.t1))
(step t.p2.t1.t1 (cl (forall ((y S)) P)) :rule bind)         ; inner closure over {y}
(step t.p2.t1 (cl (forall ((x S)) (forall ((y S)) P))) :rule bind)  ; outer closure over {x}
(step t.p2 (cl (not (forall ((x S) (y S)) P)) (forall ((x S)) (forall ((y S)) P)))
    :rule subproof :discharge (t.p2.h))

(step t (cl (= (forall ((x S)) (forall ((y S)) P)) (forall ((x S) (y S)) P)))
    :rule equiv_intro :premises (t.p1 t.p2))
```

The ← direction nests two closures, rebuilding the quantifier structure one binder at a time.

</details>

<details id="ex-miniscope-distribute">
<summary>Example: <code>miniscope_distribute</code></summary>

The full derivation (also the worked example of the parent chapter):

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

</details>

<details id="ex-miniscope-split">
<summary>Example: <code>miniscope_split</code></summary>

For `(cl (= (forall ((x S)) (or P Q)) (or (forall ((x S)) P) Q)))`, where `Q` is `x`-free (the
essential single-disjunct-with-residue instance; more disjuncts iterate the same shape, each
closing over only its own declared variables). Note the pass-through literal in the → closure:
`Q` is `x`-free, so it stays outside the wrapped literal — the generalized `bind`'s side-literal
case:

```
(anchor :step t.p1)
(assume t.p1.h (forall ((x S)) (or P Q)))
(anchor :step t.p1.t1 :args ((x S)))
(step t.p1.t1.t1 (cl (not (forall ((x S)) (or P Q))) (or P Q)) :rule forall_inst :args (x))
(step t.p1.t1.t2 (cl (or P Q)) :rule resolution :premises (t.p1.h t.p1.t1.t1))
(step t.p1.t1.t3 (cl P Q) :rule or :premises (t.p1.t1.t2))
(step t.p1.t1 (cl (forall ((x S)) P) Q) :rule bind)   ; closure wraps P; Q passes through
(step t.p1.t2 (cl (or (forall ((x S)) P) Q)) :rule or_intro :premises (t.p1.t1))
(step t.p1 (cl (not (forall ((x S)) (or P Q))) (or (forall ((x S)) P) Q))
    :rule subproof :discharge (t.p1.h))

(anchor :step t.p2)
(assume t.p2.h (or (forall ((x S)) P) Q))
(anchor :step t.p2.t1 :args ((x S)))
(step t.p2.t1.t1 (cl (forall ((x S)) P) Q) :rule or :premises (t.p2.h))
(step t.p2.t1.t2 (cl (not (forall ((x S)) P)) P) :rule forall_inst :args (x))
(step t.p2.t1.t3 (cl P Q) :rule resolution :premises (t.p2.t1.t1 t.p2.t1.t2))
(step t.p2.t1.t4 (cl (or P Q)) :rule or_intro :premises (t.p2.t1.t3))
(step t.p2.t1 (cl (forall ((x S)) (or P Q))) :rule bind)     ; unit closure over {x}
(step t.p2 (cl (not (or (forall ((x S)) P) Q)) (forall ((x S)) (or P Q)))
    :rule subproof :discharge (t.p2.h))

(step t (cl (= (forall ((x S)) (or P Q)) (or (forall ((x S)) P) Q)))
    :rule equiv_intro :premises (t.p1 t.p2))
```

</details>

<details id="ex-miniscope-ite">
<summary>Example: <code>miniscope_ite</code></summary>

For `(cl (= (forall ((x S)) (ite c P Q)) (ite c (forall ((x S)) P) (forall ((x S)) Q))))`, where
`c` is `x`-free. Both directions case split on `c` *outside* the variable anchor (legal since `c`
is `x`-free). Direction →:

```
(anchor :step t.p1)
(assume t.p1.h (forall ((x S)) (ite c P Q)))
(anchor :step t.p1.b1)                                        ; branch c
(assume t.p1.b1.h c)
(anchor :step t.p1.b1.t1 :args ((x S)))
(step t.p1.b1.t1.t1 (cl (not (forall ((x S)) (ite c P Q))) (ite c P Q))
    :rule forall_inst :args (x))
(step t.p1.b1.t1.t2 (cl (ite c P Q)) :rule resolution :premises (t.p1.h t.p1.b1.t1.t1))
(step t.p1.b1.t1.t3 (cl (not c) P) :rule ite2 :premises (t.p1.b1.t1.t2))
(step t.p1.b1.t1.t4 (cl P) :rule resolution :premises (t.p1.b1.t1.t3 t.p1.b1.h))
(step t.p1.b1.t1 (cl (forall ((x S)) P)) :rule bind)          ; unit closure over {x}
(step t.p1.b1.t2 (cl (ite c (forall ((x S)) P) (forall ((x S)) Q))
                     (not c) (not (forall ((x S)) P))) :rule ite_neg2)
(step t.p1.b1.t3 (cl (ite c (forall ((x S)) P) (forall ((x S)) Q)))
    :rule resolution :premises (t.p1.b1.t2 t.p1.b1.h t.p1.b1.t1))
(step t.p1.b1 (cl (not c) (ite c (forall ((x S)) P) (forall ((x S)) Q)))
    :rule subproof :discharge (t.p1.b1.h))
(anchor :step t.p1.b2)                                        ; branch (not c)
(assume t.p1.b2.h (not c))
(anchor :step t.p1.b2.t1 :args ((x S)))
(step t.p1.b2.t1.t1 (cl (not (forall ((x S)) (ite c P Q))) (ite c P Q))
    :rule forall_inst :args (x))
(step t.p1.b2.t1.t2 (cl (ite c P Q)) :rule resolution :premises (t.p1.h t.p1.b2.t1.t1))
(step t.p1.b2.t1.t3 (cl c Q) :rule ite1 :premises (t.p1.b2.t1.t2))
(step t.p1.b2.t1.t4 (cl Q) :rule resolution :premises (t.p1.b2.t1.t3 t.p1.b2.h))
(step t.p1.b2.t1 (cl (forall ((x S)) Q)) :rule bind)          ; unit closure over {x}
(step t.p1.b2.t2 (cl (ite c (forall ((x S)) P) (forall ((x S)) Q))
                     c (not (forall ((x S)) Q))) :rule ite_neg1)
(step t.p1.b2.t3 (cl (ite c (forall ((x S)) P) (forall ((x S)) Q)))
    :rule resolution :premises (t.p1.b2.t2 t.p1.b2.h t.p1.b2.t1))
(step t.p1.b2 (cl (not (not c)) (ite c (forall ((x S)) P) (forall ((x S)) Q)))
    :rule subproof :discharge (t.p1.b2.h))
(step t.p1.t3 (cl (ite c (forall ((x S)) P) (forall ((x S)) Q))
                  (ite c (forall ((x S)) P) (forall ((x S)) Q)))
    :rule resolution :premises (t.p1.b1 t.p1.b2))             ; pivot (not c)
(step t.p1.t4 (cl (ite c (forall ((x S)) P) (forall ((x S)) Q)))
    :rule contraction :premises (t.p1.t3))
(step t.p1 (cl (not (forall ((x S)) (ite c P Q)))
               (ite c (forall ((x S)) P) (forall ((x S)) Q)))
    :rule subproof :discharge (t.p1.h))
```

Direction ← mirrors it exactly — assume the `ite` of quantifiers, case split on `c`, extract the
corresponding quantifier with `ite2`/`ite1`, instantiate at the anchor variable, rebuild
`(ite c P Q)` with `ite_neg2`/`ite_neg1`, close over `{x}`, merge the branches by resolution +
`contraction`, discharge — and `equiv_intro` closes:

```
(anchor :step t.p2)
(assume t.p2.h (ite c (forall ((x S)) P) (forall ((x S)) Q)))
(anchor :step t.p2.b1)                                        ; branch c
(assume t.p2.b1.h c)
(step t.p2.b1.t1 (cl (not c) (forall ((x S)) P)) :rule ite2 :premises (t.p2.h))
(step t.p2.b1.t2 (cl (forall ((x S)) P)) :rule resolution :premises (t.p2.b1.t1 t.p2.b1.h))
(anchor :step t.p2.b1.t3 :args ((x S)))
(step t.p2.b1.t3.t1 (cl (not (forall ((x S)) P)) P) :rule forall_inst :args (x))
(step t.p2.b1.t3.t2 (cl P) :rule resolution :premises (t.p2.b1.t2 t.p2.b1.t3.t1))
(step t.p2.b1.t3.t3 (cl (ite c P Q) (not c) (not P)) :rule ite_neg2)
(step t.p2.b1.t3.t4 (cl (ite c P Q))
    :rule resolution :premises (t.p2.b1.t3.t3 t.p2.b1.h t.p2.b1.t3.t2))
(step t.p2.b1.t3 (cl (forall ((x S)) (ite c P Q))) :rule bind)  ; unit closure over {x}
(step t.p2.b1 (cl (not c) (forall ((x S)) (ite c P Q)))
    :rule subproof :discharge (t.p2.b1.h))
(anchor :step t.p2.b2)                                        ; branch (not c)
(assume t.p2.b2.h (not c))
(step t.p2.b2.t1 (cl c (forall ((x S)) Q)) :rule ite1 :premises (t.p2.h))
(step t.p2.b2.t2 (cl (forall ((x S)) Q)) :rule resolution :premises (t.p2.b2.t1 t.p2.b2.h))
(anchor :step t.p2.b2.t3 :args ((x S)))
(step t.p2.b2.t3.t1 (cl (not (forall ((x S)) Q)) Q) :rule forall_inst :args (x))
(step t.p2.b2.t3.t2 (cl Q) :rule resolution :premises (t.p2.b2.t2 t.p2.b2.t3.t1))
(step t.p2.b2.t3.t3 (cl (ite c P Q) c (not Q)) :rule ite_neg1)
(step t.p2.b2.t3.t4 (cl (ite c P Q))
    :rule resolution :premises (t.p2.b2.t3.t3 t.p2.b2.h t.p2.b2.t3.t2))
(step t.p2.b2.t3 (cl (forall ((x S)) (ite c P Q))) :rule bind)  ; unit closure over {x}
(step t.p2.b2 (cl (not (not c)) (forall ((x S)) (ite c P Q)))
    :rule subproof :discharge (t.p2.b2.h))
(step t.p2.t3 (cl (forall ((x S)) (ite c P Q)) (forall ((x S)) (ite c P Q)))
    :rule resolution :premises (t.p2.b1 t.p2.b2))             ; pivot (not c)
(step t.p2.t4 (cl (forall ((x S)) (ite c P Q))) :rule contraction :premises (t.p2.t3))
(step t.p2 (cl (not (ite c (forall ((x S)) P) (forall ((x S)) Q)))
               (forall ((x S)) (ite c P Q)))
    :rule subproof :discharge (t.p2.h))

(step t (cl (= (forall ((x S)) (ite c P Q))
               (ite c (forall ((x S)) P) (forall ((x S)) Q))))
    :rule equiv_intro :premises (t.p1 t.p2))
```

</details>

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

25 rules: 6 core, 9 reducible, 0 expensive, 10 aggressive.

### Core (6)

| rule | notes |
|---|---|
| `refl` | the only rule applying the context |
| `trans` | |
| `cong` | |
| `symm` | kept against the spec's "superfluous" note: explicit symmetry for elaborated output |
| `connective_def` | kept whole: propositional instances are O(1)-derivable, but the quantifier-duality instance is the R4-chosen axiom that bootstraps all ∃-reasoning, and the definition list hosts the `xor`/`ite`/`implies` axiom reductions (incl. the proposed `→` extension, divergence 6) |
| `rare_rewrite` | the designated rewrite primitive; oracle-checkable today |

### Reducible (7)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `eq_reflexive` | `refl` (empty context) | 1 | syntactic | **done** (`core` pass) |
| `eq_transitive` | subproof + `trans` (+ `symm`) | ≤ 2n | syntactic | **done** (`core` pass); the older local elaboration canonicalizes flips but keeps the rule |
| `eq_congruent` | subproof + `cong` (+ `symm`) | ≤ 2n+2 | syntactic | **done** (`core` pass); ditto |
| `eq_congruent_pred` | subproof + `cong` + `eq_mp` | ≤ 2n+3 | syntactic | **done** (`core` pass); see the spec-divergence note on its conclusion shape |
| `eq_symmetric` | two `symm` subproofs (one per direction) + `equiv_intro` | ~9 | syntactic | **done** (`core` pass); the conclusion is an *equivalence*, so both directions are needed |
| `not_symm` | subproof + `symm` + `resolution` | 4 | syntactic | **done** (`core` pass) |
| `shuffle` | `aci_simp` (rename) | 0 | ACI | **done** (`core` pass); the check coarsens from multiset comparison to full ACI normalization — sound, and `aci_simp` is the designated ACI primitive |
| `nary_elim` | `aci_simp` (rename), for the assoc-comm operators | 0 | ACI | **done** (`core` pass); chainable (`=`) and non-commutative (`→`, `-`) cases keep the binary-associativity `rare_rewrite` chain (below) and are left unchanged |
| `multi_rare_rewrite` | `rare_rewrite` chain + `trans`/`cong` | O(k·depth) | syntactic | planned; validate rule-position semantics first |

<details id="ex-eq-transitive">
<summary>Example: <code>eq_transitive</code></summary>

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

Flipped literals insert a `symm` step over the corresponding assumption.

</details>

<details id="ex-eq-congruent">
<summary>Example: <code>eq_congruent</code> and <code>eq_congruent_pred</code></summary>

`eq_congruent`:

```
(step t1 (cl (not (= a b)) (not (= c d)) (= (f a c) (f b d))) :rule eq_congruent)
```

becomes

```
(anchor :step t1)
(assume t1.a0 (= a b))
(assume t1.a1 (= c d))
(step t1.t1 (cl (= (f a c) (f b d))) :rule cong :premises (t1.a0 t1.a1))
(step t1 (cl (not (= a b)) (not (= c d)) (= (f a c) (f b d))) :rule subproof
    :discharge (t1.a0 t1.a1))
```

`eq_congruent_pred` in the veriT form (two final literals `¬(P t̄), (P ū)`) additionally assumes
`(P a c)` and applies `eq_mp`:

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

</details>

<details id="ex-eq-symmetric">
<summary>Example: <code>eq_symmetric</code> and <code>not_symm</code></summary>

`eq_symmetric` concludes an *equivalence*, so both directions are needed:

```
(step t (cl (= (= a b) (= b a))) :rule eq_symmetric)
```

becomes

```
(anchor :step t.p1)
(assume t.p1.a (= a b))
(step t.p1.t1 (cl (= b a)) :rule symm :premises (t.p1.a))
(step t.p1 (cl (not (= a b)) (= b a)) :rule subproof :discharge (t.p1.a))

(anchor :step t.p2)
(assume t.p2.a (= b a))
(step t.p2.t1 (cl (= a b)) :rule symm :premises (t.p2.a))
(step t.p2 (cl (not (= b a)) (= a b)) :rule subproof :discharge (t.p2.a))

(step t (cl (= (= a b) (= b a))) :rule equiv_intro :premises (t.p1 t.p2))
```

`not_symm` needs only one direction, resolved with its premise `t1: (cl (not (= a b)))`:

```
(anchor :step t.p)
(assume t.p.a (= b a))
(step t.p.t1 (cl (= a b)) :rule symm :premises (t.p.a))
(step t.p (cl (not (= b a)) (= a b)) :rule subproof :discharge (t.p.a))
(step t (cl (not (= b a))) :rule resolution :premises (t.p t1))
```

</details>

<details id="ex-multi-rare-rewrite">
<summary>Example: <code>multi_rare_rewrite</code></summary>

A step rewriting `(and p true (not (not q)))` to `(and p q)` by two RARE rules — `and-true-elim`
at the root and `not-not-elim` below it — unfolds into single rewrites glued by `cong`/`trans`:

```
(step s1 (cl (= (and p true (not (not q))) (and p (not (not q)))))
    :rule rare_rewrite :args ("and-true-elim" p (not (not q))))
(step s2 (cl (= (not (not q)) q))
    :rule rare_rewrite :args ("not-not-elim" q))
(step s3 (cl (= (and p (not (not q))) (and p q))) :rule cong :premises (s2))
(step s  (cl (= (and p true (not (not q))) (and p q))) :rule trans :premises (s1 s3))
```

</details>

<details id="ex-nary-elim">
<summary>Example: <code>nary_elim</code> (non-commutative fallback)</summary>

For the associative-commutative operators the reduction is a rename to `aci_simp`. The chainable
and non-commutative cases keep the binary-associativity `rare_rewrite` chain:

```
(step s1 (cl (= (=> a b c) (=> a (=> b c))))
    :rule rare_rewrite :args ("implies-unfold-binary" a b c))
(step s2 (cl (= (=> b c) (=> b (=> c))))
    :rule rare_rewrite :args ("implies-unfold-binary" b c))
(step s3 (cl (= (=> a (=> b c)) (=> a (=> b (=> c))))) :rule cong :premises (s2))
(step s  (cl (= (=> a b c) (=> a (=> b (=> c))))) :rule trans :premises (s1 s3))
```

</details>

### Aggressive (10)

| rule | reduction scheme | cost | missing prerequisite / blocker |
|---|---|---|---|
| `and_simplify`, `or_simplify`, `not_simplify`, `implies_simplify`, `equiv_simplify`, `bool_simplify`, `ite_simplify`, `eq_simplify` | `rare_rewrite` chain glued by `trans`/`cong`, replaying the rewrite trace of the fixpoint | O(trace) | instrumenting the simplification checkers to record traces (or oracle via the hole pass); RARE coverage of each rewrite |
| `aci_simp` | elementary assoc/comm/identity/idempotence rewrites | O(n²) worst case | fails R1; no canonical ACI normal form (spec's own remark) — kept as the designated ACI primitive |
| `distinct_elim` | single `rare_rewrite` instance | 1 | an n-ary RARE rule for `distinct` needs a recursive Eunoia *program* (arity-dependent output), including the Bool special case (> 2 Bool arguments → ⊥) |

## Arithmetic

**Proof system.** Abstractly, certificate checking for ordered-ring reasoning, along four axes:

- **[farkas]** — *linear order*: a clause of linear constraints is valid if a positive
  combination of the negated constraints (given by the certificate coefficients) is
  contradictory;
- **[ring]** — *equational*: `t ≈ u` whenever `t` and `u` normalize to the same polynomial;
- **[pos-cone]** — *nonlinear order*: the positive cone is closed under multiplication,
  `x > 0 ∧ y > 0 → x·y > 0`;
- **[antisym]** — *order antisymmetry*: `t ≤ u ∧ u ≤ t → t ≈ u` — the one crossing from bounds
  back to an equality.

Concretely: `la_generic` is [farkas], `poly_simp` (the extra rule promoted into the core) is
[ring], the proposed axiom `la_mult_pos_pos` is [pos-cone], and `la_disequality` is [antisym].
Everything else in the category reduces to combinations of these four plus the clausal and
equational cores.

13 specification rules (2 core, 3 reducible, 7 expensive, 1 aggressive) plus the extra rule
`poly_simp` in the core. See the
[arithmetic section](../core.md#arithmetic-la_generic-and-poly_simp-as-the-computational-core) of
the parent chapter for the recipes.

### Core (2 + 1 extra)

| rule | notes |
|---|---|
| `la_generic` | the linear computational primitive (Farkas certificates) |
| `la_disequality` | the [antisym] axiom, `▷ (t1 ≈ t2), ¬(t1 ≤ t2), ¬(t2 ≤ t1)`: premise-free clause, O(1) syntactic check. Kept core because no combination of the other axes can introduce a positive arithmetic equality (see "Lemmas, not axioms" in the RARE chapter); the exact counterpart of cvc5's dedicated `ARITH_TRICHOTOMY` rule, and literally RESOLUTE's `trichotomy` axiom modulo the `¬≤`/`<` atom flip (see the parent chapter's RESOLUTE comparison). Would become reducible only under the two-coefficient-vector generalization of `la_generic` recorded there |
| `poly_simp` (extra) | the nonlinear computational primitive: unit polynomial equality, checked by ring-normalizing both sides. Its own elaboration into `rare_rewrite` chains is the *aggressive* exemplar — see the parent chapter |

### Reducible (3)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `la_totality` | `la_generic` + `or`-term packaging (= one `or_intro`) | 6 | Farkas + syntactic | **done** (`core` pass); unit-clause-with-`or` quirk |
| `la_tautology` | `la_generic` (coeff `[1]`; binary form + `or_intro` packaging) | 1–6 | Farkas + syntactic | **done** (`core` pass); the spec itself states the equivalence |
| `la_rw_eq` | ← from `la_disequality` + `and_pos` ×2 + `resolution` + `contraction`; → by subproof + `la_generic` ×2 + `and_intro`; closed by `equiv_intro` | ~13 (O(1)) | Farkas + syntactic | **done** (`core` pass); *alternative*: a single `rare_rewrite` instance of the `la-rw-eq` RARE rule — itself a lemma by this same derivation |

<details id="ex-la-totality">
<summary>Example: <code>la_totality</code></summary>

```
(step t (cl (or (<= a b) (<= b a))) :rule la_totality)
```

becomes

```
(step t.t1 (cl (<= a b) (<= b a)) :rule la_generic :args (1 1))
(step t (cl (or (<= a b) (<= b a))) :rule or_intro :premises (t.t1))
```

(`or_intro` expands, if needed, to `or_neg` ×2 + `resolution` ×2 + `contraction`.) The binary
form of `la_tautology` is identical; its unit form is a single `la_generic` step with
coefficient `[1]`.

</details>

<details id="ex-la-rw-eq">
<summary>Example: <code>la_rw_eq</code></summary>

```
(step t (cl (= (= t1 t2) (and (<= t1 t2) (<= t2 t1)))) :rule la_rw_eq)
```

becomes — the → direction by two Farkas steps under a discharge subproof, the ← direction from
the `la_disequality` axiom, glued by `equiv_intro`:

```
(anchor :step t.p)
(assume t.p.h (= t1 t2))
(step t.p.t1 (cl (not (= t1 t2)) (<= t1 t2)) :rule la_generic :args ((- 1) 1))
(step t.p.t2 (cl (not (= t1 t2)) (<= t2 t1)) :rule la_generic :args (1 1))
(step t.p.t3 (cl (<= t1 t2)) :rule resolution :premises (t.p.t1 t.p.h))
(step t.p.t4 (cl (<= t2 t1)) :rule resolution :premises (t.p.t2 t.p.h))
(step t.p.t5 (cl (and (<= t1 t2) (<= t2 t1))) :rule and_intro :premises (t.p.t3 t.p.t4))
(step t.p (cl (not (= t1 t2)) (and (<= t1 t2) (<= t2 t1))) :rule subproof
    :discharge (t.p.h))
(step t.t1 (cl (= t1 t2) (not (<= t1 t2)) (not (<= t2 t1))) :rule la_disequality)
(step t.t2 (cl (not (and (<= t1 t2) (<= t2 t1))) (<= t1 t2)) :rule and_pos)
(step t.t3 (cl (not (and (<= t1 t2) (<= t2 t1))) (<= t2 t1)) :rule and_pos)
(step t.t4 (cl (= t1 t2) (not (and (<= t1 t2) (<= t2 t1)))
               (not (and (<= t1 t2) (<= t2 t1))))
    :rule resolution :premises (t.t1 t.t2 t.t3))
(step t.t5 (cl (= t1 t2) (not (and (<= t1 t2) (<= t2 t1)))) :rule contraction
    :premises (t.t4))
(step t (cl (= (= t1 t2) (and (<= t1 t2) (<= t2 t1)))) :rule equiv_intro
    :premises (t.p t.t5))
```

(In `t.p.t1`/`t.p.t2` the negated equality is an equation row of the Farkas combination, so it
may carry a coefficient of either sign.)

</details>

### Expensive (7)

| rule | reduction scheme | cost | what makes it expensive |
|---|---|---|---|
| `la_mult_pos` | `la_mult_pos_pos` + `poly_simp` + `la_generic` (+ `cong`, case splits for non-strict forms) | O(1) template | a syntactic schema becomes ring + Farkas checking; needs the proposed `la_mult_pos_pos` axiom |
| `la_mult_neg` | same, with `la_generic` sign-flip preprocessing | O(1) template | ditto |
| `prod_simplify`, `sum_simplify`, `minus_simplify`, `unary_minus_simplify` | rename to `poly_simp`; *alternative*: `rare_rewrite` chain over the RARE arithmetic rules | 0, or O(trace) via RARE | per-schema syntactic checking becomes the ring check (the RARE path keeps checks syntactic at trace-length cost) |
| `div_simplify` | `poly_simp` for real division by constants; `evaluate`/RARE for the integer `div`/`mod` cases | O(1) | integer division semantics are outside the ring primitive |

<details id="ex-la-mult-pos">
<summary>Example: <code>la_mult_pos</code>, strict form</summary>

```
(step t (cl (=> (and (> t1 0) (< t2 t3)) (< (* t1 t2) (* t1 t3)))) :rule la_mult_pos)
```

becomes

```
(anchor :step t.p)
(assume t.p.h (and (> t1 0) (< t2 t3)))
(step t.p.t1 (cl (> t1 0)) :rule and :premises (t.p.h) :args (0))
(step t.p.t2 (cl (< t2 t3)) :rule and :premises (t.p.h) :args (1))
(step t.p.t3 (cl (not (< t2 t3)) (> (- t3 t2) 0)) :rule la_generic :args (1 1))
(step t.p.t4 (cl (> (- t3 t2) 0)) :rule resolution :premises (t.p.t3 t.p.t2))
(step t.p.t5 (cl (=> (and (> t1 0) (> (- t3 t2) 0)) (> (* t1 (- t3 t2)) 0)))
    :rule la_mult_pos_pos)
(step t.p.t6 (cl (not (and (> t1 0) (> (- t3 t2) 0))) (> (* t1 (- t3 t2)) 0))
    :rule implies :premises (t.p.t5))
(step t.p.t7 (cl (and (> t1 0) (> (- t3 t2) 0))) :rule and_intro :premises (t.p.t1 t.p.t4))
(step t.p.t8 (cl (> (* t1 (- t3 t2)) 0)) :rule resolution :premises (t.p.t6 t.p.t7))
(step t.p.t9 (cl (= (* t1 (- t3 t2)) (- (* t1 t3) (* t1 t2)))) :rule poly_simp)
(step t.p.t10 (cl (= 0 0)) :rule eq_reflexive)
(step t.p.t11 (cl (= (> (* t1 (- t3 t2)) 0) (> (- (* t1 t3) (* t1 t2)) 0)))
    :rule cong :premises (t.p.t9 t.p.t10))
(step t.p.t12 (cl (> (- (* t1 t3) (* t1 t2)) 0)) :rule eq_mp :premises (t.p.t8 t.p.t11))
(step t.p.t13 (cl (not (> (- (* t1 t3) (* t1 t2)) 0)) (< (* t1 t2) (* t1 t3)))
    :rule la_generic :args (1 1))
(step t.p.t14 (cl (< (* t1 t2) (* t1 t3))) :rule resolution :premises (t.p.t13 t.p.t12))
(step t.p (cl (not (and (> t1 0) (< t2 t3))) (< (* t1 t2) (* t1 t3)))
    :rule subproof :discharge (t.p.h))
(step t.t1 (cl (=> (and (> t1 0) (< t2 t3)) (< (* t1 t2) (* t1 t3)))
               (and (> t1 0) (< t2 t3))) :rule implies_neg1)
(step t.t2 (cl (=> (and (> t1 0) (< t2 t3)) (< (* t1 t2) (* t1 t3)))
               (not (< (* t1 t2) (* t1 t3)))) :rule implies_neg2)
(step t.t3 (cl (not (and (> t1 0) (< t2 t3)))
               (=> (and (> t1 0) (< t2 t3)) (< (* t1 t2) (* t1 t3))))
    :rule resolution :premises (t.p t.t2))
(step t.t4 (cl (=> (and (> t1 0) (< t2 t3)) (< (* t1 t2) (* t1 t3)))
               (=> (and (> t1 0) (< t2 t3)) (< (* t1 t2) (* t1 t3))))
    :rule resolution :premises (t.t3 t.t1))
(step t (cl (=> (and (> t1 0) (< t2 t3)) (< (* t1 t2) (* t1 t3))))
    :rule contraction :premises (t.t4))
```

The `≈` form needs only `cong`; the `≤`/`≥` and disequality forms add one case split each;
`la_mult_neg` prepends the `la_generic` sign-flip `t1 < 0 → -t1 > 0` and uses `poly_simp` for
`(* (- t1) t2) ≈ (- (* t1 t2))`.

</details>

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
| `ac_simp` | decompose into one `aci_simp` step per single-connective layer, glued by `cong`/`trans` (O(d), d = alternation depth) — **fallback implemented** (`core` pass) | superseded by the more general `aci_simp`, which however normalizes a single connective at a time where `ac_simp` handles `∧` and `∨` simultaneously; removal in favor of `aci_simp` preferred over reduction |

## Extra rules beyond the specification

Carcara checks several rules that are not among the 120 specification rules. Classified the same
way, with their concern category noted:

| rule | category | level | reduction |
|---|---|---|---|
| `eq_mp` | clausal | reducible (**done**) | `equiv_pos2` + `resolution` (local and `core` passes) |
| `equiv_intro` (proposed) | clausal | reducible | iff-introduction from the two implications; `equiv_neg1/2` + resolutions + contractions (~7 steps) — names the closing pattern of every two-implication template. The `core` pass emits the expansion directly |
| `or_intro` (proposed) | clausal | reducible | packs `(cl l₁ … lₙ)` into `(cl (or l₁ … lₙ))`; `or_neg` ×n + resolutions + `contraction` — the packaging step of the LA reductions and the generalized `bind`'s unit closure. The `core` pass emits the expansion directly |
| `and_intro` | clausal | reducible (**done**, `core` pass) | `and_neg` + one `resolution` with explicit pivots |
| `strict_resolution` | clausal | core variant | strict form of `resolution` used after elaboration |
| `bounded_farkas` | arithmetic | reducible (**done**) | `la_generic` with inferred coefficients (local elaboration) |
| `poly_simp` | arithmetic | **core** (computational) | ring-normalization primitive; listed in the arithmetic core table above |
| `la_mult_pos_pos` | arithmetic | proposed core axiom | `(> x 0) ∧ (> y 0) → (> (* x y) 0)`; base of the `la_mult_*` schemes |
| `la_mult_sign` (`alethe-toolkit` branch) | arithmetic | expensive | O(n) fold of `la_mult_pos_pos` + `poly_simp` + `la_generic` |
| `div_intro`, `log2_intro`, `to_int_intro` (`alethe-toolkit` branch) | arithmetic | core (definitional) | characterization axioms of interpreted operators (division bound pair, `pow2` bounds, floor bounds) — the natural home for an `abs_intro`, which would make the `abs` RARE rule a lemma |
| `la_mult_abs_comparison` (`alethe-toolkit` branch) | arithmetic | aggressive | reducible to the same base once an `abs` definitional rewrite exists |
| `evaluate`, `mod_simplify`, `all_simplify` | equality & rewriting | aggressive | `all_simplify` already oracle-reducible via the hole pass |
| strings, PB, cutting-planes, arrays, DRUP, `sat_refutation` | theory extensions | aggressive | `sat_refutation` oracle-reducible via its dedicated pass |

<details id="ex-eq-mp">
<summary>Example: <code>eq_mp</code> (implemented)</summary>

```
(step t3 (cl F2) :rule eq_mp :premises (t1 t2))     ; t1: (cl F1), t2: (cl (= F1 F2))
```

becomes

```
(step t3.t1 (cl (not (= F1 F2)) (not F1) F2) :rule equiv_pos2)
(step t3 (cl F2) :rule resolution :premises (t3.t1 t2 t1)
    :args ((= F1 F2) false F1 false))
```

</details>

<details id="ex-equiv-or-intro">
<summary>Example: <code>equiv_intro</code>, <code>or_intro</code>, and <code>and_intro</code> (their own reductions)</summary>

`equiv_intro` from `p1: (cl (not A) B)` and `p2: (cl A (not B))`:

```
(step s1 (cl (= A B) A B)             :rule equiv_neg2)
(step s2 (cl (= A B) (not A) (not B)) :rule equiv_neg1)
(step s3 (cl (= A B) B B)             :rule resolution :premises (s1 p1))
(step s4 (cl (= A B) B)               :rule contraction :premises (s3))
(step s5 (cl (= A B) (not B) (not B)) :rule resolution :premises (s2 p2))
(step s6 (cl (= A B) (not B))         :rule contraction :premises (s5))
(step s7 (cl (= A B) (= A B))         :rule resolution :premises (s4 s6))
(step s  (cl (= A B))                 :rule contraction :premises (s7))
```

`or_intro` from `p: (cl l1 l2)`:

```
(step s1 (cl (or l1 l2) (not l1)) :rule or_neg :args (0))
(step s2 (cl (or l1 l2) (not l2)) :rule or_neg :args (1))
(step s3 (cl (or l1 l2) l2)       :rule resolution :premises (p s1))
(step s4 (cl (or l1 l2) (or l1 l2)) :rule resolution :premises (s3 s2))
(step s  (cl (or l1 l2))          :rule contraction :premises (s4))
```

`and_intro` from `p1: (cl l1)` and `p2: (cl l2)`:

```
(step s1 (cl (and l1 l2) (not l1) (not l2)) :rule and_neg)
(step s  (cl (and l1 l2)) :rule resolution :premises (s1 p1 p2))
```

</details>
