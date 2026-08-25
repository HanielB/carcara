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
| clausal | 47 | 23 | 24 | 0 | 0 | 0 |
| binder | 13 | 5 | 7 | 1 | 0 | 0 |
| equality & rewriting | 25 | 7 | 11 | 0 | 7 | 0 |
| arithmetic | 13 (+1) | 2 (+1) | 7 | 3 | 1 | 0 |
| bitvector | 14 | 14 | 0 | 0 | 0 | 0 |
| legacy | 5 | 0 | 0 | 0 | 0 | 5 |
| **total** | **120** | **54** | **49** | **4** | **8** | **5** |

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

### Reducible (24)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `th_resolution` | `resolution` | 0 | syntactic | **done** (`core` pass); same rule per the spec, normalize the name |
| `tautology` | `true` | 1 | syntactic | **done** (`core` pass); conclusion is literally `⊤`; drops the premise from the DAG |
| `reordering` | (eliminated) | 0 | — | done — reordering pass recomputes downstream conclusions |
| 19 premise clausification rules | matching CNF axiom + `resolution` | 2 each | syntactic | **done** (`core` pass); pivot = the premise formula |
| `weakening` | rename to `resolution` | 0 | RUP | negating the conclusion falsifies the premise before any propagation, so the step is a degenerate RUP derivation. The rename is only available under `resolution`'s RUP semantics — under the chain reading a resolution never *introduces* literals — which is why a chain-targeting pipeline keeps the rule |
| `contraction` | rename to `resolution` | 0 | RUP | same degenerate-RUP argument (the duplicate literal propagates nothing). Note the chain-targeting pipeline deliberately *emits* `contraction` steps, since chain resolution does not merge duplicates implicitly; the two readings of `resolution` pull in opposite directions here |

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
under three substitution disciplines, with binder congruence for `choice` folded into
[α/congr-bind] itself (`bind` is binder-generic; needed to reason under ε-witnesses);
`forall_inst` is [inst], independent
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
| `bind` | binder congruence; divergence 8 proposes generalizing it so that anchors carry fresh variables and substitutions, and the closing step additionally concludes a single ∀-closure literal (unit in practice; miniscoping only on binder *sets*, clause structure untouched) — ∀-introduction becomes the no-substitutions instance, vanilla `bind` an instance with zero extra steps, `sko_*`/`onepoint` the same closing scheme under their substitution disciplines, and `qnt_rm_unused` is absorbed. Checking stays free-variable-free: declared binder subsets verified positionally, scoping enforced by the parser (see parent chapter). The `choice` instance (formerly divergence 5) is folded in: `bind` is read as *binder-generic* — Carcara's checker already implements it that way — which is what bridges the `sko_ex`/`sko_forall` witness shapes. Together with `rare_rewrite` it covers rewriting *below* a binder |
| `let` | |
| `bind_let` | emitted by the polyeq elaboration itself |
| `sko_forall` | the designated Skolemization primitive; the spec's n-ary statement is erroneous (divergence 4) and must be fixed to the sequential choice-term form implementations already use |
| `forall_inst` | polyeq elaboration already normalizes it; independent of Skolemization — some arbitrary-term principle must be primitive (see parent chapter) |

### Reducible (11)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `onepoint` | case-split template driven by the guarded-occurrence grammar: `=`-branches transport `φ'` by deep `cong` with the point equalities; `≠`-branches derive `φ` by one CNF-axiom step per grammar production (`implies_neg1` for guards, `or_neg`/`and_pos` + `resolution` for descent, `not_not` for flips); assembled by `equiv_intro` (or its derivation) and `bind` | O(points·\|φ\|) | syntactic | **done** (`core` pass). The reduction reads its guards off the rule's own `extract_points` traversal, and its guard-escape derivation mirrors that traversal production by production, so every *body* the rule accepts is covered — both quantifiers, guards under `and`/`or`/`⇒`/negation and under inner binders, with or without a kept prefix. Not covered is the rule's other degree of freedom: its right-hand side need only be *provably* equal to the substituted body, and the subproof's own proof of that equality is checked under the anchor's substitution, so it cannot be replayed outside it; the recipe bridges the two itself, up to the orientation of equality subterms and the multiplicity of an `or`'s disjuncts, and keeps the step otherwise. Requires the spec to adopt the inductive side condition (divergence 7). Points under inner quantifiers generalize directly with the generalized `bind` (divergence 8), or via the derived `∀ȳ.⊤ ≈ ⊤`. Discharges the spec-acknowledged mutual-points gap via anchor-ordered case splits |
| `qnt_simplify` | generalized `bind` + `true` + iff-intro | 4 | syntactic | **done** (`core` pass, ∀ forms); witness-free with divergence 8, else ∀-ε-clause template |
| `qnt_rm_unused` | absorbed by the generalized `bind`'s miniscoped closure; standalone steps via `forall_inst` + closure + iff-intro | O(1) | syntactic | **done** (`core` pass). The rule compares its two binder lists as *sets*, so a list may repeat a variable and may reorder the survivors; the reduction normalizes repetitions away with a `bind` step on each side (`bind` compares binder lists as sets too, so this is exactly the normalization it licenses) and runs the removal between the normalized quantifiers, ordering the anchor so the surviving list is a subsequence of it. The `exists` case routes through the `connective_def` duality, so removal always happens on a `forall`. The rule's accepted space is covered |
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
`¬∀¬`-shaped one `sko_forall` expects is a `bind` over the `choice` binder (choice congruence;
`bind` is binder-generic) closing a `not-not` equivalence — this is what the `core` pass
implements.

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

### Expensive (1)

| rule | reduction scheme | cost | what makes it expensive |
|---|---|---|---|
| `sko_ex` | `connective_def` (duality) + `sko_forall` + `cong` ×2 + `not-not` rewrite + `trans`; existing steps additionally bridge the ∃-shaped witnesses to the ¬∀¬-shaped ones by a `bind` over the `choice` binder (choice congruence — `bind` is binder-generic, see its row) plus deep-`cong` transport | ~35 steps per binding (Δsteps ≈ 6.5 + 34.6·n measured, R² = 0.77); an ~8× local blowup — a ~10-command step region becomes ~84 steps plus ~6 anchors | The reduction is *complete and implemented* (`core/skolem.rs`, all corpus instances reduce and re-check) and every emitted step is a cheap core rule; it is classified expensive on **cost**, not feasibility. Each binding costs a witness-bridge `bind` subproof, a `connective_def` duality, an α-renaming `bind` of the quantified tail, a deep-`cong` transport, and a re-materialized copy of the double-negation helper. The `core` pass therefore leaves `sko_ex` steps alone by default; re-enabling the recipe is one map entry. Full measurements: `investigations/2026-08-18-sko-ex-cost.md` |

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

25 rules: 7 core, 11 reducible, 0 expensive, 7 aggressive.

### Core (7)

| rule | notes |
|---|---|
| `refl` | the only rule applying the context |
| `trans` | |
| `cong` | |
| `symm` | kept against the spec's "superfluous" note: explicit symmetry for elaborated output |
| `connective_def` | kept whole: propositional instances are O(1)-derivable, but the quantifier-duality instance is the R4-chosen axiom that bootstraps all ∃-reasoning, and the definition list hosts the `xor`/`ite`/`implies` axiom reductions (incl. the proposed `→` extension, divergence 6) |
| `rare_rewrite` | the designated rewrite primitive; oracle-checkable today |
| `aci_simp` | the designated ACI-normalization primitive, a computational check like `poly_simp` and `evaluate`: the spec itself remarks there is no canonical ACI normal form, so the check *is* the normalization — target of the `shuffle`/`nary_elim` renames and the `ac_simp` decomposition. It is the semilattice half of a single algebraic primitive whose ring half is `poly_simp`; the two are deliberately not merged, because embedding the semilattice level into the ring is exponential — see [the computational primitives, algebraically](../core.md#the-computational-primitives-algebraically) |

### Reducible (11)

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
| `and_simplify` | `aci_simp` (rename) for the aci-compatible instances — flattening, `true`-removal, duplicate removal, i.e. everything the rule does short of short-circuiting; a constant-size chain over the CNF axioms for the short-circuit to `false` (absorbing element by `and_pos` + the `false` axiom, complementary pair by two `and_pos` + resolution, stacked-negation parity by the double-negation recipe under `cong`) | 0 / O(1) | ACI / syntactic | **done** (`core` pass). Same check coarsening as `shuffle`/`nary_elim`, accepted for the same reason; without the rename, the recipe route is linear in the arity per removed constant, which two Averest QF_LIA proofs (hundred-argument conjunctions, ~18 000 instances) turn into a 4× logic-wide blowup |
| `or_simplify` | dual: `aci_simp` rename / short-circuit to `true` via `or_neg` + the `true` axiom and the complementary-pair template | 0 / O(1) | ACI / syntactic | **done** (`core` pass) |
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

### Aggressive (7)

| rule | reduction scheme | cost | missing prerequisite / blocker |
|---|---|---|---|
| `not_simplify`, `implies_simplify`, `equiv_simplify`, `bool_simplify`, `ite_simplify`, `eq_simplify` | `rare_rewrite` chain glued by `trans`/`cong`, replaying the rewrite trace of the fixpoint (**done** — the `core-simp-rare`/`core-taut` regimes, whose traces come from the checkers' own labeled step functions rather than from instrumentation). Their constant-folding instances are `evaluate` instances outright and rename to it (`core-taut` applies the evaluation recipe instead). `and_simplify`/`or_simplify` used to head this row; the `aci_simp` rename moved them to the *reducible* tier above | O(trace); 1 for the constant folds | none remaining for the trace route |
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

### Reducible (7)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `prod_simplify`, `sum_simplify`, `minus_simplify`, `unary_minus_simplify` | `poly_simp` (rename); the integer `div`/`mod` instances, which ring normalization cannot express, rename to `evaluate` instead | 0 | ring / evaluation | **done** (`core` pass). Promoted from *expensive* by the same criterion as `shuffle`/`nary_elim`/`and_simplify`: a one-step move onto a computational primitive the core already has. The check does coarsen — the rules' own per-schema folding becomes the ring check, measured at 12× per step (0.37 µs → 3.95 µs) on the corpus's most `prod_simplify`-dense proof, 1.5 percentage points of that file's checking and ~4 000 steps corpus-wide. Ring normalization distributes over nested products, so its worst case is worse than the folding it replaces; nothing in the corpus exercises that (p99 14 µs) |
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

### Expensive (3)

| rule | reduction scheme | cost | what makes it expensive |
|---|---|---|---|
| `la_mult_pos` | `la_mult_pos_pos` + `poly_simp` + `la_generic` (+ `cong`, case splits for non-strict forms) | O(1) template | a syntactic schema becomes ring + Farkas checking; needs the proposed `la_mult_pos_pos` axiom |
| `la_mult_neg` | same, with `la_generic` sign-flip preprocessing | O(1) template | ditto |
| `div_simplify` | `poly_simp` for real division by constants; `evaluate` for the integer `div`/`mod` cases | O(1) | both renames are implemented, so this rule is the obvious next promotion; it is held back only because its two cases take *different* primitives, and the integer one rests on the evaluation function's division semantics rather than on the ring |

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
| `qnt_cnf` | guided clausal descent against Carcara's checker semantics (NNF + ∀-prenexing + distribution): instantiate the left quantifier under the conclusion's anchor, then one CNF-axiom step per connective on the path from `φ` to the clause, branch choices guided by a CNF oracle — **fallback implemented** (`core` pass; linear resolution chain, subproof-free but for the closing `bind`) | spec-declared "placeholder rule" for the whole quantifier clausification — the *spec* gives it no semantics, so the reduction targets Carcara's implemented reading; removal still preferred |
| `ite_intro` | per ite-subterm, the selection tautology `(ite c (= s r₁) (= s r₂))` derives by a two-branch discharge over the condition — `equiv_neg1/2` + the `true`/`false` axioms turn the assumed (negated) condition into `(= c ⊤)`/`(= c ⊥)`, `cong` lifts it into `s`, and the term-level selection is the `rare_rewrite` rule `ite-true-cond`/`ite-false-cond` (alethe-toolkit rule set) — crossed with `ite_neg1/2` and packed by `and_neg`/`and_pos` + iff-introduction — **fallback implemented** (`core` pass; checking the output needs the RARE rules, e.g. `--rare-file rare-tests/rare/ite-intro.rare`) | artifact of veriT's internal ite constants (the spec's own remark); source of the ite-reordering polyeq quirk; removal still preferred |
| `bfun_elim` | case expansion over Boolean arguments: `forall_inst` at each of the `2^k` Boolean assignments + `and_neg` repack + closing `bind` over the rest — **fallback implemented** (`core` pass, top-level form; the below-uninterpreted-functions ite form is kept) | O(2^k) in the number of Boolean arguments — fails R1; removal preferred. veriT preprocessing artifact; polyeq elaboration normalizes but keeps it |
| `ac_simp` | decompose into one `aci_simp` step per single-connective layer, glued by `cong`/`trans` (O(d), d = alternation depth; linear in the term *DAG* via memoization) — **fallback implemented** (`core` pass). veriT's premise-carrying form (congruence over previously derived flattenings, incl. under-binder ones as `bind` subproofs — premises outside the spec's premise-free statement; Carcara's checker ignores them and normalizes through binders, a strictly stronger reading) is decomposed by consuming the premises as ready-made subterm equalities | superseded by the more general `aci_simp`, which however normalizes a single connective at a time where `ac_simp` handles `∧` and `∨` simultaneously; removal in favor of `aci_simp` preferred over reduction |

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
| `poly_simp_rel` (arithmetic case) | arithmetic | reducible (**done**, `core` pass) | the conclusion equates two linear relations over proportional differences, so each direction is a single `la_generic` step: weight the left relation's literal by \|c₁\| and the right's by \|c₂\|, which cancels the two linear combinations, and the strict one of the two supplies the strengthening that closes the contradiction — the absolute values are exactly why the rule requires `c₁` and `c₂` to share a sign unless the relation is `=`. For `=` a positive equality is not an `la_generic` literal, so each direction goes through `la_disequality` (the `la_rw_eq` template); `equiv_intro` glues them. **8 steps for an inequality, 20 for an equality** (10/24 when the premise is not a polynomial identity and must be carried in the certificate). All 114 015 corpus instances reduce. Needs `la_generic`'s normalization to see through `to_real`, as `poly_simp`'s already does — without that, two thirds of the QF_LIA instances are out of reach.<br><br>**On the aggregate cost.** Reducing it grows cvc5's arithmetic proofs by about a quarter (QF_LIA +22.6%, QF_LRA +22.1%, QF_UFLIA +27.5%), far more than any other single recipe, simply because cvc5 emits the rule 114 015 times. It stays *reducible* anyway, deliberately: the expensive tier means "this rule stays in the checking vocabulary", and this rule does not deserve that — it is an ad-hoc packaging of a Farkas step, carrying a premise the checker does not even validate as an identity, with a same-sign side condition that exists only because the certificate's weights are absolute values. Keeping the vocabulary small is the point of the classification; paying O(1) steps per instance to be rid of such a rule is the trade the reducible tier exists to make. Contrast `sko_ex`, which is a principled binder rule worth keeping in the vocabulary, and whose reduction costs O(bindings) steps per instance rather than a fixed 8 or 20 |
| `poly_simp_rel` (bitvector case) | arithmetic | removal | justified by odd coefficients being units modulo 2ⁿ, i.e. modular arithmetic: Farkas certificates over an ordered field and `la_disequality`'s antisymmetry cannot express it, and no bitvector core rule states that an odd constant is invertible. Awaits solver-side removal or a dedicated bitvector rule |
| `la_mult_pos_pos` | arithmetic | proposed core axiom | `(> x 0) ∧ (> y 0) → (> (* x y) 0)`; base of the `la_mult_*` schemes |
| `ite_then_intro`, `ite_else_intro` | equality & rewriting | proposed core axioms (**implemented**) | the term-`ite` selection pair, `▷ ¬c, (ite c t s) ≈ t` and `▷ c, (ite c t s) ≈ s`: premise-free clauses in `la_disequality`'s style, the definitional characterization of `ite` at arbitrary sorts (no other core rule provides one — `ite_pos/neg` are formula-level). Required by the `core-taut` regime's recipes for the term-`ite` RARE rules and by `evaluate`'s `ite` case; see "The trusted computing base, measured" in the parent chapter |
| `la_mult_sign` (`alethe-toolkit` branch) | arithmetic | expensive | O(n) fold of `la_mult_pos_pos` + `poly_simp` + `la_generic` |
| `to_int_lower`, `to_int_upper` | arithmetic | proposed core axioms (**implemented**) | the floor characterization of `to_int`, as the pair `▷ (to_real (to_int t)) ≤ t` and `▷ t < (to_real (to_int t)) + 1`. They pin `to_int t` to the unique integer in `(t − 1, t]`, which is what lets the core evaluate a ground `to_int` without an evaluator: `la_generic`'s (correctly gated) integer strengthening turns each bound into the corresponding bound on the value, and `la_disequality` closes the two into an equality. Required to bring the `core-taut` regime's `evaluate` residue to zero; see the parent chapter |
| `div_intro`, `log2_intro`, `to_int_intro` (`alethe-toolkit` branch) | arithmetic | core (definitional) | characterization axioms of interpreted operators (division bound pair, `pow2` bounds, floor bounds) — the natural home for an `abs_intro`, which would make the `abs` RARE rule a lemma. The `to_int` half is the `to_int_lower`/`to_int_upper` pair above |
| `la_mult_abs_comparison` (`alethe-toolkit` branch) | arithmetic | aggressive | reducible to the same base once an `abs` definitional rewrite exists |
| `evaluate` | equality & rewriting | **core** (computational) | constant evaluation of interpreted operators — a computational primitive on the same footing as `aci_simp` and `poly_simp`: the check *is* the (terminating, deterministic) evaluation function, and no rule-based reduction could be cheaper than re-evaluating |
| `mod_simplify`, `all_simplify` | equality & rewriting | aggressive | `all_simplify` already oracle-reducible via the hole pass |
| strings, PB, cutting-planes, arrays, DRUP, `sat_refutation` | theory extensions | aggressive | `sat_refutation` oracle-reducible via its dedicated pass |

### Outside this classification's scope

Carcara checks 181 rule names; this classification analyses the 120 specification rules plus the
extras above. The remainder are named here so that the gap is explicit rather than accidental —
they are rules that **only cvc5 produces**, and only in theories the evaluation does not
cover:

| rules | what they are | status |
|---|---|---|
| `bitblast_ashr`, `bitblast_comp`, `bitblast_const`, `bitblast_lshr`, `bitblast_shl`, `bitblast_udiv`, `bitblast_urem`, `bitblast_var` | eight bitblasting schemas Carcara checks beyond the specification's 14 | unclassified; presumably core alongside the other `bitblast_*` (same definitional character), but not analysed |
| `bitblast_equal`, `bitblast_sign_extend` | cvc5's names for the specification's `bitblast_eq` and `bitblast_sext` | naming divergence worth raising with the spec, not a semantic gap |
| 20 string rules (`concat_*`, `re_*`, `string_*`), 15 `pbblast_*`, 6 `cp_*`, 4 `arrays_*`, `drat`/`drup` | the theory-extension families of the row above | covered *collectively* as aggressive; no rule-by-rule reduction scheme is recorded |
| `ho_cong` | higher-order congruence: like `cong`, but the function position is itself equated by a premise | unclassified. It is not derivable from `cong`, which requires identical heads, so it is a genuine primitive candidate for a higher-order core |
| `strict_refl` | the strict, post-elaboration variant of `refl` (syntactic equality after applying the context) | core variant, like `strict_resolution` above |

None of them can appear in the evaluated logics (QF_UF, QF_UFLIA, QF_LIA, QF_LRA, UF, UFLIA).
The one cvc5-only rule that *does* appear there, `poly_simp_rel`, is classified in the extras
table above.

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
