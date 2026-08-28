# Rule classification

The full classification of the 120 Alethe specification rules, organized by *concern category*
(structural, clausal, binder, equality & rewriting, arithmetic, bitvector, legacy). Each category
section opens with the *proof system* it embodies — first abstractly, then as concretized by the
category's core rules — followed by its rules grouped by *reducibility level*:

- **core** — the elaboration target;
- **reducible** — a reduction meeting the criteria R1–R4 exists (linear size, checks staying
  within syntactic matching plus what the step already required, local, non-circular), and the
  pass applies it by default;
- **rare/simplify** — the rewrite vocabulary: the `*_simplify` rules and `rare_rewrite`, whose
  reduction replays a rewrite chain the checker itself computes. Complete and implemented, but
  applied only in the regimes that ask for it, since what it removes is a *rewrite interface*
  rather than a rule;
- **expensive** — the reduction is complete and implemented, but buys no checking power and
  costs a discharge subproof or a handful of steps per instance: the computational primitives
  `poly_simp` and `aci_simp`, `bind`, and `sko_ex`. These are the rules a consumer keeps if it is
  willing to implement their checks, and drops if it is not;
- **variant** — `eq_transitive` and `eq_congruent`, which state `trans`'s and `cong`'s judgments
  as premise-free clauses and which Carcara checks *with the very functions those rules call*
  (`find_chain`, `generic_congruent_rule`). A consumer implementing the core already has their
  checks, so they add nothing to the trusted base and eliminating them would trade steps for
  nothing. They are neither counted towards the core nor eliminated; the reduction exists in the
  tree (`core/equality.rs`, unregistered) should a consumer want the smaller vocabulary anyway.

The three non-core levels are *nested elimination stages*, and the evaluation measures them in
that order: a proof loses its reducible rules first, then the rewrite vocabulary, then the
expensive tier — each stage paying in proof size and checking time for a smaller trusted base.

**Oracle** names the one rule outside every stage, `lia_generic`, which carries no certificate.
Legacy rules keep their *recommendation* of removal (solvers should stop emitting
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

| category | total | core | reducible | rare/simplify | expensive | variant | oracle |
|---|---|---|---|---|---|---|---|
| structural | 3 | 3 | 0 | 0 | 0 | 0 | 0 |
| clausal | 47 | 23 | 22 | 0 | 0 | 2 | 0 |
| binder | 13 | 4 | 7 | 0 | 2 | 0 | 0 |
| equality & rewriting | 25 | 6 | 10 | 6 | 3 | 0 | 0 |
| arithmetic | 13 (+1) | 2 (+1) | 9 | 1 | 1 | 0 | 0 |
| bitvector | 14 | 14 | 0 | 0 | 0 | 0 | 0 |
| legacy | 5 | 0 | 4 | 0 | 0 | 0 | 1 |
| **total** | **120** | **52** | **52** | **7** | **6** | **2** | **1** |

Totals count *specification* rules only. The core additionally contains eight rules beyond the
specification, all of them listed in the category tables below rather than only in the extras
table at the end: `mult_pos`, `mult_neg`, `mult_distrib`, `to_int_lower` and `to_int_upper`
(arithmetic), `ite_then_intro` and `ite_else_intro` (equality & rewriting), and `qnt_duality`
(binder). Every one is implemented and checked; they are what let `la_mult_pos`/`la_mult_neg`, the
integer-rounding rewrites and `connective_def` leave the tiers they were in.

The two computational primitives `poly_simp` and `aci_simp` sit at *expensive* rather than in the
core: their reductions are implemented (`core-expensive`), so a consumer can have a proof without
them, and what it pays is steps — the ring identity becomes two Farkas bounds closed by
`la_disequality`, and the ACI equivalence becomes its two clausal directions. `evaluate` stays
core: constant evaluation has a concise statement per SMT-LIB operator, the same definitional
justification the core accepts for `bitblast_*` and `distinct_elim`, and it is the cheapest
computational primitive to check. The one rule no reduction reaches is `lia_generic`, which has no
certificate at all — the *oracle* column.

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
<summary>Example: all 19 premise clausification rules (<code>and</code>, <code>not_or</code>, <code>or</code>, <code>not_and</code>, <code>xor1</code>, <code>xor2</code>, <code>not_xor1</code>, <code>not_xor2</code>, <code>implies</code>, <code>not_implies1</code>, <code>not_implies2</code>, <code>equiv1</code>, <code>equiv2</code>, <code>not_equiv1</code>, <code>not_equiv2</code>, <code>ite1</code>, <code>ite2</code>, <code>not_ite1</code>, <code>not_ite2</code>)</summary>

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
core fragment. Spelled out, over `p`, `q`, `r` and the premises `a1 … a12` naming the twelve
formulas being clausified (`(and p q r)`, `(not (or p q r))`, `(or p q r)`, `(not (and p q))`,
`(xor p q)`, `(not (xor p q))`, `(=> p q)`, `(not (=> p q))`, `(= p q)`, `(not (= p q))`,
`(ite p q r)`, `(not (ite p q r))`):

```
(step s_not_or.c1 (cl (or p q r) (not q)) :rule or_neg :args (1))
(step s_not_or (cl (not q)) :rule resolution :premises (s_not_or.c1 a2) :args ((or p q r) true))

(step s_or.c1 (cl (not (or p q r)) p q r) :rule or_pos)
(step s_or (cl p q r) :rule resolution :premises (s_or.c1 a3) :args ((or p q r) false))

(step s_not_and.c1 (cl (and p q) (not p) (not q)) :rule and_neg)
(step s_not_and (cl (not p) (not q)) :rule resolution :premises (s_not_and.c1 a4) :args ((and p q) true))

(step s_xor1.c1 (cl (not (xor p q)) p q) :rule xor_pos1)
(step s_xor1 (cl p q) :rule resolution :premises (s_xor1.c1 a5) :args ((xor p q) false))

(step s_xor2.c1 (cl (not (xor p q)) (not p) (not q)) :rule xor_pos2)
(step s_xor2 (cl (not p) (not q)) :rule resolution :premises (s_xor2.c1 a5) :args ((xor p q) false))

(step s_not_xor1.c1 (cl (xor p q) p (not q)) :rule xor_neg1)
(step s_not_xor1 (cl p (not q)) :rule resolution :premises (s_not_xor1.c1 a6) :args ((xor p q) true))

(step s_not_xor2.c1 (cl (xor p q) (not p) q) :rule xor_neg2)
(step s_not_xor2 (cl (not p) q) :rule resolution :premises (s_not_xor2.c1 a6) :args ((xor p q) true))

(step s_implies.c1 (cl (not (=> p q)) (not p) q) :rule implies_pos)
(step s_implies (cl (not p) q) :rule resolution :premises (s_implies.c1 a7) :args ((=> p q) false))

(step s_not_implies1.c1 (cl (=> p q) p) :rule implies_neg1)
(step s_not_implies1 (cl p) :rule resolution :premises (s_not_implies1.c1 a8) :args ((=> p q) true))

(step s_not_implies2.c1 (cl (=> p q) (not q)) :rule implies_neg2)
(step s_not_implies2 (cl (not q)) :rule resolution :premises (s_not_implies2.c1 a8) :args ((=> p q) true))

(step s_equiv1.c1 (cl (not (= p q)) (not p) q) :rule equiv_pos2)
(step s_equiv1 (cl (not p) q) :rule resolution :premises (s_equiv1.c1 a9) :args ((= p q) false))

(step s_equiv2.c1 (cl (not (= p q)) p (not q)) :rule equiv_pos1)
(step s_equiv2 (cl p (not q)) :rule resolution :premises (s_equiv2.c1 a9) :args ((= p q) false))

(step s_not_equiv1.c1 (cl (= p q) p q) :rule equiv_neg2)
(step s_not_equiv1 (cl p q) :rule resolution :premises (s_not_equiv1.c1 a10) :args ((= p q) true))

(step s_not_equiv2.c1 (cl (= p q) (not p) (not q)) :rule equiv_neg1)
(step s_not_equiv2 (cl (not p) (not q)) :rule resolution :premises (s_not_equiv2.c1 a10) :args ((= p q) true))

(step s_ite1.c1 (cl (not (ite p q r)) p r) :rule ite_pos1)
(step s_ite1 (cl p r) :rule resolution :premises (s_ite1.c1 a11) :args ((ite p q r) false))

(step s_ite2.c1 (cl (not (ite p q r)) (not p) q) :rule ite_pos2)
(step s_ite2 (cl (not p) q) :rule resolution :premises (s_ite2.c1 a11) :args ((ite p q r) false))

(step s_not_ite1.c1 (cl (ite p q r) p (not r)) :rule ite_neg1)
(step s_not_ite1 (cl p (not r)) :rule resolution :premises (s_not_ite1.c1 a12) :args ((ite p q r) true))

(step s_not_ite2.c1 (cl (ite p q r) (not p) (not q)) :rule ite_neg2)
(step s_not_ite2 (cl (not p) (not q)) :rule resolution :premises (s_not_ite2.c1 a12) :args ((ite p q r) true))
```

The pivot is always the premise formula; its *polarity* argument is `false` for the nine positive
rules (the premise is the formula, the axiom carries its negation) and `true` for the ten `not_*`
rules (the premise is the negation, the axiom carries the formula). That single flag is the whole
difference between the two halves of the family.

</details>

<details id="ex-clausal-renames">
<summary>Example: <code>th_resolution</code>, <code>tautology</code>, <code>reordering</code></summary>

`th_resolution` is `resolution` under another name — the spec says so outright, and the reduction
is the rename, arguments and all:

```
(step r (cl p r) :rule th_resolution :premises (c1 c2))    ; c1: (cl p q r), c2: (cl (not q))
```

becomes

```
(step r (cl p r) :rule resolution :premises (c1 c2))
```

`tautology` concludes literally `(cl true)`, so once the premise's complementary pair has been
checked there is nothing left to transport: the conclusion is an instance of the `true` axiom, and
the premise leaves the DAG.

```
(step r (cl true) :rule tautology :premises (t))           ; t: (cl p (not p) q)
```

becomes

```
(step r (cl true) :rule true)
```

Note the direction of the trade: the reduction *drops* a dependency rather than adding steps, so
`t` survives only if something else uses it — one of the few places in the ladder where a
reduction can make the proof *smaller*.

`reordering` is not reduced but *eliminated*: the reordering pass rewrites the conclusions of the
steps below it and deletes the step. Given

```
(step c_or (cl p q r) :rule or :premises (h1))
(step r (cl r q p) :rule reordering :premises (c_or))
(step end (cl) :rule hole :premises (r))
```

the pass emits no replacement for `r` at all and repoints `end` at `c_or`:

```
(step c_or (cl p q r) :rule or :premises (h1))
(step end (cl) :rule hole :premises (c_or))
```

which is sound exactly because every core clausal rule reads its premises as sets.

</details>

<details id="ex-weakening-contraction">
<summary>Example: <code>weakening</code> and <code>contraction</code></summary>

Both renames are available only under `resolution`'s RUP reading, and both have to satisfy the
rule's two-premise minimum — which the repeated premise does, since resolution takes its premises
as a set:

```
(step w (cl p q r s) :rule weakening :premises (c_or))     ; c_or: (cl p q r)
(step c (cl p q)     :rule contraction :premises (d))      ; d:    (cl p p q)
```

become

```
(step w (cl p q r s) :rule resolution :premises (c_or c_or))
(step c (cl p q)     :rule resolution :premises (d d))
```

In both cases negating the conclusion already falsifies the premise clause, before any unit
propagation happens, so the RUP check succeeds immediately. Under the *chain* reading of
`resolution` neither rename is available — a chain resolution never introduces a literal, and it
never merges duplicates — which is why a chain-targeting pipeline keeps both rules and in fact
emits `contraction` steps of its own. That conditionality is why the two rules sit in *reducible*
rather than in the core: the rename is real but it is not available in every reading of
`resolution`. Carcára's `core` pass accordingly leaves both steps in place; the rename above is
what a RUP-only target would apply, and it costs nothing either way.

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

13 rules: 4 core, 7 reducible, 2 expensive.

### Core (4 + 1 extra)

| rule | notes |
|---|---|
| `let` | |
| `bind_let` | emitted by the polyeq elaboration itself |
| `sko_forall` | the designated Skolemization primitive; the spec's n-ary statement is erroneous (divergence 4) and must be fixed to the sequential choice-term form implementations already use |
| `forall_inst` | polyeq elaboration already normalizes it; independent of Skolemization — some arbitrary-term principle must be primitive (see parent chapter) |
| `qnt_duality` (extra) | **proposed core axiom, implemented** — `▷ (= (forall X φ) (not (exists X (not φ))))` and its dual. Carved out of `connective_def` (2026-08-25): the propositional instances of that rule derive from the CNF axioms, but nothing else in the core relates `∀` and `∃`, so *this* instance has to be primitive. Naming it separately is what lets `connective_def` become reducible |

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

#### The nonlinear multiplication pair

| rule | reduces to | growth | check power | status |
|---|---|---|---|---|
| `la_mult_pos` | `mult_pos` + `poly_simp` + `la_generic` glue (`eq_congruent` for the `=` form, one `la_disequality` case split for `≤`/`≥`) | O(1) template (~15–25 steps) | pos-cone + ring + Farkas | **done** (`core` pass, 2026-08-25). Promoted from *expensive* when the proposed axiom was adopted as `mult_pos`: the recipe validates every `la_generic` certificate and the `poly_simp` ring identity before emission, so an unanticipated shape keeps the step |
| `la_mult_neg` | same, prepending the `la_generic` sign bridge `(cl ¬(< m 0) (> (- m) 0))` and scaling by `(- m)` | O(1) template | ditto | **done** (`core` pass) |

### Expensive (2)

| rule | reduction scheme | cost | what makes it expensive |
|---|---|---|---|
| `bind` | Three routes, tried in order. **Exact renaming**: Skolemize *both* sides at the *same* witnesses and join by `symm`/`trans` — 4 steps, the body never inspected. **General α-equivalence** (nested bound names differ, equalities reoriented, bodies shadow): instantiate both sides at the target's ε-witnesses, so the two instances differ only *under nested binders* and at variables the enclosing anchor renames, and bridge those recursively — nested quantifier pairs recurse through the same construction (`∃` through `qnt_duality`), renamed free variables are contextual `refl`s, reoriented equalities go through `cong`'s four-orientation search, and two α-variant `let` terms are expanded and rejoined (`bind_let` cannot do it — its checker requires both binding lists to carry the *same* names — but a `let` is a definition, and two definitions differing only in the defined name have the same expansion). **Rewriting bodies**: the ∀-ε-clause of one side, `forall_inst` of the other at the same witnesses, and a replay of the body with the witnesses substituted (core rules are schematic, so their instances survive a uniform substitution of closed terms), in two directions closed by iff-introduction; a nested `let` scope in the body is *dissolved* — its bindings join the witness substitution and its `let` step becomes the definitional expansion it always was | 4 steps + 2 anchors (renaming); O(α-difference) (α route); 2·\|body\| + ~10 (rewriting) | **done** (`core-expensive` pass, 2026-08-27) — the admissibility argument of the "what the generalization buys" section, made executable; it buys no checking power, so the default regimes keep the rule. **Every one of the corpus's `bind` steps reduces** — 6\,592 of veriT's 6\,592 and 8\,447 of cvc5's 8\,447, over six logics — with every proof re-checking at elaborated granularity. The one exception is self-inflicted: the `sko_ex` reduction emits a `bind` over a `choice` binder to bridge its witness shapes, and *that* has no core route ([divergence 5](#divergences)) — keep `sko_ex` core, as having both `∃`-introduction and `∃`-elimination primitive means, and nothing asks for choice congruence at all |
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

25 rules: 6 core, 10 reducible, 6 rare/simplify, 3 expensive; `eq_transitive` and `eq_congruent` are *variants* (see below).

### Core (6 + 2 extra)

| rule | notes |
|---|---|
| `refl` | the only rule applying the context |
| `trans` | |
| `cong` | |
| `symm` | kept against the spec's "superfluous" note: explicit symmetry for elaborated output |
| `ite_then_intro`, `ite_else_intro` (extra) | **proposed core axioms, implemented** — the term-`ite` selection pair `▷ ¬c, (ite c t s) ≈ t` and `▷ c, (ite c t s) ≈ s`. Premise-free clauses in `la_disequality`'s style, the definitional characterization of `ite` at arbitrary sorts; no other core rule provides one, since `ite_pos`/`ite_neg` are formula-level. Required by the `core-taut` recipes for the term-`ite` RARE rules and by `evaluate`'s `ite` case |
| `rare_rewrite` | the designated rewrite primitive; oracle-checkable today |
| `distinct_elim` | the definitional computational schema for `distinct` (adopted 2026-08-25, previously in the rewrite tier): its check computes the pairwise-disequality expansion, arity-dependent output included, exactly as `bitblast_*` compute theirs. The blocker that kept it out was never the rule but its *RARE replacement* — an n-ary `distinct` rule needs a recursive Eunoia program — and waiting on that machinery bought nothing: the rule is a fixed 40-line schema, and with it core the `distinct-binary-elim`/`distinct-false` RARE rules become lemmas (one `distinct_elim` step plus Boolean glue / plus `refl` on the repeated element) |

### Reducible (10)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `eq_symmetric` | `refl` + `cong`: the equivalence between an equality and its flip is a congruence instance, since `cong`'s checker tries all four orientations of a two-argument equality pair | 2 | syntactic | **done** (`core` pass, 2026-08-27). Previously *expensive* on the ~9-step two-subproof route; the `cong` route makes it one of the cheapest reductions in the tier. The subproof route is still built where the orientation search does not apply, and the smaller kept |
| `connective_def` | quantifier duality: rename to `qnt_duality`. The three propositional instances: pure resolution over the CNF axioms of the two sides, glued by the iff-introduction pattern — no anchor | 1 for the duality, ~32 for a propositional instance | syntactic | **done** (`core` pass, 2026-08-25). It was *core* because of the duality; splitting that off as its own axiom leaves the rest derivable, which is what the "agreement lemma" note always claimed. The three propositional templates are `(= (xor a b) …)`, `(= (= a b) …)` and `(= (ite c x y) …)`; each derives `(cl ¬lhs rhs)` and `(cl lhs ¬rhs)` from the `xor`/`equiv`/`ite` and `and`/`or`/`implies` axiom families, with `not_not` discharging the `¬¬` literals that `and_neg` on a negated conjunct produces |
| `not_symm` | `refl` + `cong` + `equiv_pos1` + 2 resolutions — no anchor | 4 | syntactic | **done** (`core` pass, 2026-08-25). Contraposition needs the equivalence `(= (= a b) (= b a))`, and `cong` proves it directly: its checker tries all four orientations of a two-argument equality pair, so with the arguments flipped every pair is syntactically equal, and one `refl` satisfies its one-premise minimum. Both this and the discharge-subproof route are built and the smaller kept |
| `eq_reflexive` | `refl` (empty context) | 1 | syntactic | **done** (`core` pass); the rename is unconditional (guarded only against assigning anchors), so `eq_reflexive` never survives elaboration |
| `eq_congruent_pred` | `eq_congruent` + one `equiv_pos` axiom + `resolution` | 3 | syntactic | **done** (`core` pass, 2026-08-25). The predicate rule is the function rule read through an equivalence: where `eq_congruent` concludes `(= p(t̄) p(ū))`, the predicate variant states that equality split into its two-literal tail. The older reduction (discharge subproof + `cong` + `eq_mp`) is superseded now that `eq_congruent` is core; see the spec-divergence note on its conclusion shape |
| `shuffle` | `aci_simp` (rename) | 0 | ACI | **done** (`core` pass); the check coarsens from multiset comparison to full ACI normalization — sound, and `aci_simp` is the designated ACI primitive |
| `nary_elim` | `aci_simp` (rename), for the assoc-comm operators | 0 | ACI | **done** (`core` pass); chainable (`=`) and non-commutative (`→`, `-`) cases keep the binary-associativity `rare_rewrite` chain (below) and are left unchanged |
| `and_simplify` | `aci_simp` (rename) for the aci-compatible instances — flattening, `true`-removal, duplicate removal, i.e. everything the rule does short of short-circuiting; a constant-size chain over the CNF axioms for the short-circuit to `false` (absorbing element by `and_pos` + the `false` axiom, complementary pair by two `and_pos` + resolution, stacked-negation parity by the double-negation recipe under `cong`) | 0 / O(1) | ACI / syntactic | **done** (`core` pass). Same check coarsening as `shuffle`/`nary_elim`, accepted for the same reason; without the rename, the recipe route is linear in the arity per removed constant, which two Averest QF_LIA proofs (hundred-argument conjunctions, ~18 000 instances) turn into a 4× logic-wide blowup |
| `or_simplify` | dual: `aci_simp` rename / short-circuit to `true` via `or_neg` + the `true` axiom and the complementary-pair template | 0 / O(1) | ACI / syntactic | **done** (`core` pass) |
| `multi_rare_rewrite` | `rare_rewrite` chain + `trans`/`cong` | O(k·depth) | syntactic | planned; validate rule-position semantics first |

<details id="ex-eqrw-renames">
<summary>Example: <code>eq_reflexive</code> and <code>shuffle</code></summary>

Two one-step moves onto primitives the core already has. `eq_reflexive` states `t ≈ t` with no
context; `refl` states the same thing modulo the anchor's substitution, which on an empty context
is the identity:

```
(step r (cl (= x x)) :rule eq_reflexive)      ->   (step r (cl (= x x)) :rule refl)
```

The rename is unconditional — the only guard is against assigning it *inside* a
substitution-carrying anchor, where `refl` would mean something else — so `eq_reflexive` never
survives elaboration.

`shuffle` permutes the arguments of an associative-commutative operator, which is a special case of
what `aci_simp` normalizes:

```
(step s (cl (= (or p q r) (or r q p))) :rule shuffle)
```

becomes

```
(step s (cl (= (or p q r) (or r q p))) :rule aci_simp)
```

The check coarsens from a multiset comparison to full ACI normalization. That is a *widening* of
what the step licenses, which is sound here only because `aci_simp` is the designated ACI
primitive of the core — the same argument that promotes `nary_elim` and the `*_simplify` bundle.

</details>

<details id="ex-and-or-simplify">
<summary>Example: <code>and_simplify</code> and <code>or_simplify</code></summary>

These rules do two different jobs and take two different routes. Everything short of
short-circuiting — flattening, removing `true` from a conjunction or `false` from a disjunction,
removing duplicates — is ACI normalization, so it renames:

```
(step s (cl (= (and p true q) (and p q))) :rule and_simplify)
(step s (cl (= (or p false q) (or p q)))  :rule or_simplify)
```

become

```
(step s (cl (= (and p true q) (and p q))) :rule aci_simp)
(step s (cl (= (or p false q) (or p q)))  :rule aci_simp)
```

The short-circuit is not an ACI fact and takes a constant-size chain over the CNF axioms instead.
For the complementary pair, `and_simplify`'s `false` case:

```
(step s (cl (= (and p (not p)) false)) :rule and_simplify)
```

becomes

```
(step s.c4 (cl (= (and p (not p)) false) (and p (not p)) false) :rule equiv_neg2)
(step s.c5 (cl (not false)) :rule false)
(step s.c6 (cl (= (and p (not p)) false) (and p (not p)))
    :rule resolution :premises (s.c4 s.c5) :args (false true))
(step s.c1 (cl (not (and p (not p))) p) :rule and_pos :args (0))
(step s.c2 (cl (not (and p (not p))) (not p)) :rule and_pos :args (1))
(step s.c3 (cl (not (and p (not p)))) :rule resolution :premises (s.c1 s.c2) :args (p true))
(step s (cl (= (and p (not p)) false))
    :rule resolution :premises (s.c6 s.c3) :args ((and p (not p)) true))
```

and `or_simplify`'s `true` case is the exact dual, `and_pos`→`or_neg`, `equiv_neg2`→`equiv_neg1`,
`false`→`true`:

```
(step s.c4 (cl (= (or p (not p)) true) (not (or p (not p))) (not true)) :rule equiv_neg1)
(step s.c5 (cl true) :rule true)
(step s.c6 (cl (= (or p (not p)) true) (not (or p (not p))))
    :rule resolution :premises (s.c4 s.c5) :args (true false))
(step s.c2 (cl (or p (not p)) (not (not p))) :rule or_neg :args (1))
(step s.c1 (cl (or p (not p)) (not p)) :rule or_neg :args (0))
(step s.c3 (cl (or p (not p))) :rule resolution :premises (s.c2 s.c1) :args ((not p) false))
(step s (cl (= (or p (not p)) true))
    :rule resolution :premises (s.c6 s.c3) :args ((or p (not p)) false))
```

Seven steps either way, independent of the arity. Keeping the ACI rename for the non-short-circuit
majority is not an aesthetic choice: the recipe route for a removed constant is linear in the
arity, and two Averest QF_LIA proofs with hundred-argument conjunctions (~18 000 instances) turn
that into a 4× logic-wide blowup.

</details>

<details id="ex-connective-def">
<summary>Example: <code>connective_def</code>, propositional instance</summary>

The quantifier instance of `connective_def` is the `∀/∃` duality and renames to `qnt_duality` in
one step. The three propositional instances are pure resolution over the CNF axioms of the two
sides, glued by iff-introduction — no anchor anywhere. Taking the `=`-instance:

```
(step s (cl (= (= p q) (and (=> p q) (=> q p)))) :rule connective_def)
```

The derivation has two halves. First `(cl (and (=> p q) (=> q p)) (not (= p q)))` — the
right-to-left direction, built by proving each implication from the `equiv_pos` axioms and packing
them with `and_neg`:

```
(step s.c11 (cl (and (=> p q) (=> q p)) (not (=> p q)) (not (=> q p))) :rule and_neg)
(step s.c1 (cl (=> p q) p) :rule implies_neg1)
(step s.c3 (cl (not (= p q)) (not p) q) :rule equiv_pos2)
(step s.c4 (cl (=> p q) (not (= p q)) q) :rule resolution :premises (s.c1 s.c3) :args (p true))
(step s.c2 (cl (=> p q) (not q)) :rule implies_neg2)
(step s.c5 (cl (=> p q) (not (= p q))) :rule resolution :premises (s.c4 s.c2) :args (q true))
(step s.c12 (cl (and (=> p q) (=> q p)) (not (=> q p)) (not (= p q)))
    :rule resolution :premises (s.c11 s.c5) :args ((=> p q) false))
(step s.c6 (cl (=> q p) q) :rule implies_neg1)
(step s.c8 (cl (not (= p q)) p (not q)) :rule equiv_pos1)
(step s.c9 (cl (=> q p) (not (= p q)) p) :rule resolution :premises (s.c6 s.c8) :args (q true))
(step s.c7 (cl (=> q p) (not p)) :rule implies_neg2)
(step s.c10 (cl (=> q p) (not (= p q))) :rule resolution :premises (s.c9 s.c7) :args (p true))
(step s.c13 (cl (and (=> p q) (=> q p)) (not (= p q)))
    :rule resolution :premises (s.c12 s.c10) :args ((=> q p) false))
```

The mirror half — steps `s.c14` through `s.c24`, ending in
`(cl (= p q) (not (and (=> p q) (=> q p))))` — is the same shape with every polarity swapped:
`and_pos` selects each conjunct, `implies_pos` consumes it, `equiv_neg1/2` assembles the
equivalence. The two halves then meet at the iff-introduction pattern:

```
(step s.c25 (cl (= (= p q) (and (=> p q) (=> q p))) (= p q) (and (=> p q) (=> q p)))
    :rule equiv_neg2)
(step s.c27 (cl (= (= p q) (and (=> p q) (=> q p))) (and (=> p q) (=> q p)))
    :rule resolution :premises (s.c25 s.c13) :args ((= p q) true))
(step s.c26 (cl (= (= p q) (and (=> p q) (=> q p))) (not (= p q))
                (not (and (=> p q) (=> q p)))) :rule equiv_neg1)
(step s.c28 (cl (= (= p q) (and (=> p q) (=> q p))) (not (and (=> p q) (=> q p))))
    :rule resolution :premises (s.c26 s.c24) :args ((= p q) false))
(step s.c29 (cl (= (= p q) (and (=> p q) (=> q p)))
                (= (= p q) (and (=> p q) (=> q p))))
    :rule resolution :premises (s.c27 s.c28) :args ((and (=> p q) (=> q p)) true))
(step s (cl (= (= p q) (and (=> p q) (=> q p)))) :rule contraction :premises (s.c29))
```

30 steps for the `=`-instance, 34 for `(= (xor p q) (or (and (not p) q) (and p (not q))))` and 32
for `(= (ite p q r) (and (=> p q) (=> (not p) r)))`. The differences are the `not_not` steps that
discharge the `¬¬` literals `and_neg`/`or_neg` produce on a *negated* conjunct — two of them in
the `xor` case, one in the `ite` case — plus, in the `xor` case, the extra `or_neg`/`or_pos` layer
its disjunctive right-hand side needs. All constant-size, and none of the three needs a subproof.

</details>

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

`eq_symmetric` concludes the *equivalence* `(= (= a b) (= b a))`, which is exactly what `cong`
proves — with the argument lists flipped, every argument pair of the two equalities is already
syntactically equal, and the rule's one-premise minimum is met by a `refl`. Two steps:

```
(step t (cl (= (= a b) (= b a))) :rule eq_symmetric)
```

becomes

```
(step t.c1 (cl (= a a)) :rule refl)
(step t (cl (= (= a b) (= b a))) :rule cong :premises (t.c1))
```

Where `cong`'s orientation search does not apply, the subproof route is used instead — one `symm`
subproof per direction, glued by the iff-introduction pattern (~9 steps and two anchors) — and the
pass keeps whichever came out smaller:

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

### Expensive (3)

`aci_simp` is the one in this category (`poly_simp` and `sko_ex` are the other two, under
arithmetic and binder):

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `aci_simp` | the two clausal directions of the equivalence: each side taken apart with `and_pos`/`or_pos` and the other put together with `and_neg`/`or_neg`, closed by the iff-introduction pattern | ~4 per leaf | syntactic | **done** (`core-expensive` pass). Linear in the number of leaves for a flat term, leaves × depth for a nested one. The reduction covers the semilattice connectives — the only headers the corpus exercises — and the identity element (`true` for `and`, `false` for `or`) through the corresponding axiom; an arithmetic or bitvector head keeps the step. Being *expensive* rather than core is a measured call, not a stylistic one: on veriT's proofs `aci_simp` is 5% of the elaborated steps but **46% of the checking time**, and the reductions that target it (`ac_simp`, `and_simplify`/`or_simplify`, `shuffle`, `nary_elim`) take 2.6 s of original checking into 7.2 s of it |

### Variants (2)

`eq_transitive` and `eq_congruent` state `trans`'s and `cong`'s judgments as premise-free clauses.
Carcara checks them **with the very functions those rules call** — `eq_transitive`'s checker is
`find_chain`, which `trans` calls, and `eq_congruent`'s is `generic_congruent_rule`, which `cong`'s
shares — so a consumer that implements the core already has their checks. They add nothing to the
trusted base, and eliminating them would trade steps for nothing: they are neither counted towards
the core nor reduced.

That is not a statement about difficulty. Both reductions are written and complete
(`core/equality.rs`, unregistered): a discharge subproof assuming the negated equalities, closed by
`trans` (≤ 2n steps and an anchor, plus a `symm` per flipped link) or by `cong` (≤ 2n+2 and an
anchor). Applying them was measured at roughly three quarters of the `core` pass's growth on veriT
proofs, which is what the tier used to be *called* expensive for; the sharper statement is that the
growth buys nothing, since the checkers are shared.

The reverse direction is available too, and cheaper: `trans` becomes `eq_transitive` + one
resolution and `cong` becomes `eq_congruent` + one resolution — **two steps each**, except that
`eq_congruent` requires one literal per argument pair where `cong` lets identical arguments skip a
premise, so each skipped argument adds a `refl`. Which side a consumer prefers is conventional
(R4); the classification keeps both and reduces neither.

**A second reason to keep them.** They are the target vocabulary of the `deep-hoist` pass's
clausal replay, which turns a lemma scope inside out: assumptions become hypothesis literals and
the body's `cong`/`trans`/`symm` steps become `eq_congruent`/`eq_transitive` instances. Reducing
those back into discharge subproofs undoes exactly what the replay achieved — with them reduced,
`deep-hoist` + `core` produced *more* scopes than the input; with them kept, the same pipeline
gives 21% fewer commands than the input and eliminates 95% of cvc5's anchors.

### Rare/simplify (6)

| rule | reduction scheme | cost | missing prerequisite / blocker |
|---|---|---|---|
| `not_simplify`, `implies_simplify`, `equiv_simplify`, `bool_simplify`, `ite_simplify`, `eq_simplify` | `rare_rewrite` chain glued by `trans`/`cong`, replaying the rewrite trace of the fixpoint (**done** — the `core-simp-rare`/`core-taut` regimes, whose traces come from the checkers' own labeled step functions rather than from instrumentation). Their constant-folding instances are `evaluate` instances outright and rename to it (`core-taut` applies the evaluation recipe instead). `and_simplify`/`or_simplify` used to head this row; the `aci_simp` rename moved them to the *reducible* tier above | O(trace); 1 for the constant folds | none remaining for the trace route |

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

Concretely: `la_generic` is [farkas], the adopted axioms `mult_pos`/`mult_neg` are [pos-cone] and
`la_disequality` is [antisym]. [ring] is the one axis with *two* realizations: the `poly_simp`
primitive, which decides an arbitrary polynomial identity, and the `mult_distrib` axiom, which
states the single ring law — distributivity over subtraction — that the reductions actually need.
Keeping both is what lets `poly_simp` sit at *expensive*: with `mult_distrib` core, no reduction
depends on ring normalization, and `poly_simp`'s own instances reduce to Farkas bounds whenever
they are linear.

13 specification rules (2 core, 9 reducible, 1 rare/simplify, 1 expensive) plus four extra rules
in the core. See the
[arithmetic section](../core.md#arithmetic-la_generic-as-the-computational-core) of
the parent chapter for the recipes.

### Core (2 + 6 extra)

| rule | notes |
|---|---|
| `la_generic` | the linear computational primitive (Farkas certificates) |
| `la_disequality` | the [antisym] axiom, `▷ (t1 ≈ t2), ¬(t1 ≤ t2), ¬(t2 ≤ t1)`: premise-free clause, O(1) syntactic check. Kept core because no combination of the other axes can introduce a positive arithmetic equality (see "Lemmas, not axioms" in the RARE chapter); the exact counterpart of cvc5's dedicated `ARITH_TRICHOTOMY` rule, and literally RESOLUTE's `trichotomy` axiom modulo the `¬≤`/`<` atom flip (see the parent chapter's RESOLUTE comparison). Would become reducible only under the two-coefficient-vector generalization of `la_generic` recorded there |
| `mult_pos`, `mult_neg` (extra) | **proposed core axioms, implemented** (`mult_pos` proposed as `la_mult_pos_pos`) — the [pos-cone] pair `▷ ¬(> x 0), ¬(> y 0), (> (* x y) 0)` and `▷ ¬(< x 0), ¬(> y 0), (< (* x y) 0)`, the sign rules for a product, stated as premise-free clauses in `la_disequality`'s style. Genuinely nonlinear, so no Farkas combination replaces them; base of the `la_mult_*` reductions. Stating the negative case separately, rather than bridging `(< m 0)` to `(> (- m) 0)`, is what keeps the ring identity underneath those reductions inside `mult_distrib`'s reach |
| `mult_distrib` (extra) | **proposed core axiom, implemented** — distributivity over subtraction, `▷ (* x (- y z)) ≈ (- (* x y) (* x z))`. The one ring law the core needs beyond `la_generic`'s linear reasoning: scaling a comparison relates the scaled sides' difference to the multiplier times the original difference, and that identity is nonlinear whenever the multiplier is symbolic. It is exactly the step the `la_mult_*` reductions used to delegate to `poly_simp` |
| `to_int_lower`, `to_int_upper` (extra) | **proposed core axioms, implemented** — the floor characterization of `to_int`, `▷ (to_real (to_int t)) ≤ t` and `▷ t < (to_real (to_int t)) + 1`. They pin `to_int t` to the unique integer in `(t − 1, t]`, which is what lets the core evaluate a ground `to_int` with no evaluator: `la_generic`'s integer strengthening turns each bound into a bound on the value and `la_disequality` closes the two into an equality. The `to_int` half of the definitional `*_intro` family; `div` and `mod` would need the same and do not have it |

### Reducible (9)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `prod_simplify`, `sum_simplify`, `minus_simplify`, `unary_minus_simplify` | `poly_simp` (rename); the integer `div`/`mod` instances, which ring normalization cannot express, rename to `evaluate` instead. `poly_simp` is itself *expensive*, so under `core-expensive` these end at the Farkas bounds its reduction produces | 0 | ring / evaluation | **done** (`core` pass). Promoted from *expensive* by the same criterion as `shuffle`/`nary_elim`/`and_simplify`: a one-step move onto a computational primitive the core already has. The check does coarsen — the rules' own per-schema folding becomes the ring check, measured at 12× per step (0.37 µs → 3.95 µs) on the corpus's most `prod_simplify`-dense proof, 1.5 percentage points of that file's checking and ~4 000 steps corpus-wide. Ring normalization distributes over nested products, so its worst case is worse than the folding it replaces; nothing in the corpus exercises that (p99 14 µs) |
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

<details id="ex-la-tautology">
<summary>Example: <code>la_tautology</code>, both forms</summary>

The unit form is the whole reduction — the Farkas certificate is the single coefficient `1`:

```
(step u (cl (>= x x)) :rule la_tautology)   ->   (step u (cl (>= x x)) :rule la_generic :args (1.0))
```

The binary form concludes an `or`-*term* rather than a two-literal clause, so after the
`la_generic` step the disjunction has to be re-introduced — the `or_intro` packaging above, written
out:

```
(step t (cl (or (not (<= x 0)) (<= x 1))) :rule la_tautology)
```

becomes

```
(step t.c1 (cl (not (<= x 0)) (<= x 1)) :rule la_generic :args (1.0 1.0))
(step t.c2 (cl (or (not (<= x 0)) (<= x 1)) (not (not (<= x 0)))) :rule or_neg :args (0))
(step t.c3 (cl (<= x 1) (or (not (<= x 0)) (<= x 1)))
    :rule resolution :premises (t.c1 t.c2) :args ((not (<= x 0)) true))
(step t.c4 (cl (or (not (<= x 0)) (<= x 1)) (not (<= x 1))) :rule or_neg :args (1))
(step t (cl (or (not (<= x 0)) (<= x 1)))
    :rule resolution :premises (t.c3 t.c4) :args ((<= x 1) true))
```

Five steps rather than the six of `la_totality`'s `or_intro`: resolution reads its premises as
sets, so the duplicate copy of the conclusion that `or_intro`'s generic expansion would leave
behind — and its closing `contraction` — never appears here.

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

#### The nonlinear multiplication pair

| rule | reduces to | growth | check power | status |
|---|---|---|---|---|
| `la_mult_pos` | `mult_pos` + `poly_simp` + `la_generic` glue (`eq_congruent` for the `=` form, one `la_disequality` case split for `≤`/`≥`) | O(1) template (~15–25 steps) | pos-cone + ring + Farkas | **done** (`core` pass, 2026-08-25). Promoted from *expensive* when the proposed axiom was adopted as `mult_pos`: the recipe validates every `la_generic` certificate and the `poly_simp` ring identity before emission, so an unanticipated shape keeps the step |
| `la_mult_neg` | same, prepending the `la_generic` sign bridge `(cl ¬(< m 0) (> (- m) 0))` and scaling by `(- m)` | O(1) template | ditto | **done** (`core` pass) |
| `div_simplify` | `poly_simp` (real division by a constant is a ring identity) or `evaluate` (the integer `div`/`mod` cases over constants) — a rename either way, chosen by trying the ring check first | 0 | ring / evaluation | **done** (`core` pass, 2026-08-25). Promoted from *expensive*: the objection was that its two cases take *different* primitives, which is a fact about the recipe, not a cost. All 94 corpus instances are already-folded rational constants, i.e. `poly_simp` renames |


<details id="ex-arith-simplify-bundle">
<summary>Example: <code>prod_simplify</code>, <code>sum_simplify</code>, <code>minus_simplify</code>, <code>unary_minus_simplify</code>, <code>div_simplify</code></summary>

`prod_simplify`, `sum_simplify`, `minus_simplify` and `unary_minus_simplify` each fold a different
family of arithmetic identities, and every one of those identities is a ring identity — which is
precisely `poly_simp`'s check. So all four are renames:

```
(step a1 (cl (= (* 2 3 x) (* 6 x))) :rule prod_simplify)
(step a2 (cl (= (+ x 0 y) (+ x y)))  :rule sum_simplify)
(step a3 (cl (= (- x 0) x))          :rule minus_simplify)
(step a4 (cl (= (- (- x)) x))        :rule unary_minus_simplify)
```

become

```
(step a1 (cl (= (* 2 3 x) (* 6 x))) :rule poly_simp)
(step a2 (cl (= (+ x 0 y) (+ x y)))  :rule poly_simp)
(step a3 (cl (= (- x 0) x))          :rule poly_simp)
(step a4 (cl (= (- (- x)) x))        :rule poly_simp)
```

`div_simplify` is the same rename whenever the identity is a ring one. All 94 corpus instances are
already-folded rational constants, where it is trivially so:

```
(step d (cl (= (/ 3.0 2.0) 1.5)) :rule div_simplify)   ->   (step d (cl (= 3/2 3/2)) :rule poly_simp)
```

The exception is the integer `div`/`mod` cases. Euclidean division is not a ring operation, so
`poly_simp`'s normalization cannot express the identity at all; on constants it is a plain
evaluation, and the rename goes to the other computational primitive:

```
(step d (cl (= (div 7 2) 3)) :rule div_simplify)   ->   (step d (cl (= (div 7 2) 3)) :rule evaluate)
```

The pass picks between the two by *trying* the ring check first and falling back — the objection
that once put `div_simplify` in *expensive* was that its cases need different primitives, which is
a fact about the recipe's shape, not a cost. A non-constant integer instance such as
`(= (div x 1) x)` satisfies neither check and the step is kept unchanged; nothing in the corpus
produces one. Under `core-taut`, where `evaluate` is itself reduced, the second case routes
through the evaluation recipe instead of the rename (see
[Rewrite recipes](./rewrite-recipes.md)).

</details>

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
    :rule mult_pos)
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

### Expensive (1)

| rule | reduces to | steps | check | status / notes |
|---|---|---|---|---|
| `poly_simp` (extra) | two Farkas bounds closed by `la_disequality`: `t ≤ u`, `u ≤ t`, the antisymmetry axiom, its `or_pos` unpacking and two resolutions | 6 | Farkas | **done** (`core-expensive` pass), for the *linear* identities — which is every instance the corpus contains, since the multipliers solvers emit are numerals. A genuinely nonlinear identity (`(* x y) ≈ (* y x)`, a binomial expansion) has no core route and keeps the step; the reductions that used to need one now go through `mult_distrib` instead. Ring normalization is 12 µs a step, 11% of cvc5's elaborated checking time for 0.56% of its steps, and its own elimination into `rare_rewrite` chains is the exponential case documented in the parent chapter — so the rule earns its tier on cost from both directions |

### Rare/simplify (1)

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
the long-term recommendation stays *removal*: solvers should stop emitting them, or the
specification should replace them with principled counterparts. Meanwhile four of the five have
implemented reductions and count as *reducible*; only `lia_generic` is *oracle*.

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
| `mult_pos` | arithmetic | core axiom (**implemented**, 2026-08-25; proposed as `la_mult_pos_pos`) | the positive cone's closure under multiplication, as the premise-free clause `▷ ¬(> x 0), ¬(> y 0), (> (* x y) 0)` — `la_disequality`'s style rather than an implication term, so it resolves directly against the recipes' bridges. Base of the `la_mult_*` reductions; genuinely nonlinear, hence underivable from `la_generic` |
| `ite_then_intro`, `ite_else_intro` | equality & rewriting | proposed core axioms (**implemented**) | the term-`ite` selection pair, `▷ ¬c, (ite c t s) ≈ t` and `▷ c, (ite c t s) ≈ s`: premise-free clauses in `la_disequality`'s style, the definitional characterization of `ite` at arbitrary sorts (no other core rule provides one — `ite_pos/neg` are formula-level). Required by the `core-taut` regime's recipes for the term-`ite` RARE rules and by `evaluate`'s `ite` case; see "The trusted computing base, measured" in the parent chapter |
| `la_mult_sign` (`alethe-toolkit` branch) | arithmetic | expensive | O(n) fold of `mult_pos` + `poly_simp` + `la_generic` |
| `to_int_lower`, `to_int_upper` | arithmetic | proposed core axioms (**implemented**) | the floor characterization of `to_int`, as the pair `▷ (to_real (to_int t)) ≤ t` and `▷ t < (to_real (to_int t)) + 1`. They pin `to_int t` to the unique integer in `(t − 1, t]`, which is what lets the core evaluate a ground `to_int` without an evaluator: `la_generic`'s (correctly gated) integer strengthening turns each bound into the corresponding bound on the value, and `la_disequality` closes the two into an equality. Required to bring the `core-taut` regime's `evaluate` residue to zero; see the parent chapter |
| `div_intro`, `log2_intro`, `to_int_intro` (`alethe-toolkit` branch) | arithmetic | core (definitional) | characterization axioms of interpreted operators (division bound pair, `pow2` bounds, floor bounds) — the natural home for an `abs_intro`, which would make the `abs` RARE rule a lemma. The `to_int` half is the `to_int_lower`/`to_int_upper` pair above |
| `la_mult_abs_comparison` (`alethe-toolkit` branch) | arithmetic | blocked | reducible to the same base once an `abs` definitional rewrite exists |
| `evaluate` | equality & rewriting | **core** (computational) | constant evaluation of interpreted operators — a computational primitive on the same footing as `aci_simp` and `poly_simp`: the check *is* the (terminating, deterministic) evaluation function, and no rule-based reduction could be cheaper than re-evaluating |
| `mod_simplify`, `all_simplify` | equality & rewriting | rewrite tier | `all_simplify` already oracle-reducible via the hole pass |
| strings, PB, cutting-planes, arrays, DRUP, `sat_refutation` | theory extensions | out of scope | `sat_refutation` oracle-reducible via its dedicated pass |

### Outside this classification's scope

Carcara checks 181 rule names; this classification analyses the 120 specification rules plus the
extras above. The remainder are named here so that the gap is explicit rather than accidental —
they are rules that **only cvc5 produces**, and only in theories the evaluation does not
cover:

| rules | what they are | status |
|---|---|---|
| `bitblast_ashr`, `bitblast_comp`, `bitblast_const`, `bitblast_lshr`, `bitblast_shl`, `bitblast_udiv`, `bitblast_urem`, `bitblast_var` | eight bitblasting schemas Carcara checks beyond the specification's 14 | unclassified; presumably core alongside the other `bitblast_*` (same definitional character), but not analysed |
| `bitblast_equal`, `bitblast_sign_extend` | cvc5's names for the specification's `bitblast_eq` and `bitblast_sext` | naming divergence worth raising with the spec, not a semantic gap |
| 20 string rules (`concat_*`, `re_*`, `string_*`), 15 `pbblast_*`, 6 `cp_*`, 4 `arrays_*`, `drat`/`drup` | the theory-extension families of the row above | covered *collectively* as out of scope; no rule-by-rule reduction scheme is recorded |
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
