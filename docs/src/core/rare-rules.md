# RARE rules for the rewrite routes

Several reduction schemes in the [classification](./classification.md) go through `rare_rewrite`:
the Boolean `*_simplify` bundles, the RARE alternative for the arithmetic simplifications, and
the optional elaboration of `poly_simp` itself. This chapter catalogues the RARE 2.0 rules those routes require, in Carcara's
`declare-rare-rule` syntax (the concrete implementation of RARE 2.0's `declare-rule`; see the
[Checking Rare rewrites](../checking/rare.md) chapter). The rewrite sets are taken from the
fixpoint systems the Alethe specification gives for each `*_simplify` rule.

Conventions used below:

- Parameters marked `:list` match (possibly empty) argument sublists of an n-ary operator, so one
  rule expresses "remove one occurrence anywhere"; the fixpoint iterates it.
- `(@T Type)` declares a polymorphic sort parameter (not passed in `:args`).
- Rules whose right-hand side must be *computed* (constant folding) use Eunoia's computational
  operators (`eo::add`, `eo::mul`, ...) and apply only when the matched parameters are literal
  values; they are marked **[eval]**. This is the one place the route leans on Eunoia beyond
  pattern matching.

Where a rule coincides with an existing rule of cvc5's RARE database, an implementation should
reuse the established name rather than the systematic names used here.

## Boolean connectives

### `not_simplify`

```lisp
(declare-rare-rule not-not-elim ((phi Bool))
  :args (phi)
  :conclusion (= (not (not phi)) phi))
(declare-rare-rule not-false ()
  :conclusion (= (not false) true))
(declare-rare-rule not-true ()
  :conclusion (= (not true) false))
```

### `and_simplify` / `or_simplify`

The two bundles are dual; only the `and` rules are shown, the `or` versions swap
`and`/`or` and `true`/`false`. The spec's parity-of-negations contradiction case
(`φ_i = ¬ⁿψ`, `φ_j = ¬ᵐψ`, opposite parity) is handled by normalizing with `not-not-elim`
first, so only the base `φ`/`¬φ` clash needs a rule.

```lisp
(declare-rare-rule and-true-elim ((xs Bool :list) (ys Bool :list))
  :args (xs ys)
  :conclusion (= (and xs true ys) (and xs ys)))
(declare-rare-rule and-dup-elim ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list))
  :args (xs b ys zs)
  :conclusion (= (and xs b ys b zs) (and xs b ys zs)))
(declare-rare-rule and-false ((xs Bool :list) (ys Bool :list))
  :args (xs ys)
  :conclusion (= (and xs false ys) false))
(declare-rare-rule and-contra ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list))
  :args (xs b ys zs)
  :conclusion (= (and xs b ys (not b) zs) false))
(declare-rare-rule and-contra-flip ((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list))
  :args (xs b ys zs)
  :conclusion (= (and xs (not b) ys b zs) false))
```

The `(and ⊤ ... ⊤) ⇒ ⊤` case falls out of iterating `and-true-elim` down to the unit
application, relying on the list semantics collapsing `(and x)` to `x` (and the empty
application to the neutral element). If the implementation's list semantics do not provide
that, two explicit unit rules are needed per operator.

### `implies_simplify`

```lisp
(declare-rare-rule implies-contra ((p Bool) (q Bool))
  :args (p q)
  :conclusion (= (=> (not p) (not q)) (=> q p)))
(declare-rare-rule implies-false-l ((p Bool))
  :args (p)
  :conclusion (= (=> false p) true))
(declare-rare-rule implies-true-r ((p Bool))
  :args (p)
  :conclusion (= (=> p true) true))
(declare-rare-rule implies-true-l ((p Bool))
  :args (p)
  :conclusion (= (=> true p) p))
(declare-rare-rule implies-false-r ((p Bool))
  :args (p)
  :conclusion (= (=> p false) (not p)))
(declare-rare-rule implies-refl ((p Bool))
  :args (p)
  :conclusion (= (=> p p) true))
(declare-rare-rule implies-neg-l ((p Bool))
  :args (p)
  :conclusion (= (=> (not p) p) p))
(declare-rare-rule implies-neg-r ((p Bool))
  :args (p)
  :conclusion (= (=> p (not p)) (not p)))
```

### `equiv_simplify`

```lisp
(declare-rare-rule equiv-neg-both ((p Bool) (q Bool))
  :args (p q)
  :conclusion (= (= (not p) (not q)) (= p q)))
(declare-rare-rule equiv-refl ((p Bool))
  :args (p)
  :conclusion (= (= p p) true))
(declare-rare-rule equiv-neg-r ((p Bool))
  :args (p)
  :conclusion (= (= p (not p)) false))
(declare-rare-rule equiv-neg-l ((p Bool))
  :args (p)
  :conclusion (= (= (not p) p) false))
(declare-rare-rule equiv-true-l ((p Bool))
  :args (p)
  :conclusion (= (= true p) p))
(declare-rare-rule equiv-true-r ((p Bool))
  :args (p)
  :conclusion (= (= p true) p))
(declare-rare-rule equiv-false-l ((p Bool))
  :args (p)
  :conclusion (= (= false p) (not p)))
(declare-rare-rule equiv-false-r ((p Bool))
  :args (p)
  :conclusion (= (= p false) (not p)))
```

### `bool_simplify`

```lisp
(declare-rare-rule bool-implies-de-morgan ((p Bool) (q Bool))
  :args (p q)
  :conclusion (= (not (=> p q)) (and p (not q))))
(declare-rare-rule bool-or-de-morgan ((p Bool) (q Bool))
  :args (p q)
  :conclusion (= (not (or p q)) (and (not p) (not q))))
(declare-rare-rule bool-and-de-morgan ((p Bool) (q Bool))
  :args (p q)
  :conclusion (= (not (and p q)) (or (not p) (not q))))
(declare-rare-rule bool-implies-uncurry ((p Bool) (q Bool) (r Bool))
  :args (p q r)
  :conclusion (= (=> p (=> q r)) (=> (and p q) r)))
(declare-rare-rule bool-implies-peirce ((p Bool) (q Bool))
  :args (p q)
  :conclusion (= (=> (=> p q) q) (or p q)))
(declare-rare-rule bool-and-mp-r ((p Bool) (q Bool))
  :args (p q)
  :conclusion (= (and p (=> p q)) (and p q)))
(declare-rare-rule bool-and-mp-l ((p Bool) (q Bool))
  :args (p q)
  :conclusion (= (and (=> p q) p) (and p q)))
```

### `ite_simplify`

The specification notes this rule set is **not confluent** — the elaboration must replay the
checker's actual application order, not re-search it.

```lisp
(declare-rare-rule ite-true-cond ((@T Type) (t @T) (s @T))
  :args (t s)
  :conclusion (= (ite true t s) t))
(declare-rare-rule ite-false-cond ((@T Type) (t @T) (s @T))
  :args (t s)
  :conclusion (= (ite false t s) s))
(declare-rare-rule ite-same-branches ((@T Type) (c Bool) (t @T))
  :args (c t)
  :conclusion (= (ite c t t) t))
(declare-rare-rule ite-not-cond ((@T Type) (c Bool) (t @T) (s @T))
  :args (c t s)
  :conclusion (= (ite (not c) t s) (ite c s t)))
(declare-rare-rule ite-nested-then ((@T Type) (c Bool) (t1 @T) (t2 @T) (t3 @T))
  :args (c t1 t2 t3)
  :conclusion (= (ite c (ite c t1 t2) t3) (ite c t1 t3)))
(declare-rare-rule ite-nested-else ((@T Type) (c Bool) (t1 @T) (t2 @T) (t3 @T))
  :args (c t1 t2 t3)
  :conclusion (= (ite c t1 (ite c t2 t3)) (ite c t1 t3)))
(declare-rare-rule ite-then-true-else-false ((c Bool))
  :args (c)
  :conclusion (= (ite c true false) c))
(declare-rare-rule ite-then-false-else-true ((c Bool))
  :args (c)
  :conclusion (= (ite c false true) (not c)))
(declare-rare-rule ite-then-true ((c Bool) (p Bool))
  :args (c p)
  :conclusion (= (ite c true p) (or c p)))
(declare-rare-rule ite-else-false ((c Bool) (p Bool))
  :args (c p)
  :conclusion (= (ite c p false) (and c p)))
(declare-rare-rule ite-then-false ((c Bool) (p Bool))
  :args (c p)
  :conclusion (= (ite c false p) (and (not c) p)))
(declare-rare-rule ite-else-true ((c Bool) (p Bool))
  :args (c p)
  :conclusion (= (ite c p true) (or (not c) p)))
```

### `eq_simplify`

```lisp
(declare-rare-rule eq-refl ((@T Type) (t @T))
  :args (t)
  :conclusion (= (= t t) true))
(declare-rare-rule eq-const-diff ((@T Type) (c1 @T) (c2 @T))   ; [eval]
  :args (c1 c2)
  :conclusion (= (= c1 c2) false))
```

`eq-const-diff` applies only when `c1`, `c2` are distinct numeric literals — a value-disequality
test on the matched parameters (Eunoia: guard with `eo::is_eq`/negation over values). The spec's
third case, `¬(t ≈ t) ⇒ ⊥` for a numeric constant `t`, is derivable from `eq-refl` +
`not-true` and needs no rule of its own.

## Arithmetic

### Elementary ring rules (the `poly_simp` elaboration and `prod`/`sum`/`minus`/`unary_minus_simplify`)

The rewrite route for the ring normalization: unfold subtraction and negation, distribute,
reassociate and commute into a canonical monomial order, and fold constants. Shown for `Int`;
the `Real` (and, with modulo, bitvector) versions are identical modulo the sort.

```lisp
(declare-rare-rule arith-neg-unfold ((x Int))
  :args (x)
  :conclusion (= (- x) (* (- 1) x)))
(declare-rare-rule arith-sub-unfold ((x Int) (y Int))
  :args (x y)
  :conclusion (= (- x y) (+ x (* (- 1) y))))
(declare-rare-rule arith-distrib ((x Int) (y Int) (z Int))
  :args (x y z)
  :conclusion (= (* x (+ y z)) (+ (* x y) (* x z))))
(declare-rare-rule arith-add-comm ((xs Int :list) (x Int) (y Int) (ys Int :list))
  :args (xs x y ys)
  :conclusion (= (+ xs x y ys) (+ xs y x ys)))
(declare-rare-rule arith-mul-comm ((xs Int :list) (x Int) (y Int) (ys Int :list))
  :args (xs x y ys)
  :conclusion (= (* xs x y ys) (* xs y x ys)))
(declare-rare-rule arith-add-flatten ((xs Int :list) (ys Int :list) (zs Int :list))
  :args (xs ys zs)
  :conclusion (= (+ xs (+ ys) zs) (+ xs ys zs)))
(declare-rare-rule arith-mul-flatten ((xs Int :list) (ys Int :list) (zs Int :list))
  :args (xs ys zs)
  :conclusion (= (* xs (* ys) zs) (* xs ys zs)))
(declare-rare-rule arith-add-zero ((xs Int :list) (ys Int :list))
  :args (xs ys)
  :conclusion (= (+ xs 0 ys) (+ xs ys)))
(declare-rare-rule arith-mul-one ((xs Int :list) (ys Int :list))
  :args (xs ys)
  :conclusion (= (* xs 1 ys) (* xs ys)))
(declare-rare-rule arith-mul-zero ((xs Int :list) (ys Int :list))
  :args (xs ys)
  :conclusion (= (* xs 0 ys) 0))
(declare-rare-rule arith-fold-add ((c1 Int) (c2 Int))          ; [eval]
  :args (c1 c2)
  :conclusion (= (+ c1 c2) (eo::add c1 c2)))
(declare-rare-rule arith-fold-mul ((c1 Int) (c2 Int))          ; [eval]
  :args (c1 c2)
  :conclusion (= (* c1 c2) (eo::mul c1 c2)))
(declare-rare-rule arith-fold-neg ((c Int))                    ; [eval]
  :args (c)
  :conclusion (= (- c) (eo::neg c)))
(declare-rare-rule arith-collect ((xs Int :list) (c1 Int) (c2 Int) (m Int) (ys Int :list)) ; [eval]
  :args (xs c1 c2 m ys)
  :conclusion (= (+ xs (* c1 m) (* c2 m) ys) (+ xs (* (eo::add c1 c2) m) ys)))
```

These rules cover, as special cases, the entire `prod_simplify`, `sum_simplify`,
`minus_simplify`, and `unary_minus_simplify` bundles (their "fold the constants out of the
n-ary application" steps are iterations of the `-comm` and `-fold-` rules). They are also
exactly the vocabulary the `poly_simp` elaboration replays: both sides of a `poly_simp` step
rewrite to the shared normal form, and the two chains meet through `trans`/`symm`. The
worst-case exponential growth noted in the parent chapter shows up as the length of the
`arith-distrib` cascade.

### `div_simplify`, `comp_simplify`

```lisp
(declare-rare-rule div-same ((t Real))
  :args (t)
  :conclusion (= (/ t t) 1))          ; guard: t not a zero literal, per theory semantics
(declare-rare-rule div-one ((t Real))
  :args (t)
  :conclusion (= (/ t 1) t))
(declare-rare-rule div-fold ((c1 Real) (c2 Real))              ; [eval]
  :args (c1 c2)
  :conclusion (= (/ c1 c2) (eo::qdiv c1 c2)))
```

Integer `div`/`mod` folding needs the corresponding integer evaluation operators — this is the
"integer division semantics" blocker in the classification.

```lisp
(declare-rare-rule comp-lt-fold ((c1 Int) (c2 Int))            ; [eval]
  :args (c1 c2)
  :conclusion (= (< c1 c2) (eo::is_neg (eo::add c1 (eo::neg c2)))))
(declare-rare-rule comp-lt-irrefl ((s Int))
  :args (s)
  :conclusion (= (< s s) false))
(declare-rare-rule comp-leq-refl ((s Int))
  :args (s)
  :conclusion (= (<= s s) true))
(declare-rare-rule comp-geq-flip ((s1 Int) (s2 Int))
  :args (s1 s2)
  :conclusion (= (>= s1 s2) (<= s2 s1)))
(declare-rare-rule comp-lt-elim ((s1 Int) (s2 Int))
  :args (s1 s2)
  :conclusion (= (< s1 s2) (not (<= s2 s1))))
(declare-rare-rule comp-gt-elim ((s1 Int) (s2 Int))
  :args (s1 s2)
  :conclusion (= (> s1 s2) (not (<= s1 s2))))
```

Like `ite_simplify`, this set is order-sensitive (the folding rules overlap with `comp-lt-elim`);
the elaboration replays the checker's order.

### Single-schema rules

```lisp
(declare-rare-rule la-rw-eq ((t Int) (u Int))
  :args (t u)
  :conclusion (= (= t u) (and (<= t u) (<= u t))))
(declare-rare-rule abs-def ((t Int))
  :args (t)
  :conclusion (= (abs t) (ite (>= t 0) t (- t))))
```

`la-rw-eq` can discharge the `la_rw_eq` rule in one `rare_rewrite` step, though with
`la_disequality` in the core the preferred reduction derives it instead (see the
classification's arithmetic section) and the RARE rule is a lemma; `abs-def` is the prerequisite the
`la_mult_abs_comparison` scheme names. Note that the proposed `la_mult_pos_pos` axiom is *not* a
RARE rule: its conclusion is an implication, not an equality, so it stays a proper Alethe rule.

## ACI and n-ary structure

For the `aci_simp` expansion scheme, the `ac_simp` decomposition, and `nary_elim` (shown for a
generic ACI operator `op` — instantiated per operator of `aci_simp`'s list):

```lisp
(declare-rare-rule op-flatten ((xs S :list) (ys S :list) (zs S :list))
  :args (xs ys zs)
  :conclusion (= (op xs (op ys) zs) (op xs ys zs)))
(declare-rare-rule op-comm ((xs S :list) (x S) (y S) (ys S :list))
  :args (xs x y ys)
  :conclusion (= (op xs x y ys) (op xs y x ys)))
(declare-rare-rule op-identity ((xs S :list) (ys S :list))
  :args (xs ys)
  :conclusion (= (op xs id ys) (op xs ys)))
(declare-rare-rule op-idem ((xs S :list) (x S) (ys S :list) (zs S :list))   ; ACI operators only
  :args (xs x ys zs)
  :conclusion (= (op xs x ys x zs) (op xs x ys zs)))
(declare-rare-rule op-unfold-binary ((x S) (ys S :list))                    ; nary_elim direction
  :args (x ys)
  :conclusion (= (op x ys) (op x (op ys))))
```

Since the specification itself notes there is no canonical ACI normal form, an `aci_simp`
expansion must replay a *particular* normalization order; `op-comm` applications encode the
chosen adjacent transpositions (the O(n²) bound of the classification).

## Lemmas, not axioms

A natural question: are these RARE rules *axioms* (trust extensions) or *lemmas* (derivable from
the core)? For the rules catalogued here — i.e., exactly the rewrites the reduction routes need —
the answer is: **all lemmas** — granted one deliberate choice in the core itself, keeping
`la_disequality` as the order-antisymmetry axiom [antisym].

- **Boolean rules, ACI/n-ary rules for `∧`/`∨`, `eq-refl`**: each instance is a propositional
  equivalence; both implications fall to resolution over the CNF axioms (the Tseitin defining
  clauses, so propositional completeness applies), closed by `equiv_intro`.
- **Ring rules**: each instance is a polynomial identity — literally one `poly_simp` step. This
  is the exact converse of the `poly_simp`-into-RARE trust-reduction; the two directions are
  interderivable, as a trust anchor should be.
- **Comparison rules and constant folds, `eq-const-diff`**: Farkas consequences — `la_generic` +
  `equiv_intro`. The `div` rules follow from the toolkit's `div_intro` characterization (below)
  plus `la_generic` for the constant cases.
- **ACI instances for the bitvector operators** (`bvand`, `bvadd`, …, at *symbolic* arguments):
  derivable by bitblasting both sides — the `bitblast_*` rules apply to arbitrary terms (their
  right-hand sides use `bitOf i x` on symbolic `x`), so e.g. `bvand a b ≈ bvand b a` follows from
  two `bitblast_and` steps, per-bit propositional commutativity (clausal core), `cong` over
  `bbterm`, and `trans`/`symm`. O(width) core steps.
- **`abs-def`**: derivable once `abs` has a *characterization axiom* in the `alethe-toolkit`
  branch's `*_intro` family — the established home for definitional axioms of interpreted
  operators (`div_intro`: the division bound pair; `log2_intro`; `to_int_intro`). An `abs_intro`
  in that style yields `abs-def` by a case split + the `ite` axioms + `equiv_intro`.
- **`la-rw-eq` — a lemma via the core's [antisym] axiom.** Its → direction is Farkas-derivable,
  but the ← direction —
  `t ≤ u ∧ u ≤ t` entails `t ≈ u` — is *order antisymmetry*: refuting the negated conclusion (a
  disequality) against inequality premises needs **two** independent Farkas combinations, one per
  bound, which `la_generic`'s single coefficient vector cannot express. The
  [`la_generic` extension of spec issue #72](https://github.com/alethe-proofs/specification/issues/72)
  does not reach it either (two independent Carcara implementations agree: the issue's reference
  branch `la-generic-extension`, and the leaner one on `ext-phpp` reusing `Operator::Distinct`,
  which errors on any disequality × inequality combination): its combination lattice lets
  equations combine with anything, but a disequality combines only with equations — covering
  affine consequences (equality conclusions from equality premises), not antisymmetry. Nor do
  *two* `la_generic` steps help: they derive both bounds, but no core rule can then conjoin them
  into the equality literal — a positive arithmetic equality cannot appear in a `la_generic`
  conclusion (only negated ones can, since their negations are equations the combination can
  use), `refl`/`trans`/`cong`/`symm` need an equality to start from, and the `equiv` axioms are
  Boolean-sorted. The bounds-to-equality crossing is a genuine axiom (cf. cvc5's dedicated
  `ARITH_TRICHOTOMY` rule) — which is exactly why the classification keeps **`la_disequality` in
  the core** as [antisym]: with it, `la-rw-eq` derives in ~13 core steps (← from
  `la_disequality` + `and_pos` + resolution; → by two `la_generic` steps under a discharge
  subproof; `equiv_intro` closing — worked example in the classification), and the axiom lives
  in the core proper, where axioms belong, rather than in the rewrite database. RESOLUTE
  corroborates the architecture: its `farkas` certificate rule stays minimal and its
  `trichotomy` axiom — literally `la_disequality` modulo the `¬≤`/`<` atom flip — is the
  designated positive-equality introducer (see the parent chapter's comparison). The only way to
  make `la_disequality` itself derivable would be to generalize `la_generic` once more, and the
  generalization is well-defined: designate
  one disequality `L ≠ 0` and supply **two** coefficient vectors `u`, `v` over the remaining
  rows, checked by running the linear fold twice — `Σuᵢ·rowᵢ = L` and `Σvᵢ·rowᵢ = −L` — forcing
  `L = 0` against `L ≠ 0`. By convexity this is complete (a convex set inside a finite union of
  hyperplanes lies in one of them, so one designated disequality suffices), and both existing
  forms are degenerations: no equality literal ⇒ `v` absent (today's rule); the issue-72 /
  `ext-phpp` case ⇒ `v = −u` over equation rows. Antisymmetry itself is `u = [1,0]`,
  `v = [0,1]` on the two `≤` rows. Two folds instead of one — same checking class.

The consequence: for these routes, `rare_rewrite`'s effective trust contribution is its
substitution-matching machinery *only* — every catalogued rule is derivable from the core, whose
axioms (the CNF axioms, `la_disequality`, the `bitblast_*` and `*_intro` definitional schemas)
carry all of the trust. A general RARE database should be
partitioned the same way — *lemma rules* (shipped with a core derivation, checkable once) versus
*axiom rules* (genuine extensions) — with the system's trust base being the core plus the axiom
partition only.

## Summary

| route | rules needed | fully expressible in RARE 2.0 today? |
|---|---|---|
| `not/and/or/implies/equiv/bool/ite_simplify` | 43 rules above | yes (given `:list` semantics for unit/empty applications) |
| `eq_simplify` | 2 | yes, with one **[eval]** value-disequality guard |
| ring rules (`poly_simp` route, `prod/sum/minus/unary_minus_simplify`) | 14 per sort | yes, with **[eval]** constant folding |
| `div_simplify`, `comp_simplify` | 9 | mostly; integer `div`/`mod` folding needs more evaluation operators |
| `la_rw_eq` (alternative route), `abs` | 2 | yes; `la_rw_eq`'s preferred reduction now goes through the core's `la_disequality` instead |
| ACI / `nary_elim` | 5 per operator | yes; normalization order must be replayed, not searched |

The *other* regime — `rare_rewrite` out of the core entirely, every rewrite derived — is catalogued
in [Recipes for eliminating the RARE rewrites](./rewrite-recipes.md), which gives the core
derivation and its measured cost for each of the 53 rewrites the corpus exercises. A complementary
analysis lives in the parent chapter's ["The trusted computing base,
measured"](../core.md#the-trusted-computing-base-measured) section: if `rare_rewrite` itself is
removed from the core over a *frozen* rule set, every rewrite above and every non-BV/array rule
of cvc5's `rewrites.eo` needs a recipe in core terms instead of a RARE declaration. The
lemma/axiom partition of this chapter survives that regime intact — the same rules stay lemmas,
with the recipes materializing the derivations this chapter only argues exist — and the axiom
partition acquires precise membership: the term-`ite` selection pair, `distinct_elim` as a
definitional schema, the `*_intro` family with the division-by-zero fixings, and
`la_mult_pos_pos`.
