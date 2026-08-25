# Can `aci_simp` and `poly_simp` be combined algebraically?

*2026-08-25*

The question was whether the two computational-primitive rules of the reducible target could be
unified hierarchically, by the algebraic structures they normalize in — groups, rings, and so on.
They can be *organized* that way, and doing so is worthwhile, but they should not be *merged*.
Working the hierarchy out also exposed a soundness bug in `aci_simp`, which this note records and
which the accompanying commit fixes.

## What each rule actually normalizes

`aci_simp` (`carcara/src/checker/rules/simplification.rs`) picks the top-level operator of each
side, flattens nested applications of *that same* operator, drops duplicate arguments, drops the
operator's unit, and compares the two resulting argument lists as multisets. Everything that is not
an application of the top operator — including a nested application of a *different* operator — is
an opaque atom. So it works in a single-operator structure: the free algebra on the atoms, quotiented
by associativity, commutativity, idempotence and the unit law.

`poly_simp` (`carcara/src/checker/rules/polynomial.rs`) builds a `Polynomial`: an `IndexMap` from
`Monomial` (a pointer-sorted multiset of atoms) to a `Rational` coefficient, plus a constant term.
`add_term` recurses through `+`, `-`, unary minus, `*`, `to_real`, division by a nonzero constant,
and their bitvector counterparts; `mul` distributes. For a bitvector sort the coefficients are then
reduced mod 2^w. So it works in a commutative ring — two interacting operations, additive inverses,
distributivity, and a quotient.

That is already the hierarchy:

| level | laws | operators | rule |
|---|---|---|---|
| semigroup | A | `concat` | `aci_simp` (comparison by equality, not multiset) |
| commutative monoid | A, C, unit | — | the shared floor of both rules |
| bounded semilattice | + idempotence | `and`, `or`, `bvand`, `bvor` | `aci_simp` |
| abelian group, exponent 2 | + self-inverse | `bvxor` | `aci_simp` (partially) |
| commutative ring | + distributivity, inverses | `+`, `*`, `bvadd`, `bvmul` | `poly_simp` |
| ℤ/2^w | + quotient | the bitvector ring ops | `poly_simp` |

The two rules meet at the commutative-monoid level and diverge above it in *different directions*.
Neither subsumes the other.

## The bug: idempotence was applied at the monoid level

`is_assoc` listed `and`, `or`, `+`, `*`, `bvadd`, `bvor`, `bvmul`, `bvand`, `bvxor`, `concat`, and
`apply_aci_simp` applied the same normalization — including a set-based `dedup()` of the argument
list — to all of them. But idempotence is a *semilattice* law, not a monoid law. Verified against
the checker before the fix, every one of these was **accepted**:

```
(step t1 (cl (= (+ i i) i))     :rule aci_simp)   ; (+ i i) is 2i
(step t1 (cl (= (* x x) x))     :rule aci_simp)   ; (* x x) is x²
(step t1 (cl (= (* x x x) x))   :rule aci_simp)
(step t1 (cl (= (+ i i j) (+ i j))) :rule aci_simp)
(step t1 (cl (= (bvadd a a) a)) :rule aci_simp)
(step t1 (cl (= (bvmul a a) a)) :rule aci_simp)
(step t1 (cl (= (bvxor a a) a)) :rule aci_simp)   ; (bvxor a a) is zero
```

`concat` escapes only by accident: it is excluded from the multiset comparison, and the ill-sorted
equality its dedup would justify (`(= (concat a a) a)`, 8 bits against 4) is rejected by the parser's
sort check rather than by the rule.

`ac_simp` is not affected — its `apply_ac_simp` matches only `And | Or`.

### The fix

A new `is_idempotent(op)` gates the `dedup()`, admitting only `and`, `or`, `bvand`, `bvor`. The
other operators keep associativity, commutativity and unit removal, which are sound for them. The
doc comment states the hierarchy so the split is not silently reintroduced. Regression test:
`aci_simp_idempotence_is_only_for_semilattices` in `carcara/tests/rules/simplification.rs`.

The whole test suite passes, and the elaborated corpus re-checks clean, which is expected: of the
**1 353 734** `aci_simp` steps Carcara emits across the corpus, **zero** are headed by an arithmetic
or bitvector operator. The unsoundness was reachable only by a hand-written or adversarial proof.

## Containment: `poly_simp` already covers the ring half

Test `poly_simp_subsumes_aci_simp_on_ring_operators` checks this directly. Every arithmetic and
bitvector-ring case in the existing `aci_simp` test — flattening, commutativity, unit removal, for
`+`, `*`, `bvadd`, `bvmul` — is accepted by `poly_simp`. All four of the unsound idempotence cases
are rejected by it. And `poly_simp` reaches strictly further: it sees through `-`, `to_real` and
constant division, it recurses through *mixed* operators where `aci_simp` stops at the first change
of operator, and it distributes.

The converse fails: `poly_simp` rejects `(= (bvor a #b0000) a)`, `(= (bvand a #b1111) a)` and
`(= (bvxor a b c) (bvxor c b a))`, since those operators are atoms to it.

So `{+, *, bvadd, bvmul}` could be dropped from `aci_simp` outright with no loss of proving power
and a small reduction in the trusted computing base. That is a tier decision, not made here.

## Why not merge them into one rule

Three reasons, in increasing order of weight.

1. **A merged rule is not a simpler checker.** Any unified `alg_simp` would have to recover the law
   set from the operator before it could normalize, which is the operator match the two rules
   already are. The merge moves a dispatch entry; it does not remove code, so it does not shrink the
   TCB number in `docs/src/core.md`.

2. **Cost.** `aci_simp` is on the hot path: it is the target of the `and_simplify`/`or_simplify`
   renames and accounts for 1.35M steps of the elaborated corpus. Its Boolean path is a flatten, a
   set dedup and a multiset compare. The polynomial path allocates a `Monomial` per term, hashes
   vectors of pointers, and does `Rational` arithmetic. Routing the Boolean traffic through it would
   be a large regression on the most common rewrite in the corpus.

3. **The embedding is exponential — this is the decisive one.** Putting `and`/`or` into the ring
   engine means the Boolean-ring (Zhegalkin / algebraic normal form) encoding over 𝔽₂: `x ∧ y = xy`,
   `x ⊕ y = x + y`, `¬x = 1 + x`, and therefore

   ```
   x₁ ∨ … ∨ xₙ  =  1 + (1 + x₁)(1 + x₂) ⋯ (1 + xₙ)
   ```

   which expands to 2ⁿ monomials. `Polynomial::mul` is a double loop over monomial maps, so it would
   genuinely build them. A rule that is linear in the term size today would become exponential in the
   arity of a disjunction — on a corpus where wide `or`s are exactly what `aci_simp` is used for.
   The gain would be a *complete* decision procedure for the propositional fragment, which is far
   more than the coarse check the core wants, and much more than it should pay for.

The semilattice level is not a degenerate case of the ring level; it is a quotient that the ring
cannot represent compactly. That is the real content of the hierarchy, and it is an argument for
keeping the two rules apart.

## What the hierarchy is good for

- **Correctness.** It is what makes the bug above obvious, and `is_idempotent` is the hierarchy
  written down in the checker.
- **A cheap capability gain, if wanted.** `bvxor` sits at the exponent-2 abelian group level: its
  law is self-inversion, `x ⊕ x = 0`, i.e. keep each argument's occurrence count mod 2 instead of
  deduplicating. That is a few lines in the same normalizer and would let `aci_simp` prove
  `(= (bvxor a b a) b)`. Not implemented here, since it widens the rule's specification.
- **Documentation.** The classification chapter can present `aci_simp` and `poly_simp` as one
  parameterized primitive — normalize in the structure the operator generates — with the operator
  table above as the parameter, rather than as two unrelated rules that happen to both be reducible
  targets.
