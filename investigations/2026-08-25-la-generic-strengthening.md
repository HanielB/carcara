# `la_generic` applied integer strengthening to real rows

*2026-08-25*

Found while working out what the core needs in order to eliminate the last `rare_rewrite` steps:
the residue is integer-rounding rewrites, so the first question was whether `la_generic` already
knows how to round. It does — and it was rounding rows that are not over the integers.

## The bug

`la_generic` checks a Farkas certificate: negate every literal, scale each by its coefficient, add
them up, and require the sum to be contradictory. Between the negation and the scaling it applies
the *strengthening rules*, which sharpen a bound on an integer quantity: `Σ ≥ d` becomes
`Σ ≥ ⌈d⌉`, and `Σ > d` becomes `Σ ≥ ⌊d⌋ + g` for the gcd `g` of the coefficients.

`strengthen` decided whether a row was "over the integers" from the *constant* alone:

```rust
let is_integer = if *a == 0 { true }
    else if *a == 1 { disequality.1.is_integer() }
    else { (disequality.1.clone() * a).is_integer() };
```

Nothing looked at the sorts of the atoms. So a row over a real variable whose constant happened to
be an integer was strengthened too, and

```
(step t1 (cl (not (>= x 0.5)) (>= x 1.0)) :rule la_generic :args (1 1))
```

was **accepted** for a real `x`. It is false at `x = 0.7`. Negating the two literals gives `x ≥ 0.5`
and `x < 1`; the second flips to `-x > -1`, whose constant `-1` is an integer, so it was strengthened
to `-x ≥ 0`, and `x ≥ 0.5` plus `-x ≥ 0` sums to the contradiction `0 ≥ 0.5`.

The same reasoning also mis-fires on an integer atom with a rational coefficient: `n/2 > 1` gives
`n ≥ 3`, i.e. `n/2 ≥ 3/2`, not the `n/2 ≥ 2` the rule derived.

## The fix

A row may be strengthened only when its value is an integer under every valuation, which needs both
halves: every atom integer-sorted *and* every coefficient an integer.

```rust
fn is_integer_valued(&self, pool: &mut dyn TermPool) -> bool {
    self.0.iter().all(|(atom, coeff)| {
        coeff.is_integer() && matches!(pool.sort(atom).as_sort(), Some(Sort::Int))
    })
}
```

`LinearComb::add_term` already treats `to_real` as transparent, so `(to_real n)` is recognized as
the integer atom `n` — which matters, because that is exactly the shape cvc5 emits around
`poly_simp_rel` and in the integer-tightening rewrites. Deciding integrality *after* that
normalization is what keeps the real cases and the tightening cases apart.

Threading the sorts in required a pool, so `la_generic_partial` now takes one; its four callers all
had one to hand.

## A second bug the fix exposed

With the strengthening gone from real rows, `(cl (> a 0.0) (<= a 0.0))` — a genuine tautology —
started failing. The accumulated operator was computed as

```rust
let new_op = match (acc_op, op) {
    (_, Operator::GreaterEq) => Operator::GreaterEq,
    (Operator::Equals, Operator::GreaterThan) => Operator::GreaterThan,
    _ => acc_op,
};
```

which loses strictness: combining `-a ≥ 0` with `a > 0` gave `0 ≥ 0` (satisfiable) instead of
`0 > 0` (contradictory). It had been masked because strengthening turned every `>` into a `≥`
before the combination ever saw one. Adding two relations gives the weaker of the two and a strict
row makes the sum strict, so:

```rust
let new_op = match (acc_op, op) {
    (Operator::GreaterThan, _) | (_, Operator::GreaterThan) => Operator::GreaterThan,
    (Operator::GreaterEq, _) | (_, Operator::GreaterEq) => Operator::GreaterEq,
    _ => acc_op,
};
```

## Validation

Regression test `la_generic_strengthening_is_integer_only` covers both directions: the tightening
that *is* valid over the integers (including through `to_real`), the same shapes over the reals, the
rational-coefficient case, and the strictness propagation.

The whole suite passes, and the elaborated corpus re-checks at **3 299 / 3 299**, so nothing in it
depended on the unsound strengthening.

## Why it matters here

`la_generic` is the arithmetic trust anchor of the core fragment: `poly_simp` is the ring primitive,
and everything else in the arithmetic category reduces onto one of the two. A checker that rounds
real bounds would let the core "prove" false arithmetic clauses, and the reduction recipes —
`atom_equiv`, `la_clause`, the `bounded_farkas` elaboration — all validate their certificates by
calling this function, so they would have inherited it.

The upside is that the *correct* strengthening turns out to be strong enough to do the work the
integer-rounding rewrites needed, with no new axiom: see
[the rewrite-vocabulary note](./2026-08-25-rare-rewrite-to-zero.md).
