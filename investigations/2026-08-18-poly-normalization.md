# Global normalization of arithmetic atoms: a negative result

**Branch:** `inv/poly-normalization` (commit `9aed0a76`, analysis tooling only).
**Verdict:** **not viable.** Normalizing arithmetic atoms proof-wide, so that the two sides of
every `poly_simp_rel` conclusion become the same atom, would collapse **52% of cvc5's arithmetic
vocabulary** and turn all 113 820 corpus instances into `refl`. But it invalidates about as many
steps as it removes — 118 882 in the most favourable scope — and each repair is itself a
`poly_simp_rel`-shaped Farkas bridge. The measurement did turn up a contained alternative worth
more than the original idea: **72% of the `poly_simp_rel` instances are literal duplicates**, and
hoist-and-share would cut the reduction's cost from +24.8% to +6.1% of proof size.

## Why the `reordering` analogy fails

`reordering` steps are pure bookkeeping: premise and conclusion are the same clause, and every
consuming rule is order-insensitive or recomputable, so global elimination is free.
`poly_simp_rel` steps carry content. They are one link of the chain by which cvc5 rewrites an
assertion's atom into its internal normal form — `arith-elim-lt`, then `cong` over a `poly_simp`,
then `poly_simp_rel` — and that chain is pinned at one end by the `assume` boundary and checked
at every other link by a rule that compares syntactically. Collapsing the middle link breaks its
neighbours.

## What was measured

A new analysis-only module (`carcara/src/polynorm.rs`, behind a hidden `carcara poly-norm`
subcommand) groups every arithmetic atom into its *scaling class* using the checker's own
`LinearComb` — so two atoms share a class exactly when a `poly_simp_rel` step could relate them —
elects a representative per class preferring an atom that occurs at the `assume` boundary, and
reports the collapse and the per-rule blast radius under three scopes.

| scope | atoms → classes | `poly_simp_rel` → `refl` | steps → `(= t t)` | atom-sensitive steps broken | `assume`s broken |
|---|---|---|---|---|---|
| all atoms | 520 082 → 249 549 (52%) | 113 820 | 397 512 | 524 387 | 60 |
| order atoms only | 223 612 → 140 129 (37%) | 65 170 | 200 909 | 266 967 | 31 |
| `poly_simp_rel` sides only | 56 563 → 26 760 (53%) | 113 820 | 140 309 | 118 882 | 14 |

208 of 209 cvc5 proofs over QF_LIA/QF_LRA/QF_UFLIA (one overflows the stack on the recursive
subterm walk — the file the evaluation already fails on). Per logic the collapse is 33% / 78% /
66%; one file's vocabulary goes from 21 908 atoms to 293, with a single class of 15 321 atoms.

## The obstacles, rule by rule

**Indifferent.** All clausal bookkeeping — resolution, the CNF axioms, `contraction`,
`weakening`, `reordering`, `subproof`, `and_intro` — only selects and compares whole literals, so
a uniform rewrite leaves it passing; likewise `refl`, and `trans`/`symm` over Boolean equalities.
`evaluate` survives too: the classification puts ground atoms in classes by truth value, verified
on `(>= 3 5)` and `(>= 0 7)`.

**Repairable.** `la_generic` is *not* indifferent — verified: rescaling a literal's atom by λ and
keeping `:args` makes the step invalid; dividing that coefficient by λ restores it. The integer
strengthening in `strengthen` is scale-covariant, so the repair is exact and mechanical.

**Broken.** `cong` into an atom is the killer: `(= (>= (+ x y) 0) (>= (+ y x) 0))` checks by
`cong`, and `(= (>= (+ x y) 0) (>= (* 2 (+ y x)) 0))` — equally true — does not. Re-deriving it
*is* a `poly_simp_rel`. 26 405 such steps even in the narrowest scope. `rare_rewrite` compares
its instantiated conclusion syntactically, and 79–98% of cvc5's `rare_rewrite` steps here are
`arith-*` relational normalizations; 40 538 break. `la_mult_pos/neg` require the scaled sides
literally as `(* m l)`, `(* m r)`; `la_disequality`/`la_totality`/`la_tautology` state templates
over the same two terms in atoms of different classes. All destroyed.

**The boundary, and a tension with no resolution.** `assume` matches the problem's assertions
exactly under `--check-granularity elaborated`, and up to `Polyeq` otherwise. Electing
representatives from the boundary protects it almost perfectly — only 14–60 top-level `assume`s
of 657 164 belong to a class with a competing boundary atom. But representative-election is
exactly what breaks `rare_rewrite`: a *synthesized* canonical form `(⋈ P 0)` would keep
`arith-elim-lt` as a valid instance (args `(P, 0)`) and make `arith-elim-leq` a `refl` — and would
break all 198 585 arithmetic `assume`s. Election preserves the boundary and breaks the rewrites;
synthesis preserves the rewrites and breaks the boundary.

**A structural obstacle.** `(= t s)` over an arithmetic sort is simultaneously a theory atom and
the judgment form of the proof's own rewriting layer. Including it in scope rewrites `poly_simp`,
`cong`, `trans` and `symm` out from under themselves (235 517 `poly_simp` steps touched);
excluding it drops QF_UFLIA's collapse from 39 239 instances to 1 279, since QF_UFLIA's instances
are almost all equalities. No scope gets both.

## What the cost measurement says about `poly_simp_rel` itself

Worth recording separately: `poly_simp_rel` is essentially **free to check** (0.18–0.21 µs per
step, 0.3–0.4% of checking time). Its entire aggregate cost is the Farkas checking its
*reduction* introduces — across the three logics total checking goes 6.27 s → 7.15 s, and the
`la_generic` line alone accounts for +0.83 s of that +0.88 s. Meanwhile the dominant arithmetic
checking cost is `poly_simp` (7–8 µs/step, 15–29% of checking time), which no elaboration touches
because it is a core computational primitive; together with `rare_rewrite` (13–20 µs/step) the two
normalizers are two thirds of the bill.

## What to do instead: hoist-and-share

Distinct step conclusions in the *original* cvc5 proofs:

| rule | steps | distinct | duplicates |
|---|---|---|---|
| `poly_simp_rel` | 114 015 | 31 866 | **72%** |
| `poly_simp` | 236 766 | 64 396 | 73% |
| `evaluate` | 244 698 | 24 668 | 90% |
| `rare_rewrite` | 132 543 | 57 881 | 56% |
| **all premise-free steps** | **2 300 197** | **1 153 597** | **50%** |

The duplication is entirely *cross-subproof* (within a single scope there is essentially none),
so sharing requires hoisting — which is sound here: these proofs contain no variable-binding
anchor at all (21 047 + 7 280 + 79 464 anchors, all `:args`-free), and a `poly_simp_rel`
derivation is closed, since its premise is a premise-free `poly_simp` and the recipe's
`la_generic`, `la_disequality` and `equiv_neg*` steps are premise-free. The general guard is
"the derivation's terms mention no anchor-bound variable".

Memoizing the recipe by conclusion and emitting the shared derivation once at depth 0:

| logic | added steps now | memoized | proof growth |
|---|---|---|---|
| QF_LIA | +427 169 | +130 054 | +22.6% → **+6.9%** |
| QF_LRA | +227 282 | +95 288 | +22.1% → **+9.3%** |
| QF_UFLIA | +731 113 | +113 549 | +27.5% → **+4.3%** |
| total | +1 385 564 | **+338 891** | +24.8% → **+6.1%** |

On `wisas__xs_15_25` (3 806 instances, 550 distinct) the elaborated proof would grow 3.3% instead
of 23%.

Generalized to all premise-free steps, the same mechanism is a **~22% compression of cvc5's
arithmetic proofs before any elaboration**, touching no rule's semantics: one structural
hash-cons of the proof DAG plus the anchor-freedom guard. That deserves its own investigation.

## Recommendation

1. Drop global atom normalization, in all three scopes.
2. Keep the `poly_simp_rel` recipe — the per-instance derivation is right; only its multiplicity
   is wrong.
3. Add cross-step memoization with depth-0 hoisting to the `core` pass.
4. Then consider general proof-DAG hash-consing, which subsumes (3).
