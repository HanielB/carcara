# `bfun_elim`: the remaining case, and what to revisit

**Status:** done, same day — the fix and items 1–4 and 6 of the list below are implemented
(`carcara/src/elaborator/core/legacy.rs`, `Builder::leaf` in `core/mod.rs`); item 5 waits for the
cluster. Results at the end. Branch `coreAlethe`.

## Where things stand

`bfun_elim` reduces both of its checker's steps at any position of the premise: the ite expansion
of applications (second step) as a subproof-free equivalence, the Boolean-quantifier expansion
(first step) as an implication at the top of the premise and as an equivalence anywhere else, with
`exists` routed through the quantifier duality. Six veriT proofs covering every shape veriT was
seen to emit reduce to zero `bfun_elim` steps and check at elaborated granularity.

One shape is still kept, locked in by `bfun_elim_case_split_under_a_binder_is_kept`:

```
(or q (forall ((x Bool)) (forall ((z Int)) (p z x))))
▷ (or q (and (forall ((z Int)) (p z false)) (forall ((z Int)) (p z true))))
```

a Boolean quantifier *below the top* whose variable occurs *under a binder of its body*.

## Why it is kept today

The equivalence's ← direction needs, per branch `σ`, the clause `(cl (= ψ ψ[σ]) L₁ … Lₖ)` — the
body rewritten at the branch's assignment, under the branch's hypothesis literals. It is built by
`conditional_substitution`: the hypothesis stays a *literal* (`(cl (= x ⊤) ¬x)`) and the clausal
`eq_congruent` carries it up through applications and operations, accumulating the literal.

That route cannot cross a binder. To go from `(cl (= (p z x) (p z ⊤)) ¬x)` to
`(cl (= (∀z. p z x) (∀z. p z ⊤)) ¬x)` one needs a `bind`, and neither form of `bind` does it:
the vanilla form wants a *unit* equality as its previous step, and the generalized form closes a
literal *as a quantifier* — it would give `(cl (∀z. (= (p z x) (p z ⊤))) ¬x)`, a different
statement. So `conditional_substitution` treats binders as opaque, the branch's term does not
match the instance, and the recipe gives the step up.

## The fix: assume the hypothesis in the ← direction

The subproof-free discipline was adopted for one reason: a *ground* case split (the second step
on a ground application) is then hoistable, since the sharing memo and the `hoist` pass both
refuse a derivation that reaches an assumption or a subproof. **That reason does not apply to the
← direction.** Its case split is on the *anchor's own variables* — the whole direction lives under
an anchor over `X`, and nothing that mentions `x` is context-free — so nothing in it was ever
going to be shared. Keeping it subproof-free buys nothing and costs the binder crossing.

So: derive the ← direction's rewriting under a discharge subproof, with **unit** hypotheses, and
cross binders with the **vanilla** `bind`.

```
(anchor over X, already open)
  assume aᵢ := xᵢ                      for σ(xᵢ) = ⊤, xᵢ free in ψ
  assume aᵢ := (not xᵢ)                for σ(xᵢ) = ⊥, xᵢ free in ψ
  (cl (= xᵢ ⊤))                        equiv_neg1 + true, resolved with aᵢ      (unit)
  (cl (= xᵢ ⊥))                        equiv_neg2 + false, resolved with aᵢ     (unit)
  (cl (= ψ ψ[σ]))                      unit congruence: `cong` through App/Op/ParamOp with
                                       the changed arguments' units as premises — no `refl`,
                                       `cong` skips equal arguments — and, under a forall/exists,
                                       an anchor of Variable args, the recursion, and a vanilla
                                       `bind` (unit in, unit out)
  (cl ¬a₁ … ¬aₖ (= ψ ψ[σ]))            close_subproof
  (cl x … (= ψ ψ[σ]))                  not_not for each ⊥ assignment (¬(not x) ⇒ x)
```

then exactly what follows today: `equiv_pos1` against the selected instance, the branches resolved
on the Boolean variables, `close_bind` over `X`.

Points to get right:

- **Shadowing.** `Substitution::apply` (which produces the instances) does not substitute under a
  binder that rebinds a substituted variable; it restricts the substitution and never renames when
  there is no capture (`ast/substitution.rs`, "a binder that merely shadows"). The unit walk must
  restrict the same way at such a binder, so that its term equals the instance. Capture cannot
  arise: the values are `⊤`/`⊥`.
- **Which variables to assume.** Only those free in `ψ` (`pool.free_vars_ref`). The branch
  combination already tolerates a variable that does not occur (`contains(&variable)`), and this
  keeps the discharge clause exactly the literals it expects.
- **Binders the walk may cross.** `forall` and `exists` — the vanilla `bind` checker takes any
  binder kind, but `bind` over `choice`/`lambda` is what the classification deliberately keeps out
  of the core (divergence 5). A `choice`/`lambda`/`let` with an occurrence returns
  `Err(Inapplicable)` explicitly, rather than today's silent `None` caught by a downstream
  mismatch.
- **Nesting.** The discharge subproof sits inside the anchor over `X`, and the `bind` anchors sit
  inside the discharge subproof; the unit `(= xᵢ v)` is used from inside those anchors as an
  outbound premise from an enclosing scope, which `subproof_node` collects. The Builder's id stack
  handles arbitrary nesting; `close_subproof` needs the last inner step unit, which `cong`/`bind`
  give.

**Cost.** Neutral to better. For a flat body `(p 1 x)`: today `equiv_neg1` + `true` + resolution
(the literal), `eq_congruent` + `refl` + resolution = 7 steps; after, `assume` + `equiv_neg1` +
`true` + resolution + `cong` + `subproof` = 6, plus `not_not` on the ⊥ branch = 7. For a wide or
deep body the unit route wins outright: each `cong` is one step where `eq_congruent` costs one
step plus a `refl` per untouched argument. The `44`/`58` figures should not move up.

**Simplification.** With this in, `conditional_substitution` has no caller (the second step uses
`clausal_congruence` directly and must stay clausal — that *is* the ground, hoistable case) and is
deleted. One route per direction: clausal where sharing is possible, assumed where it is not.

**Validation.** The kept-shape test flips to `== 0`; a veriT proof of that shape
(`(assert (or q (forall ((x Bool)) (forall ((z Int)) (p z x)))))` and a contradiction) joins the
six; an inner *Boolean* quantifier under the split variable
(`(or q (forall ((x Bool)) (forall ((y Bool)) (p x y))))`) exercises the crossing followed by a
nested first step.

## What to revisit in what is already there

In order of value.

1. **`ite_intro` on the clausal route.** `ite_selection_tautology` still derives each branch
   `(cl ¬c (= s r₁))` by an assumption, `cong`, and the `rare_rewrite` rules
   `ite-true-cond`/`ite-false-cond` — ~24 steps and two subproofs per tautology, and its output
   *needs `--rare-file rare-tests/rare/ite-intro.rare` to check* (classification, `ite_intro` row).
   `ite_then_intro` states that branch clause outright. New shape: `ite_then_intro` (+
   `eq_symmetric` + `equiv_pos2` when the rule wrote the equality flipped), `ite_neg2`, one
   resolution, the dual, one resolution — 7 to 11 steps, subproof-free, no RARE dependency, and
   shareable. Same family as this work, and it removes a checking-time requirement.

2. **Memoize a recipe's repeated leaves.** On `(g a b c)` (7 ite nodes, 147 steps) the
   second step emits `refl` 28 times for 5 distinct terms and the conditional literal
   `(cl (= c v) ∓c)` 14 times for 6 distinct pairs — a third of the derivation. A per-recipe memo
   for `refl`, the conditional literals and the `true`/`false` axioms, holding only nodes built at
   the recipe's base depth (visible from every scope the recipe opens), brings that example to
   ~100. A `hoist` stage after `core` would do the same across recipes and inside anchors; the
   memo is the part that costs nothing to have regardless.

3. **One → derivation.** `expand_bool_quantifier` and the → block of `quantifier_equivalence` are
   the same derivation twice (instantiate per distinct instance, pack, close over `ȳ`). Extract
   `quantifier_implication` and have both call it. No change in output.

4. **Explicit refusals.** Where the rewriting cannot proceed (`let`, `choice`, `lambda` with
   something to expand or a variable to split on), return `Err(ElaborationError::Inapplicable)`
   at the spot rather than `None` and a downstream mismatch. Same behaviour — the pass keeps the
   step and logs — but the log then names the reason.

5. **Measure sharing before changing pipeline defaults.** The second step's ground branches are
   hoistable but nothing collects them today (`core`'s memo is keyed by the elaborated step's
   conclusion; `hoist` runs first). On the veriT UF/UFLIA arm, count distinct vs. total conditional
   literals and selection tautologies after `core`, and run `… core hoist …` once to see the step
   reduction. Decide from the numbers whether a second `hoist` belongs in the default pipelines.

6. **A three-step saving in the ȳ-empty conjunction case.** With no quantifier left,
   `and_pos` alone gives `(cl ¬χ ψ[σ])`, which already *is* `(cl ¬rhs ψ[σ])`; the
   `excluded_middle` stand-in (`refl` + `equiv_pos2` + resolution) and the per-branch resolution
   against it are only needed for the dual packing. Trivial special case; `−3 − 2ᵏ` steps.

Not worth doing: the `exists` case with no non-Boolean variable spends ~8 steps on
`double_negation` where a direct `equiv_intro` over the two dualities would spend ~12 differently;
and a conclusion only *polyeq*-equal to the expansion is the `polyeq` pass's job, which every
pipeline runs first.

## Order

(1) the fix above, since it closes the last shape and deletes code; (3) and (4) alongside it, as
they touch the same functions; then the `ite_intro` conversion, which is independent; then the
memo, measured on the `(g a b c)` example and the corpus arm; the sharing measurement last, since
its outcome is a pipeline decision rather than a recipe.

## Results

- **The remaining case is closed.** `case_split_substitution` assumes the branch's hypotheses and
  `unit_substitution` carries the unit equalities by `cong` and the vanilla `bind`; the
  `conditional_substitution` route is gone. A veriT proof of the shape
  (`(or q (forall ((x Bool)) (forall ((z Int)) (p z x))))`) joins the six earlier ones: all seven
  reduce to zero `bfun_elim` steps and check at elaborated granularity. Two tests cover the
  crossing, one with an inner *Boolean* quantifier (crossing followed by a nested first step).
  Cost, one Boolean variable, added steps only: top-level implication **8**, equivalence
  **41** (was 42 with the literal route, before the `and_pos` shortcut), `exists` **60** (was 58:
  the body `¬(f x)` is one `cong` deeper on the unit route than on the clausal one).
- **`ite_intro` on the selection axioms.** Per tautology ~31 → 13 (direct) / 20 (flipped)
  steps, no subproof, no `rare_rewrite`; the output of a proof with `ite_intro` now checks without
  `--rare-file`. veriT writes the equalities flipped, so the `refl` + `cong` + `equiv_pos2`
  orientation is the common path.
- **`Builder::leaf`.** Per-reduction memo of premise-free leaves built at the base depth. The
  three-argument second-step example goes 147 → **99** steps; the first-step figures do not move
  (their leaves sit inside anchors, which the memo leaves to `hoist`).
- **One → derivation** (`quantifier_implication`), used by the top-level path and the
  equivalence; **explicit refusals** (`ElaborationError::Inapplicable`) for `let`/`choice`/`lambda`
  wherever the checker would transform what the walk cannot reach — decided by running
  `apply_bfun_elim` on the subterm — and for anything that would leave the ← branch clause
  without the body.
- **Not done: the sharing measurement.** There is no proof with `bfun_elim` or `ite_intro` in
  the local `benchmarks/` tree; the count of duplicate leaves across steps, and the effect of a
  `hoist` stage after `core`, need the veriT UF/UFLIA arm on the cluster. Local evidence is the
  generated proofs only, where a second `hoist` has nothing left to find after `Builder::leaf`.
