# What the `sko_ex` reduction costs

**Branch:** `inv/sko-ex-cost` (measurement only, no code change).
**Question:** the `sko_ex` recipe emits a lot of machinery per step — should the rule stay
*reducible*, or move to *expensive* (i.e. be left unreduced)?
**Verdict:** the measurements below argue either way, and the call was made for
**expensive**: the reduction is complete, linear in the number of bindings and emits only cheap
core rules — the corpus-wide cost is a mere +0.71% of steps — but the ~8× *local* blowup is a
price the classification is not willing to pay by default. The recipe stays in the tree
(`core/skolem.rs`, unregistered) and re-enabling it is one map entry.

## Method

Two release binaries: the pass as it is, and one with the `"sko_ex" => skolem::sko_ex` entry
commented out of `get_elaboration_function`. Both elaborate all 11 affected proofs and both
outputs check `valid` at elaborated granularity — so leaving the rule unreduced is
operationally viable, and the question is purely one of cost versus core-fragment membership.
A third, temporarily instrumented binary produced exact per-instance numbers (an env gate
reducing exactly one instance, plus emitted-step and DAG-size counters).

Corpus: 17 instances across 11 veriT proofs in UF/UFLIA. Binder arity 1 (6 instances), 2 (7),
3 (3), 4 (1) — note the 4-binding instance, `coinductive_list…2360383` step `t127`.

## Step blowup

| | steps |
|---|---|
| the 11 proofs, `sko_ex` kept | 6027 |
| the 11 proofs, `sko_ex` reduced | 7278 |
| delta | **+1251** (mean **+73.6**/instance, median 57, min 37, max 167) |

Per-instance deltas are additive (they sum exactly to the total), so instances do not interact.
Anchors grow by 91 (5.4/instance).

Locally the blowup is about **8×**: an unreduced `sko_ex` region is ~10.4 commands (the step,
its anchor and a mean 8.4 inner steps) and becomes ~84 steps plus ~6 anchors. Corpus-wide it is
noise: +1251 against 175 447 steps in the elaborated UF+UFLIA/veriT corpus, i.e. **+0.71%**
(+20.8% on the 11 affected files).

The recipe *directly* emits 18–34 steps per instance; the printed proof carries 2–5× that,
because a shared helper derivation — the double-negation iff-introduction (excluded middle +
`not_not` + two `equiv_neg` + resolutions + `contraction`) — is re-materialized in every
subproof context that uses it: a shared `Rc<ProofNode>` referenced from inside two different
`bind` subproofs must be printed twice. **That re-materialization is the single biggest lever
if the recipe is ever tuned.**

## Checking cost

Medians of 5 runs, summed over the 11 files, elaborated granularity:

| phase | `sko_ex` kept | reduced | delta |
|---|---|---|---|
| parsing | 61.87 ms | 66.55 ms | +4.68 ms (+7.6%) |
| checking | 4.71 ms | 5.95 ms | **+1.24 ms (+26.3%)** |
| elaboration | 20.35 ms | 24.81 ms | +4.46 ms (+21.9%) |

Per instance: +73 µs of checking, +263 µs of elaboration. Note that on this corpus *re-parsing*
the larger proof (+4.68 ms) costs more than checking the extra steps (+1.24 ms).

Where the added checking time goes — not where one would guess:

- **`refl`: 66% of it.** Only +155 steps, but they average 4.75 µs against a 0.07 µs median for
  the rule — the `variable_facts` refls are checked under the renaming context, so `strict_refl`
  applies a context substitution to an ε-witness term.
- **`sko_forall`: 35%.** One per instance, median 11.7 µs, max 105 µs — the α-modulo comparison
  of the step's witnesses against the recomputed `¬∀¬`-shaped ones.
- Everything else together is <15%: +564 `cong`, +148 `resolution`, +71 `trans`, +66 `bind`,
  +38 `contraction`, +38/+38/+34/+34 `equiv_neg1`/`equiv_neg2`/`equiv_pos2`/`not_not`. Anchor
  checking is irrelevant (0.16 µs each, +8 µs in total).

Removing the 17 `sko_ex` checks saves 0.185 ms, so the region's checking cost goes from ~16 µs
to ~89 µs: a **~5–6× multiple**, sublinear in the ~8× step growth because the emitted steps are
cheap core rules.

## Term size

Terms grow by a bounded constant factor and the ε-witnesses stay shared in the DAG:

| bindings | original conclusion (DAG) | largest emitted conclusion | ratio |
|---|---|---|---|
| 1 | 16–66 | 21–77 | 1.2–1.4× |
| 2 | 15–44 | 30–74 | 1.7–2.0× |
| 3 | 32–42 | 74–83 | 2.0–2.3× |
| 4 | 62 | 133 | 2.1× |

The factor comes from the `¬∀¬`-shaped witnesses `wᵢ` coexisting with the `∃`-shaped `vᵢ`; it
is per binding and does not compound. Printed size over the 11 files: 1 000 243 → 1 229 685
bytes (**+22.9%**, +13.5 KB per instance), which is what drives the parsing delta.

## Scaling

| bindings | k | per-instance deltas | mean |
|---|---|---|---|
| 1 | 6 | 37, 45, 49, 49, 57, 61 | 49.7 |
| 2 | 7 | 54, 54, 54, 54, 74, 74, 84 | 64.0 |
| 3 | 3 | 98, 98, 142 | 112.7 |
| 4 | 1 | 167 | 167 |

Least squares: **Δsteps ≈ 6.5 + 34.6 · nbind**, R² = 0.77. The growth is in binder arity, not
term size: corr(Δ, nbind) = 0.88 versus corr(Δ, conclusion DAG size) = 0.42. Each extra binding
adds ~35 printed steps — a witness-bridge `bind` subproof, a `connective_def` duality, an
α-renaming `bind` of the quantified tail, a deep-`cong` transport, and a re-materialized copy
of the double-negation helper. The `Arrow_Order` outlier (142 for 3 bindings) has a wider
transport because its body is a three-way disequality conjunction.

## The measurement against criterion R1

Against criterion R1 — linear in the step's size with a small constant, emitted steps cheap to
check:

- **Linear, in the right variable.** ~35 steps per binding, no super-linear behaviour, and term
  size grows by a bounded factor that is flat in arity from 2 upward.
- **Emitted steps are cheap.** Every one of them is a core rule, all with sub-microsecond to
  ~12 µs medians. Nothing lands in an expensive checker.
- **Absolute cost is negligible here.** +0.71% of the corpus's steps; +1.24 ms of checking.

**How the decision came out.** R1 is met on every axis measured, so the reduction is not
*infeasible* — and it stays available in the tree for that reason. What decided the
classification is the local price rather than the corpus-wide one: it is cheap here *because
there are only 17 instances*. The per-instance blowup is
~8× locally, growing at ~35 steps per binding, so on a Skolemization-heavy corpus it would
matter — a proof that is 10% `sko_ex` by step count would grow ~1.8×, with checking up ~40% at
the measured 5–6× per-region multiple. Rather than let the classification depend on how
Skolemization-heavy a corpus happens to be, `sko_ex` is classified **expensive** and the `core`
pass leaves it alone.

If it is ever promoted back, the first thing to fix is not the recipe's shape but the
re-materialization of its shared helper derivations across subproof contexts: the recipe emits
18–34 steps and 37–167 get printed, so that alone accounts for most of the blowup.
