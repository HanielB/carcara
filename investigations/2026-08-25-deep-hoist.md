# Collapsing lemma scopes: the `deep-hoist` pass

*2026-08-25*

The [`hoist` pass](./2026-08-21-hoist-pass.md) removes duplicated *closed derivations*. It leaves
the scopes themselves alone. This note is about the other direction: eliminating a scope outright,
by using the clausal rule that proves what the scope discharges.

## The observation

A solver that proves a lemma by *scoping* assumes its hypotheses, derives the conclusion under them,
and discharges the whole block into one clause. cvc5 does this constantly — **190 375 subproofs
across 309 of its 494 corpus proofs**, against 3 149 from veriT. The smallest and most common shape
is pure congruence closure:

```
(anchor :step t7)
(assume t7.a0 (= a b))
(assume t7.a1 (= b c))
(step t7.t0 (cl (= a c)) :rule trans :premises (t7.a0 t7.a1))
(step t7 (cl (not (= a b)) (not (= b c)) (= a c)) :rule subproof :discharge (t7.a0 t7.a1))
```

The hypotheses are re-introduced inside the scope only so that a *context-sensitive* rule — `trans`
here — can consume them as premises. But they are already spelled out, negated, in the clause the
scope discharges, and Alethe has a *clausal* rule that concludes exactly that clause from nothing.
Four commands become one:

```
(step t7 (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)
```

## The pass

`carcara/src/elaborator/scopes.rs`, run as `--pipeline deep-hoist`, which is `hoist` plus this. The
two are run together because they feed each other: hoisting the contents of a scope first is what
leaves some scopes with nothing but the step the collapse recognizes, and a collapsed scope leaves a
premise-free step at the enclosing depth, which is then a hoisting candidate like any other.

**The pass never looks at what a scope contains.** It takes the discharged clause and offers it to a
battery of premise-free rules — `eq_transitive`, `eq_congruent`, `eq_congruent_pred`, the CNF
axioms, the unit `la_*` rules, `aci_simp`, `poly_simp`, `evaluate` — keeping the first that the
*checker* accepts. That is what makes the replacement sound whatever the scope was doing internally:
the emitted step is validated by the same function that will later check it, with no premises, no
context and no discharge, so it proves its clause outright. It is the same argument that makes
`hoist`'s conclusion-only key complete, applied to a different subgraph.

Two rules take arguments the clause determines, and are tried with those synthesized:

- `and_pos` and `or_neg` need the index of the selected conjunct or disjunct. The index is
  *searched for* and the rule then run with it, so a clause that matches the shape but not the rule
  is still rejected.
- `la_generic` needs one Farkas coefficient per literal. Only the leading one has to be chosen (1,
  as in the `bounded_farkas` elaboration); the checker infers the rest by requiring each literal's
  linear combination to cancel against the accumulated one.

**The `false` tail.** A lemma proved by deriving `false` under its hypotheses discharges
`(cl ¬A … ¬Z false)`. That literal is redundant — the clause without it is stronger — and it is the
shorter clause a rule can prove. So when the battery fails on the whole clause and the last literal
is `false`, the pass retries on the rest and emits two steps: the rule, and a `weakening` that puts
the literal back, leaving every consumer unaffected. This is what reaches cvc5's *arithmetic* lemma
scopes, whose bodies are thirty-odd steps of rewriting to normal form ending in a `false`.

The battery is filtered by `--allowed-rules` for the same reason `hoist` filters its candidates: a
rule the checker was told to accept as a hole must not become the justification of something that
had a real derivation.

**One supporting change.** `mutate_impl` did not call the pass callback on `Subproof` nodes at all,
so no pass could replace a scope. It does now, after popping the context, so the node is seen at the
depth it lives at — which is also the depth any replacement has to be built for. The two passes that
asserted the case was unreachable now pass subproofs through.

## Results

Over cvc5's 494 proofs, against `hoist` alone:

| | commands | anchors | elaboration |
|---|---:|---:|---:|
| original | 10 594 028 | 198 268 | — |
| `hoist` | 8 400 222 | 198 239 | 161.4 s |
| `deep-hoist` | 8 196 819 | 179 613 | 164.6 s |
| `deep-hoist` + `false` tail | **8 174 467** | **178 002** | 148.2 s |

**19 045 of 198 239 scopes collapse (9.6%)**: `eq_transitive` 16 495, `la_generic` 2 507,
`eq_congruent` 43. That is 20 237 anchors gone and 225 755 commands below `hoist`, 2.7% of its
output and 22.8% below the original. The extra cost is inside the noise — the three timings above
were taken on the same machine minutes apart and the pass's own work is one battery of cheap shape
tests per scope, each of which bails on the first literal that does not match.

Over veriT's 489 proofs the pass is a **complete no-op**: 3 441 093 commands and 12 856 anchors
either way, byte for byte. veriT barely uses the construct, and the few scopes it emits are `bind`
and `sko_*` anchors, which carry a substitution and are excluded by construction.

Every one of cvc5's elaborated proofs re-checks.

## Why only 9.6%

The scopes that collapse are the ones whose conclusion is a tautology of the equality or arithmetic
theory. The other 90% are cvc5's *CNF-conversion and theory-lemma* scopes, whose discharged clause
relates a formula to its rewritten form — profiles like
`{cong, equiv1, equiv2, equiv_simplify, not_not, resolution, symm, trans}`, 55 000 scopes between
the three commonest — and no premise-free rule proves those, because the rewriting genuinely has
content. Collapsing them would mean *clausifying the scope body* step by step, threading the
hypotheses through as extra literals: possible, but it grows a long body rather than shrinking it,
which is the opposite of what this pass is for.

The 9.6% is therefore not a coverage gap to close by adding rules; it is the fraction of cvc5's
scopes that were never doing any work.

## The clausal replay (v2, same day)

The battery only sees scopes whose discharged clause one rule proves *outright*, which misses most
congruence scopes: cvc5's `cong` skips identical argument pairs, so the discharged clause has fewer
equality literals than a whole-clause `eq_congruent` demands. On Haniel's direction the pass now
**replays the body clausally** when the battery fails:

- the scope's assumptions become *hypothesis literals*, their negations threaded through every
  translated step's clause — exactly where the discharge would have put them;
- `cong` → `eq_congruent` over every argument pair, `refl` supplying the identical pairs;
- `trans` → `eq_transitive`; `symm` → `eq_transitive` + `refl`;
- premise-carrying clausification steps → their paired axioms (`equiv1`→`equiv_pos2`,
  `and`→`and_pos`, `not_and`→`and_neg` with the connective term stripped, …);
- `resolution` stays `resolution`, an `assume` premise turning into the literal its unit clause
  would have resolved away; `contraction`/`reordering`/`weakening` recomputed from what the
  translated premises actually carry;
- closed body steps are rebuilt outside unchanged; a final `weakening`/`reordering` matches the
  discharged clause exactly.

Every instance is checker-validated before emission and an uncovered body rule bails the scope out.
Five bugs surfaced on the way, all with the corpus as witness: a replayed node's conclusion is not
its first literal; `weakening` is not a permutation; a *negated* hypothesis used as a resolution
unit leaves the residual `φ`, not `¬h` (bridged to the `¬¬φ` the discharged clause states by
excluded middle on the hypothesis); the body translation must be iterative (solver bodies run
thousands of steps deep); and a repeated `cong` premise has nothing left to discharge the second
time, resolution's set semantics having removed every copy at the first — the fifth member of the
set-semantics bug family. Separately, the sweep exposed that the *parser* overflows the default
8 MiB stack on 54 deeply nested corpus files (plain `check`, no elaboration involved); the CLI now
runs on a spawned thread with a 512 MiB stack.

**Standalone `deep-hoist` (cvc5, 494 proofs):** 19 045 scopes collapse to one step and **169 573
replay** — **188 618 of 198 239 eliminated (95.1%)**, anchors 198 268 → **9 559** (the remainder:
`bind`/`sko_*` anchors and uncovered bodies). Commands 8 639 158, +5.7% over the battery-only pass
and still 18.5% below the original: the replay emits ~28 steps per scope, and its instances
currently bypass the sharing memo, so identical `eq_congruent` instances and `refl` fills across
scopes are not deduplicated — routing them through the memo is the obvious optimization.

**The core-pipeline tension, and how it was resolved.** At first the replay was counterproductive
in the full core pipeline: that pass reduced the clausal `eq_*` rules *into* discharge subproofs,
so replaying a scope into `eq_congruent`/`eq_transitive` steps handed it material to re-expand, and
the corpus run ended at 12.09 M commands and 567 k anchors — more scopes than the input had. The
diagnosis was that scope-freedom and the core vocabulary were in tension: the core had no
premise-free clausal equality rules, so a proof could be scope-free (the replay, with `eq_*` kept)
or core (where the discharge subproof *is* the normal form), not both.

Haniel resolved it the other way, by **making the clausal rules core**: `eq_transitive`,
`eq_congruent`, `eq_symmetric` and `not_symm` are the clausal variants of `trans`, `cong` and
`symm`, their checkers are literally the same functions, and keeping the pair costs no checking
power. With that, the replay's output *is* core, and the two passes compose as intended — on
`mathsat hard10`, `deep-hoist` + core gives 87 728 commands and 59 anchors against `hoist` + core's
98 416 and 2 652, i.e. 11% smaller with the scopes gone, and 21% below the original.

Two bugs surfaced in that composition, both fixed: `prune` had dropped the assumes from the root
list, so the printer emitted them after the steps (Alethe wants them first); and `local`'s
`eq_transitive` canonicalization, which drops the hypotheses the chain does not need, could emit a
*two*-literal `eq_transitive` — which the rule's own checker rejects, since it requires at least
three. That one is pre-existing and was simply never reachable before: the replay emits chains with
a reflexivity link, where a single premise closes the chain.
