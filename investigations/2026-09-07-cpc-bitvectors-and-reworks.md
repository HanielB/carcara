# CPC checking: bit-vector logics and cvc5's reworked Alethe translation

Branch `cpcCheck-bv`, commits `a3e1601c`, `c4a98abe`, `449b7e07` (2026-09-07), on top of the
port recorded in [2026-09-06-cpc-port.md](./2026-09-06-cpc-port.md). Two goals: check the CPC
proofs of the bit-vector logics, and bring the CPC-to-Alethe translation up to what cvc5's
`alethebv` post-processor (`1eb17718e1`) emits, so that a CPC proof checked through carcara is
as lean as a native Alethe one. The per-rule description of the cvc5 changes used as the
specification (SCOPE chain, the three round-trip short-circuits of `reorganize`, `absorb`,
bitblast rules, `div_by_zero_intro`, `or_neg` rebuild, inst constants) was produced from the
`git diff aee87424..1eb17718e1 -- src/proof/alethe/` of cvc5.

## Bit-vectors

What the regressions needed, in order of appearance:

- cvc5's bitblasting terms: `(@bit i x)` is `((_ @bit_of i) x)`, `(@from_bools ...)` is
  `(@bbterm ...)`, `@bv_empty` is the zero-width bitvector (the neutral element of `concat`).
- RARE list arguments: cvc5 prints an empty list as the neutral element of the operator the
  list is spliced into (`#b0000` for `bvor`, ones for `bvand`, 1 for `bvmul`, `@bv_empty` for
  `concat`, and likewise 0/1 for `+`/`*`) and a singleton list as a *unary* application of
  the operator (`(concat x)`). The translator now finds the operator from the parameter's
  occurrence in the rule's conclusion, and the parser accepts unary n-ary applications in CPC
  mode.
- `bv_bitblast_step` maps to `bv_bitblast_step_<kind>` by the kind of the bitblasted term,
  except that cvc5 bitblasts some terms opaquely, as the bits of the term itself (an
  `extract` of an input variable): those use `bv_bitblast_step_var` whatever the kind.
  `bv_poly_norm`/`bv_poly_norm_eq` are `poly_simp`/`poly_simp_rel`; `bv-repeat-elim` and
  `bv-bitwise-slicing` have dedicated rules.
- Congruences over indexed operators (`extract`) were holed by `cong_premises_fit`.
- The overflow predicates and `bvredor`/`bvredand` are new operators; the eight
  `bv-*-eliminate` rules commented out in `~/carcara/rewrites.eo` for lack of them are back.
- `~/carcara/rewrites.eo` premises of `bv-mult-slt-mult-1/2` and
  `bv-extract-mult-leading-bit` were missing conditions that cvc5's `Rewrites.eo` has, as
  `(= (>= n tn) true)` premises proved by `evaluate` (a systematic comparison of `:premises`
  against cvc5's file found no other divergence beyond `let`/`eo::define` spelling).
- Rewrites with neither a translation nor a RARE definition (`bv-umulo-elim`,
  `bv-smulo-elim`, `int-to-bv-elim`, `uf-int2bv-bv2nat`) are holes, as in cvc5's printer.

## The translation reworks

- `absorb` uses carcara's `absorb` rule (any operator) instead of the Boolean-only expansion.
- `@int_div_by_zero`/`@mod_by_zero`/`@div_by_zero` applications become the choice terms
  `(choice ((y T)) (= y (op a 0)))` (with `y` fresh w.r.t. `a`), and the `arith_reduction`
  eliminating a division by a possibly-zero divisor is one `div_by_zero_intro` step. This
  removes the whole "unsupported `arith_reduction` equality" hole class (45 warnings in 13
  files on the port sweep; zero now). Congruences over those skolems then need the `bind`
  subproof's body equality derived by congruence rather than re-stated (`derive_equality`);
  cvc5's own Alethe pipeline fails the same two regressions (`arith/div.08`,
  `quantifiers/dd_full_xor-rcons-open`) with "term is not an application or operation".
- The `or_neg` rebuild of a clause used as a singleton resolves each distinct literal once.
- The three round-trip short-circuits, at translation time: `implies_elim`/`modus_ponens`
  over the implication of a `process_scope` reuse its folded clause (`scope_implication`);
  a `not_and` whose premise is a resolution over that folded clause becomes the same
  resolution over the subproof clause (`scope_fold`, `not_and_shortcut`); a top-level
  subproof/resolution/reordering/contraction concluding the literals of an earlier top-level
  subproof reuses it, through `reordering` if the order differs (`subproof_by_literals`,
  hooked in `push_step` and `translate_scope_subproof`). Bypassed steps are dropped by
  `ProofNodeForest::from_commands(..).into_commands_pruned()` at the end of the translation.
  Gotchas found: positions `(depth, index)` are reused when frames are popped and pushed, so
  recorded positions are validated against the live step before reuse; and a `bind` whose
  body equality is exactly a premise outside the subproof must re-state it inside (the
  proof-node conversion panics on a subproof with a single step).
- Also new: cvc5's abstract constants `(@const i T)` (mbqi) as uninterpreted constants.

On 35 scope-bearing regressions the translated proofs go from 9,455 to 8,062 steps (-15%).

## Sweep (cvc5 main `1689f13331`, 30 s timeouts, `~/carcara/rewrites.eo`, all AUFBVNIRA logics)

| set | valid | holey | invalid | no proof | skipped |
|---|---|---|---|---|---|
| regress0 | 439 | 29 | 7 | 1 | 420 |
| regress1 | 98 | 20 | 1 | 0 | 144 |

The AUFNIRA subset is unchanged from the port sweep except that the `arith_reduction` holes are
gone (`div.03`, `mod.02`, ... now valid). The 328 bit-vector-logic files: 315 valid, 9 holey,
3 invalid. Holes: 38 of 49 files only `trust`; 93 `ho_cong` + 20 `cong` steps broken by
beta-reduced defines; 4 rewrite rules without definitions. Invalids: the two `evaluate`s of
`(div 0 0)` (total-operator conflation); `bv/holes/ite-merge-then-else` (cvc5 bitblasts
`bvite` over already-bitblasted children as the bits of a different term; the Alethe pipeline
fails identically); `bv/holes/srem-eliminate` (carcara aborts allocating 8 GB while *printing*
the error term of a failed step, so the failing rule is unknown: a CLI robustness issue);
`eqrange2` (`eqrange` operator); `issue11750` (higher-order partial application);
`nomerge-alethe-pf`, `bug812_approx` (overloaded symbols). `bv/test-bv_intro_pow2` is unsat
without a proof from cvc5.

## cpcCarcaraEval

Experiment files in `~/exp/cpcCarcaraEval/`: the runner `run-cpcc.sh` (the pfcmp GNU-time
runner contract with `cvc5 --dump-proofs --proof-print-conclusion` and `carcara check --stats
--proof-format cpc --allow-int-real-subtyping --rare-file`; `proof_bytes` = body without the
outer parentheses as in the CPC+ethos runner), `make-sample-set.py` (20 per set of the 26
union sets, 510 benchmarks, `sets/benchmark_set_cpcc_sample`), and the two submission
scripts for the test job (`cpcctest`, the sample, results `cpcCarcaraEval/test`) and the
full job (`cpccall`, the 26 sets, results `cpcCarcaraEval/all`), octa `-j 12`, wall 1900 s,
10 GB, 1 cpu. Toolchain: cvc5 alethebv `1eb17718e1` static (the pfcmp bin12 one; the CPC
printer is untouched by every alethebv commit) + carcara `cpcCheck-bv` `449b7e07` static-pie
(`target/x86_64-unknown-linux-gnu/release/carcara`) + `~/carcara/rewrites.eo` as modified
above. Not yet uploaded or submitted.
