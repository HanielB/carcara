# Alethe BV proofs: cvc5 production + carcara checking (2026-08-30)

**Question.** How far are cvc5 (worktree `~/cvc5/wt-alethebv`, branch `alethebv` off upstream
main @ aee8742404) and carcara (branch `parsing-subst-fixes`) from producing and checking
*valid* Alethe proofs for pure QF_BV problems, with the BV RARE rules in `../rewrites.eo`?

**Answer.** After the fixes below: **every complete proof cvc5 produces checks fully valid,
zero holes** — 55/55 pure-BV cvc5 regressions, and 133/133 on a 251-benchmark stratified
SMT-LIB QF_BV sample (the other 118 samples are cvc5 90s-timeouts: 77 while solving, 41
killed while dumping the proof; no checking failures of any kind).

## Setup

- cvc5: `--dump-proofs --proof-format=alethe --proof-granularity=dsl-rewrite`, timeout 90s
  (60s for regressions).
- carcara: `check --stats --expand-let-bindings --allow-int-real-subtyping
  --allow-higher-order-indexed-ops --rare-file ~/carcara/rewrites.eo`, timeout 300s,
  `ulimit -s unlimited`. The `--allow-higher-order-indexed-ops` flag is required: cvc5 prints
  RARE-style non-indexed applications like `(extract 30 0 x)` inside rare_rewrite-related
  terms.
- Regression corpus: 59 unsat pure-QF_BV files from `test/regress/cli/{regress0,regress1}`
  (55 produce proofs; 2 timeouts, 2 harness quirks).
- QF_BV sample: 251 benchmarks from `~/benchmarks/smtlib/QF_BV`, ≤8 per family, ≤200KB,
  catalog `:status unsat`, 25 families represented among the valid results. 826MB of proofs;
  largest checked proof 93MB. All checks within 300s.

## Baseline (before changes)

4/55 regressions valid. Failure buckets: unparseable RARE-style terms (~34 files, fixed by
the CLI flag alone), missing BV rules in rewrites.eo (~11), `bv_bitblast_step_*` names
unknown to carcara (6).

## cvc5 changes (branch `alethebv`, src/proof/alethe/ only)

1. New `AletheRule` values + names: `bv_bitblast_step_bv{udiv,urem,shl,lshr,ashr}`, `absorb`.
2. `BV_BITBLAST_STEP` for udiv/urem/shl/lshr/ashr: emit the proper rule instead of `hole`
   (the code said "no checking for those yet in Carcara" — carcara has checkers, fixed below).
3. `ABSORB` elaboration fallback (non-and/or operators, i.e. BV absorptions like
   `(= (bvand x #b0…0) #b0…0)`): emit the new `absorb` rule instead of
   `hole :args ("failed absorb")`. Before: 40 such holes across 18 regression files.

## carcara changes (branch `parsing-subst-fixes`)

1. `src/ast/substitution.rs`: apply substitutions inside indexed-operator arguments
   (`Term::ParamOp.op_args`; was a literal TODO). Without it, instantiated RARE conclusions
   keep `(_ zero_extend n1)` with the rule variable — the largest failure bucket (~23 files).
2. `src/ast/pool/mod.rs`: BV n-ary/concat sort computation tolerates `Sort::Var` (the
   placeholder sort of an *empty* rare-list, transient until meta-rewriting flattens it);
   was `unreachable!()` panics.
3. `src/ast/evaluate.rs` — **soundness bug**: `as_signed_bitvec` returned `m - val` (positive
   magnitude) instead of `val - m` (negative two's-complement). Broke evaluation of
   sign_extend, signed comparisons, bvsub/bvsdiv/bvsrem, sbv_to_int. Repro:
   `((_ sign_extend 1) #b101010000100)` evaluated to `(_ bv1404 13)` instead of
   `(_ bv6788 13)` (4096−2692 vs 8192−1404).
4. `src/checker/shared.rs`: dispatch cvc5's `bv_bitblast_step_*` names to the existing
   `bitblast_*` checkers; register `bv_repeat_elim` and `absorb`.
5. `src/checker/rules/bitvectors.rs`:
   - `get_term_bits`: bits of a BV *constant* are boolean constants (cvc5's bitblaster
     constant-folds `@bit_of` on constants; carcara kept them symbolic).
   - `bitblast_shift_op`: out-of-range **ashr** fills with the sign bit (was `false` for all
     three shifts — wrong for ashr semantics and for cvc5's encoding).
   - `ripple_carry_adder`: returned carry was the carry *into* the last bit, not the carry
     *out* of the addition. Invisible in add/mult (they discard it); broke the `sign` tests
     in udiv/urem bitblasting.
   - `bitblast_udiv_urem_rec`: the remainder update is
     `r1[i] := ite(sign, r1[i], r_minus_b[i])` per cvc5's `uDivModRec`
     (bitblast_strategies_template.h); carcara hardcoded `true` for the else branch.
   - `bitwise_slicing`: generalized to bvor/bvxor (was bvand-only) and to either operand
     order inside slices (the ops are commutative).
   - new `repeat_elim`: `(= ((_ repeat n) x) (concat x … x))` with n copies (n=1 ⇒ rhs = x).
6. `src/checker/rules/extras.rs`: new generic `absorb` rule: `(= t c)` where `c` is the
   absorbing element of `t`'s top operator (and→false, or→true, bvand/bvmul→0, bvor→ones)
   and occurs among `t`'s arguments modulo same-operator flattening. Mirrors cvc5's
   `ProofRule::ABSORB`. *Design point open to veto — the alternative is elaborating via
   ac_simp + new RARE rules that neither tool has.*
7. `src/checker/rules/polynomial.rs`: `Polynomial::modulo` drops coefficients that reduce to
   0 mod 2^w (e.g. `1 + (2^w − 1)`); zero-coefficient entries made `poly_simp` falsely
   reject equal BV polynomials (hit on Sage2/bench_13083, a 32k-step proof, now valid).

Carcara test suite: all green (203 lib tests + integration, 0 failed). A UF proof was
spot-checked valid — non-BV behavior unaffected.

## rewrites.eo changes (~/carcara/rewrites.eo)

- Uncommented the `;;; BV` block (9 rules); converted **all** rules from `rewrites-bv.eo`
  (131 appended): `declare-rule` → `declare-rare-rule`, `(eo::list_singleton_elim <op> X)` →
  `X` (implicit in carcara's rare-list meta-rewriting). Canonical format per steering:
  everything `declare-rare-rule`, singleton-elim implicit.
- `bv-ashr-by-const-2`: added the missing premise `(= (< amount1 (int.pow2 (@bvsize x1))) true)`
  — cvc5's define-cond-rule has 4 conditions and the printer emits all 4 as premise steps.
- 9 rules commented out (`;; not parseable by carcara yet`): they use operators carcara's
  parser lacks — `bvredor`, `bvredand`, overflow predicates (`bvuaddo`, `bvsaddo`, `bvusubo`,
  `bvssubo`, `bvsdivo`, `bvnego`), and `mod_total` (`uf-int2bv-bv2nat`). They can only fire
  for inputs using those cvc5-extension operators, so the standard corpus is unaffected.
- `rewrites-bv.eo`: removed scratch junk (stale duplicate `bv-extract-concat-2` + notes,
  old lines 22–37).

Empirical note: cvc5 emits RARE-rule premises as real proof steps (evaluate/symm chains), so
carcara's premise matching is the right mechanism — the `.eo` definitions must list exactly
the cond-rule conditions in cvc5's order. All 74+ BV rules that fire now do.

## Known gaps / follow-ups

- cvc5-side: 90s was too short for 118/251 sampled benchmarks (77 solving, 41 proof-dumping)
  — a real evaluation needs cluster-scale timeouts; checking was never the bottleneck (all
  133 proofs, up to 93MB, checked within 300s).
- carcara parser lacks `bvredor`/`bvredand`/overflow predicates/`mod_total` — needed to
  re-enable the 9 commented rules and to check benchmarks using those operators.
- 50 distinct `bv-*` RARE rules fired across the QF_BV sample proofs; the regression corpus
  exercised 99 rules total (incl. bool/ite/eq).
- Repro scripts and per-file results: session scratchpad `sweep-*.sh`, `qfbv-results.tsv`
  (not committed).
