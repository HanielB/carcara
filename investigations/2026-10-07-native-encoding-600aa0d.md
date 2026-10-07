# The native and rare-list Eunoia encodings of AletheInEunoia 600aa0d

**Date:** 2026-10-07.
**Question:** AletheInEunoia `600aa0d` ("Re-organize between native and non-native rules
generation") declares the list-based operators and rules twice: the plain names now use
rare-lists (`distinct` with `:arg-list @rare-list-cons`, `aci_simp` and `distinct_elim`
checked by library programs) and `_native` names the `eo::List` encoding over Ethos's list
builtins. Its translator side is caotic123/carcara `b2e5092a`, written on the translator of
`5e32c07a`. What does it take to bring it onto `bv-fixes`, so that nothing but the Eunoia
translation changes, and does the result check what the current translator checks?

**Answer:** `b2e5092a` touches only the translation (the `translate eunoia` options, the
Eunoia translator, its RARE test and the RARE docs page). Ported onto this branch's
translator, with this branch's `--native-rules` folded into its `--native` flag, it checks
exactly what the current translator checks, proof by proof, in both encodings. The current
translator cannot check anything against a signature that has `600aa0d`, so the two land
together.

## The port

- `b2e5092a`'s `Encoding` (`alethe_signature/encoding.rs`) chooses the symbol of `distinct`,
  the sequences and the associative spines of the generated RARE rules. Its `rare.rs` is
  split into the `rare/` module. Both build terms in the hash-consing store this branch's
  translator uses (main's, since `ee0688d6`), as this branch's `rare.rs` did; that is the
  bulk of the port and is mechanical.
- One flag, `--native` (default `true`), replaces `b2e5092a`'s `--native` and this branch's
  `--native-rules`. In the native encoding a step of rule `r` is checked with `r_native`
  whenever the signature declares it, read from the rule files: the variants
  `rules/native.eo` generates and the ones `alethe.eo` declares itself (`aci_simp_native`,
  `distinct_elim_native`, and `semilattice_simp_native` in the merge). `b2e5092a`
  hard-coded the two it had. `rules/native.eo` is included only in the native encoding,
  and only when the signature has it (`600aa0d` does not).
- `--native false` emits rare-lists and the plain rules. `distinct_native` is reserved
  for user symbols like `distinct`.

## Setup

| | |
|---|---|
| baseline | `bv-fixes` `03fd7c8b`, `--native-rules` |
| new | `bv-fixes` with the port, `--native true` / `--native false` |
| Tiago's | caotic123/carcara `b2e5092a`, `--native true` / `--native false` |
| signatures | `alethe-toolkit` `489615c` (the QF_UF round-two signature); `600aa0d` (`aletheineunoia/wt-tiago`, clean); `600aa0d` with `686beb0` applied; a snapshot (2026-10-07 13:06) of the in-progress, uncommitted merge of `600aa0d` into `alethe-toolkit` |
| RARE | `big.rare` of `489615c` (106 rules) |
| Ethos | 0.2.5 (`08e4aa40`) |
| inputs | the elaborated proofs (`elab.alethe`) of two local runs of `~/exp/alethe-eunoia/local-run.sh` over the 40-benchmark QF_UF sample, cvc5 and veriT, 77 proofs each: `qfuf-03-wtdiff` (before the core pipeline) and `qfuf-11-native-chain` (core pipeline, 22,597 `semilattice_simp` steps) |

Reproduction, per configuration (`scripts/eunoia-encoding-matrix.sh`):

```bash
CASES=cases.txt RARE=big.rare ETHOS=~/alethe/ethos/build/src/ethos \
  investigations/scripts/eunoia-encoding-matrix.sh new-merged-native \
  target/release/carcara <signature> --native true
```

`wt-tiago`'s own `big.rare` cannot be used by either translator: Carcara's RARE parser
rejects its `Seq` sort (`error: sort 'Seq' is not defined`), so every translation fails.

## Results

`qfuf-11-native-chain`:

| translator | signature | correct | other |
|---|---|---|---|
| baseline | `alethe-toolkit` | 77 | |
| new, native | merge | 77 | |
| new, rare-list | merge | 76 | 1 Ethos timeout (180 s) |

The verdicts of the native encoding are those of the baseline on every proof; it emits the
baseline's 18 `_native` rules plus `semilattice_simp_native` (the 22,597 steps the baseline
checks with the plain `semilattice_simp`) and `distinct_elim_native`, and `distinct_native`
for `distinct`. On `qfuf-03` it likewise adds `aci_simp_native` (3,287 steps) and
`distinct_elim_native` to the baseline's 20. The rare-list timeout is `verit.NEQ__NEQ004_size5`, the
largest proof (13 MB of Eunoia, 38,712 `resolution` steps): the native encoding checks it in
39 s (810 MB); the rare-list one is still running, CPU-bound, at 900 s (2.7 GB). This is the
cost of the plain rules, not of the rare-lists: the baseline translator without
`--native-rules` (plain rules, `eo::List` sequences, `alethe-toolkit`) also times out at
180 s on this proof.

`qfuf-03-wtdiff`:

| translator | signature | correct | `ac_simp` | other |
|---|---|---|---|---|
| baseline | `alethe-toolkit` | 47 | 30 | |
| baseline, without `--native-rules` | `alethe-toolkit` | 47 | 30 | |
| baseline | merge | 0 | | 77 `Could not find symbol $normalize_eo_list` |
| new, native | merge | 47 | 30 | |
| new, rare-list | merge | 47 | 30 | |
| Tiago's, either encoding | `600aa0d` | 46 | 30 | 1 type-checking failure |
| new, either encoding | `600aa0d` | 12 | 30 | 35 `refl` |
| new, either encoding | `600aa0d` + `686beb0` | 47 | 30 | |

- The 30 `ac_simp` failures belong to these inputs: the `qfuf-03-wtdiff` run itself
  recorded the same 30, and they are the same proofs in every configuration, Tiago's
  translator included. The core pipeline (`qfuf-11`) rewrites these steps.
- The new translator's verdicts are the baseline's on every proof, against the merge in
  both encodings and against `600aa0d` + `686beb0`.
- The 35 `refl` failures on bare `600aa0d` are a signature mismatch, not the encoding:
  this branch passes `refl` the substitution its context induces, defined once per context
  (`f71d63e5`, `(step t292 (@cl (= @t151 @t151)) :rule refl :args (subst_ctx1))`), which
  `alethe-toolkit`'s `refl` takes since `686beb0`; `600aa0d` branched from `3b6ec34`,
  before it, and its `refl` takes the context. With `686beb0` applied they all check.
- Tiago's translator fails one proof the new one checks,
  `cvc5.20190906-CLEARSY__0009__00125`: `(declare-const interval (-> U U U))` does not
  type-check. This branch's translator renames user symbols that collide with signature
  names (`3da16091`); otherwise the two agree on all 77 proofs.

## Consequences

- The port and the signature merge land together: the current translator fails every
  proof against a signature with `600aa0d` (`$normalize_eo_list` became
  `$normalize_eo_list_native`), and the new one emits `distinct_native` and
  `$normalize_eo_list_native`, which `alethe-toolkit` before the merge does not declare.
- `--native-rules` is gone. `~/exp/alethe-eunoia/run-eunoia.sh` passes it for
  `NATIVE_RULES=1`; it needs `--native true` (or `false`). The old vanilla configuration
  (plain rules with `eo::List` sequences) does not exist after the merge: `--native false`
  is the rare-list encoding.
- Validation: `cargo test` passes; `test_eunoia_rare`'s Ethos test (both encodings) passes
  against `600aa0d` and against the merge snapshot.
