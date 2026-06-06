# Checking CPC proofs

Carcara can check proofs in the CPC (Cooperating Proof Calculus) format, which is the format
produced by cvc5 by default when passing `--dump-proofs`. This is done by translating the CPC
proof into an Alethe proof, which is then checked with the regular Alethe checker. The
translation mirrors cvc5's own internal-to-Alethe proof conversion.

## Generating checkable CPC proofs

CPC proofs normally omit the conclusions of most proof steps, since the Ethos checker can compute
them from the rules. Carcara does not implement the Eunoia semantics of the CPC rules, so it
requires the conclusions to be present. To produce a checkable proof, pass the
`--proof-print-conclusion` option to cvc5:

```bash
cvc5 --dump-proofs --proof-print-conclusion problem.smt2 > proof.cpc
```

## Checking

Use the `--proof-format cpc` flag of the `check` subcommand:

```bash
carcara check --proof-format cpc --allow-int-real-subtyping --rare-file rewrites.eo proof.cpc problem.smt2
```

CPC proofs use cvc5's RARE rewrite rules (e.g. `bool-and-de-morgan`), which are translated into
Alethe `rare_rewrite` steps. Checking these steps requires the RARE rules file, given with
`--rare-file` (the `rewrites.eo` file in the repository root contains the rules needed for the
AUFNIRA fragment).

Steps using cvc5's `trust` rule, as well as the few rules that are not yet supported by the
translation, are translated into `hole` steps, in which case the proof is reported as "holey"
(valid with holes).

The translated Alethe proof can be inspected with the `parse` subcommand:

```bash
carcara parse --proof-format cpc --translate --allow-int-real-subtyping proof.cpc problem.smt2
```

## Validating against the cvc5 regressions

The script `scripts/validate-cpc.sh` runs cvc5 on its own regression tests (restricted to the
AUFNIRA fragment) and checks every generated proof with Carcara:

```bash
scripts/validate-cpc.sh ~/cvc5/test/regress/cli/regress0
```

## Known limitations

- The initial target is the AUFNIRA fragment: bitvectors, strings, datatypes, etc. are not yet
  supported.
- Operators that have no Carcara representation (e.g. `^`, `iand`) cause parse errors.
- Problems using symbol overloading or higher-order features are not supported (cvc5's own
  Alethe output does not support higher-order logic either).
- The `skolemize` rule and alpha equivalence with clashing variable names are translated as
  holes.
