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
`--rare-file` (the `rewrites.eo` file converted from cvc5's RARE rules, the same one used for
checking cvc5's Alethe proofs).

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

The translation mirrors cvc5's own Alethe output, including the short-circuits of its
post-processor: the implication `(=> (and F1 ... Fn) G)` derived from a scope is not rebuilt
when the consumer only needs the clause `(cl (not (and F1 ... Fn)) G)` again, a `not_and` step
over such a clause is replaced by a resolution over the scope's subproof clause, and a
top-level step concluding the same literals as an earlier top-level subproof reuses that
subproof. The steps these short-circuits bypass are pruned from the translated proof.

## Known limitations

- The supported fragment is AUFBVNIRA: strings, datatypes, floating points, etc. are not yet
  supported.
- Problems using symbol overloading or higher-order features are not supported (cvc5's own
  Alethe output does not support higher-order logic either).
- cvc5's total division and modulo operators are mapped to the SMT-LIB partial ones, so an
  `evaluate` step over a division by a literal zero (e.g. `(= (div_total 0 0) 0)`) cannot be
  checked.
- Congruence steps whose terms change structure when applications of defined functions are
  beta-reduced during parsing are translated as holes.
