# Proof elaboration
Besides checking a proof, Carcara is also capable of _proof elaboration_. You can elaborate a proof
file using the `elaborate` command:
```
carcara elaborate example.smt2.alethe example.smt2
```

This will check and elaborate the given proof, and print the elaborated proof to the standard
output. By default, Carcara will print proofs using term sharing, i.e., using the `(! ... :named
...)` syntax. You can change this behavior with the `--no-print-with-sharing`/`-v` option.

Many of the same options used in the `check` command also apply to the `elaborate` command. See
`carcara elaborate --help` for more details.

## Elaboration pipeline
The specific way in which Carcara elaborates the proof is controlled via a `--pipeline` option.
This takes a series of _elaboration passes_, and will apply them in the given order. The possible
elaboration passes are:
- `hoist`
- `deep-hoist`
- [`polyeq`](./elaboration/polyeq.md)
- [`lia-generic`]()
- [`core`](./elaboration/core.md)
- [`local`](./elaboration/local.md)
- [`uncrowd`](./elaboration/uncrowding.md)
- [`reordering`](./elaboration/reordering.md)
- [`hole`]()

`hoist` lifts every repeated *closed* derivation — one that proves its conclusion outright, with no
assumption, no discharge and no dependence on an enclosing scope — to depth 0, and re-points every
other use at the single copy. Solvers emit a great deal of such reasoning more than once, and almost
always in different subproofs, so nothing that stays inside one scope can remove it.

`deep-hoist` does that and, in addition, replaces a *lemma scope* by the single clausal step that
proves what the scope discharges. A solver that proves a lemma by scoping assumes its hypotheses,
derives the conclusion under them, and discharges the block into one clause; but the hypotheses are
already spelled out, negated, in that clause, and Alethe usually has a premise-free rule concluding
exactly it. So

```
(anchor :step t7)
(assume t7.a0 (= a b))
(assume t7.a1 (= b c))
(step t7.t0 (cl (= a c)) :rule trans :premises (t7.a0 t7.a1))
(step t7 (cl (not (= a b)) (not (= b c)) (= a c)) :rule subproof :discharge (t7.a0 t7.a1))
```

becomes one step:

```
(step t7 (cl (not (= a b)) (not (= b c)) (= a c)) :rule eq_transitive)
```

The pass never inspects what a scope contains: it offers the discharged clause to a battery of
premise-free rules and keeps the first the *checker* accepts, so the replacement is sound whatever
the scope was doing internally. Two rules whose arguments the clause determines are tried with those
arguments synthesized — `and_pos`/`or_neg` (the index of the selected conjunct or disjunct) and
`la_generic` (one Farkas coefficient per literal, all but the first inferred by the checker). This
matters almost exclusively for cvc5, which scopes constantly; veriT barely uses the construct.

By default, Carcara will attempt to apply all of these except `core` and `deep-hoist` in the listed
order. The
`core` pass — which reduces every rule in the *reducible* tier of the
[core classification](./core.md) to the core fragment — is opt-in; a typical invocation is:
```
carcara elaborate example.smt2.alethe --pipeline polyeq core local core uncrowd reordering
```

### Example
The following command will elaborate the given proof file with the `uncrowd` and `polyeq`
elaboration passes, in that order:
```
carcara elaborate example.smt2.alethe --pipeline uncrowd polyeq
```
Note that, if you pass a positional argument (e.g. the proof filename) after the pipeline argument,
you need an extra `--` argument to denote the end of the pipeline list:
```
carcara elaborate --pipeline uncrowd polyeq -- example.smt2.alethe
```
