# Vendored egglog 0.4.0

A copy of the `egglog` 0.4.0 crate from crates.io (`src/`, `build.rs`,
`Cargo.toml`, `LICENSE`, `README.md`, `CHANGELOG.md`; the crate's own tests
and benches are left out and the manifest's test/bench targets dropped), used
through `[patch.crates-io]` in the top-level `Cargo.toml`.

Changes against the released crate:

- `serialize-one-extractor.patch` (`src/serialize.rs`): `EGraph::serialize`
  built a fresh `Extractor` — a cost computation over the whole e-graph — for
  every primitive value it printed, so serializing an e-graph was quadratic
  in its size (about 2 ms per node on Carcara's hole e-graphs, 10 s for a
  5,500-node graph).  One extractor is now built lazily per `serialize`
  call.  Carcara's post-hoc reconstruction snapshots the e-graph through
  `serialize`, and this cost was where most holes died under a 30 s budget.
- `join-order-connected.patch` (`src/gj.rs`): the generic join's variable
  order.  A query is joined one variable at a time, each bound to the values
  every atom mentioning it allows given the variables bound before it, and
  egglog picks the next variable greedily by (number of atoms it occurs in,
  atoms shared with the variables already chosen, smallest table).  So a
  variable that occurs often goes first even when none of its atoms mentions
  a bound variable, and then it ranges over a whole column.  Carcara's
  encoding wraps every pattern leaf in `Mk`, one atom `(Mk leaf _)` per use of
  the leaf, so a rule's leaves occur most and were bound one after the other
  before any atom related them: on RARE's `ite-eq` (`C` in 4 atoms, `t1` and
  `t2` in 3) over 1,788 `Mk` nodes, 1,686 x 1,788 x 1,788 partial bindings,
  and the hole's worker died in that join.  The key now starts with whether
  the variable shares an atom with one already bound, so after the first
  variable the join walks along the pattern's atoms.  The matches are the
  same in any order; what changes is the work to enumerate them.
