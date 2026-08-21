# Lifting repeated closed steps

**Branch:** `inv/hoist-pass` (commit `2d443a0e`) — **merged into `coreAlethe`**.
**Verdict:** a new first pass in the elaboration pipelines. On its own it removes **17.0%** of the
steps of the evaluation corpus and **34.7%** of the steps of cvc5's QF_LIA/QF_LRA/QF_UFLIA proofs,
before any elaboration runs. End to end the core pipeline's output is **10.8%** smaller,
elaboration is 2% faster and checking 5.8% faster. Every proof re-checks with the same verdict; no
proof grows and none becomes holey.

## The observation

The [derivation-sharing note](./2026-08-18-share-derivations.md) removed the duplication that the
`core` pass *creates*. The same duplication is already in the solver's output. Over the cvc5
proofs of QF_LIA, QF_LRA and QF_UFLIA, **half of all premise-free steps are exact duplicates**:
2 300 197 steps with 1 153 597 distinct conclusions — `evaluate` 244 698 → 24 668 distinct (90%),
`poly_simp` 236 766 → 64 396 (73%), `poly_simp_rel` 114 015 → 31 866 (72%), `rare_rewrite`
132 543 → 57 881 (56%). Within one scope there is essentially none of it, so it can only be removed
by hoisting.

## The pass

`carcara/src/elaborator/hoist.rs`, run as `--pipeline hoist` and first in the default pipeline. It
derives each distinct closed conclusion once, at depth 0, and re-points every other use at it.
Since premises are `Rc` pointers in a `ProofNodeForest`, replacing a node redirects every consumer,
and a use from inside a subproof becomes an ordinary outbound premise. The name is `hoist` rather
than `share` because "sharing" already means term/DAG sharing (`:named`, `--print-with-sharing`)
here and in SMT-LIB.

A step is a candidate only if its derivation is

- **closed** — every node reachable from it is a `Step` with empty `:discharge` and no
  `previous_step`, at either the candidate's own depth (a step the hoist copies) or depth 0 (a step
  already visible everywhere). One predicate excludes assumptions, enclosing-scope steps and
  subproofs, and forces the leaves to be premise-free;
- **context-free** — no clause or argument term of a step that moves has a free variable that an
  anchor in scope binds;
- **hole-free** — no step uses `hole`, `lia_generic`, a rule in `--allowed-rules`, or a rule the
  checker does not know.

**The key is the conclusion clause alone.** Closedness makes the derivation prove its clause
outright, so two closed derivations of the same clause are interchangeable whatever they contain.
That argument is about the shape of the subgraph, not about its provenance, so it holds for the
solver's own steps exactly as it did for the `core` pass's freshly built ones.

**One guard the `core` pass does not need.** Its candidates are its own output; these are steps in
arbitrary positions, so the *replacement* direction needs the context check too, not just the
hoisting direction. An anchor may shadow a problem symbol — `(anchor :args ((x Int)))` over a
`(declare-const x Int)` — and then a step inside concluding `(= x x)` and a step outside concluding
the syntactically identical `(= x x)` are about different variables. A candidate whose clause
mentions a bound name is rejected before the memo is consulted.

**Hole-freeness is what keeps the pass from laundering a hole.** A proof can contain both a real
derivation of a clause and a `hole`-like step concluding it; replacing the former by the latter
would silently turn a valid proof holey. A holey derivation is neither recorded nor replaced, so
holeyness moves in neither direction and the pass is verdict-preserving by construction. Preferring
the hole-free candidate would also be sound and would *remove* holes, but it would make the
validation an inequality rather than an equality; it was not taken.

**When to lift.** A derivation already at depth 0 is recorded as it is. One inside a subproof is
copied out as soon as it is seen *when there is a single step to copy* — then every reference is
re-pointed at the copy and the original is left with none, so the proof keeps exactly the size it
had. Running bottom-up makes that the common case, since the premises have already been lifted.
When several steps would have to be copied, some may still be used where they are, so the
derivation is held aside and lifted only once a second step needs it, as `core`'s sharing does. On
every corpus proof the "dropped" count equals the step reduction exactly, and nothing grows.

## Supporting changes

- `mutate_impl` records a subproof's steps of smaller depth — the ones a pass moved out of it — as
  outbound premises, so later traversals visit them under the right context and the printer emits
  them before the anchor. Every non-last command of a subproof sits in its `extra_steps`, so
  without this a hoisted step would be elaborated under the subproof's context by the next pass.
  `core`'s sharing already created this situation; it was invisible only because nothing that runs
  after it reads the context.
- `ContextStack` maintains the set of names its anchors bind as they are pushed and popped, and
  answers `binds_nothing()`/`binds(name)` in O(1). Reading it off the stack on demand was
  quadratic: on a QF_LIA veriT proof with 503 anchors nested ~94 deep, the per-step calls summed to
  17.9 M stack frames and 74.8 M name clones, and the pass took **241 s** where the rest of the run
  took 4.
- `PrimitivePool::free_vars_ref` returns the cached free-variable set instead of a copy.
- The memo is keyed by a 64-bit digest of the clause with a collision bucket, not by the clause: a
  hash map over clauses re-reads every key when it grows, and clauses in this corpus reach 96 000
  literals.

After these, the pass costs 0.45 s on that 493 k-step proof, and the full pipeline on it runs in
82.5 s against the baseline's 81.6 s.

## Numbers

`--pipeline hoist` alone, steps before → after, over the 948 proofs that produce output:

| logic/solver | steps in | steps out | reduction | best file |
|---|---:|---:|---:|---:|
| QF_LIA/cvc5 | 1 698 540 | 891 423 | **47.5%** | 53.1% |
| QF_LRA/cvc5 | 927 242 | 575 262 | **38.0%** | 55.0% |
| QF_UFLIA/cvc5 | 2 463 472 | 1 854 638 | **24.7%** | 46.1% |
| UFLIA/cvc5 | 210 199 | 170 899 | 18.7% | 43.4% |
| QF_UF/cvc5 | 4 045 789 | 3 675 798 | 9.1% | 12.2% |
| UF/cvc5 | 36 916 | 34 953 | 5.3% | 25.5% |
| all veriT | 3 421 713 | 3 420 069 | 0.05% | 7.1% |
| **total** | **12 803 871** | **10 623 042** | **17.0%** | |

The cvc5 reduction over the three arithmetic logics is **34.7%**, above the ~22% estimate, because
that estimate counted only premise-free steps whereas the pass also lifts short closed chains built
on them. veriT is flat — its proofs have almost no cross-subproof duplication — but never negative.

Full pipeline, `hoist polyeq core local core reordering` against `polyeq core local core
reordering`: output 17 496 788 → 15 610 826 steps (**−10.8%**), elaboration 610.5 s → 598.2 s
(−2.0%), checking 222.8 s → 210.0 s (−5.8%, up to −23% on QF_LRA/cvc5). No file's output grew.

## Validation

- **Pass alone.** All 983 proofs: the baseline binary checking the input versus checking the pass's
  output — 890 valid→valid, 58 holey→holey, **0 mismatches**. The 35 invalid/error files fail to
  elaborate on the baseline binary too, since `elaborate` checks first.
- **Full pipelines.** Both outputs re-checked with the *baseline* binary at elaborated granularity:
  888 valid|valid, 58 holey|holey, 36 elab-failed both, 1 invalid|invalid (both runs hit the 300 s
  cap and truncated). **0 mismatches; nothing became holey.**
- Idempotence: a second run reports `lifted 0, dropped 0` and leaves the step-id sequence
  identical.
- `cargo test --release`, `cargo fmt`, `cargo clippy --release --all-targets` clean. Seven tests in
  `carcara/tests/test_hoist.rs`: shared across subproof scopes and landing at the top level; not
  shared when it depends on an assumption; not shared under a shadowing anchor; a `hole`-rooted
  duplicate never replacing a real derivation and vice versa; the same for an `--allowed-rules`
  rule; positional steps never lifted; idempotence.

## Caveat

The pass deletes derivations, so if an input proof is invalid and a bogus step's clause is also
proved correctly elsewhere, the output could check where the input did not. This is not reachable
through the CLI — `check_and_elaborate` checks the input first — but it is the reason not to relax
the guard to "replace any step whose clause is in the memo".
