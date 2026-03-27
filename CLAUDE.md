# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Carcara is a proof checker and elaborator for SMT proofs in the Alethe format, written in Rust. Published at TACAS 2023.

## Build & Development Commands

```bash
# Build
cargo build

# Run tests (use --release, some tests are slow otherwise)
cargo test --release

# Run a single test
cargo test --release <test_name>

# Lint (CI enforces warnings as errors)
cargo clippy --all-targets --all-features --tests --no-deps -- -D warnings

# Format
cargo fmt --check   # check only
cargo fmt            # fix

# Run CLI
cargo run -- check <proof.alethe> <problem.smt2>
cargo run -- elaborate <proof.alethe> <problem.smt2>
```

Requires Rust 1.87+ (pinned in `rust-toolchain.toml`).

## Workspace Structure

Three crates in the workspace:

- **`carcara/`** — Core library: parsing, checking, elaboration
- **`cli/`** — CLI binary (clap v3), depends on `carcara`
- **`test-generator/`** — Proc macro (`#[from_dir(...)]`) that generates test functions from `.alethe` proof files

## Architecture (carcara crate)

The pipeline is: **parse → check → elaborate**.

- **`parser/`** — Lexer + parser for Alethe proofs and SMT-LIB problems. `mod.rs` is the largest module.
- **`ast/`** — Core data structures: `Term`, `ProofNode`, `Proof`, `Sort`. Includes term pooling (`pool/`) for memory-efficient term sharing, polyequality checking (`polyeq.rs`), and substitution.
- **`checker/`** — Proof verification. `rules/` contains one file per rule family (resolution, simplification, linear_arithmetic, bitvectors, strings, quantifier, etc.). Supports parallel checking via `parallel/`.
- **`elaborator/`** — Transforms proofs by adding detail (filling holes, uncrowding resolution steps, elaborating polyequality).
- **`resolution.rs`** / **`drup.rs`** — Resolution and DRUP proof utilities.
- **`slice.rs`** — Proof slicing (extracting subproofs).

## Key Conventions

- **Custom `Rc`**: `std::rc::Rc::new` is banned via clippy. Use the project's `Rc` type from `ast/rc.rs`.
- **`CarcaraResult<T>`**: The standard result alias used throughout.
- **Undocumented unsafe blocks are denied** (`clippy::undocumented_unsafe_blocks`).
- **Term pooling**: Terms are interned via `PrimitivePool`/`AdvancedPool` — always create terms through the pool, never construct them directly.

## Testing

Integration tests live in `carcara/tests/`. The `test-generator` proc macro auto-generates test cases from `.alethe` files in `carcara/tests/rules/` — add a new proof file to add a new test case.
