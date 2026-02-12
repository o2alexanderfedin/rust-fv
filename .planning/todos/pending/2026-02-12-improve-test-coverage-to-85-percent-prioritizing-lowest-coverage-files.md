---
created: 2026-02-12T05:25:32.370Z
title: Improve test coverage to 85%+ prioritizing lowest coverage files
area: testing
files:
  - crates/driver/src/callbacks.rs:38.87%
  - crates/driver/src/cargo_verify.rs:78.19%
  - crates/analysis/src/simplify.rs:79.91%
  - crates/analysis/src/encode_term.rs:73.88%
  - crates/analysis/src/vcgen.rs:79.38%
  - crates/analysis/src/monomorphize.rs:82.78%
  - crates/analysis/src/encode_quantifier.rs:83.48%
  - crates/macros/src/lib.rs:73.33%
---

## Problem

Current workspace coverage is 84.37% lines (up from 70.10% after first round of improvements). The target is 85%+ overall. Several files remain below 85%:

- `callbacks.rs` (38.87%) - mostly rustc-dependent `after_analysis`, but testable portions exist
- `encode_term.rs` (73.88%) - many uncovered Term encoding branches
- `macros/lib.rs` (73.33%) - proc macro expansion paths
- `cargo_verify.rs` (78.19%) - `run_cargo_verify` and `read_crate_name` untestable without cargo
- `vcgen.rs` (79.38%) - complex VC generation paths
- `simplify.rs` (79.91%) - uncovered simplification rules
- `monomorphize.rs` (82.78%) - generic substitution edge cases
- `encode_quantifier.rs` (83.48%) - quantifier encoding edge cases

Files at 0% (`main.rs`, `mir_converter.rs`, `parallel.rs`) are fully rustc-dependent and cannot be unit tested.

## Solution

Prioritize by impact (lowest coverage first, excluding untestable files):
1. `encode_term.rs` (73.88%) - add tests for uncovered Term variant encoding
2. `macros/lib.rs` (73.33%) - add proc macro expansion tests
3. `cargo_verify.rs` (78.19%) - max out testable parse functions
4. `vcgen.rs` (79.38%) - test uncovered VC generation paths
5. `simplify.rs` (79.91%) - test uncovered simplification rules
6. `monomorphize.rs` (82.78%) - test generic substitution edge cases
7. `encode_quantifier.rs` (83.48%) - test remaining quantifier paths

Note: `callbacks.rs` at 38.87% drags down overall average but most code requires rustc context. Focus on the analysis crate files where unit testing is straightforward.
