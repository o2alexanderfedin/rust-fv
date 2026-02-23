---
phase: 23-async-await
plan: "04"
subsystem: async-vcgen-tdd
tags: [async, tdd, integration-test, z3, qf-lia, asy-01, asy-02]
dependency_graph:
  requires: [23-01, 23-02, 23-03]
  provides: [async-vc-tdd-validation]
  affects: [spec_parser, async_vcgen]
tech_stack:
  added: [async_verification integration test suite]
  patterns: [QF_LIA axiom injection, Z3 solver check_sat, TDD RED/GREEN cycle]
key_files:
  created:
    - crates/analysis/tests/async_verification.rs
  modified:
    - crates/analysis/src/async_vcgen.rs
    - crates/analysis/src/spec_parser.rs
decisions:
  - parse_spec_expr_qf_lia uses in_int_mode=true for QF_LIA-compatible integer term generation
  - convert_path allows free SMT constant references in int_mode (for awaited_result_N constants)
  - Axiom injection pattern (clone commands without check-sat, add code constraint, add check-sat) re-used from hof_closures.rs pattern
  - BV mode strict variable checking preserved (in_int_mode=false path unchanged)
metrics:
  duration: 716
  completed: 2026-02-22
  tasks_completed: 1
  files_modified: 3
---

# Phase 23 Plan 04: ASY-01 and ASY-02 TDD Integration Test Suite Summary

**One-liner:** QF_LIA async integration test suite (6 Z3 tests) proving ASY-01 postcondition and ASY-02 state invariant verification, with auto-fix for BitVec/QF_LIA incompatibility in spec parser.

## What Was Built

### `crates/analysis/tests/async_verification.rs` (NEW)

6-test TDD integration test suite following the `hof_closures.rs` pattern.

**ASY-01 tests (postcondition):**

1. `async_postcondition_verified` — inject code path `_0 = x+1`, assert `ensures(_0 == x+1)` → UNSAT (proven)
2. `async_postcondition_violated` — inject code path `_0 = x*2`, assert `ensures(_0 == x*3)` → SAT (violated)
3. `async_requires_precondition` — with `x>=0` precondition + `_0=x`: UNSAT; without precondition: SAT

**ASY-02 tests (state invariant):**

4. `async_state_invariant_verified` — 2 Yield states, inject `counter >= 5`, all 4 VCs → UNSAT
5. `async_state_invariant_violated_at_suspension` — 1 Yield state, `counter > 0` invariant, no constraint → SAT; verifies `poll_iter` present and kind is `AsyncStateInvariantSuspend`
6. `async_state_invariant_resumption_references_await_result` — `awaited_result_0 >= 0` invariant, `awaited_result_0` is free constant → SAT

**Helper infrastructure:**
- `solver_or_skip()` — creates `Z3Solver` or panics with `Z3_NOT_AVAILABLE`
- `commands_without_check_sat()` — strips trailing `(check-sat)` for axiom injection
- `build_script()` — constructs `Script` from `Vec<Command>`
- `make_async_func()` — minimal async `Function` factory with params, persistent_fields, states, contracts
- `yield_state()` / `return_state()` — `CoroutineState` constructors

### `crates/analysis/src/spec_parser.rs` (MODIFIED — Rule 1 auto-fix)

**Bug found:** `parse_spec_expr_with_db` generates BitVec terms (`bvmul`, `bvsge`) incompatible with QF_LIA scripts used in async VCs.

**Fix 1:** Added `parse_spec_expr_qf_lia()` public function that calls `convert_expr_with_db` with `in_int_mode: true`, producing integer arithmetic terms (`IntMul`, `IntGe`, etc.) compatible with QF_LIA.

**Fix 2:** `convert_path()` now accepts `in_int_mode` parameter. When `in_int_mode = true`, unknown identifiers (not in `func.params`/`func.locals`) are treated as free SMT constant references (e.g., `awaited_result_0`). When `in_int_mode = false` (BV mode), strict variable checking is preserved — `parse_unknown_variable_returns_none` test continues to pass.

### `crates/analysis/src/async_vcgen.rs` (MODIFIED — Rule 1 auto-fix)

Changed import and all spec parsing calls from `parse_spec_expr_with_db` to `parse_spec_expr_qf_lia` to generate QF_LIA-compatible integer terms in the async VC scripts.

## Test Results

```
cargo test -p rust-fv-analysis --test async_verification
running 6 tests
test async_postcondition_verified                              ... ok
test async_postcondition_violated                              ... ok
test async_requires_precondition                              ... ok
test async_state_invariant_verified                           ... ok
test async_state_invariant_violated_at_suspension             ... ok
test async_state_invariant_resumption_references_await_result ... ok

test result: ok. 6 passed; 0 failed
```

```
cargo test --workspace → 0 failed (1200+ tests all pass, no regressions)
cargo clippy --workspace -- -D warnings → clean
cargo fmt --all --check → clean
```

## Verification

- `test_async_postcondition_verified` → UNSAT (postcondition proven)
- `test_async_postcondition_violated` → SAT (AsyncPostcondition kind counterexample)
- `test_async_state_invariant_verified` → all 4 VCs UNSAT
- `test_async_state_invariant_violated_at_suspension` → AsyncStateInvariantSuspend SAT; `poll_iter` present
- `test_async_state_invariant_resumption_references_await_result` → `awaited_result_0` declared free, SAT

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] BitVec/QF_LIA incompatibility in async VC spec parsing**
- **Found during:** Task 1 (RED phase, test execution)
- **Issue:** `parse_spec_expr_with_db` uses BV mode by default, generating `bvmul`/`bvsge` terms. QF_LIA scripts reject BitVec sorts — Z3 returned `(error "unknown constant bvmul (Int (_ BitVec 32))")`.
- **Fix:** Added `parse_spec_expr_qf_lia()` to spec_parser.rs with `in_int_mode: true`; updated `convert_path()` to accept `in_int_mode` and allow free SMT constants in integer mode; updated `async_vcgen.rs` to use the new function.
- **Files modified:** `crates/analysis/src/spec_parser.rs`, `crates/analysis/src/async_vcgen.rs`
- **Commits:** 87022e6 (RED), 10db604 (GREEN)

## Commits

| Hash | Message |
|------|---------|
| 87022e6 | test(23-04): add failing ASY-01 and ASY-02 integration tests |
| 10db604 | feat(23-04): all async/await integration tests pass — ASY-01 and ASY-02 complete |

## Self-Check: PASSED
