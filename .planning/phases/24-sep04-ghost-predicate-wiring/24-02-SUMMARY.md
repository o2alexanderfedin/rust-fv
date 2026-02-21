---
phase: 24-sep04-ghost-predicate-wiring
plan: 02
subsystem: verification
tags: [ghost-predicates, driver, e2e, tdd, sep-logic, integration-test]

# Dependency graph
requires:
  - phase: 24-sep04-ghost-predicate-wiring
    plan: 01
    provides: generate_vcs_with_db, VerificationTask.ghost_pred_db, parse_spec_expr_with_db wiring
  - phase: 20-separation-logic
    provides: GhostPredicateDatabase, GhostPredicate types
provides:
  - "crates/driver/tests/ghost_predicate_e2e.rs: E2E integration test for SEP-04 production wiring"
  - "crates/driver/src/types.rs: VerificationResult moved to rustc-internal-free module"
  - "parallel module exported from lib.rs: enables driver integration tests"
affects: [any future driver integration tests needing parallel module]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "types.rs extraction: move shared types to rustc-internal-free module to enable lib export"
    - "requires+ensures pair in E2E tests: requires spec is assumed when proving ensures VC"
    - "VcKind::Precondition = call-site check (caller satisfies callee requires); not function's own requires"

key-files:
  created:
    - crates/driver/tests/ghost_predicate_e2e.rs
    - crates/driver/src/types.rs
  modified:
    - crates/driver/src/lib.rs
    - crates/driver/src/callbacks.rs
    - crates/driver/src/parallel.rs
    - crates/driver/src/main.rs

key-decisions:
  - "VcKind::Precondition is for call-site checks (caller satisfies callee requires) — function's own requires is an assumption in postcondition VCs; E2E tests must include both requires and ensures"
  - "VerificationResult moved to types.rs (rustc-free) to enable parallel module export from lib.rs for integration tests"
  - "callbacks.rs re-exports VerificationResult from types.rs (pub use crate::types::VerificationResult)"

patterns-established:
  - "Driver E2E test pattern: requires+ensures pair proves ghost predicate is assumed in VC generation"

requirements-completed: [SEP-04]

# Metrics
duration: 11min
completed: 2026-02-21
---

# Phase 24 Plan 02: Ghost Predicate E2E Driver Integration Test Summary

**Driver-level E2E integration tests validate SEP-04 ghost predicate production wiring end-to-end via `verify_functions_parallel()` — distinct from Phase 20 unit tests that bypass the driver pipeline**

## Performance

- **Duration:** 11 min
- **Started:** 2026-02-21T02:51:12Z
- **Completed:** 2026-02-21T03:02:14Z
- **Tasks:** 1 (TDD: RED + GREEN + REFACTOR)
- **Files created:** 2
- **Files modified:** 4

## Accomplishments

- Created `crates/driver/tests/ghost_predicate_e2e.rs` with 2 E2E integration tests:
  - `ghost_predicate_expands_to_vc_via_driver_path`: validates full pipeline from `VerificationTask` through `verify_functions_parallel()` → `generate_vcs_with_db()` → `parse_spec()` → `parse_spec_expr_with_db()` with ghost predicate expansion
  - `empty_ghost_pred_db_is_backward_compatible`: validates plain specs with empty DB still verify correctly
- Created `crates/driver/src/types.rs`: extracted `VerificationResult` from `callbacks.rs` into a rustc-internal-free module, enabling `parallel` module export from `lib.rs`
- Updated `lib.rs` to export `parallel`, `json_output`, and `types` modules
- Updated `callbacks.rs` to re-export `VerificationResult` from `types.rs`
- Updated `parallel.rs` to use `crate::types::VerificationResult`
- All 2 new E2E tests pass; zero regressions in full test suite (analysis + driver)

## Task Commits

1. **GREEN: E2E ghost predicate driver integration tests** - `4193276`
   (RED and GREEN combined into single compilable commit due to pre-commit hook)

## Files Created/Modified

- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/tests/ghost_predicate_e2e.rs` - 2 E2E integration tests exercising verify_functions_parallel with ghost predicate in requires
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/types.rs` - VerificationResult type extracted to rustc-free module for lib export
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/lib.rs` - Added parallel, json_output, types module exports
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/callbacks.rs` - Changed VerificationResult definition to re-export from types.rs
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/parallel.rs` - Updated to use crate::types::VerificationResult
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/main.rs` - Added mod types declaration

## Decisions Made

- `VcKind::Precondition` is for call-site checks — the function's own `requires` is an *assumption* in postcondition VCs, not a standalone VC. E2E tests must include both `requires` and `ensures` to trigger VC generation where the ghost predicate assumption matters.
- `VerificationResult` moved to `types.rs` (rustc-free) to enable `parallel` module export from `lib.rs` for integration tests — `callbacks.rs` has rustc dependencies (`rustc_driver`, `rustc_middle`) that cannot be exported from the lib crate
- `callbacks.rs` now re-exports `VerificationResult` from `types.rs` preserving public API

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] `parallel` module not exported from lib.rs**
- **Found during:** RED phase (compiler error)
- **Issue:** `crates/driver/src/lib.rs` only exported `cache`, `cex_render`, and `invalidation`. The `parallel` module needed for E2E tests was not exported.
- **Fix:** Added `parallel` and `json_output` exports to `lib.rs`, but `parallel.rs` uses `crate::callbacks::VerificationResult` and `callbacks` depends on rustc internals — cannot be exported from lib crate.

**2. [Rule 3 - Blocking] `VerificationResult` in `callbacks.rs` has transitive rustc dependencies**
- **Found during:** RED phase (8 compiler errors when adding callbacks to lib.rs)
- **Issue:** `callbacks.rs` imports `rustc_driver`, `rustc_middle`, `rustc_interface` — only linkable as a rustc driver plugin, not as a normal library.
- **Fix:** Extracted `VerificationResult` (which has zero rustc dependencies) to `types.rs`, updated `callbacks.rs` to re-export from `types.rs`, updated `parallel.rs` to use `crate::types::VerificationResult`, added `mod types` to `main.rs`. Non-architectural: `VerificationResult` was co-located with rustc code only by convention.

**3. [Rule 3 - Blocking] Test design: `requires`-only function generates zero VCs**
- **Found during:** RED phase (test assertions fail with `task_results.is_empty()`)
- **Issue:** `generate_contract_vcs` returns early if `func.contracts.ensures.is_empty()`. A function with only `requires` (no `ensures`) generates zero VCs — nothing to check. The plan's test design assumed a precondition VC would be generated for the function's own `requires`.
- **Fix:** Updated test functions to include both `requires: is_positive(_1)` (ghost pred) and `ensures: _1 > 0` (provable from expanded ghost pred). The postcondition VC is generated, the ghost predicate assumption is added, and Z3 verifies it. This correctly tests the wiring end-to-end.
- **Architecture note documented in test:** `VcKind::Precondition` = call-site check; function's own `requires` = assumption in postcondition VCs.

---

**Total deviations:** 3 auto-fixed (2 compiler errors, 1 test design fix)
**Impact on plan:** All fixes required; no scope creep.

## Issues Encountered

- Pre-commit hook enforces `cargo clippy` passing — RED test written first but combined with GREEN into single compilable commit.
- `parallel` module's dependency chain on `callbacks` (rustc internals) required `VerificationResult` extraction to make driver integration testing possible.

## Next Phase Readiness

- SEP-04 gap is now fully closed with E2E validation: ghost predicates extracted in `callbacks.rs` are threaded into `parse_spec()` via `generate_vcs_with_db()`, proven by integration tests going through `verify_functions_parallel()`
- Phase 25 (ASY-01/02 async/await) is the next pending milestone

## Self-Check: PASSED

- FOUND: crates/driver/tests/ghost_predicate_e2e.rs
- FOUND: crates/driver/src/types.rs
- FOUND: crates/driver/src/lib.rs (modified)
- FOUND: crates/driver/src/callbacks.rs (modified)
- FOUND: crates/driver/src/parallel.rs (modified)
- FOUND: crates/driver/src/main.rs (modified)
- FOUND: commit 4193276 (GREEN — E2E ghost predicate driver integration tests pass)

---
*Phase: 24-sep04-ghost-predicate-wiring*
*Completed: 2026-02-21*
