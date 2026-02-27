---
phase: 24-sep04-ghost-predicate-wiring
plan: 01
subsystem: verification
tags: [ghost-predicates, vcgen, parallel, tdd, sep-logic]

# Dependency graph
requires:
  - phase: 20-separation-logic
    provides: GhostPredicateDatabase, parse_spec_expr_with_db, extract_ghost_predicates
  - phase: 22-higher-order-closures
    provides: generate_vcs public API (unchanged)
provides:
  - "generate_vcs_with_db() public function in vcgen.rs accepting &GhostPredicateDatabase"
  - "VerificationTask.ghost_pred_db: Arc<GhostPredicateDatabase> field in parallel.rs"
  - "parse_spec() in vcgen.rs calls parse_spec_expr_with_db (ghost predicate expansion)"
  - "verify_single() calls generate_vcs_with_db() not generate_vcs()"
  - "callbacks.rs populates ghost_pred_db in VerificationTask at task push"
affects: [25-async-await, any phase using generate_vcs or VerificationTask]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Delegation shim: generate_vcs() delegates to generate_vcs_with_db with empty DB — backward-compatible API extension"
    - "Arc-once pattern: ghost_pred_db_arc created once before per-function loop, Arc::clone per task"
    - "Parameter threading: ghost_pred_db threaded through 5 private helper functions and 1 encoding helper"

key-files:
  created: []
  modified:
    - crates/driver/src/parallel.rs
    - crates/analysis/src/vcgen.rs
    - crates/driver/src/callbacks.rs

key-decisions:
  - "generate_vcs() made a backward-compatible delegation shim to generate_vcs_with_db with empty GhostPredicateDatabase — 6+ test sites unchanged"
  - "parse_spec() updated to call parse_spec_expr_with_db (not db-less parse_spec_expr) — ghost predicates now expand in all 13 parse_spec call sites"
  - "encode_callee_postcondition_assumptions also required ghost_pred_db threading (discovered during compiler error resolution)"
  - "generate_vcs_with_mode uses empty GhostPredicateDatabase — does not support ghost preds (out of scope for this plan)"

patterns-established:
  - "Ghost predicate threading: add ghost_pred_db param to internal helpers, pass through from generate_vcs_with_db"
  - "TDD with compile-enforced pre-commit hooks: write tests that express correct semantics, implement to pass"

requirements-completed: [SEP-04]

# Metrics
duration: 14min
completed: 2026-02-21
---

# Phase 24 Plan 01: Ghost Predicate DB Production Wiring Summary

**`GhostPredicateDatabase` threaded through `VerificationTask` → `generate_vcs_with_db` → `parse_spec` → `parse_spec_expr_with_db`, closing the SEP-04 gap where ghost predicates were extracted but silently ignored in production VcGen**

## Performance

- **Duration:** 14 min
- **Started:** 2026-02-21T02:34:34Z
- **Completed:** 2026-02-21T02:48:02Z
- **Tasks:** 1 (TDD: RED + GREEN + REFACTOR)
- **Files modified:** 3

## Accomplishments

- Added `ghost_pred_db: Arc<GhostPredicateDatabase>` field to `VerificationTask` struct in parallel.rs
- Added `generate_vcs_with_db()` as public API in vcgen.rs; made `generate_vcs()` delegate to it with empty DB (6+ existing test sites unaffected)
- Updated `parse_spec()` to call `parse_spec_expr_with_db` (not db-less `parse_spec_expr`) — ghost predicates now expand at all 13 call sites
- Updated `verify_single()` to call `generate_vcs_with_db(&task.ghost_pred_db)` instead of `generate_vcs()`
- Populated `ghost_pred_db_arc` once before per-function loop in callbacks.rs, `Arc::clone` per task
- All 1185 analysis lib tests and 92 driver lib tests pass; zero clippy warnings

## Task Commits

TDD execution (combined into single GREEN commit due to pre-commit hook requiring compilable code):

1. **RED + GREEN: Ghost predicate wiring** - `f4450ec` (feat: complete GREEN implementation with tests)

_Note: RED tests were written first but merged into GREEN commit due to pre-commit hook requiring zero compiler errors_

## Files Created/Modified

- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/parallel.rs` - Added `ghost_pred_db: Arc<GhostPredicateDatabase>` field; updated `verify_single()` to call `generate_vcs_with_db`; added sentinel test
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/vcgen.rs` - Added `generate_vcs_with_db()` public function; made `generate_vcs()` delegate; updated `parse_spec()` to call `parse_spec_expr_with_db`; threaded `ghost_pred_db` through 5 private helpers + `encode_callee_postcondition_assumptions`; added functional RED/GREEN test
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/callbacks.rs` - Added `ghost_pred_db_arc` before per-function loop; added `ghost_pred_db` field to `VerificationTask` push

## Decisions Made

- `generate_vcs()` made a backward-compatible delegation shim to `generate_vcs_with_db` with empty `GhostPredicateDatabase` — 6+ test sites unchanged
- `parse_spec()` updated to call `parse_spec_expr_with_db` (not db-less `parse_spec_expr`) — ghost predicates now expand in all 13 `parse_spec` call sites
- `encode_callee_postcondition_assumptions` also required `ghost_pred_db` threading (discovered during compiler error resolution — Rule 3 auto-fix)
- `generate_vcs_with_mode` uses empty `GhostPredicateDatabase` — does not support ghost predicates (out of scope)

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] encode_callee_postcondition_assumptions required ghost_pred_db parameter**
- **Found during:** GREEN phase (compiler error)
- **Issue:** `parse_spec(&post.raw, &callee_func_context, ghost_pred_db)` called inside `encode_callee_postcondition_assumptions` which didn't have `ghost_pred_db` in scope
- **Fix:** Added `ghost_pred_db: &GhostPredicateDatabase` parameter to `encode_callee_postcondition_assumptions` and its one call site in `generate_contract_vcs`
- **Files modified:** crates/analysis/src/vcgen.rs
- **Verification:** Compiler error resolved; all tests pass
- **Committed in:** f4450ec (GREEN commit)

---

**Total deviations:** 1 auto-fixed (1 blocking compiler error)
**Impact on plan:** Essential fix — compiler required it. No scope creep.

## Issues Encountered

- Pre-commit hook enforces `cargo clippy` passing — could not commit RED tests as a separate failing commit. Combined RED + GREEN into a single compilable commit. The RED test was written first and confirmed the correct semantics before implementation.
- `crate::ir::Spec` does not exist — actual type is `SpecExpr` (discovered during test writing; fixed immediately).

## Next Phase Readiness

- SEP-04 production wiring gap is now closed: ghost predicates extracted in `callbacks.rs` are now threaded into `parse_spec()` via `generate_vcs_with_db()`
- Ready for Phase 25 (ASY-01/02 async/await) or integration testing of ghost predicate expansion end-to-end

## Self-Check: PASSED

- FOUND: crates/driver/src/parallel.rs
- FOUND: crates/analysis/src/vcgen.rs
- FOUND: crates/driver/src/callbacks.rs
- FOUND: commit f4450ec (GREEN — ghost predicate wiring)

---
*Phase: 24-sep04-ghost-predicate-wiring*
*Completed: 2026-02-21*
