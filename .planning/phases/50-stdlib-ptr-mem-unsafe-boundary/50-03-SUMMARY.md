---
phase: 50-stdlib-ptr-mem-unsafe-boundary
plan: 03
subsystem: analysis
tags: [async, vcgen, diagnostics, W080, sequential-model, thread-spawn]

# Dependency graph
requires:
  - phase: 50-stdlib-ptr-mem-unsafe-boundary
    provides: async coroutine IR infrastructure (CoroutineInfo)
provides:
  - VcKind::AsyncSequentialModel variant for W080 warning
  - generate_async_model_vcs function detecting thread spawning in async fns
  - W080 diagnostic with Warning severity in driver
  - vc_kind_to_string mapping for async_sequential_model
affects: [56-async-concurrency-extensions]

# Tech tracking
tech-stack:
  added: []
  patterns: [warning-only VC with BoolLit(true) assertion, callee name pattern matching in basic block terminators]

key-files:
  created:
    - crates/analysis/tests/async_w080_test.rs
  modified:
    - crates/analysis/src/vcgen.rs
    - crates/driver/src/diagnostics.rs
    - crates/driver/src/callbacks.rs

key-decisions:
  - "Thread spawn detection via Terminator::Call callee name pattern matching rather than IR thread_spawns field -- covers tokio/rayon/crossbeam/async-std spawn patterns"
  - "Single W080 VC per function (deduplicated) with BoolLit(true) assertion -- warning-only, verification continues"

patterns-established:
  - "Warning-only VC pattern: BoolLit(true) assertion in Script, Warning severity in diagnostics, continues verification"

requirements-completed: [COMPL-25]

# Metrics
duration: 53min
completed: 2026-03-06
---

# Phase 50 Plan 03: W080 Async Sequential Model Warning Summary

**W080 diagnostic for async functions spawning threads -- sequential polling assumption documented via VcKind::AsyncSequentialModel warning VC**

## Performance

- **Duration:** 53 min
- **Started:** 2026-03-07T01:02:54Z
- **Completed:** 2026-03-07T01:55:57Z
- **Tasks:** 1
- **Files modified:** 4

## Accomplishments
- Added VcKind::AsyncSequentialModel variant for W080 async multi-thread warning
- Implemented generate_async_model_vcs detecting tokio::spawn, std::thread::spawn, rayon::spawn, crossbeam::scope in async function basic blocks
- Added W080 diagnostic with Warning severity, description text, and suggest_fix in driver
- Created 9 integration tests covering positive/negative cases, description text, VC distinctness, and spawn pattern variants

## Task Commits

Each task was committed atomically:

1. **Task 1: W080 async multi-thread sequential model warning** - `c83936d` (feat, analysis-side -- AsyncSequentialModel variant + generate_async_model_vcs + tests, included in 50-02 batch commit) + `5dde20c` (feat, driver-side -- diagnostics + callbacks)

Note: Analysis-side changes (vcgen.rs variant, generation function, integration tests) were committed alongside plan 50-02 formatting cleanup in commit c83936d. Driver-side changes (diagnostics, callbacks) committed separately in 5dde20c.

## Files Created/Modified
- `crates/analysis/src/vcgen.rs` - AsyncSequentialModel variant + generate_async_model_vcs function + wiring into generate_vcs_with_db
- `crates/analysis/tests/async_w080_test.rs` - 9 integration tests for W080 detection
- `crates/driver/src/diagnostics.rs` - W080 description, Warning severity, suggest_fix + 3 unit tests
- `crates/driver/src/callbacks.rs` - async_sequential_model string mapping + 1 unit test

## Decisions Made
- Thread spawn detection uses Terminator::Call callee name pattern matching (contains-based) rather than the existing IR `thread_spawns` field. This is because `thread_spawns` only tracks std::thread::spawn, while the plan requires detecting tokio::spawn, rayon::spawn, crossbeam::scope, and async_std::task::spawn patterns.
- Single W080 VC emitted per async function (not per spawn site) to avoid diagnostic noise.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Fixed pre-existing compile errors in unsafe_analysis.rs**
- **Found during:** Task 1 (initial compilation check)
- **Issue:** UnsafeOperation::TransmuteUnsafe and FfiCall variants added in plan 50-02 were missing from match arms in classify_provenance and needs_null_check
- **Fix:** Added match arms returning RawPtrProvenance::Unknown and false respectively
- **Files modified:** crates/analysis/src/unsafe_analysis.rs
- **Verification:** cargo check passes

**2. [Rule 3 - Blocking] Applied cargo fmt across codebase**
- **Found during:** Task 1 (pre-commit hook failure)
- **Issue:** Pre-existing formatting debt from plan 50-02 field additions (maybeuninit_ghost_states indentation across 60+ files)
- **Fix:** Ran cargo fmt --all
- **Verification:** rustfmt check passes in pre-commit hook

---

**Total deviations:** 2 auto-fixed (2 blocking)
**Impact on plan:** Both fixes necessary to unblock compilation and commit. No scope creep.

## Issues Encountered
- Analysis-side changes were committed as part of plan 50-02 batch commit (c83936d) due to `git add -A` during pre-commit hook workaround. Driver-side changes committed separately in 5dde20c.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- W080 diagnostic ready for Phase 56 (Async & Concurrency Extensions)
- Sequential polling assumption properly documented for users
- All verification continues under sequential model when W080 fires

---
*Phase: 50-stdlib-ptr-mem-unsafe-boundary*
*Completed: 2026-03-06*
