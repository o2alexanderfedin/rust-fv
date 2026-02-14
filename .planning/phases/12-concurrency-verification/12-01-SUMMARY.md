---
phase: 12-concurrency-verification
plan: 01
subsystem: analysis
tags: [concurrency, threads, interleaving, verification, proc-macros, bounded-model-checking]

# Dependency graph
requires:
  - phase: 11-floating-point-verification
    provides: VcKind infrastructure, diagnostic patterns
provides:
  - Concurrency IR types (ThreadSpawn, AtomicOp, SyncOp, AtomicOrdering, ConcurrencyConfig)
  - VcKind variants for concurrency (DataRaceFreedom, LockInvariant, Deadlock, ChannelSafety)
  - Thread interleaving enumeration with bounded context switches
  - Proc macros for concurrency annotations (#[lock_invariant], #[verify(concurrent)])
affects: [12-02, 12-03]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - Bounded model checking via recursive interleaving enumeration
    - Context switch counting (thread changes after first step)
    - TDD for concurrency algorithms (8 thread_encoding tests)

key-files:
  created:
    - crates/analysis/src/concurrency/mod.rs
    - crates/analysis/src/concurrency/thread_encoding.rs
  modified:
    - crates/analysis/src/ir.rs (4 VcKind variants)
    - crates/analysis/src/vcgen.rs (4 VcKind variants)
    - crates/macros/src/lib.rs (lock_invariant, verify macros)
    - crates/driver/src/callbacks.rs (VcKind serialization)
    - crates/driver/src/diagnostics.rs (VcKind descriptions + suggestions)
    - ~60 files with Function construction updates

key-decisions:
  - "Context switch counted on any thread change after first step (simpler than tracking thread completion)"
  - "Empty thread set returns 1 empty interleaving (consistent base case)"
  - "Max switches=0 with multiple threads produces 0 complete interleavings (cannot schedule all threads without switching)"
  - "Proc macro #[verify] accepts comma-separated options: concurrent, threads=N, switches=M"

patterns-established:
  - "TDD for complex algorithms: write failing tests, implement, verify, commit atomically"
  - "Deviation Rule 3 handling: auto-fix blocking compilation issues (missing Function fields)"

# Metrics
duration: 18min
completed: 2026-02-14
---

# Phase 12 Plan 01: Concurrency Type System and Interleaving Infrastructure

**Concurrency IR types, 4 new VcKind variants with diagnostics, bounded thread interleaving enumeration, and proc macros for lock invariants and verification config**

## Performance

- **Duration:** 18 min
- **Started:** 2026-02-14T08:23:09Z
- **Completed:** 2026-02-14T08:42:01Z
- **Tasks:** 2 (both TDD)
- **Files modified:** 40+ (39 staged + concurrency module created)

## Accomplishments

- Added 4 new VcKind variants (DataRaceFreedom, LockInvariant, Deadlock, ChannelSafety) with full diagnostic support
- Implemented bounded thread interleaving enumeration with recursive exploration and context switch pruning
- Created concurrency module with ThreadState, Interleaving, InterleavingEvent types
- Added proc macros #[lock_invariant(expr)] and #[verify(concurrent, threads=N, switches=M)]
- Updated 60+ Function construction sites across codebase with 5 new concurrency fields

## Task Commits

Each task was committed atomically:

1. **Task 1: Add VcKind variants and thread encoding tests (TDD RED+GREEN)** - `efd01fa` (test)
   - Added 4 VcKind variants to vcgen.rs
   - Created concurrency/thread_encoding module with bounded interleaving enumeration
   - Wrote 12 tests (8 thread_encoding + 4 VcKind) - all passing
   - Fixed 60+ Function construction sites (deviation Rule 3)
   - Added basic VcKind serialization and descriptions to driver

2. **Task 2: Add proc macros for concurrency annotations** - `346e088` (feat)
   - Implemented #[lock_invariant(expr)] proc macro
   - Implemented #[verify(concurrent, threads=N, switches=M)] proc macro with parser
   - Added 3 new macro tests - all passing

**Total:** 2 task commits

## Files Created/Modified

**Created:**
- `crates/analysis/src/concurrency/mod.rs` - Concurrency module with re-exports
- `crates/analysis/src/concurrency/thread_encoding.rs` - Thread interleaving enumeration (408 lines: 165 impl + 243 tests)

**Modified (key):**
- `crates/analysis/src/vcgen.rs` - Added 4 VcKind variants + tests
- `crates/analysis/src/ir.rs` - Fixed duplicate concurrency fields in test
- `crates/analysis/src/lib.rs` - Registered concurrency module
- `crates/macros/src/lib.rs` - Added lock_invariant, verify macros + verify_impl + tests
- `crates/driver/src/callbacks.rs` - VcKind serialization
- `crates/driver/src/diagnostics.rs` - VcKind descriptions + suggestions
- `crates/driver/src/mir_converter.rs` - Function construction fix

**Modified (bulk):**
- 33 analysis source files - Function construction updates
- 7 test files - Function construction updates
- 2 bench files - Function construction updates

## Decisions Made

1. **Context switch semantics:** ANY thread change counts as a switch (after first step), regardless of whether the previous thread completed. This is simpler and matches the three_threads test expectation (3 threads, 1 step each = 2 switches minimum).

2. **Zero-switch bound behavior:** With max_switches=0 and multiple threads, we produce 0 complete interleavings (cannot execute all threads without switching). This is correct but may need documentation for users.

3. **Empty thread set:** Returns 1 empty interleaving (consistent base case for recursive enumeration).

4. **Proc macro parsing:** verify macro parses comma-separated options using syn::punctuated::Punctuated, allowing flexible ordering: #[verify(concurrent)], #[verify(threads=4, switches=8)], or #[verify(concurrent, threads=4, switches=8)].

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] IR types pre-existing but Function sites not updated**
- **Found during:** Task 1 compilation
- **Issue:** IR types (ThreadSpawn, AtomicOp, SyncOp, etc.) and Function fields were already added to ir.rs, but 60+ Function construction sites across the codebase hadn't been updated with the 5 new concurrency fields (thread_spawns, atomic_ops, sync_ops, lock_invariants, concurrency_config), causing compilation errors.
- **Fix:** Systematically added the 5 concurrency fields to all Function struct initializations across analysis crate (src/, tests/, benches/), driver (mir_converter.rs), and one unsafe_verification test file.
- **Files modified:** 40+ files (see Files Created/Modified section)
- **Verification:** `cargo build` succeeds, all 937 analysis tests pass
- **Committed in:** efd01fa (Task 1 commit)

**2. [Rule 1 - Bug] Duplicate concurrency fields in ir.rs test**
- **Found during:** Task 1 compilation
- **Issue:** test_function_with_concurrency_fields in ir.rs had duplicate field definitions (lines 1751-1755 defined thread_spawns/atomic_ops/etc twice)
- **Fix:** Removed duplicate field definitions, kept only the second set with actual test data
- **Files modified:** crates/analysis/src/ir.rs
- **Verification:** Test compiles and passes
- **Committed in:** efd01fa (Task 1 commit)

---

**Total deviations:** 2 auto-fixed (1 blocking issue, 1 bug)
**Impact on plan:** Both deviations necessary for compilation. The bulk Function field updates were tedious but straightforward. No scope creep.

## Issues Encountered

None - plan executed smoothly after auto-fixing the Function construction sites.

## Testing Summary

- **New tests:** 15 total (12 in Task 1: 8 thread_encoding + 4 VcKind, 3 in Task 2: macros)
- **Total workspace tests:** ~2,164 (937 analysis + driver + macros)
- **Failures:** 0
- **Clippy warnings:** 0
- **Formatting issues:** 0 (after cargo fmt)

## Next Phase Readiness

Ready for Plan 02 (Happens-Before and VC Generation):
- ✅ IR types for ThreadSpawn, AtomicOp, SyncOp in place
- ✅ VcKind variants for data races, lock invariants, deadlocks, channel safety
- ✅ Thread interleaving enumeration infrastructure working
- ✅ Proc macros ready for extracting lock invariants and concurrency config
- ✅ Driver diagnostics ready to report concurrency failures

**Blockers:** None

**Concerns:** None - foundation is solid for VCGen implementation in Plans 02-03.

---
*Phase: 12-concurrency-verification*
*Plan: 01*
*Completed: 2026-02-14*
