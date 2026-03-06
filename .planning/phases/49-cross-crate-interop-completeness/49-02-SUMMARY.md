---
phase: 49-cross-crate-interop-completeness
plan: 02
subsystem: analysis
tags: [nonnull, static-mut, data-race, unsafe, vcgen, smt]

requires:
  - phase: 48-advanced-ownership-borrows
    provides: UnsafeOperation enum and unsafe_analysis module
provides:
  - Ty::NonNull IR variant with null-check and alignment VC suppression
  - StaticMutAccess UnsafeOperation variant with DataRaceFreedom VCs
  - V100 diagnostic for mutable static synchronization
  - needs_data_race_check function for static mut analysis
affects: [50-stdlib-ptr-mem, 56-async-concurrency]

tech-stack:
  added: []
  patterns:
    - "NonNull type suppresses both null-check and alignment VCs via ptr_ty check"
    - "StaticMutAccess synchronized flag computed at MIR conversion time"

key-files:
  created:
    - crates/analysis/tests/nonnull_test.rs
    - crates/analysis/tests/static_mut_test.rs
  modified:
    - crates/analysis/src/ir.rs
    - crates/analysis/src/encode_sort.rs
    - crates/analysis/src/unsafe_analysis.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/monomorphize.rs
    - crates/driver/src/cex_render.rs
    - crates/driver/src/diagnostics.rs

key-decisions:
  - "NonNull encoded as BitVec(64) in SMT -- same as RawPtr but with null/alignment VC suppression"
  - "StaticMutAccess includes synchronized field computed during MIR conversion"
  - "DataRaceFreedom VC uses trivially-SAT assertion for unsynchronized accesses"

patterns-established:
  - "Ty::NonNull check in needs_null_check for VC suppression based on type"
  - "StaticMutAccess synchronized field for Mutex/RwLock guard scope detection"

requirements-completed: [COMPL-15, COMPL-17]

duration: 38min
completed: 2026-03-06
---

# Phase 49 Plan 02: NonNull Encoding + Static Mut Data-Race VCs Summary

**Ty::NonNull IR variant suppresses null/alignment VCs; StaticMutAccess generates DataRaceFreedom VCs with V100 diagnostic requiring Mutex/RwLock synchronization**

## Performance

- **Duration:** 38 min
- **Started:** 2026-03-06T06:00:15Z
- **Completed:** 2026-03-06T06:38:32Z
- **Tasks:** 2
- **Files modified:** 9

## Accomplishments
- Added Ty::NonNull(Box<Ty>) IR variant that encodes as BitVec(64) but suppresses null-check and alignment VCs
- Added StaticMutAccess UnsafeOperation variant with synchronized flag for Mutex/RwLock guard detection
- DataRaceFreedom VCs generated for unsynchronized mutable static accesses, suppressed when synchronized
- V100 diagnostic wired for mutable static synchronization failures
- 11 passing tests (6 NonNull + 5 static_mut)

## Task Commits

Each task was committed atomically:

1. **Task 1: Add Ty::NonNull IR variant + NonNull null-check suppression** - `50f7e95` (feat)
2. **Task 2: Add StaticMutAccess DataRaceFreedom VCs + V100 diagnostic** - `212b765` (feat)

_Note: Task 2 vcgen and test code were committed as part of a concurrent plan execution (49-01 f636cce) due to shared git workspace. The diagnostic update was committed in 212b765._

## Files Created/Modified
- `crates/analysis/src/ir.rs` - Added Ty::NonNull variant and StaticMutAccess UnsafeOperation variant
- `crates/analysis/src/encode_sort.rs` - NonNull encodes as BitVec(64); collect_from_type recurses into NonNull
- `crates/analysis/src/unsafe_analysis.rs` - needs_null_check returns false for NonNull; added needs_data_race_check
- `crates/analysis/src/vcgen.rs` - DataRaceFreedom VC generation for StaticMutAccess; NonNull in ty_alignment
- `crates/analysis/src/monomorphize.rs` - substitute_ty handles NonNull
- `crates/driver/src/cex_render.rs` - NonNull renders as pointer in counterexamples
- `crates/driver/src/diagnostics.rs` - V100 diagnostic text for DataRaceFreedom
- `crates/analysis/tests/nonnull_test.rs` - 6 tests for NonNull encoding and VC suppression
- `crates/analysis/tests/static_mut_test.rs` - 5 tests for static mut data-race VCs

## Decisions Made
- NonNull encoded as BitVec(64) in SMT (same representation as RawPtr) -- the difference is only in VC suppression, not in the SMT encoding itself
- StaticMutAccess carries a `synchronized: bool` field computed at MIR conversion time, rather than computing it during VCGen -- this keeps vcgen stateless
- DataRaceFreedom VC for unsynchronized access uses trivially-SAT assertion (BoolLit(true)) since the point is to flag the access, not prove a complex property

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Added StaticMutAccess to UnsafeOperation enum in Task 1**
- **Found during:** Task 1 (NonNull implementation)
- **Issue:** Adding NonNull to Ty required updating match arms on UnsafeOperation which would fail without StaticMutAccess
- **Fix:** Added StaticMutAccess variant early to keep compilation passing
- **Files modified:** crates/analysis/src/ir.rs, crates/analysis/src/unsafe_analysis.rs
- **Verification:** Both tasks compile and tests pass
- **Committed in:** 50f7e95 (Task 1 commit)

---

**Total deviations:** 1 auto-fixed (1 blocking)
**Impact on plan:** Minor ordering change -- StaticMutAccess IR added in Task 1 instead of Task 2 to maintain compilation. No scope creep.

## Issues Encountered
- Concurrent plan execution (49-01) picked up unstaged Task 2 files during its cargo fmt pass, resulting in some Task 2 code being committed under 49-01's commit hash (f636cce). All code is present and correct.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- NonNull and StaticMutAccess infrastructure ready for MIR converter wiring (when Rust nightly driver is available)
- V100 diagnostic pipeline complete for static mut data-race checking
- Ready for next plan in phase 49

---
*Phase: 49-cross-crate-interop-completeness*
*Completed: 2026-03-06*
