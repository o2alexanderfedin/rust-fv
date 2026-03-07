---
phase: 50-stdlib-ptr-mem-unsafe-boundary
plan: 02
subsystem: analysis
tags: [ffi, transmute, maybeuninit, unsafe, vcgen, ghost-state, smt]

requires:
  - phase: 48-advanced-ownership-borrows
    provides: "RefCellGhostState pattern for ghost boolean tracking"
  - phase: 49-cross-crate-interop-completeness
    provides: "NonNull encoding pattern and UnsafeOperation enum extension pattern"
provides:
  - "VcKind::FfiOpaqueCallee (V110) for uncontracted extern C calls"
  - "VcKind::TransmuteSafety (V120) with size/alignment/validity VCs for transmute"
  - "VcKind::MaybeUninitSafety with ghost is_initialized tracking"
  - "UnsafeOperation::TransmuteUnsafe and FfiCall variants"
  - "MaybeUninitGhostState struct and Function field"
  - "generate_ffi_vcs, generate_transmute_vcs, generate_maybeuninit_vcs functions"
affects: [50-03, 51, 54]

tech-stack:
  added: []
  patterns: ["Ghost boolean state tracking for MaybeUninit (follows RefCellGhostState)", "UnsafeOperation-driven VC generation for transmute and FFI"]

key-files:
  created:
    - "crates/analysis/tests/ffi_opaque_test.rs"
    - "crates/analysis/tests/transmute_test.rs"
    - "crates/analysis/tests/maybeuninit_test.rs"
  modified:
    - "crates/analysis/src/ir.rs"
    - "crates/analysis/src/vcgen.rs"
    - "crates/analysis/src/unsafe_analysis.rs"
    - "crates/driver/src/diagnostics.rs"
    - "crates/driver/src/callbacks.rs"

key-decisions:
  - "Transmute size VCs use static ty_size_bytes helper with direct UNSAT/SAT encoding (no SMT arithmetic needed)"
  - "FFI opaque callee VCs driven by UnsafeOperation::FfiCall has_contract flag (not call site scanning)"
  - "MaybeUninit ghost state follows RefCellGhostState pattern: linear block walk, per-local tracking"
  - "MaybeUninitSafety generates VCs for both safe (UNSAT) and unsafe (SAT) cases for completeness"
  - "FfiOpaqueCallee and TransmuteSafety get Warning severity (like AlignmentSafety V070)"

patterns-established:
  - "Ghost boolean tracking: MaybeUninitGhostState follows RefCellGhostState linear walk pattern"
  - "UnsafeOperation-driven VCs: generate_ffi_vcs and generate_transmute_vcs scan unsafe_operations list"

requirements-completed: [LANG-15, LANG-16]

duration: 37min
completed: 2026-03-07
---

# Phase 50 Plan 02: FFI V110 + Transmute V120 + MaybeUninit Ghost State Summary

**FFI extern "C" calls get V110 opaque callee warnings, transmute gets size/alignment/validity VCs (V120), and MaybeUninit tracks initialization via ghost booleans**

## Performance

- **Duration:** 37 min
- **Started:** 2026-03-07T01:02:57Z
- **Completed:** 2026-03-07T01:40:28Z
- **Tasks:** 2
- **Files modified:** 85 (primarily due to MaybeUninitGhostState field addition across all Function constructions)

## Accomplishments
- FFI extern "C" function calls without contracts generate V110 FfiOpaqueCallee warning VCs; contracted calls are suppressed
- transmute operations generate TransmuteSafety VCs: size check (UNSAT for matching sizes, SAT for mismatch), alignment check (bvsmod), and validity check (bool 0/1 constraint)
- MaybeUninit ghost state tracks initialization: uninit() sets false, write()/new() sets true, assume_init() asserts true
- V110 and V120 diagnostics fully wired in driver (vc_kind_description, suggest_fix, vc_kind_to_string, Warning severity)
- 13 new tests across 3 test files (2 FFI + 4 transmute + 7 MaybeUninit)

## Task Commits

Each task was committed atomically:

1. **Task 1: FFI V110 + transmute V120 VCs + IR extensions** - `c83936d` (feat)
2. **Task 2: MaybeUninit ghost state tracking tests** - `b6ebb40` (test)

## Files Created/Modified
- `crates/analysis/src/ir.rs` - Added TransmuteUnsafe, FfiCall UnsafeOperation variants; MaybeUninitGhostState struct; maybeuninit_ghost_states field on Function; has_maybeuninit_locals() helper
- `crates/analysis/src/vcgen.rs` - Added VcKind::FfiOpaqueCallee, TransmuteSafety, MaybeUninitSafety; generate_ffi_vcs, generate_transmute_vcs, generate_maybeuninit_vcs, ty_size_bytes, extract_maybeuninit_method functions; wired into generate_vcs_with_db
- `crates/analysis/src/unsafe_analysis.rs` - Extended classify_provenance and needs_null_check match arms for new UnsafeOperation variants
- `crates/driver/src/diagnostics.rs` - V110 and V120 descriptions, Warning severity, suggest_fix entries
- `crates/driver/src/callbacks.rs` - vc_kind_to_string mappings for new VcKind variants
- `crates/analysis/tests/ffi_opaque_test.rs` - FFI opaque callee V110 tests (2 tests)
- `crates/analysis/tests/transmute_test.rs` - Transmute safety V120 tests (4 tests)
- `crates/analysis/tests/maybeuninit_test.rs` - MaybeUninit ghost state tests (7 tests)

## Decisions Made
- Transmute size VCs use static ty_size_bytes helper returning Option<u64> for concrete types; None for ADTs/generics. Direct UNSAT/SAT encoding avoids SMT arithmetic overhead.
- FFI opaque callee detection is driven by UnsafeOperation::FfiCall with has_contract flag, rather than scanning call sites at VC generation time. This pushes classification to the MIR conversion phase.
- MaybeUninit ghost state uses the same linear block walk pattern as RefCell (Phase 48). Branch join analysis is deferred (consistent with RefCell decision).
- MaybeUninitSafety generates VCs for both safe (UNSAT, initialized) and unsafe (SAT, uninitialized) assume_init calls. This provides explicit verification evidence in both cases.
- FfiOpaqueCallee and TransmuteSafety get Warning severity (like AlignmentSafety V070), not Error, since they are informational diagnostics.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Fixed pre-existing clippy doc_lazy_continuation warning**
- **Found during:** Task 1 (commit hook)
- **Issue:** Pre-existing `doc_lazy_continuation` clippy warning in vcgen.rs line 6133 blocked commit
- **Fix:** Added two-space indent to doc comment continuation line
- **Files modified:** crates/analysis/src/vcgen.rs
- **Verification:** clippy passes clean
- **Committed in:** c83936d (Task 1 commit)

**2. [Rule 3 - Blocking] Fixed clippy len_zero warning in transmute_test.rs**
- **Found during:** Task 1 (commit hook)
- **Issue:** `transmute_vcs.len() >= 1` flagged by clippy as `len_zero`
- **Fix:** Changed to `!transmute_vcs.is_empty()`
- **Files modified:** crates/analysis/tests/transmute_test.rs
- **Verification:** clippy passes clean
- **Committed in:** c83936d (Task 1 commit)

---

**Total deviations:** 2 auto-fixed (2 blocking)
**Impact on plan:** Both auto-fixes required to pass pre-commit hooks. No scope creep.

## Issues Encountered
None

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- FFI, transmute, and MaybeUninit VC generation complete
- V110 and V120 diagnostics fully wired
- Ready for plan 50-03 (remaining Phase 50 items)
- MaybeUninit MIR detection (populating maybeuninit_ghost_states from rustc MIR) is a future driver-side task

---
*Phase: 50-stdlib-ptr-mem-unsafe-boundary*
*Completed: 2026-03-07*
