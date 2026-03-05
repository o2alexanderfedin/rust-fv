---
phase: 47-mir-coverage-hardening
plan: 03
subsystem: analysis
tags: [spec-validation, diagnostics, v080, vcgen, error-propagation]

requires:
  - phase: 47-01
    provides: "VCGen infrastructure with CastKind and alignment VCs"
provides:
  - "SpecValidationError type for spec parse failure propagation"
  - "V080 diagnostic formatting for invalid spec expressions"
  - "spec_errors field on FunctionVCs for driver-level error reporting"
  - "Fix suggestion heuristics for common spec errors"
affects: [48-advanced-ownership, 49-cross-crate-interop]

tech-stack:
  added: []
  patterns: [thread-local-error-collection, try-wrapper-pattern, v080-diagnostic-format]

key-files:
  created:
    - "crates/analysis/tests/spec_validation_tests.rs"
    - "crates/driver/tests/spec_diagnostic_e2e.rs"
  modified:
    - "crates/analysis/src/vcgen.rs"
    - "crates/driver/src/diagnostics.rs"
    - "crates/driver/src/callbacks.rs"
    - "crates/driver/src/parallel.rs"
    - "crates/driver/src/lib.rs"

key-decisions:
  - "Thread-local RefCell collector for spec errors avoids threading &mut Vec through 15+ helper functions"
  - "Box<SpecValidationError> in Result to satisfy clippy result_large_err lint"
  - "try_parse_spec wrapper returns Option for backward-compatible caller pattern"
  - "Duplicate spec errors from multiple VC generators accepted (same spec parsed by overflow + contract generators)"

patterns-established:
  - "Thread-local error collection: SPEC_ERRORS thread_local + collect_spec_error + drain_spec_errors pattern"
  - "V080 diagnostic format: error[V080] with source span and fix suggestions"

requirements-completed: [COMPL-06]

duration: 40min
completed: 2026-03-05
---

# Phase 47 Plan 03: Spec Validation Error Diagnostics Summary

**SpecValidationError propagation through VCGen with V080 rustc-style diagnostics for invalid spec expressions**

## Performance

- **Duration:** 40 min
- **Started:** 2026-03-05T21:37:34Z
- **Completed:** 2026-03-05T22:17:49Z
- **Tasks:** 2
- **Files modified:** 7

## Accomplishments
- Invalid `#[requires(...)]` and `#[ensures(...)]` expressions now produce structured `SpecValidationError` instead of silently returning `None`
- V080 diagnostic format with source file/line, error description, and fix suggestions
- Broken annotations are skipped while remaining valid contracts and code-level VCs continue verification
- Full driver pipeline integration: spec errors flow from VCGen through parallel verification to diagnostic output

## Task Commits

Each task was committed atomically:

1. **Task 1: Add SpecValidationError type and propagate through VCGen** - `35f1de5` (feat)
2. **Task 2: Wire spec errors to V080 diagnostics and E2E test** - `c7da913` (feat)

## Files Created/Modified
- `crates/analysis/src/vcgen.rs` - SpecValidationError/SpecErrorKind types, parse_spec returns Result, thread-local error collection, spec_errors field on FunctionVCs
- `crates/analysis/tests/spec_validation_tests.rs` - 5 unit tests for error propagation, continued VC generation, no regression
- `crates/driver/src/diagnostics.rs` - format_spec_validation_error, report_spec_validation_error, suggest_spec_fix
- `crates/driver/src/callbacks.rs` - Spec error reporting before SMT solving
- `crates/driver/src/parallel.rs` - spec_errors field on VerificationTaskResult
- `crates/driver/src/lib.rs` - Export diagnostics module for E2E testing
- `crates/driver/tests/spec_diagnostic_e2e.rs` - 4 E2E tests for V080 format, fix suggestions, continued verification

## Decisions Made
- Used thread-local RefCell collector pattern to avoid threading `&mut Vec<SpecValidationError>` through 15+ nested helper functions in vcgen.rs
- Boxed SpecValidationError in Result to satisfy clippy's result_large_err lint (128+ bytes)
- Created try_parse_spec/try_parse_spec_postcondition wrappers that return Option for backward compatibility with all existing callers
- Accepted duplicate spec errors when the same invalid spec is parsed by multiple VC generators (overflow + contract), since deduplication would add complexity without user-visible benefit

## Deviations from Plan

None - plan executed exactly as written.

## Issues Encountered
- Clippy required `const` initializer for thread_local and `Box<SpecValidationError>` for Result size -- fixed inline
- Multiple parse attempts of same invalid spec from different VC generators produce duplicate errors -- accepted as non-harmful

## User Setup Required

None - no external service configuration required.

## Next Phase Readiness
- Phase 47 complete (all 3 plans done): CastKind PtrToPtr + alignment VCs, match arm audit, spec validation diagnostics
- Ready for Phase 48 (Advanced Ownership & Borrows) or Phase 49 (Cross-Crate & Interop Completeness)

---
*Phase: 47-mir-coverage-hardening*
*Completed: 2026-03-05*
