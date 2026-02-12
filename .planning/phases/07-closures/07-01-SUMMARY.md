---
phase: 07-closures
plan: 01
subsystem: verification-core
tags: [closure-verification, ir-types, smt-encoding, defunctionalization-prep]

# Dependency graph
requires:
  - phase: 06-recursion
    provides: VcKind pattern for new verification condition types
provides:
  - Closure IR types (ClosureTrait enum, ClosureInfo struct, Ty::Closure variant)
  - Closure analysis infrastructure (detect, classify, validate FnOnce single-call)
  - SMT datatype encoding for closure environments
affects: [07-02-defunctionalization, 07-03-closure-verification]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "ClosureTrait enum for Fn/FnMut/FnOnce classification"
    - "ClosureInfo struct with env_fields, params, return_ty, trait_kind"
    - "Closure environments encoded as SMT datatypes (same pattern as structs)"
    - "VcKind::ClosureContract for closure-specific diagnostics"

key-files:
  created:
    - crates/analysis/src/closure_analysis.rs
  modified:
    - crates/analysis/src/ir.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/encode_term.rs
    - crates/analysis/src/encode_sort.rs
    - crates/driver/src/callbacks.rs
    - crates/driver/src/diagnostics.rs

key-decisions:
  - "Closure environments encoded as SMT datatypes with mk-{closure_name} constructor and {closure_name}-{field_name} selectors"
  - "Closure parameters and return type stored in ClosureInfo but NOT part of environment datatype (environment is state, signature is type)"
  - "FnOnce validation function provided for future use (detects multiple calls to FnOnce closures)"

patterns-established:
  - "Pattern: New IR types follow existing derive patterns (Debug, Clone, PartialEq, Eq for ClosureInfo like Ty)"
  - "Pattern: VcKind enum extended by adding new variant + updating driver diagnostics/callbacks"
  - "Pattern: SMT encoding follows struct pattern (datatype with constructor + field selectors)"

# Metrics
duration: 7min
completed: 2026-02-12
---

# Phase 7 Plan 01: Closure IR and Analysis Infrastructure Summary

**Closure IR types (Fn/FnMut/FnOnce classification, environment encoding) with detection, classification, and SMT datatype encoding**

## Performance

- **Duration:** 7 min
- **Started:** 2026-02-12T10:07:28Z
- **Completed:** 2026-02-12T10:15:00Z (approx)
- **Tasks:** 2 (both TDD)
- **Files modified:** 9

## Accomplishments
- ClosureTrait enum with Fn/FnMut/FnOnce variants for Rust closure trait classification
- ClosureInfo struct with environment fields, parameters, return type, and trait kind
- Ty::Closure variant in IR type system with is_closure() helper
- closure_analysis module with extract_closure_info, detect_closure_calls, classify_closure_trait, validate_fnonce_single_call
- SMT datatype encoding for closure environments (mk-{closure_name} constructor, field selectors)
- VcKind::ClosureContract for closure-specific verification condition diagnostics

## Task Commits

Each task was committed atomically following TDD (test-first):

1. **Task 1: Add closure types to IR** - `e8cc3ec` (feat)
   - TDD: 6 tests written first (RED), then implementation (GREEN)
   - ClosureTrait enum, ClosureInfo struct, Ty::Closure variant, AggregateKind::Closure, VcKind::ClosureContract
   - Updated encode_term.rs and encode_sort.rs for new variants
   - Updated driver callbacks and diagnostics

2. **Task 2: Create closure_analysis module and extend encode_sort** - `8afb64e` (feat)
   - TDD: 13 tests total (10 closure_analysis + 3 encode_sort)
   - closure_analysis.rs with ClosureCallSite, extraction, detection, classification, FnOnce validation
   - Ty::Closure handling in collect_from_type (SMT datatype with environment fields)

## Files Created/Modified
- `crates/analysis/src/closure_analysis.rs` - Closure detection and analysis infrastructure (NEW)
- `crates/analysis/src/ir.rs` - ClosureTrait enum, ClosureInfo struct, Ty::Closure variant
- `crates/analysis/src/vcgen.rs` - VcKind::ClosureContract variant
- `crates/analysis/src/encode_term.rs` - AggregateKind::Closure encoding (mk-{name} constructor)
- `crates/analysis/src/encode_sort.rs` - Ty::Closure → Sort::Datatype, collect_from_type extension
- `crates/analysis/src/lib.rs` - Register closure_analysis module
- `crates/driver/src/callbacks.rs` - VcKind::ClosureContract JSON serialization
- `crates/driver/src/diagnostics.rs` - VcKind::ClosureContract human-readable description

## Decisions Made
- **Closure environments as SMT datatypes:** Follows struct encoding pattern (mk-{closure_name} constructor, {closure_name}-{field_name} selectors). Environment is the captured state; parameters/return type are signature metadata.
- **ClosureInfo in Ty::Closure boxed:** Prevents recursive type size explosion (ClosureInfo contains Vec<Ty>).
- **FnOnce validation function provided:** validate_fnonce_single_call detects multiple calls to FnOnce closures (unsound). Available for future defunctionalization phase but not yet integrated into VCGen.
- **Closure classification via callee name:** classify_closure_trait parses "call_once"/"call_mut"/"call" from function names. Matches Rust's trait hierarchy (FnOnce is most specific, Fn is most general).

## Deviations from Plan

None - plan executed exactly as written. All TDD tests passed on first GREEN phase implementation.

## Issues Encountered

**Minor: Clippy empty-line-after-doc-comments warning**
- **Issue:** closure_analysis.rs had empty line after module-level doc comments
- **Resolution:** Changed `///` (item-level) to `//!` (module-level) doc comments to match Rust convention
- **Files:** crates/analysis/src/closure_analysis.rs
- **Verification:** Clippy passes with 0 warnings

**Minor: rustfmt formatting adjustments**
- **Issue:** Long lines in closure_analysis tests and encode_sort tests
- **Resolution:** Ran cargo fmt --all to apply standard formatting
- **Verification:** cargo fmt --all -- --check passes

## User Setup Required

None - no external service configuration required.

## Next Phase Readiness
- **Ready for 07-02 (Defunctionalization):** Closure IR types and analysis functions available
- **Ready for 07-03 (Closure Verification):** VcKind::ClosureContract ready for closure contract VCs
- **Test coverage:** 19 new tests (6 IR types, 10 closure_analysis, 3 encode_sort), all passing
- **Total workspace tests:** 752 passing (increased from 739)
- **No blockers:** All dependencies satisfied

---
*Phase: 07-closures*
*Completed: 2026-02-12*

## Self-Check: PASSED

**Files Verified:**
- ✓ crates/analysis/src/closure_analysis.rs exists
- ✓ .planning/phases/07-closures/07-01-SUMMARY.md exists

**Commits Verified:**
- ✓ e8cc3ec (Task 1: IR types)
- ✓ 8afb64e (Task 2: closure_analysis module)
- ✓ fdc3145 (SUMMARY.md and STATE.md)

**Tests Verified:**
- ✓ 19 closure tests passing (6 IR + 10 closure_analysis + 3 encode_sort)
- ✓ All 752 analysis crate tests passing
- ✓ 0 clippy warnings, 0 formatting issues
