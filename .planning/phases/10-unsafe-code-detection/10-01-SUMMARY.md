---
phase: 10-unsafe-code-detection
plan: 01
subsystem: verification-infrastructure
tags: [unsafe, memory-safety, ir, proc-macros, diagnostics, vcs]

# Dependency graph
requires:
  - phase: 09-lifetime-reasoning
    provides: BorrowInfo, LifetimeParam, prophecy encoding for &mut T verification
provides:
  - Unsafe code IR types (RawPtrProvenance, UnsafeBlockInfo, UnsafeOperation, UnsafeContracts)
  - VcKind::MemorySafety for unsafe-specific verification diagnostics
  - Proc macros for unsafe contracts (#[unsafe_requires], #[unsafe_ensures], #[trusted])
  - Function struct extensions with unsafe tracking fields
  - Memory safety diagnostic infrastructure
affects: [10-02-unsafe-detection, 10-03-unsafe-e2e, memory-model, heap-verification]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - Unsafe IR extension pattern (follows lifetime/closure/trait IR patterns)
    - Safety contract proc macros following spec_attribute pattern
    - VcKind extensions for domain-specific diagnostics

key-files:
  created:
    - crates/analysis/tests/unsafe_ir_tests.rs
  modified:
    - crates/analysis/src/ir.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/encode_sort.rs
    - crates/macros/src/lib.rs
    - crates/driver/src/diagnostics.rs
    - crates/driver/src/callbacks.rs

key-decisions:
  - "UnsafeContracts uses Default derive (not manual impl) per clippy recommendation"
  - "RawPtrProvenance tracks pointer origin for null-check optimization (FromRef pointers guaranteed non-null)"
  - "VcKind::MemorySafety produces warnings (not errors) per USF-06 requirement"
  - "ptr_addr_sort() returns 64-bit bitvector sort for pointer addresses"
  - "#[trusted] macro embeds 'rust_fv::trusted' (documented as #[verifier::trusted] for users)"
  - "Function struct extended with 4 unsafe fields (unsafe_blocks, unsafe_operations, unsafe_contracts, is_unsafe_fn)"

patterns-established:
  - "Unsafe IR types placed after ReborrowChain, before ClosureInfo (ordered by phase)"
  - "Memory safety diagnostics provide three-tier explanation (detection, basic checks, trust boundaries)"
  - "Unsafe contract proc macros follow spec_attribute pattern (no special parsing needed)"

# Metrics
duration: 11min
completed: 2026-02-13
---

# Phase 10 Plan 01: Unsafe Code IR Foundation Summary

**Unsafe code IR types (RawPtrProvenance, UnsafeBlockInfo, UnsafeOperation, UnsafeContracts), VcKind::MemorySafety diagnostics, and three proc macros (#[unsafe_requires], #[unsafe_ensures], #[trusted]) for memory safety verification infrastructure**

## Performance

- **Duration:** 11 min 13 sec
- **Started:** 2026-02-13T05:37:55Z
- **Completed:** 2026-02-13T05:49:08Z
- **Tasks:** 2 (both TDD)
- **Files modified:** 32
- **Tests added:** 19 (13 IR unit tests + 6 proc macro tests)
- **Total workspace tests:** 2,011 (up from 1,998)

## Accomplishments

- Extended IR with four new unsafe types for memory safety tracking
- Extended Function struct with unsafe-specific fields (235+ construction sites updated)
- Added VcKind::MemorySafety with comprehensive diagnostic support
- Implemented three new proc macros for unsafe safety contracts
- All tests passing, 0 clippy warnings, 0 formatting issues

## Task Commits

Each task was committed atomically following TDD protocol:

1. **Task 1: Add unsafe IR types, VcKind::MemorySafety, and Function extensions (TDD)** - `cd4910d` (feat)
   - Added RawPtrProvenance, UnsafeBlockInfo, UnsafeOperation, UnsafeContracts types
   - Extended Function with unsafe_blocks, unsafe_operations, unsafe_contracts, is_unsafe_fn
   - Added VcKind::MemorySafety variant
   - Added ptr_addr_sort() helper
   - Added memory safety diagnostics (description, suggestions, help messages)
   - Updated 235+ Function construction sites across workspace
   - Added 13 unit tests in unsafe_ir_tests.rs

2. **Task 2: Add unsafe contract proc macros (TDD)** - `b4f5fdf` (feat)
   - Added #[unsafe_requires(expr)] proc macro
   - Added #[unsafe_ensures(expr)] proc macro
   - Added #[trusted] proc macro
   - Implemented trusted_impl() helper
   - Added 6 comprehensive unit tests

## Files Created/Modified

### Created
- `crates/analysis/tests/unsafe_ir_tests.rs` - Unit tests for unsafe IR types and VcKind::MemorySafety (13 tests)

### Modified (Key Files)
- `crates/analysis/src/ir.rs` - Added 4 new types, extended Function struct
- `crates/analysis/src/vcgen.rs` - Added VcKind::MemorySafety variant
- `crates/analysis/src/encode_sort.rs` - Added ptr_addr_sort() helper
- `crates/macros/src/lib.rs` - Added 3 proc macros and trusted_impl()
- `crates/driver/src/diagnostics.rs` - Added memory safety diagnostics (description, suggestions, help messages)
- `crates/driver/src/callbacks.rs` - Added MemorySafety to vc_kind_to_string
- `crates/driver/src/mir_converter.rs` - Updated Function construction with unsafe fields
- 24+ test/benchmark files - Updated Function construction sites

## Decisions Made

1. **UnsafeContracts Default derive:** Changed from manual Default impl to #[derive(Default)] per clippy::derivable_impls lint. Vec and bool already have proper defaults.

2. **RawPtrProvenance for optimization:** Tracks pointer origin (FromRef, FromInt, Unknown) to enable null-check optimization. Pointers derived from safe references are guaranteed non-null.

3. **VcKind::MemorySafety as warnings:** Memory safety VCs produce warnings (not errors) per USF-06 requirement. Unsafe code detection is advisory, not blocking.

4. **ptr_addr_sort() 64-bit:** Raw pointer addresses represented as 64-bit bitvectors for address arithmetic and null checks.

5. **#[trusted] naming:** Proc macro named `#[trusted]` (Rust limitation - no `::` in macro names), documented as `#[verifier::trusted]` for users. Embeds `rust_fv::trusted` doc attribute.

6. **Function struct extension pattern:** Added 4 unsafe fields after reborrow_chains, maintaining chronological IR ordering (Phase 9 → Phase 10).

## Deviations from Plan

None - plan executed exactly as written.

## Issues Encountered

1. **Indentation formatting after bulk update:** The script to add unsafe fields to 235+ Function construction sites initially added incorrect indentation (extra 4 spaces). Resolved by running `cargo fmt --all` which normalized all indentation automatically.

2. **LifetimeContext false positive:** The bulk update script incorrectly added unsafe fields to LifetimeContext struct (which has a `reborrow_chains` field but is NOT a Function). Manually reverted those 4 lines. Future automation should match `Function {` context, not just `reborrow_chains:`.

3. **UnsafeContracts PartialEq limitation:** Initially derived `PartialEq, Eq` but removed because `Vec<SpecExpr>` requires SpecExpr to implement Eq, which it doesn't (intentionally - SpecExpr contains String which is compared structurally, not by value in verification context). Matched Contracts pattern (no Eq derivation).

## User Setup Required

None - no external service configuration required.

## Next Phase Readiness

**Ready for Phase 10 Plan 02 (Unsafe Block Detection):**
- IR types available for MIR analysis
- VcKind::MemorySafety ready for VC generation
- Proc macros ready for contract parsing

**Blocked on:** None

**Concerns:** None - foundation solid for detection and verification phases

---
*Phase: 10-unsafe-code-detection*
*Completed: 2026-02-13*
