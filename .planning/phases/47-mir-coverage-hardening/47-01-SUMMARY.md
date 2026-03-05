---
phase: 47-mir-coverage-hardening
plan: 01
subsystem: analysis
tags: [cast-kind, alignment, ptr-to-ptr, smt, vcgen, pointer-safety]

requires:
  - phase: 28-smt-vcgen-completeness
    provides: "CastKind enum with 5 variants and encode_cast infrastructure"
  - phase: 29-to-fix-the-identified-gaps
    provides: "MIR converter mapping Rust CastKinds to IR CastKind::Pointer"
provides:
  - "CastKind::PtrToPtr (renamed from Pointer) with alignment VC side-effect"
  - "VcKind::AlignmentSafety for pointer alignment verification"
  - "generate_alignment_vcs: bvsmod-based alignment check for PtrToPtr casts"
  - "5 structurally distinct CastKind SMT encodings verified by tests"
affects: [47-mir-coverage-hardening, 50-stdlib-ptr-mem]

tech-stack:
  added: []
  patterns: ["Alignment VC via bvsmod on 64-bit bitvector pointers"]

key-files:
  created:
    - "crates/analysis/tests/cast_kind_tests.rs"
    - "crates/driver/tests/alignment_e2e.rs"
  modified:
    - "crates/analysis/src/ir.rs"
    - "crates/analysis/src/encode_term.rs"
    - "crates/analysis/src/vcgen.rs"
    - "crates/driver/src/callbacks.rs"
    - "crates/driver/src/diagnostics.rs"
    - "crates/driver/src/mir_converter.rs"

key-decisions:
  - "Alignment VC uses bvsmod (signed modulo) on 64-bit bitvector for SMT-LIB compatibility"
  - "AlignmentSafety gets Warning severity (V070) matching MemorySafety pattern"
  - "PtrToPtr alignment VC is a side-effect in vcgen, not in encode_cast return value"
  - "ty_alignment returns 1 for unknown types (no VC emitted)"

patterns-established:
  - "Alignment VCs generated per-statement by scanning for CastKind::PtrToPtr with align > 1"
  - "encode_ptr_to_ptr_cast is identity; alignment check emitted at call site in vcgen"

requirements-completed: [COMPL-02, COMPL-03]

duration: 3253s
completed: 2026-03-05
---

# Phase 47 Plan 01: CastKind PtrToPtr Rename & Alignment Safety Summary

**Renamed CastKind::Pointer to PtrToPtr, added VcKind::AlignmentSafety with bvsmod-based alignment VCs, verified all 5 CastKind variants produce structurally distinct SMT output**

## Performance

- **Duration:** 54 min
- **Started:** 2026-03-05T20:37:39Z
- **Completed:** 2026-03-05T21:31:52Z
- **Tasks:** 2
- **Files modified:** 8

## Accomplishments

- CastKind::Pointer renamed to CastKind::PtrToPtr across entire codebase (ir.rs, encode_term.rs, vcgen.rs, mir_converter.rs)
- VcKind::AlignmentSafety added with V070 diagnostic code, Warning severity, suggest_fix
- generate_alignment_vcs implemented: scans for PtrToPtr casts, emits bvsmod-based alignment check for target types with alignment > 1
- 17 unit tests verify all 5 CastKind variants produce structurally distinct SMT output
- 5 E2E tests verify alignment VC generation for u32 (4-byte), u64 (8-byte), u8 (no VC), script structure, and multiple casts

## Task Commits

1. **Task 1: Rename CastKind::Pointer to PtrToPtr, add VcKind::AlignmentSafety** - `98c9698` (feat)
2. **Task 2: E2E alignment VC verification test** - `f3d6118` (test)

## Files Created/Modified

- `crates/analysis/src/ir.rs` - CastKind::PtrToPtr rename with alignment VC doc-comment
- `crates/analysis/src/encode_term.rs` - encode_ptr_to_ptr_cast helper, PtrToPtr match arm
- `crates/analysis/src/vcgen.rs` - VcKind::AlignmentSafety, generate_alignment_vcs, ty_alignment, format_ty
- `crates/driver/src/callbacks.rs` - AlignmentSafety => "alignment_safety" in vc_kind_to_string
- `crates/driver/src/diagnostics.rs` - V070 description, Warning severity, suggest_fix
- `crates/driver/src/mir_converter.rs` - Updated MIR CastKind mapping to ir::CastKind::PtrToPtr
- `crates/analysis/tests/cast_kind_tests.rs` - 17 unit tests for CastKind variants and AlignmentSafety
- `crates/driver/tests/alignment_e2e.rs` - 5 E2E tests for alignment VC generation

## Decisions Made

- Used bvsmod (signed bitvector modulo) for alignment check in SMT-LIB because it works correctly with 64-bit pointer bitvectors
- Made AlignmentSafety Warning severity (like MemorySafety) since alignment violations are UB but not always exploitable
- PtrToPtr alignment VC is emitted as a side-effect in vcgen.rs generate_alignment_vcs, not inside encode_cast itself, because encode_cast returns a single Term and cannot return VCs
- ty_alignment returns 1 for unknown/complex types, meaning no alignment VC is emitted (conservative: no false positives)

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Fixed Ty::Ref pattern mismatch**
- **Found during:** Task 1 (compilation)
- **Issue:** Plan assumed Ty::Ref has 3 fields (lifetime, inner, mutability) but it has 2 (inner, mutability)
- **Fix:** Changed `Ty::Ref(_, inner, _)` to `Ty::Ref(inner, _)` in ty_alignment and generate_alignment_vcs
- **Files modified:** crates/analysis/src/vcgen.rs
- **Verification:** cargo check passes

**2. [Rule 3 - Blocking] Fixed CfgPath structure mismatch**
- **Found during:** Task 1 (compilation)
- **Issue:** Plan suggested using CfgPath.blocks field for path constraint encoding, but CfgPath has no blocks field
- **Fix:** Simplified alignment VC generation to encode preceding assignments directly from basic_blocks slice
- **Files modified:** crates/analysis/src/vcgen.rs
- **Verification:** All tests pass including alignment VC generation

---

**Total deviations:** 2 auto-fixed (2 blocking)
**Impact on plan:** Both were compile-time type mismatches from imprecise plan context. No scope change.

## Issues Encountered

- Pre-commit hook linter race: rustfmt kept modifying vcgen.rs between Read and Edit tool calls, requiring Python-based file manipulation for some edits
- An unexpected parallel agent commit (8414bd0) captured some Task 1 changes; final commit 98c9698 captured remaining formatting changes

## User Setup Required

None - no external service configuration required.

## Next Phase Readiness

- CastKind::PtrToPtr and VcKind::AlignmentSafety are fully wired
- Phase 47 plans 02-04 can proceed with COMPL-06, COMPL-12 coverage
- Phase 50 (stdlib ptr/mem) can use AlignmentSafety for unsafe pointer operations

---
*Phase: 47-mir-coverage-hardening*
*Completed: 2026-03-05*
