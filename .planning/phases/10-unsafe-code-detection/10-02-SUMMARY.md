---
phase: 10-unsafe-code-detection
plan: 02
subsystem: unsafe-verification
tags: [unsafe, memory-safety, heap-model, null-check, bounds-check, vcgen]
dependency_graph:
  requires: [10-01]
  provides: [unsafe_analysis, heap_model, unsafe_vcgen]
  affects: [vcgen]
tech_stack:
  added: []
  patterns: [heap-as-array, smt-array-theory, provenance-tracking]
key_files:
  created:
    - crates/analysis/src/unsafe_analysis.rs
    - crates/analysis/src/heap_model.rs
  modified:
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/lib.rs
decisions:
  - key: heap-as-array-model
    summary: "Byte-addressable heap model with allocation metadata"
    rationale: "SMT array theory provides natural encoding for memory; allocation metadata (base, size) enables bounds checking; null address axiom (0 not allocated) enforces null safety"
    alternatives: "Full separation logic (deferred to v0.3+), region-based analysis"
  - key: null-check-vc-for-non-fromref-only
    summary: "FromRef pointers skip null-check generation"
    rationale: "Pointers derived from safe references (&T, &mut T) are guaranteed non-null by Rust's type system; checking them would produce false positives"
    alternatives: "Check all pointers (produces false positives), trust annotations (less automated)"
  - key: diagnostic-vc-for-missing-contracts
    summary: "Unannotated unsafe functions produce always-SAT diagnostic VC"
    rationale: "Flows through normal VC pipeline; consistent with Phase 6 missing-decreases pattern; warning not error per USF-06 requirement"
    alternatives: "Separate error path (more complex), hard error (breaks v0.1 compatibility)"
  - key: heap-model-only-for-ptr-arithmetic
    summary: "Heap model declarations generated only when PtrArithmetic exists"
    rationale: "Null checks don't need allocation metadata (just ptr != 0); reduces SMT overhead for dereference-only code"
    alternatives: "Always include heap model (slower), lazy declaration per VC (more complex)"
metrics:
  duration_minutes: 99
  tasks_completed: 2
  files_modified: 4
  tests_added: 45
  total_workspace_tests: 2056
  completed_date: "2026-02-13"
---

# Phase 10 Plan 02: Unsafe Block Detection

**One-liner:** Unsafe analysis engine with heap-as-array model for null/bounds-check VC generation

## Overview

Implemented core unsafe verification infrastructure: `unsafe_analysis` module detects and classifies unsafe operations, `heap_model` module provides SMT heap-as-array encoding, and VCGen integration generates memory safety VCs with provenance-aware null checking and allocation-bounded pointer arithmetic.

## What Was Built

### Task 1: unsafe_analysis and heap_model Modules (TDD)

**Duration:** ~40 minutes

Created two new analysis modules following TDD protocol (RED → GREEN → REFACTOR):

**unsafe_analysis.rs (9 functions, 18 tests):**
- `detect_unsafe_blocks`: Returns unsafe_blocks or synthetic block for `unsafe fn` with empty blocks
- `extract_unsafe_operations`: Simple accessor for func.unsafe_operations
- `classify_provenance`: Returns FromRef/FromInt/Unknown; PtrArithmetic always Unknown (arithmetic invalidates provenance)
- `needs_null_check`: true for RawDeref unless FromRef (safe references never null)
- `needs_bounds_check`: true for PtrArithmetic only (deref/cast don't change address)
- `check_missing_unsafe_contracts`: warns about `unsafe fn` without #[unsafe_requires]/#[unsafe_ensures]/#[trusted]
- `is_trusted_function`: checks is_trusted flag
- `get_unsafe_requires`/`get_unsafe_ensures`: contract accessors

**heap_model.rs (4 functions, 8 tests):**
- `declare_heap_model`: Declares 5 SMT constructs:
  - `heap`: (BitVec 64 → BitVec 8) byte-addressable memory
  - `allocated`: (BitVec 64 → Bool) allocation validity predicate
  - `alloc_base`: (BitVec 64 → BitVec 64) allocation base address
  - `alloc_size`: (BitVec 64 → BitVec 64) allocation size
  - Axiom: `(not (allocated #x0000000000000000))` — null not allocated
- `generate_null_check_assertion`: Returns `(= ptr #x0000000000000000)` (bad condition for VC)
- `generate_bounds_check_assertion`: Returns `(not (bvult effective_offset alloc_size))` where effective_offset = (ptr - alloc_base(ptr)) + offset
- `heap_model_declarations_needed`: true if any PtrArithmetic operation exists

**Test Coverage:**
- 18 unsafe_analysis tests: block detection (3), operation extraction (1), provenance (2), null/bounds predicates (5), contract checking (6), accessor tests (2)
- 8 heap_model tests: declaration count/structure (4), assertion generation (2), heap model necessity (2)
- 19 integration tests from Phase 10-01 still passing

### Task 2: VCGen Integration (TDD)

**Duration:** ~59 minutes

Integrated unsafe analysis into VCGen pipeline at lines 427-626 (after borrow validity, before loop invariants):

**Trusted Function Handling:**
- Early return with empty VCs if `is_trusted_function(func)` returns true
- Logs: "Trusted function - skipping body verification"
- Body verification skipped; contracts enforced at call sites

**Unsafe Block Detection:**
- Calls `detect_unsafe_blocks(func)` and logs count
- Blocks flagged for Phase 10-03 diagnostics

**Missing Contract Warning:**
- Calls `check_missing_unsafe_contracts(func)` for `unsafe fn` without annotations
- Generates diagnostic VC: `(assert true); check-sat` (always-SAT = warning)
- VcKind::MemorySafety
- Description: warning message from check_missing_unsafe_contracts
- Implements USF-06: advisory warnings not blocking errors

**Null-Check VCs:**
- For each unsafe operation where `needs_null_check(op)`:
  - Extracts ptr_local and block_index from RawDeref
  - Builds script with QF_BV logic, datatype declarations, variable declarations
  - Asserts `generate_null_check_assertion(ptr_local)` — ptr == 0 is violation
  - VcKind::MemorySafety
  - Description: "null-check: raw pointer dereference of '{ptr}' requires non-null"
- FromRef provenance skips null-check generation (safe reference origin)

**Bounds-Check VCs:**
- For each unsafe operation where `needs_bounds_check(op)`:
  - Extracts ptr_local, offset_local, block_index from PtrArithmetic
  - Prepends `declare_heap_model()` commands if needed
  - Builds script with heap model, datatype declarations, variable declarations
  - Asserts `generate_bounds_check_assertion(ptr, offset)` — offset out of bounds is violation
  - VcKind::MemorySafety
  - Description: "bounds-check: pointer arithmetic on '{ptr}' with offset '{offset}'"

**Test Coverage:**
- 6 new VCGen integration tests:
  - `test_vcgen_trusted_function_skipped`: Verifies trusted functions produce 0 VCs
  - `test_vcgen_missing_contracts_warning`: Verifies unsafe fn without contracts produces MemorySafety diagnostic VC
  - `test_vcgen_null_check_generated`: Verifies RawDeref (Unknown provenance) produces null-check VC
  - `test_vcgen_null_check_skipped_from_ref`: Verifies RawDeref (FromRef provenance) skips null-check
  - `test_vcgen_bounds_check_generated`: Verifies PtrArithmetic produces bounds-check VC with heap model
  - `test_vcgen_safe_function_no_unsafe_vcs`: Verifies safe functions produce no MemorySafety VCs

## Deviations from Plan

None - plan executed exactly as written.

## Auth Gates

None encountered.

## Tests & Verification

**Test Metrics:**
- New tests added: 45 (18 unsafe_analysis + 8 heap_model + 6 vcgen + 13 from Phase 10-01)
- Total workspace tests: 2,056 (up from 2,011 baseline)
- Test breakdown:
  - Unit tests: 26 (18 unsafe_analysis + 8 heap_model)
  - Integration tests: 19 (6 vcgen + 13 IR/macros from 10-01)
- All tests passing: ✓
- 0 regressions

**Verification:**
```bash
cargo test --workspace            # 2,056 tests pass
cargo clippy --workspace -- -D warnings  # 0 warnings
cargo fmt --all -- --check        # 0 formatting issues
```

**Key Test Cases:**
- Synthetic unsafe block for `unsafe fn` with no explicit blocks
- FromRef provenance skips null-check (no false positives)
- Bounds-check includes heap model declarations
- Trusted functions produce 0 body VCs
- Missing contracts produce advisory warnings (not errors)

## Self-Check: PASSED

**Files created:**
```bash
$ [ -f "crates/analysis/src/unsafe_analysis.rs" ] && echo "FOUND" || echo "MISSING"
FOUND
$ [ -f "crates/analysis/src/heap_model.rs" ] && echo "FOUND" || echo "MISSING"
FOUND
```

**Commits exist:**
```bash
$ git log --oneline --all | grep -q "f838c7c" && echo "FOUND" || echo "MISSING"
FOUND
$ git log --oneline --all | grep -q "96026bb" && echo "FOUND" || echo "MISSING"
FOUND
```

**Module exports:**
```bash
$ grep -q "pub mod unsafe_analysis" crates/analysis/src/lib.rs && echo "FOUND" || echo "MISSING"
FOUND
$ grep -q "pub mod heap_model" crates/analysis/src/lib.rs && echo "FOUND" || echo "MISSING"
FOUND
```

**VCGen integration:**
```bash
$ grep -q "crate::unsafe_analysis::is_trusted_function" crates/analysis/src/vcgen.rs && echo "FOUND" || echo "MISSING"
FOUND
$ grep -q "crate::heap_model::declare_heap_model" crates/analysis/src/vcgen.rs && echo "FOUND" || echo "MISSING"
FOUND
```

All self-checks passed.

## Next Steps

1. **Phase 10 Plan 03:** End-to-end unsafe verification tests
   - Add e2e test file with unsafe code patterns
   - Verify null-check, bounds-check, and trusted function diagnostics
   - Validate USF-06 warning behavior
2. **Optional:** Add spec parser support for `final(*x)` nested prophecy syntax (deferred from Phase 9)
3. **Optional:** MIR-based live range computation for precise NLL semantics (deferred from Phase 9)

## Commits

- `f838c7c`: feat(10-02): add unsafe_analysis and heap_model modules
- `96026bb`: feat(10-02): integrate unsafe analysis into VCGen pipeline
