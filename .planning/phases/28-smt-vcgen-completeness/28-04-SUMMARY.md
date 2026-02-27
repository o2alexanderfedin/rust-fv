---
phase: 28-smt-vcgen-completeness
plan: 04
subsystem: vcgen
tags: [bounds-check, array-index, slice-len, memory-safety, vcgen]
dependency_graph:
  requires: [28-03]
  provides: [bounds-check-vc-generation, rvalue-len-encoding]
  affects: [crates/analysis/src/encode_term.rs, crates/analysis/src/vcgen.rs]
tech_stack:
  added: []
  patterns: [MemorySafety VC generation, len-constant model for slices]
key_files:
  created: []
  modified:
    - crates/analysis/src/encode_term.rs
    - crates/analysis/src/vcgen.rs
decisions:
  - "bounds_check_term takes idx_bits parameter for zero-extension to match 64-bit len constant"
  - "Rvalue::Len models length as named SMT constant '{arr}_len' (not a concrete value)"
  - "BoundsCheck VCs use VcKind::MemorySafety (not a new BoundsCheck variant) — test accepts MemorySafety"
  - "generate_index_bounds_vcs scans all statements rather than working per-path — simpler, sufficient for the test"
  - "encode_assignment_len_returns_none test updated to encode_assignment_len_emits_len_constant to reflect new behavior"
metrics:
  duration_seconds: 444
  completed: "2026-02-24"
  tasks_completed: 2
  files_modified: 2
---

# Phase 28 Plan 04: Array Index Bounds VCs and Slice Length Encoding Summary

Array index bounds-check VC generation (Projection::Index) and Rvalue::Len encoding as a named SMT constant, making vcgen_01_array_index and vcgen_01_slice_len tests GREEN alongside the regression guard vcgen_01_field_projection.

## What Was Built

Two complementary changes that enable automatic bounds checking for array/slice index accesses in the SMT VCGen pipeline.

### encode_term.rs: Two New Helpers

**`bounds_check_term(idx: Term, idx_bits: u32, len: Term) -> Term`**

Builds the safety predicate `(and (bvule #x0 idx_64) (bvult idx_64 len))` for array access bounds checking. Handles narrower index types (e.g., `usize` as 32-bit on 32-bit targets) via zero-extension to 64 bits before comparison with the 64-bit length constant.

**`len_constant_name(arr_local: &str) -> String`**

Generates the SMT constant name `{arr_local}_len` used to model slice/array lengths as uninterpreted constants.

### vcgen.rs: Three Changes

**1. Rvalue::Len encoding (encode_assignment)**

Changed from `return None` to returning `Term::Const(len_constant_name(&len_place.local))`. This makes `_0 = Len(_1)` produce `(assert (= _0 _1_len))` in the SMT script — the assignment form required by `vcgen_01_slice_len`.

**2. len constant declarations (collect_declarations)**

Added a scan of all basic blocks to detect `Rvalue::Len` uses. For each such use, adds `(declare-const {arr}_len (_ BitVec 64))` to the variable declarations so the SMT solver can see the constant.

**3. generate_index_bounds_vcs + extract_index_operand**

New function that scans all statements for `Rvalue::Use(operand)` where the operand contains `Projection::Index(idx_local)`. For each such access, emits a `VcKind::MemorySafety` VC with script:
```
(set-logic QF_BV)
(declare-const _1 (Array (_ BitVec 64) (_ BitVec 32)))
(declare-const _2 (_ BitVec 64))
(declare-const _1_len (_ BitVec 64))
...
(assert (not (and (bvule #x0000000000000000 _2) (bvult _2 _1_len))))
(check-sat)
```

Description format: `"bounds check: {arr} index {idx} in bounds at block {N}"` — matches the test's `description.contains("bounds")` check.

## Tests Results

| Test | Before | After |
|------|--------|-------|
| vcgen_01_array_index | FAILED | PASSED |
| vcgen_01_slice_len | FAILED | PASSED |
| vcgen_01_field_projection | ok | ok (regression guard) |
| Full lib test suite (1200 tests) | 1200 pass | 1200 pass |
| vcgen_04_* | FAILED | FAILED (planned plan 05) |

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Updated stale encode_assignment_len_returns_none test**
- **Found during:** Task 2 full test run
- **Issue:** Existing unit test `encode_assignment_len_returns_none` asserted `result.is_none()`, which broke after the intentional change to make `Rvalue::Len` return `Some`
- **Fix:** Renamed test to `encode_assignment_len_emits_len_constant` and updated assertion to verify the new behavior: `result.is_some()` and RHS is `Term::Const("_1_len")`
- **Files modified:** `crates/analysis/src/vcgen.rs`
- **Commit:** bcee72c

**2. [Rule 2 - Deviation] `bounds_check_term` signature uses `idx_bits: u32` parameter**
- **Found during:** Task 1 implementation
- **Issue:** Plan showed `bounds_check_term(idx: Term, len: Term)` but the implementation note said to handle narrower indexes. The test uses `_2: usize` which maps to 64-bit, but correctness requires knowing the bit width.
- **Fix:** Added `idx_bits: u32` parameter to `bounds_check_term` so callers can pass the correct width. The default fallback is 64 bits (conservative).
- **Files modified:** `crates/analysis/src/encode_term.rs`, `crates/analysis/src/vcgen.rs`

## Key Links Implemented

| From | To | Via |
|------|----|-----|
| vcgen.rs Projection::Index | encode_term.rs bounds_check_term() | generate_index_bounds_vcs → extract_index_operand |
| vcgen.rs Rvalue::Len | SMT declarations | collect_declarations adds DeclareConst for {arr}_len |

## Commits

| Hash | Description |
|------|-------------|
| c99166d | feat(28-04): add bounds_check_term() and len_constant_name() helpers |
| bcee72c | feat(28-04): wire Rvalue::Len and BoundsCheck VCs into vcgen.rs |

## Self-Check: PASSED
