---
phase: 29-to-fix-the-identified-gaps
plan: 04
subsystem: mir-converter
tags: [mir-converter, type-mapping, rvalue, generic-types, array-repeat]
requirements: [MIRCONV-01]

dependency_graph:
  requires: [29-03]
  provides: [TyKind::Param→Generic mapping, Rvalue::Repeat IR variant, CopyForDeref/RawPtr/Repeat converter arms]
  affects: [crates/analysis/src/ir.rs, crates/driver/src/mir_converter.rs, crates/analysis/src/vcgen.rs, crates/analysis/src/monomorphize.rs]

tech_stack:
  added: []
  patterns:
    - "TyKind::Param arm before wildcard in convert_ty for correct generic type recognition"
    - "Debug-format count extraction for Rvalue::Repeat (robust across nightly API changes)"
    - "Rvalue::RawPtr (nightly-2026-02-11 rename of AddressOf) maps to ir::Rvalue::Ref"

key_files:
  created: []
  modified:
    - crates/analysis/src/ir.rs
    - crates/driver/src/mir_converter.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/monomorphize.rs

decisions:
  - "NullaryOp (SizeOf/AlignOf) removed from nightly-2026-02-11 MIR Rvalue enum — no arm needed"
  - "AddressOf renamed to RawPtr(RawPtrKind, Place) in nightly-2026-02-11 — arm uses new name"
  - "Repeat count extracted via debug format string parsing — avoids nightly Const API instability"
  - "Rvalue::Repeat in vcgen.rs returns None (deferred encoding) — sound, no false claims"

metrics:
  duration_seconds: 648
  completed_date: "2026-02-24"
  tasks_completed: 1
  files_modified: 4
---

# Phase 29 Plan 04: TyKind::Param Fix and Missing Rvalue Variants Summary

Fix TyKind::Param→Ty::Generic type mapping and add CopyForDeref, RawPtr (AddressOf), and Repeat Rvalue variants to complete MIR converter coverage for common Rust constructs.

## Tasks Completed

| # | Task | Commit | Files |
|---|------|--------|-------|
| 1 | Fix TyKind::Param mapping and add missing Rvalue variants | f1abab0 | ir.rs, mir_converter.rs, vcgen.rs, monomorphize.rs |

## What Was Built

### Step 1: ir::Rvalue::Repeat variant (ir.rs)
Added `Repeat(Operand, usize)` variant to the `Rvalue` enum. This represents `[x; N]` array fill expressions at the IR level.

### Step 2: TyKind::Param fix (mir_converter.rs)
Inserted `ty::TyKind::Param(t) => ir::Ty::Generic(t.name.as_str().to_string())` arm BEFORE the wildcard `_ => ir::Ty::Named(...)` in `convert_ty`. Previously, generic type parameters like `T` were erroneously mapped to `Named("T")` instead of `Generic("T")`, breaking the Phase 28 generic VCGen infrastructure.

### Step 3: Missing Rvalue converter arms (mir_converter.rs)
Added to `convert_rvalue`:
- **CopyForDeref**: Maps to `ir::Rvalue::Use(Operand::Copy(...))` — identity copy semantics
- **RawPtr** (nightly-2026-02-11 rename of `AddressOf`): Maps to `ir::Rvalue::Ref(Shared, ...)` — transparent pointer identity
- **Repeat**: Extracts count via debug-format string parsing (robust against nightly Const API changes); maps to `ir::Rvalue::Repeat(operand, n)`

### Exhaustive match fixes
- **vcgen.rs `encode_assignment`**: Added `Rvalue::Repeat(..) => return None` (VCGen encoding deferred — sound, no false assertions)
- **monomorphize.rs `substitute_rvalue`**: Added `Rvalue::Repeat(op, count) => Rvalue::Repeat(op.clone(), *count)`

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] NullaryOp not present in nightly-2026-02-11 MIR API**
- **Found during:** Task 1, Step 3
- **Issue:** The plan specified handling `mir::Rvalue::NullaryOp` for SizeOf/AlignOf, but this variant does not exist in nightly-2026-02-11's `Rvalue` enum (it was removed upstream)
- **Fix:** Omitted NullaryOp arm entirely; added comment explaining the omission; removed `known_size_bytes`/`known_align_bytes` helpers that were only needed for NullaryOp
- **Files modified:** crates/driver/src/mir_converter.rs

**2. [Rule 1 - Bug] AddressOf renamed to RawPtr in nightly-2026-02-11**
- **Found during:** Task 1, Step 3
- **Issue:** The plan used `mir::Rvalue::AddressOf(_, place)` but this variant was renamed to `mir::Rvalue::RawPtr(RawPtrKind, Place)` in nightly-2026-02-11
- **Fix:** Used `mir::Rvalue::RawPtr(_, place)` with same semantics (mapped to `ir::Rvalue::Ref(Shared, ...)`)
- **Files modified:** crates/driver/src/mir_converter.rs

## Test Results

```
Phase 28: 10/10 GREEN
Phase 29: 7/10 GREEN (3 ignored — reserved for Plan 05)
Clippy: clean (no warnings)
Rustfmt: clean
```

## Self-Check: PASSED

Files exist:
- FOUND: crates/analysis/src/ir.rs
- FOUND: crates/driver/src/mir_converter.rs
- FOUND: crates/analysis/src/vcgen.rs
- FOUND: crates/analysis/src/monomorphize.rs

Commits:
- FOUND: f1abab0 (feat(29-04): fix TyKind::Param->Generic; add CopyForDeref, RawPtr, Repeat)
