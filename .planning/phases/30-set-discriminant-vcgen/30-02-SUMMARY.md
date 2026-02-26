---
phase: 30-set-discriminant-vcgen
plan: "02"
subsystem: vcgen
tags: [vcgen, set-discriminant, smt, assertion]
dependency_graph:
  requires: [30-01]
  provides: [VCGEN-06]
  affects: [crates/analysis/src/vcgen.rs]
tech_stack:
  added: []
  patterns: [discriminant-{local} naming convention, UNSAT-based assertion VCs]
key_files:
  created: []
  modified:
    - crates/analysis/src/vcgen.rs
decisions:
  - "Term::IntLit takes i128 (not i64) — cast variant_idx as i128"
  - "generate_set_discriminant_vcs uses base_script (not inline script) for logic selection"
  - "No DeclareFun needed — Z3 accepts Term::App without explicit declare-fun (Phase 28 precedent)"
metrics:
  duration: 87
  completed: "2026-02-26"
---

# Phase 30 Plan 02: SetDiscriminant VCGen Implementation Summary

**One-liner:** VCGen now emits `discriminant-{local}({local}) == variant_idx` assertion VCs for every `Statement::SetDiscriminant` by adding `generate_set_discriminant_vcs()` wired after index bounds VCs in `generate_vcs_with_db`.

## Tasks Completed

| Task | Name | Commit | Files |
|------|------|--------|-------|
| 1 | Implement generate_set_discriminant_vcs + wire-in | 3b41fa6 | crates/analysis/src/vcgen.rs |

## What Was Built

Added `generate_set_discriminant_vcs()` (~62 lines) to `crates/analysis/src/vcgen.rs`:

- Iterates all basic blocks and statements in the function
- For each `Statement::SetDiscriminant(place, variant_idx)`, emits one assertion VC
- SMT encoding: `(assert (not (= (discriminant-{local} {local}) {variant_idx})))` — UNSAT proves discriminant set correctly
- Uses `VcKind::Assertion` (correctness, not safety)
- Uses same `discriminant-{local}` naming as `Rvalue::Discriminant` encoder
- Calls `base_script()` for logic selection (QF_BV/QF_UFBVDT/ALL based on types)

Wire-in in `generate_vcs_with_db` (lines 324-325):
```rust
let mut disc_vcs = generate_set_discriminant_vcs(func, &datatype_declarations, &declarations);
conditions.append(&mut disc_vcs);
```

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Term::IntLit requires i128, not i64**
- **Found during:** Task 1 — compile error
- **Issue:** Plan specified `Term::IntLit(*variant_idx as i64)` but `Term::IntLit` signature takes `i128`
- **Fix:** Changed cast to `*variant_idx as i128`
- **Files modified:** crates/analysis/src/vcgen.rs
- **Commit:** 3b41fa6 (fixed inline before commit)

## Test Results

- `vcgen_06_set_discriminant_unit`: GREEN (was RED)
- `vcgen_06_set_discriminant_assertion`: GREEN (was RED)
- `mirconv_02_set_discriminant`: GREEN (regression guard)
- `vcgen_completeness29` full suite: 11/11 PASS
- `rust-fv-analysis` doc tests: 1/1 PASS (28 ignored)
- Clippy: 0 errors

## Self-Check: PASSED

- [x] `crates/analysis/src/vcgen.rs` modified — FOUND
- [x] Commit 3b41fa6 exists — FOUND
- [x] `generate_set_discriminant_vcs` in vcgen.rs — CONFIRMED
- [x] Call site `disc_vcs` in `generate_vcs_with_db` — CONFIRMED
- [x] Both vcgen_06 tests GREEN — CONFIRMED
