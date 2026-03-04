---
phase: 39-fnmut-prophecy-variable-encoding-for-mutable-closure-capture-verification-implement-prophecy-pre-post-state-tracking-in-closure-analysis-rs-vcgen-rs-so-fnmut-closures-with-contracts-on-mutated-captured-state-can-be-verified
plan: "01"
subsystem: analysis
tags: [closures, fnmut, prophecy, ir, capture-mode]
dependency_graph:
  requires: []
  provides: [CaptureMode enum, detect_closure_prophecies, ProphecyInfo.closure_name]
  affects: [encode_prophecy, ir, vcgen, encode_sort, hof_vcgen, defunctionalize]
tech_stack:
  added: []
  patterns: [TDD red-green, iterator filter+map for prophecy detection]
key_files:
  created: []
  modified:
    - crates/analysis/src/ir.rs
    - crates/analysis/src/encode_prophecy.rs
    - crates/analysis/src/encode_sort.rs
    - crates/analysis/src/hof_vcgen.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/defunctionalize.rs
    - crates/analysis/tests/closure_verification.rs
    - crates/analysis/tests/hof_closures.rs
decisions:
  - "CaptureMode enum added before ClosureInfo following ClosureTrait pattern — ByMove | ByRef | ByMutRef"
  - "ProphecyInfo.closure_name: Option<String> distinguishes closure env field prophecies from &mut T param prophecies"
  - "detect_closure_prophecies uses iterator filter+map — minimal, idiomatic, matches detect_prophecies style"
  - "All existing env_fields 2-tuple sites migrated to 3-tuple with CaptureMode::ByMove as default"
  - "build_closure_info test helper defaults to CaptureMode::ByMove to avoid pervasive call-site changes"
metrics:
  duration_seconds: 1184
  completed_date: "2026-03-02"
  tasks_completed: 2
  files_modified: 8
---

# Phase 39 Plan 01: FnMut Prophecy IR Foundation Summary

**One-liner:** CaptureMode enum + ClosureInfo 3-tuple env_fields + ProphecyInfo.closure_name + detect_closure_prophecies(closure_info) -> Vec<ProphecyInfo> for ByMutRef-only prophecy detection

## What Was Built

Two tasks completed:

**Task 1 — IR types (TDD green):**
- `CaptureMode` enum in `ir.rs` with `ByMove | ByRef | ByMutRef` variants
- `ClosureInfo.env_fields` changed from `Vec<(String, Ty)>` to `Vec<(String, Ty, CaptureMode)>`
- `ProphecyInfo.closure_name: Option<String>` added (None = &mut T param prophecy, Some = closure env field)
- All existing 2-tuple `env_fields` sites migrated to 3-tuples with `CaptureMode::ByMove`
- 3 new tests: `test_capture_mode_variants`, `test_closure_info_env_fields_with_capture_mode`, `test_prophecy_info_closure_name_none_for_param_prophecies`

**Task 2 — detect_closure_prophecies (TDD green):**
- `detect_closure_prophecies(closure_info: &ClosureInfo) -> Vec<ProphecyInfo>` in `encode_prophecy.rs`
- Filters `env_fields` for `CaptureMode::ByMutRef` only — ByMove/ByRef produce no prophecies
- Sets `closure_name: Some(closure_info.name.clone())` on each produced `ProphecyInfo`
- Naming convention: `{field_name}_initial`, `{field_name}_prophecy` (mirrors detect_prophecies)
- `deref_level: 0` (no nested prophecies for closure env fields in this plan)
- 7 new tests covering: empty, ByMove no-prophecy, ByRef no-prophecy, naming convention, multiple ByMutRef, mixed modes, prophecy_declarations reusability

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Integration test files with old 2-tuple env_fields**
- **Found during:** Task 1 (pre-commit hook ran clippy on all test targets)
- **Issue:** `closure_verification.rs` and `hof_closures.rs` integration tests used 2-tuple `env_fields` that no longer compiled after the struct change
- **Fix:** Updated `build_closure_info` helper in `closure_verification.rs` to add `CaptureMode::ByMove` in the map closure; updated `hof_closures.rs` inline 2-tuple to 3-tuple and added `CaptureMode` to imports
- **Files modified:** `crates/analysis/tests/closure_verification.rs`, `crates/analysis/tests/hof_closures.rs`
- **Commit:** f906601

**2. [Rule 1 - Bug] defunctionalize.rs loop using old 2-tuple destructure**
- **Found during:** Task 1
- **Issue:** `for (field_name, field_ty) in &info.env_fields` no longer matched the 3-tuple
- **Fix:** Changed to `for (field_name, field_ty, _capture_mode) in &info.env_fields`
- **Files modified:** `crates/analysis/src/defunctionalize.rs`
- **Commit:** f906601

**3. [Rule 3 - Blocking] IntTy alias conflict in detect_closure_prophecies_multiple_by_mut_ref test**
- **Found during:** Task 2
- **Issue:** `IntTy` was already in scope from `use crate::ir::{...}` in the test module, causing a name conflict when using `IntTy::I64`
- **Fix:** Used `use crate::ir::{..., IntTy as IITy}` in the specific test function to avoid conflict
- **Files modified:** `crates/analysis/src/encode_prophecy.rs`
- **Commit:** 86380ce

## Commits

| Task | Commit | Description |
|------|--------|-------------|
| Task 1 | f906601 | feat(39-01): Add CaptureMode enum, update ClosureInfo + ProphecyInfo in ir.rs |
| Task 2 | 86380ce | feat(39-01): Add detect_closure_prophecies in encode_prophecy.rs |

## Test Results

- All 1255+ existing tests pass (zero regressions)
- 10 new tests added: 3 in ir.rs, 7 in encode_prophecy.rs
- `cargo clippy -p rust-fv-analysis` — zero errors
- `cargo fmt` check passes

## Self-Check: PASSED

Files created/modified exist:
- `crates/analysis/src/ir.rs` — FOUND (CaptureMode enum at line 29, env_fields 3-tuple at line 310, closure_name at line 585)
- `crates/analysis/src/encode_prophecy.rs` — FOUND (detect_closure_prophecies function added)
- Commits f906601 and 86380ce — FOUND in git log
