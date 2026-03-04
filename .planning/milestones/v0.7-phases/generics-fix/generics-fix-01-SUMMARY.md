---
phase: generics-fix
plan: 01
subsystem: driver/mir_converter
tags: [generics, vcgen, parametric-axioms, mir-converter]
dependency_graph:
  requires: []
  provides: [GENERICS-01]
  affects: [driver/mir_converter, driver/parallel, analysis/vcgen]
tech_stack:
  added: []
  patterns: [rustc-generics-api, predicates-of, parametric-axioms]
key_files:
  created:
    - crates/analysis/tests/generics_e2e.rs
    - crates/driver/tests/generics_driver_e2e.rs
  modified:
    - crates/driver/src/mir_converter.rs
    - crates/driver/src/parallel.rs
decisions:
  - "Use parametric axiom path (generate_vcs_with_db) for generic functions — monomorphization requires call-site registry not yet available (GENERICS-02)"
  - "Skip Sized bounds in convert_generic_params — always implied, adds no verification value"
  - "Filter trait bounds by self_ty == Param(param_name) to avoid cross-parameter bound mixing"
metrics:
  duration: "< 5 minutes"
  completed: "2026-03-02"
  tasks_completed: 3
  files_modified: 2
---

# Phase generics-fix Plan 01: Populate generic_params in MIR converter Summary

Activated the dead parametric axiom branch in vcgen.rs by populating `Function.generic_params` from `tcx.generics_of(def_id)` in the MIR converter, so generic functions like `fn max<T: Ord>(a: T, b: T) -> T` now get trait-bound assumptions injected at verification time.

## What Was Implemented

### Task 1: RED - Test files (already existed, all passing)

Both test files were pre-written as part of earlier plan setup:
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/tests/generics_e2e.rs` — 3 analysis-layer tests for the parametric axiom path
- `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/tests/generics_driver_e2e.rs` — 2 driver-layer tests confirming generic IR produces non-empty VC results

All 5 tests passed in GREEN from the start (analysis layer correctly handles `generic_params`; the gap was only at the driver MIR conversion level).

### Task 2: GREEN - convert_generic_params in mir_converter.rs

Added private function `convert_generic_params(tcx, def_id) -> Vec<ir::GenericParam>`:

```rust
fn convert_generic_params(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<ir::GenericParam> {
    use rustc_middle::ty::GenericParamDefKind;
    let generics = tcx.generics_of(def_id);
    let predicates = tcx.predicates_of(def_id);
    generics.own_params.iter()
        .filter_map(|param| {
            if !matches!(param.kind, GenericParamDefKind::Type { .. }) { return None; }
            let param_name = param.name.as_str().to_string();
            let trait_bounds = predicates.predicates.iter()
                .filter_map(|(clause, _)| {
                    let tp = clause.as_trait_clause()?.skip_binder();
                    // Only bounds on THIS type parameter
                    if let TyKind::Param(p) = tp.trait_ref.self_ty().kind() {
                        if p.name.as_str() != param_name { return None; }
                    } else { return None; }
                    let name = tcx.def_path_str(tp.trait_ref.def_id)
                        .split("::").last().unwrap_or("").to_string();
                    if name == "Sized" { return None; }  // always implied
                    Some(name)
                }).collect();
            Some(ir::GenericParam { name: param_name, trait_bounds })
        }).collect()
}
```

Replaced `generic_params: vec![]` in `convert_mir()` with `generic_params: convert_generic_params(tcx, def_id)`.

### Task 3: GREEN - parallel.rs routing comment and debug log

Added a clear comment in `verify_single()` before the `generate_vcs_with_db` call:
- Documents the parametric axiom routing decision
- Explains why `generate_vcs_monomorphized` is not used yet (requires call-site registry — GENERICS-02)
- Adds `tracing::debug!` log when a generic function is encountered

## Files Modified

### `crates/driver/src/mir_converter.rs`
- **Added:** `convert_generic_params(tcx, def_id) -> Vec<ir::GenericParam>` (lines 42-108)
- **Changed:** `generic_params: vec![]` → `generic_params: convert_generic_params(tcx, def_id)` in `convert_mir()`

### `crates/driver/src/parallel.rs`
- **Added:** Generic routing comment + `tracing::debug!` block before `generate_vcs_with_db` call in `verify_single()`

## Test Results

```
cargo test --workspace: ALL PASS

generics_e2e (analysis):
  test parametric_axioms_fire_for_generic_function ... ok
  test empty_generic_params_produces_vcs_from_ensures ... ok
  test generic_function_vc_count_matches_non_generic ... ok

generics_driver_e2e (driver):
  test generic_ir_function_produces_nonempty_results_when_generic_params_populated ... ok
  test generic_function_with_empty_generic_params_still_verifies ... ok

All workspace tests: 0 failures
cargo clippy --workspace: 0 errors
cargo fmt --check: no diff
```

## Deferred Items

**GENERICS-02: Monomorphization-based verification (generate_vcs_monomorphized)**

The `generate_vcs_monomorphized` path requires a populated `MonomorphizationRegistry` with call-site instantiation data. This requires type-checking the caller body to determine what concrete types are used at each generic call site. This is tracked as a separate future task and documented in `parallel.rs` with a code comment.

## Commit Hash

`24214ed` — feat(generics-fix-01): populate generic_params from tcx.generics_of() in mir_converter

## Self-Check: PASSED

- [x] `convert_generic_params` function exists in mir_converter.rs
- [x] `generic_params: convert_generic_params(tcx, def_id)` used in convert_mir()
- [x] No `generic_params: vec![]` in convert_mir() (only in test helper)
- [x] commit 24214ed exists
- [x] All test files exist
- [x] cargo test --workspace exits 0
