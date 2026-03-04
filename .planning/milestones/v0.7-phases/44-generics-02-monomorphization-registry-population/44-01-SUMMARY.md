---
phase: 44-generics-02-monomorphization-registry-population
plan: 01
subsystem: verification
tags: [rust, generics, monomorphization, mir, rustc, formal-verification]

# Dependency graph
requires:
  - phase: 40-generics-verification-completion
    provides: MonomorphizationRegistry + generate_vcs_monomorphized routing in parallel.rs
provides:
  - populate_monomorphization_registry() function in callbacks.rs
  - Shared MonomorphizationRegistry pre-populated from MIR call sites before VerificationTask creation
  - Production path: cargo verify automatically discovers and registers concrete generic instantiations
affects:
  - parallel.rs routing (generate_vcs_monomorphized fires in production for T->i32 etc.)
  - all future generic function verification via the production pipeline

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "MIR traversal via tcx.hir_body_owners() + tcx.optimized_mir() + terminator iteration"
    - "GenericArg::as_type() for extracting ty::Ty from generic args (nightly-2026-02-11 API)"
    - "Deduplication via existing.substitutions == new_substitutions comparison"
    - "Shared Arc<MonomorphizationRegistry> created once, cloned into all VerificationTasks"

key-files:
  created: []
  modified:
    - crates/driver/src/callbacks.rs
    - crates/driver/tests/generics_driver_e2e.rs

key-decisions:
  - "Use GenericArg::as_type() instead of .unpack() for type extraction (nightly-2026-02-11 does not have unpack())"
  - "Skip entire instantiation if ANY arg remains ty::Param (caller is generic — unresolvable)"
  - "Dedup uses HashMap equality (substitutions == substitutions) before calling registry.register()"
  - "Label parts built from param name lowercased with underscore prefix, joined (e.g. _t becomes _t)"
  - "Collapsible if/let patterns fixed per clippy::collapsible_match into single pattern match"

patterns-established:
  - "populate_monomorphization_registry() pattern: iterate hir_body_owners, get optimized_mir, walk terminators for FnDef calls"
  - "Shared-Arc wiring: create Arc once before task loop, use Arc::clone per task (mirrors ghost_pred_db_arc pattern)"

requirements-completed: [GENERICS-02]

# Metrics
duration: 23min
completed: 2026-03-04
---

# Phase 44 Plan 01: MonomorphizationRegistry Population Summary

**MIR call-site analysis in callbacks.rs populates a shared MonomorphizationRegistry before VerificationTask creation, activating the generate_vcs_monomorphized production path for concrete generic instantiations (e.g., max::<i32>)**

## Performance

- **Duration:** ~23 min
- **Started:** 2026-03-04T05:00:14Z
- **Completed:** 2026-03-04T05:23:29Z
- **Tasks:** 2
- **Files modified:** 2

## Accomplishments

- Implemented `populate_monomorphization_registry(tcx, &mut registry)` that traverses all MIR function bodies to find `TerminatorKind::Call` sites with `FnDef` callees, extracting concrete generic type substitutions
- Wired shared `Arc<MonomorphizationRegistry>` created once before task loop, replacing the per-task `MonomorphizationRegistry::new()` pattern — all `VerificationTask`s now share the pre-populated registry
- Added 5 source-level unit tests in callbacks.rs verifying structural properties (function exists, deduplication logic, skip patterns, Arc::clone wiring)
- Added 2 new E2E integration tests in `generics_driver_e2e.rs`: `monomorphized_path_produces_labeled_vcs` and `multiple_instantiations_produce_vcs_for_each` — all 5 E2E tests pass

## Task Commits

Each task was committed atomically:

1. **Task 1: Implement populate_monomorphization_registry and wire shared registry** - `a12c8c6` (feat)
2. **Task 2: Add E2E integration tests for production monomorphization path** - `958b851` (test)

## Files Created/Modified

- `crates/driver/src/callbacks.rs` - Added `populate_monomorphization_registry()` function (~115 lines); added shared registry wiring before task creation; replaced per-task `MonomorphizationRegistry::new()` with `Arc::clone(&mono_registry_arc)`; added 5 unit tests
- `crates/driver/tests/generics_driver_e2e.rs` - Added `monomorphized_path_produces_labeled_vcs` and `multiple_instantiations_produce_vcs_for_each` integration tests

## Decisions Made

- Used `GenericArg::as_type()` instead of `.unpack()` — the nightly-2026-02-11 `GenericArg` type does not expose `.unpack()` as a method; `as_type()` returns `Option<ty::Ty>` directly
- Skip entire instantiation if ANY type arg is still `ty::Param` (soundness: parametric axiom path remains as fallback when caller is also generic)
- Deduplication uses `HashMap` equality (`existing.substitutions == substitutions`) before calling `registry.register()`
- Label parts built from param name lowercased with underscore prefix (e.g., param "T" → "_t"), joined for the label string
- Collapsible if/let patterns refactored per `clippy::collapsible_match` into a single `if let` with nested tuple pattern

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] GenericArg::unpack() not available in nightly-2026-02-11**
- **Found during:** Task 1 (initial compilation)
- **Issue:** The plan specified `arg.unpack()` returning `ty::GenericArgKind::Type`, but `nightly-2026-02-11` does not expose `.unpack()` on `GenericArg`
- **Fix:** Replaced with `arg.as_type()` which returns `Option<ty::Ty<'_>>` — functionally equivalent for type-only matching; non-type args (lifetimes, consts) return `None` and are skipped via `continue`
- **Files modified:** crates/driver/src/callbacks.rs
- **Verification:** `cargo clippy --all-targets` passes clean; all tests pass
- **Committed in:** a12c8c6 (Task 1 commit)

**2. [Rule 1 - Bug] Clippy collapsible_match warnings**
- **Found during:** Task 1 (clippy run)
- **Issue:** Nested `if let` pattern for `TerminatorKind::Call { func, .. }` + `mir::Operand::Constant` + `ty::TyKind::FnDef` triggered `clippy::collapsible_match`
- **Fix:** Collapsed into a single `if let` with the `func: mir::Operand::Constant(...)` inline pattern, then used `let ... else { continue }` for the FnDef extraction
- **Files modified:** crates/driver/src/callbacks.rs
- **Verification:** `cargo clippy --all-targets` passes with no warnings from our code
- **Committed in:** a12c8c6 (Task 1 commit)

---

**Total deviations:** 2 auto-fixed (both Rule 1 - Bug: API mismatch and style)
**Impact on plan:** Both auto-fixes necessary for compilation and linting compliance. No scope creep. Implementation intent fully preserved.

## Issues Encountered

None beyond the two auto-fixed deviations above.

## Self-Check

- [x] `populate_monomorphization_registry` function exists in callbacks.rs (line 1414)
- [x] `Arc::clone(&mono_registry_arc)` used in task creation loop (not `MonomorphizationRegistry::new()`)
- [x] `MonomorphizationRegistry::new()` only appears in shared registry creation and test strings
- [x] 5 generics_driver_e2e tests all pass
- [x] Full `cargo test` suite: 0 failures
- [x] `cargo clippy --all-targets` clean

## Next Phase Readiness

- GENERICS-02 production path now active: `cargo verify` on a crate calling generic functions with concrete types will automatically populate the registry and route through `generate_vcs_monomorphized`
- The parametric axiom fallback (Phase 40) remains for functions with unresolvable generic args
- No blockers for subsequent phases

---
*Phase: 44-generics-02-monomorphization-registry-population*
*Completed: 2026-03-04*
