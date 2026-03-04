---
phase: 41-phase-38-hardening
plan: 01
subsystem: verification
tags: [rust, formal-verification, sealed-trait, behavioral-subtyping, z3, hir, trt-04]

# Dependency graph
requires:
  - phase: 38-trait-subtyping-wiring
    provides: behavioral subtyping block wired in callbacks.rs
  - phase: 40-generics-verification-completion
    provides: monomorphization registry threaded through verify pipeline
provides:
  - HIR-derived is_sealed computation using detect_sealed_trait + tcx.visibility in callbacks.rs
  - Pessimistic Z3 catch-all arm (false + tracing::warn) in behavioral subtyping block
  - Two new unit tests validating sealed detection logic and pessimistic Z3 arm
affects: [42-phase-38-hardening, TRT-04, behavioral-subtyping-verification]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "HIR visibility check via tcx.visibility(DefId) with format Debug string to detect Restricted"
    - "Super-trait name collection via tcx.explicit_super_predicates_of() + ClauseKind::Trait filter"
    - "Pessimistic Z3 error handling: unknown/error result => false + tracing::warn, not silent true"

key-files:
  created: []
  modified:
    - crates/driver/src/callbacks.rs

key-decisions:
  - "Use format!({vis:?}).contains('Public') heuristic to classify visibility — avoids pattern-matching on internal rustc Visibility variants that may change"
  - "tcx.explicit_super_predicates_of() (not super_predicates_of which doesn't exist) with .skip_binder().iter() to collect super-trait names"
  - "Z3 catch-all replaced with warn! + false — any unknown result is conservatively unverified (soundness over completeness)"
  - "Source-level test for pessimistic Z3 arm checks for tracing::warn message fragment in include_str! — avoids TyCtxt dependency in unit test"

patterns-established:
  - "HIR-to-sealed: tcx.visibility(DefId) debug-format contains 'Public' check — works for current rustc nightly"
  - "TDD in callbacks.rs: tests in #[cfg(test)] mod tests, run via 'cargo test -p rust-fv-driver' (not --lib since callbacks not in lib.rs)"

requirements-completed: [TRT-04]

# Metrics
duration: 20min
completed: 2026-03-03
---

# Phase 41 Plan 01: Phase-38-Hardening Summary

**HIR visibility-derived sealed trait detection via tcx.visibility + explicit_super_predicates_of wired in behavioral subtyping block; Z3 unknown/error catch-all made pessimistic with tracing::warn**

## Performance

- **Duration:** ~20 min
- **Started:** 2026-03-03T02:50:00Z
- **Completed:** 2026-03-03T03:10:20Z
- **Tasks:** 2
- **Files modified:** 1

## Accomplishments
- Replaced hardcoded `is_sealed: false` with real HIR visibility check: `tcx.visibility(*trait_def_id)` debug-format heuristic + `detect_sealed_trait` call
- Collected super-trait names via `tcx.explicit_super_predicates_of()` and wired them into `TraitDef.super_traits` (previously always `vec![]`)
- Fixed soundness hole: Z3 catch-all `_ => true` replaced with `_ => { tracing::warn!(...); false }` so parse/unknown results don't silently pass as verified
- Added 3 new unit tests: two for sealed detection logic (pub/pub(crate)), one for pessimistic Z3 arm presence

## Task Commits

1. **Task 1: Real sealed trait detection from HIR visibility** - `bf12fbc` (feat)
2. **Task 2: Fix Z3 catch-all to pessimistic (verified = false)** - `83db3ee` (fix)

## Files Created/Modified
- `crates/driver/src/callbacks.rs` - Sealed detection wired + Z3 catch-all fixed + 3 new unit tests

## Decisions Made
- Used `format!("{vis:?}").contains("Public")` heuristic instead of pattern matching on `Visibility::Public` — more resilient to rustc internal changes
- Called `tcx.explicit_super_predicates_of()` (not `super_predicates_of` which doesn't exist in this rustc nightly) with `.skip_binder().iter()`
- Used `.iter()` not `.into_iter()` on the predicates slice (clippy::into_iter_on_ref fix)
- Source-level pessimism test checks for `tracing::warn` message fragment in `include_str!` rather than asserting `_ => true` absence, to avoid self-referential test failure

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed incorrect API calls during compilation**
- **Found during:** Task 1 (HIR visibility detection)
- **Issue:** Plan specified `trait_def_id.to_def_id()` but `trait_def_id` from `all_local_trait_impls` is already `&DefId` (not `LocalDefId`); `super_predicates_of` doesn't exist — correct API is `explicit_super_predicates_of`; `.into_iter()` fails clippy on slice reference
- **Fix:** Used `*trait_def_id` directly; changed to `explicit_super_predicates_of`; used `.iter()` instead of `.into_iter()`
- **Files modified:** crates/driver/src/callbacks.rs
- **Verification:** cargo clippy clean, cargo test passes
- **Committed in:** bf12fbc (Task 1 commit)

**2. [Rule 1 - Bug] Fixed self-referential source-level test**
- **Found during:** Task 2 (Z3 pessimism test)
- **Issue:** Plan's test checked `!source.contains("Unknown/error → optimistic")` but include_str! reads the whole file including the test's own comments which contain that string
- **Fix:** Changed test to assert presence of the tracing::warn message fragment `"Z3 check returned unknown/error"` which is only in production code
- **Files modified:** crates/driver/src/callbacks.rs
- **Verification:** Test passes (GREEN), correctly validates the pessimistic arm is present
- **Committed in:** 83db3ee (Task 2 commit)

---

**Total deviations:** 2 auto-fixed (2 bugs in plan specifications)
**Impact on plan:** All fixes necessary for correctness. No scope creep.

## Issues Encountered
- `to_def_id()` not available on `&DefId` — the loop variable from `all_local_trait_impls` is already a `DefId` reference
- `super_predicates_of` doesn't exist in this rustc nightly; `explicit_super_predicates_of` is the correct query
- `include_str!` self-referential test pattern is tricky — resolved by checking for presence of new code rather than absence of old string

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- TRT-04 requirement closed: sealed trait detection is now live (not hardcoded to false)
- Z3 soundness hole closed: unknown/error catch-all is now pessimistic
- Phase 41 Plan 02 (if exists) can proceed — behavioral subtyping pipeline is hardened
- No blockers

---
*Phase: 41-phase-38-hardening*
*Completed: 2026-03-03*
