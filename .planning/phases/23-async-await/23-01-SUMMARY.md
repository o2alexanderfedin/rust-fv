---
phase: 23-async-await
plan: "01"
subsystem: analysis
tags: [async, coroutine, ir, vcgen, proc-macro, state-invariant]

# Dependency graph
requires:
  - phase: 22-hof-closures
    provides: FnSpec IR types and fn_spec macro pattern used as model for state_invariant
  - phase: 24-sep04-ghost-predicate-wiring
    provides: GhostPredicateDatabase and spec_attribute pattern in macros/lib.rs
provides:
  - CoroutineExitKind, CoroutineState, CoroutineInfo types in ir.rs
  - state_invariant: Option<SpecExpr> field on Contracts struct
  - coroutine_info: Option<CoroutineInfo> field on Function struct
  - AsyncStateInvariantSuspend, AsyncStateInvariantResume, AsyncPostcondition VcKind variants
  - "#[state_invariant(expr)] proc macro attribute in macros/src/lib.rs"
  - state_invariant extraction from doc attributes in callbacks.rs extract_contracts()
affects:
  - 23-02 (MIR converter: populates coroutine_info from rustc coroutine bodies)
  - 23-03 (Async VC generator: uses VcKind async variants and state_invariant contract)
  - 23-04 (E2E async verification tests: uses all Plan 01 types)

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "spec_attribute pattern: proc macro stores expr as doc attribute rust_fv::KIND::EXPR"
    - "Option field pattern: all new IR fields default to None for backward compatibility"
    - "Exhaustive VcKind match: new variants must be added to vc_kind_to_string() and vc_kind_description()"

key-files:
  created: []
  modified:
    - crates/analysis/src/ir.rs
    - crates/analysis/src/vcgen.rs
    - crates/macros/src/lib.rs
    - crates/driver/src/callbacks.rs
    - crates/driver/src/mir_converter.rs
    - crates/driver/src/diagnostics.rs

key-decisions:
  - "CoroutineExitKind uses PartialEq derive to allow == comparison in test assertions"
  - "state_invariant field added to Contracts (not Function) to follow existing requires/ensures pattern"
  - "coroutine_info field added to Function (not Contracts) — it is structural metadata, not a contract"
  - "All Contracts construction sites updated explicitly rather than using Default::default() — maintains compile-time exhaustiveness"
  - "VcKind async variants follow naming convention: Async prefix + Suspend/Resume/Postcondition suffixes"

patterns-established:
  - "AsyncStateInvariantSuspend/Resume: check invariant at both sides of every .await boundary"
  - "AsyncPostcondition: separate from Postcondition — async fn completion is Poll::Ready, not direct return"
  - "coroutine_info: None at all existing Function construction sites — zero-overhead for non-async code"

requirements-completed:
  - ASY-01
  - ASY-02

# Metrics
duration: 25min
completed: 2026-02-22
---

# Phase 23 Plan 01: Async IR Types + #[state_invariant] Macro + Contract Extraction Summary

**CoroutineInfo/CoroutineState IR types, three async VcKind variants, #[state_invariant] proc macro, and callbacks.rs extraction — additive foundation for async verification with zero regressions**

## Performance

- **Duration:** ~25 min
- **Started:** 2026-02-22T00:00:00Z
- **Completed:** 2026-02-22T00:25:00Z
- **Tasks:** 1 (TDD: RED + GREEN + REFACTOR)
- **Files modified:** 58 files (core: 6, construction-site updates: 52)

## Accomplishments
- Added `CoroutineExitKind`, `CoroutineState`, `CoroutineInfo` types to `ir.rs` with `Debug + Clone + PartialEq`
- Added `state_invariant: Option<SpecExpr>` to `Contracts` struct and `coroutine_info: Option<CoroutineInfo>` to `Function` struct
- Added `AsyncStateInvariantSuspend`, `AsyncStateInvariantResume`, `AsyncPostcondition` to `VcKind` enum and updated all exhaustive matches
- Added `#[state_invariant(expr)]` proc macro using existing `spec_attribute` pattern
- Added `rust_fv::state_invariant::` extraction in `callbacks.rs` `extract_contracts()`
- All 1,500+ tests pass with zero regressions; cargo clippy and cargo fmt clean

## Task Commits

TDD cycle (single atomic commit):

1. **RED + GREEN + REFACTOR: Async IR types, VcKind async variants, state_invariant macro** - `638505e` (feat)

## Files Created/Modified
- `crates/analysis/src/ir.rs` - Added CoroutineExitKind/State/Info types; state_invariant on Contracts; coroutine_info on Function
- `crates/analysis/src/vcgen.rs` - Added AsyncStateInvariantSuspend/Resume/AsyncPostcondition to VcKind enum
- `crates/macros/src/lib.rs` - Added #[state_invariant(expr)] proc macro attribute
- `crates/driver/src/callbacks.rs` - Added state_invariant extraction; HirContracts state_invariant field; VcKind arms
- `crates/driver/src/mir_converter.rs` - Added coroutine_info: None to Function construction
- `crates/driver/src/diagnostics.rs` - Added AsyncState/Postcondition arms to vc_kind_description()
- 52 other files: coroutine_info/state_invariant field updates at construction sites

## Decisions Made
- `CoroutineExitKind` derives `PartialEq` to allow equality assertions in tests
- `state_invariant` placed in `Contracts` (not `Function`) following the requires/ensures precedent
- `coroutine_info` placed in `Function` (not `Contracts`) — it is structural metadata about the async state machine, not a contract clause
- Kept all existing construction sites explicit (no `..Default::default()`) to preserve compiler-enforced exhaustiveness
- `AsyncPostcondition` separate from `Postcondition` — async completion path is `Poll::Ready`, semantically different from synchronous return

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed incorrect indentation from sed substitution**
- **Found during:** REFACTOR step (cargo fmt --check)
- **Issue:** sed substitution added 20-space indentation for `state_invariant: None,` instead of 12-space
- **Fix:** cargo fmt --all normalized all indentation
- **Files modified:** 20+ test and bench files
- **Verification:** cargo fmt --all --check passes
- **Committed in:** 638505e (part of main feat commit)

**2. [Rule 1 - Bug] Removed spuriously added coroutine_info from VerificationFailure struct**
- **Found during:** GREEN step (cargo build --workspace)
- **Issue:** sed substitution added `coroutine_info: None,` to VerificationFailure constructions (wrong struct)
- **Fix:** Removed via targeted sed delete; VerificationFailure has no coroutine_info field
- **Files modified:** crates/driver/src/diagnostics.rs, crates/driver/src/parallel.rs
- **Verification:** cargo build --workspace succeeds
- **Committed in:** 638505e (part of main feat commit)

---

**Total deviations:** 2 auto-fixed (both Rule 1 - Bug: sed-induced indentation/wrong-struct issues)
**Impact on plan:** Both auto-fixes were minor mechanical corrections from batch sed substitution. No scope creep, no architectural changes.

## Issues Encountered
- Construction sites for `Contracts` and `Function` structs were spread across 58 files (stdlib_contracts, tests, benches, src). The batch `sed` approach worked but produced wrong indentation in some files and incorrectly targeted non-Function structs. Fixed by cargo fmt and targeted corrections.

## Next Phase Readiness
- Plan 02 (MIR converter) can now populate `coroutine_info` when detecting rustc coroutine MIR bodies
- Plan 03 (async VC generator) can use `AsyncStateInvariantSuspend/Resume/AsyncPostcondition` VcKind variants
- All IR foundation types are in place and tested

---
*Phase: 23-async-await*
*Completed: 2026-02-22*
