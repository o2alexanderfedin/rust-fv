---
phase: 23-async-await
plan: "02"
subsystem: driver
tags: [async, coroutine, mir, extract_coroutine_info, state-machine, rust-fv-driver]

# Dependency graph
requires:
  - phase: 23-async-await/23-01
    provides: CoroutineInfo/CoroutineState/CoroutineExitKind IR types in ir.rs; coroutine_info field on Function struct
provides:
  - extract_coroutine_info() in crates/driver/src/mir_converter.rs
  - count_coroutine_await_points() in crates/driver/src/mir_converter.rs
  - Coroutine detection wired into convert_mir() — async fn bodies produce Some(CoroutineInfo); sync fns produce None
  - Post-transform MIR shape validation documented: nightly-2026-02-11 uses SwitchInt discriminant, not TerminatorKind::Yield
affects:
  - 23-03 (Async VC generator: uses coroutine_info.states to generate per-state invariant VCs)
  - 23-04 (E2E async verification tests: relies on coroutine_info being populated by driver)

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Post-transform MIR coroutine detection: body.coroutine.is_some() + CoroutineKind::Desugared(Async, _) check"
    - "SwitchInt discriminant counting: bb0 SwitchInt targets with val >= 3 = number of .await suspension points"
    - "Persistent fields via var_debug_info: names not starting with _ are user-named locals across .await boundaries"
    - "coroutine_layout is None at after_analysis — must use var_debug_info for persistent fields (not unwrap coroutine_layout)"

key-files:
  created: []
  modified:
    - crates/driver/src/mir_converter.rs
    - crates/analysis/tests/float_verification.rs

key-decisions:
  - "Post-transform MIR has no TerminatorKind::Yield — nightly-2026-02-11 after_analysis hook sees state-machine form with SwitchInt discriminant in bb0"
  - "count_coroutine_await_points() counts SwitchInt targets with discriminant >= 3 (values 0, 1, 2 are initial/done/panicked states)"
  - "extract_coroutine_info() creates one Yield CoroutineState per .await and one Return state — matches plan structural contract"
  - "Persistent fields use var_debug_info filter (names not starting with _) — conservative but correct at after_analysis"
  - "extract_coroutine_info() and count_coroutine_await_points() are pub for testability from MIR body type-alias tests"

patterns-established:
  - "MIR shape validation first: run RUSTFLAGS=-Zunpretty=mir to verify Yield vs SwitchInt before implementing"
  - "Fallback from Yield to SwitchInt: if Yield terminators absent, count discriminant >= 3 entries in bb0 SwitchInt"
  - "coroutine_info: None for all sync fn construction sites — backward-compatible, zero-overhead for non-async code"

requirements-completed:
  - ASY-01
  - ASY-02

# Metrics
duration: 4min
completed: 2026-02-22
---

# Phase 23 Plan 02: MIR Coroutine Detection and CoroutineInfo Extraction Summary

**extract_coroutine_info() in mir_converter.rs detects async fn bodies via post-transform SwitchInt discriminant pattern (not Yield terminators), extracting states and persistent fields into ir::CoroutineInfo**

## Performance

- **Duration:** ~4 min (implementation was pre-completed in same session as Plan 01)
- **Started:** 2026-02-22T02:45:09Z
- **Completed:** 2026-02-22T02:49:09Z
- **Tasks:** 1 (TDD: RED + GREEN + REFACTOR combined in implementation commit)
- **Files modified:** 2 (mir_converter.rs + float_verification.rs auto-fix)

## Accomplishments
- Validated MIR shape: nightly-2026-02-11 `after_analysis` hook shows post-transform coroutine MIR with no `TerminatorKind::Yield`; state machine uses SwitchInt on coroutine discriminant in bb0
- Implemented `extract_coroutine_info()`: detects async fn via `body.coroutine.is_some()` + `CoroutineKind::Desugared(Async, _)`, counts suspension points from bb0 SwitchInt (discriminant >= 3), and extracts persistent fields from `var_debug_info`
- Implemented `count_coroutine_await_points()`: counts SwitchInt targets with value >= 3 to determine number of `.await` suspension points
- Wired `coroutine_info` into `convert_mir()`: async fn bodies produce `Some(CoroutineInfo)`, sync functions produce `None`
- Added 5 tests covering structural contracts: non-async = None, 1-await = 2 states, 2-await = 3 states, persistent fields shape, and function signature type checks
- All 49 workspace test suites pass, 0 failures; clippy clean; rustfmt clean

## Task Commits

TDD cycle:

1. **GREEN + REFACTOR: Coroutine detection and CoroutineInfo extraction** - `1041b4a` (feat)
2. **Auto-fix: float_verification.rs missing coroutine_info field** - `b7474bd` (fix)

## Files Created/Modified
- `crates/driver/src/mir_converter.rs` - Added `extract_coroutine_info()`, `count_coroutine_await_points()`, coroutine detection in `convert_mir()`, and 5 tests
- `crates/analysis/tests/float_verification.rs` - Auto-fix: added `coroutine_info: None` to two Function construction sites missed in Plan 01 batch update

## Decisions Made
- Post-transform MIR at `after_analysis` has no `TerminatorKind::Yield` — fallback to SwitchInt discriminant counting as documented in RESEARCH.md Pitfall strategy
- `count_coroutine_await_points()` counts discriminant targets >= 3 because values 0 (initial), 1 (done/completed), 2 (panicked) are reserved non-resume states
- `coroutine_layout` is None at `after_analysis` time — use `var_debug_info` for persistent fields (filters names starting with `_` as compiler-generated)
- Both `extract_coroutine_info()` and `count_coroutine_await_points()` are `pub` to enable unit-level type alias tests without TyCtxt

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 2 - Missing Field] Added coroutine_info: None to float_verification.rs construction sites**
- **Found during:** Post-implementation verification (cargo test --workspace)
- **Issue:** Two Function construction sites in `float_verification.rs` were missing the `coroutine_info` field added in Plan 01; they compiled because the diff was already staged but would cause issues if reverting
- **Fix:** Added `coroutine_info: None,` to both `build_float_add_function` and `build_float_mul_function` helpers
- **Files modified:** `crates/analysis/tests/float_verification.rs`
- **Verification:** `cargo build --workspace` succeeds; `cargo test -p rust-fv-analysis` passes 1192 tests
- **Committed in:** `b7474bd`

---

**Total deviations:** 1 auto-fixed (Rule 2: missing struct field at construction site)
**Impact on plan:** Minor mechanical fix; no scope creep, no architectural changes.

## Issues Encountered
- MIR shape differs from plan's RESEARCH.md Pitfall 3 — Yield terminators are NOT present at `after_analysis`. The SwitchInt fallback (documented in RESEARCH.md Pitfall strategy) was applied. The bb0 SwitchInt approach correctly identifies suspension points via discriminant value >= 3 counting.

## Next Phase Readiness
- Plan 03 (Async VC generator) can now consume `ir::Function.coroutine_info` with states and persistent_fields populated for async fn bodies
- Plan 04 (E2E tests) can verify the full pipeline produces `CoroutineInfo` with correct state counts from real async fn compilation
- All non-async functions remain unaffected (`coroutine_info: None` — zero-overhead)

---
*Phase: 23-async-await*
*Completed: 2026-02-22*
