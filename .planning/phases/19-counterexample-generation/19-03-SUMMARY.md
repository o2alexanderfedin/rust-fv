---
phase: 19-counterexample-generation
plan: "03"
subsystem: diagnostics
tags: [ariadne, counterexample, diagnostics, source-spans, rust-fv-driver]

# Dependency graph
requires:
  - phase: 19-01
    provides: source_names field on ir::Function, fill_vc_locations, build_source_location_map
  - phase: 19-02
    provides: cex_render::render_counterexample, CexVariable/CexValue types
provides:
  - ariadne multi-label counterexample rendering at actual source spans
  - report_with_ariadne reads source file from disk via std::fs::read_to_string
  - per-variable Label messages in format "name: ty = value"
  - two-value SSA variables get (initial) and (at failure) separate Labels
  - graceful fallback to report_text_only when source file unreadable
  - source_names/locals/params threaded from ir::Function through VerificationTaskResult to VerificationFailure
affects: [20-heap-model, 21-weak-memory, diagnostics, counterexample-output]

# Tech tracking
tech-stack:
  added: [ariadne::Source (previously imported but unused)]
  patterns: [ariadne multi-source eprint pattern, byte-offset computation from line+column]

key-files:
  created: []
  modified:
    - crates/driver/src/diagnostics.rs
    - crates/driver/src/callbacks.rs
    - crates/driver/src/parallel.rs

key-decisions:
  - "Use counterexample field (raw SMT pairs) + render_counterexample in diagnostics.rs to satisfy plan's render_counterexample call requirement, rather than using counterexample_v2 directly (which already has typed data)"
  - "Add source_names/locals/params to VerificationTaskResult (not just VerificationFailure) so the data flows from parallel.rs through to callbacks.rs where VerificationFailure is constructed"
  - "Committed Task 1 and Task 2 together in a single commit to avoid clippy dead-code errors on the new fields (which would only be used after Task 2 is implemented)"
  - "Used std::fs::read_to_string for source file reading; graceful fallback avoids panics when source not on disk"

patterns-established:
  - "ariadne Label byte offsets computed as: line_start (sum of line lengths 0..line_idx) + column (1-based minus 1)"
  - "Variable search: search source_text[byte_offset..] for single-value vars; backward rfind before line_start for initial (param) label"

requirements-completed: [CEX-03]

# Metrics
duration: 8min
completed: 2026-02-20
---

# Phase 19 Plan 03: Ariadne Multi-Label Counterexample Rendering Summary

**ariadne span labels wired: report_with_ariadne reads source from disk via Source::from and places per-variable CexVariable Labels at spec use sites with "name: ty = value" format**

## Performance

- **Duration:** 8 min
- **Started:** 2026-02-20T02:04:31Z
- **Completed:** 2026-02-20T02:12:35Z
- **Tasks:** 2
- **Files modified:** 3

## Accomplishments
- `report_with_ariadne` now reads source files from disk and passes them to ariadne `Source::from` — no more unconditional `report_text_only` fallback
- `render_counterexample` called from `diagnostics.rs` to get typed `CexVariable` list for per-variable Labels
- Label format: `x: i32 = 5` (Rust declaration syntax) at the variable use site in the failing spec line
- Two-value variables (SSA initial/at_failure) get two separate Labels with `(initial)` and `(at failure)` suffixes
- `source_names`, `locals`, `params` threaded from `ir::Function` through `VerificationTaskResult` to `VerificationFailure`
- `source_column` wired from `VcLocation` (was `None` in callbacks.rs — now populated)
- Graceful fallback to `report_text_only` when source file is unreadable (e.g. test fixtures, compiled binaries)

## Task Commits

Each task was committed atomically (Tasks 1 and 2 combined in one commit to avoid dead-code clippy errors):

1. **Task 1 + Task 2: Extend VerificationFailure and wire ariadne multi-label rendering** - `100b8e6` (feat)

**Plan metadata:** _(docs commit follows)_

## Files Created/Modified
- `crates/driver/src/diagnostics.rs` - Added `source_names`/`locals`/`params` fields to `VerificationFailure`; replaced `report_with_ariadne` body with working disk-read + ariadne Label implementation; added `ariadne::Source` import
- `crates/driver/src/callbacks.rs` - Populated `source_names`/`locals`/`params` from `task_result` in `VerificationFailure` construction; `source_column` now comes from `VcLocation` instead of `None`
- `crates/driver/src/parallel.rs` - Added `source_names`/`locals`/`params` to `VerificationTaskResult`; populated them from `task.ir_func` in `verify_single()` and cached task path

## Decisions Made
- Tasks 1 and 2 committed together to avoid clippy `-D dead_code` errors on new fields that would only be live once Task 2 was complete
- `counterexample` field (raw SMT pairs) is used to call `render_counterexample` in diagnostics, satisfying the plan's `render_counterexample` call requirement (rather than duplicating data from `counterexample_v2`)
- `source_names`/`locals`/`params` are added to `VerificationTaskResult` so they flow from `parallel.rs` → `callbacks.rs` → `VerificationFailure` — this is the correct architectural seam

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Task 1 and Task 2 combined in single commit**
- **Found during:** Task 1 commit attempt
- **Issue:** Pre-commit hook enforces clippy `-D warnings`; new fields on `VerificationFailure` were flagged as dead code until Task 2 used them
- **Fix:** Implemented Task 2 before committing, then committed both together
- **Files modified:** diagnostics.rs, parallel.rs, callbacks.rs
- **Verification:** `cargo clippy --package rust-fv-driver -- -D warnings` passes cleanly
- **Committed in:** `100b8e6`

---

**Total deviations:** 1 auto-fixed (commit ordering to satisfy pre-commit hook)
**Impact on plan:** No scope creep; all plan requirements met. Tasks 1 and 2 are logically coupled anyway.

## Issues Encountered
None beyond the pre-commit hook ordering issue documented above.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- CEX-03 requirement complete: ariadne renders counterexample values as inline source spans
- `render_counterexample` is now called from both `diagnostics.rs` (ariadne output) and `parallel.rs` (JSON v2 output), establishing consistent typed rendering
- Phase 20 (heap model / separation logic) can proceed; no counterexample rendering blockers remain

---
*Phase: 19-counterexample-generation*
*Completed: 2026-02-20*
