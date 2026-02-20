---
phase: 19-counterexample-generation
plan: 01
subsystem: verification
tags: [rust, mir, vcgen, counterexample, source-map, var_debug_info]

# Dependency graph
requires:
  - phase: 18-bv2int-optimization
    provides: "SolverInterface trait, VcOutcome enum, differential testing infrastructure"
provides:
  - "VcOutcome::Sat carries Vec<(String,String)> structured model pairs (not flat string)"
  - "ir::Function.source_names: HashMap<String,String> maps SSA names to Rust source names"
  - "VcLocation.source_column: Option<usize> for precise error column reporting"
  - "mir_converter::build_source_names harvests body.var_debug_info for SSA name recovery"
  - "Ghost detection via __ghost_ prefix convention in local debug names"
  - "Source location plumbing: build_source_location_map + VerificationTask.source_locations"
  - "fill_vc_locations helper for direct TyCtxt+Body+FunctionVCs contexts"
affects:
  - 19-02-cex-render
  - 19-03-ariadne-labels
  - 19-04-json-output

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Pre-build source location maps in after_analysis while TyCtxt is live; pass to parallel workers via VerificationTask.source_locations"
    - "Ghost local detection via __ghost_ name prefix (proc macro convention)"
    - "Structured model pairs Vec<(String,String)> throughout solver output chain"

key-files:
  created: []
  modified:
    - "crates/analysis/src/differential.rs — VcOutcome::Sat type changed to Vec<(String,String)>"
    - "crates/analysis/src/ir.rs — Function.source_names field added"
    - "crates/analysis/src/vcgen.rs — VcLocation.source_column field added"
    - "crates/driver/src/mir_converter.rs — build_source_names + is_ghost_local helpers"
    - "crates/driver/src/callbacks.rs — build_source_location_map + fill_vc_locations helpers"
    - "crates/driver/src/parallel.rs — VerificationTask.source_locations field; worker fills VcLocations"
    - "crates/driver/src/diagnostics.rs — VerificationFailure.source_column field"
    - "crates/driver/src/json_output.rs — JsonFailure.source_column field"

key-decisions:
  - "Source location plumbing uses pre-built HashMap approach: build_source_location_map() during after_analysis while TyCtxt is live, then pass HashMap into parallel tasks — avoids TyCtxt lifetime issues in rayon threads"
  - "Ghost detection via __ghost_ name prefix is simpler than HIR attribute scanning and sufficient for the proc macro convention used in the codebase"
  - "source_column stored 1-based (col_display + 1) to match convention in source_line"

patterns-established:
  - "TyCtxt-dependent data extraction pattern: extract all needed data in after_analysis into owned structures (HashMap/Vec), pass into parallel workers without TyCtxt"
  - "Structured counterexample chain: solver returns Vec<(String,String)> assignments → VcOutcome::Sat carries them → VerificationResult.counterexample → VerificationFailure → diagnostics"

requirements-completed:
  - CEX-01

# Metrics
duration: 33min
completed: 2026-02-20
---

# Phase 19 Plan 01: Structured Counterexample Data Foundation Summary

**Structured counterexample foundation: VcOutcome::Sat carries Vec<(String,String)> model pairs, ir::Function gets source_names from var_debug_info, VcLocation gains source_column, MIR source locations plumbed into parallel verification tasks**

## Performance

- **Duration:** 33 min
- **Started:** 2026-02-20T01:03:49Z
- **Completed:** 2026-02-20T01:37:00Z
- **Tasks:** 2
- **Files modified:** 49

## Accomplishments

- Changed `VcOutcome::Sat` from `Option<String>` to `Option<Vec<(String,String)>>` throughout the entire codebase — no more fragile `split(", ")` model re-parsing
- Added `source_names: HashMap<String,String>` to `ir::Function` and implemented `build_source_names` in `mir_converter.rs` using `body.var_debug_info` for SSA-to-Rust-name recovery
- Added `source_column: Option<usize>` to `VcLocation`, `VerificationFailure`, and `JsonFailure` for precise column-level error reporting
- Implemented `build_source_location_map` in `callbacks.rs` to extract MIR `SourceInfo` spans into an owned `HashMap` while `TyCtxt` is live, then pass it to parallel workers via `VerificationTask.source_locations`
- Ghost local detection: `is_ghost_local()` marks IR locals with `__ghost_` prefix as `is_ghost: true`

## Task Commits

1. **Task 1: VcOutcome::Sat structured model pairs** - `4f0d175` (feat)
2. **Task 2: source_names, var_debug_info, ghost detection, source location plumbing** - `767cfa5` (feat)

## Files Created/Modified

- `crates/analysis/src/differential.rs` — VcOutcome::Sat type changed, format_model_detail updated, Phase 19 TDD tests added
- `crates/analysis/src/ir.rs` — Function.source_names field + TDD tests
- `crates/analysis/src/vcgen.rs` — VcLocation.source_column field
- `crates/driver/src/mir_converter.rs` — build_source_names() + is_ghost_local() helpers
- `crates/driver/src/callbacks.rs` — build_source_location_map() + fill_vc_locations() helpers, source_locations plumbing
- `crates/driver/src/parallel.rs` — VerificationTask.source_locations field; worker fills VcLocations
- `crates/driver/src/diagnostics.rs` — VerificationFailure.source_column
- `crates/driver/src/json_output.rs` — JsonFailure.source_column with serde skip_serializing_if
- 41 other files — Function/VcLocation/VerificationFailure struct literals updated with new fields

## Decisions Made

- Used `build_source_location_map` + `VerificationTask.source_locations` approach instead of passing `TyCtxt` into parallel workers, to avoid lifetime/Send constraints
- Ghost detection via `__ghost_` name prefix chosen over HIR attribute scanning (simpler, sufficient for proc macro convention)
- `source_column` stored 1-based (matching `source_line` convention)

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 2 - Missing Critical] Added source_column to VerificationFailure and JsonFailure structs**
- **Found during:** Task 2 (source location plumbing)
- **Issue:** Plan asked for source_column in VcLocation; downstream structs VerificationFailure and JsonFailure also need it for complete source location reporting
- **Fix:** Added source_column field to both structs with serde skip_serializing_if for JsonFailure
- **Files modified:** crates/driver/src/diagnostics.rs, crates/driver/src/json_output.rs
- **Verification:** All tests pass, clippy clean
- **Committed in:** 767cfa5 (Task 2)

---

**Total deviations:** 1 auto-fixed (missing critical)
**Impact on plan:** Auto-fix ensures complete source location propagation chain. No scope creep.

## Issues Encountered

- `cargo fmt` required before commit — multiple code style issues in newly added code (collapsible if, long lines in let-else). Fixed with `cargo fmt --all` before each commit.
- Pre-commit hook also checks bench targets (`benches/stress_bench.rs`, `benches/vcgen_bench.rs`) which were missed by initial `cargo build` pass. Fixed by running `cargo clippy --all-targets` before committing.
- Python script for adding `source_names` to struct literals had false positives: it incorrectly added `source_column: None` inside struct *definitions* (not struct literals) in vcgen.rs, diagnostics.rs, json_output.rs. Fixed manually.

## Next Phase Readiness

- All downstream plans (19-02 cex_render, 19-03 ariadne labels, 19-04 JSON output) can now use:
  - `result.counterexample: Vec<(String,String)>` for structured model access
  - `func.source_names` for SSA-to-source-name lookup
  - `vc.location.source_file/source_line/source_column` for precise location reporting
- No blockers

---
*Phase: 19-counterexample-generation*
*Completed: 2026-02-20*
