---
phase: 31-z3-bv2int-fix-ghost-locals
plan: "03"
subsystem: vcgen
tags: [vcgen, smt, ghost-locals, bv2int, formal-verification, phase04-gap]

requires:
  - phase: 31-z3-bv2int-fix-ghost-locals
    provides: "TDD RED test phase04_ghost_local_leaks_into_vc scaffolded in plan 31-01"
  - phase: 31-z3-bv2int-fix-ghost-locals
    provides: "phase04_bv2int_logic_selection GREEN from plan 31-02"
  - phase: 04
    provides: "IR Local.is_ghost field; vcgen encode_assignment(); collect_declarations()"

provides:
  - "is_ghost_place() helper in vcgen.rs — searches return_local/params/locals by name, returns local.is_ghost"
  - "Ghost guard in encode_assignment() — returns None for ghost local LHS, erasing ghost assignments from executable VCs"
  - "Ghost locals filtered from collect_declarations() — declare-const not emitted for is_ghost=true locals"
  - "phase04_ghost_local_leaks_into_vc test GREEN"
  - "Phase 04 ghost locals gap fully closed"

affects:
  - 32
  - milestone-v0.1

tech-stack:
  added: []
  patterns:
    - "Ghost-filter pattern: is_ghost_place() + collect_declarations() guard — two-site erasure ensures ghost locals appear neither in declarations nor in assignment assertions"
    - "is_ghost_place() mirrors find_local_type() search pattern: return_local → params → locals"

key-files:
  created: []
  modified:
    - crates/analysis/src/vcgen.rs

key-decisions:
  - "Filtered ghost locals from collect_declarations() in addition to encode_assignment() — the test asserts __ghost_x absent from all SMT output, which includes declare-const; plan prose said 'keep declared' but the RED test (ground truth) requires complete exclusion"
  - "is_ghost_place() placed immediately after find_local_type() — same search pattern, natural proximity"
  - "collect_declarations() comment updated to reflect new behavior: ghost locals excluded, not merely 'may not be used'"

patterns-established:
  - "Ghost erasure at two sites: (1) collect_declarations() skips is_ghost locals, (2) encode_assignment() returns None for ghost LHS — complete erasure from executable VCs"

requirements-completed:
  - Phase-04-ghost

duration: 5min
completed: 2026-02-26
---

# Phase 31 Plan 03: Z3 bv2int + Ghost Locals Fix — Ghost Local Erasure Summary

**is_ghost_place() helper + two-site ghost erasure (encode_assignment + collect_declarations) closes Phase 04 ghost locals gap; phase04_ghost_local_leaks_into_vc RED→GREEN**

## Performance

- **Duration:** 5 min
- **Started:** 2026-02-26T21:13:00Z
- **Completed:** 2026-02-26T21:16:36Z
- **Tasks:** 1
- **Files modified:** 1

## Accomplishments

- Added `is_ghost_place()` helper in vcgen.rs immediately after `find_local_type()` — same search pattern (return_local/params/locals by name), returns `local.is_ghost`
- Added ghost guard at entry of `encode_assignment()`: `if is_ghost_place(place, func) { return None; }` — ghost assignments erased from SMT VCs
- Filtered ghost locals from `collect_declarations()` so `declare-const` is also excluded — complete erasure of ghost locals from executable SMT output
- `phase04_ghost_local_leaks_into_vc` test: RED → GREEN
- All 13 vcgen_completeness29 tests pass (both Phase 04 gaps now closed: bv2int + ghost)
- `cargo clippy`: 0 errors; `cargo fmt --check`: clean

## Task Commits

1. **Task 1: Add is_ghost_place() helper and guard in encode_assignment()** - `3835d0d` (feat)

## Files Created/Modified

- `crates/analysis/src/vcgen.rs` — Added is_ghost_place() helper (+21 lines), ghost guard in encode_assignment() (+5 lines), ghost filter in collect_declarations() (+2 lines changed)

## Decisions Made

- Filtered ghost locals from `collect_declarations()` in addition to `encode_assignment()`. The plan prose stated "ghost locals remain declared as SMT constants", but the RED test (the binding acceptance criterion) asserts `!all_smt.contains("__ghost_x")` — which requires no `declare-const __ghost_x` either. The test is the ground truth; the prose description was aspirational but contradicted by the test contract.
- `is_ghost_place()` placed immediately after `find_local_type()` for natural co-location of related local-search helpers.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Ghost locals must also be filtered from collect_declarations()**
- **Found during:** Task 1 (running phase04_ghost_local_leaks_into_vc test after encode_assignment fix)
- **Issue:** Plan said "ghost locals remain declared as DeclareConst" but the test asserts `!all_smt.contains("__ghost_x")` — the `(declare-const __ghost_x ...)` command still contains `__ghost_x`, causing the test to fail even after the encode_assignment() guard was added
- **Fix:** Added `if local.is_ghost { continue; }` guard in `collect_declarations()` local loop, excluding ghost locals from declare-const entirely
- **Files modified:** crates/analysis/src/vcgen.rs
- **Verification:** phase04_ghost_local_leaks_into_vc now passes GREEN; all 13 vcgen_completeness29 tests pass
- **Committed in:** 3835d0d (part of Task 1 commit)

---

**Total deviations:** 1 auto-fixed (1 bug — plan prose contradicted test contract; test is binding)
**Impact on plan:** Essential fix. Without filtering collect_declarations(), the test would remain RED. The test is the acceptance criterion and takes precedence over plan prose.

## Issues Encountered

- Plan stated "ghost locals remain declared as SMT constants" but the RED test required complete absence. Resolved by treating the RED test as the binding specification and filtering both encode_assignment() and collect_declarations().

## Next Phase Readiness

- Phase 04 ghost locals gap fully closed (both declare-const and assert erased for ghost locals)
- Phase 04 bv2int gap closed by plan 31-02
- All Phase 31 gaps resolved — Phase 31 complete
- Ready for Phase 32 (next gap closure phase)

---
*Phase: 31-z3-bv2int-fix-ghost-locals*
*Completed: 2026-02-26*

## Self-Check: PASSED

- FOUND: crates/analysis/src/vcgen.rs
- FOUND: .planning/phases/31-z3-bv2int-fix-ghost-locals/31-03-SUMMARY.md
- FOUND: 3835d0d
