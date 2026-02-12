---
phase: 06-recursive-functions
plan: 01
subsystem: analysis
tags: [proc-macro, petgraph, scc, tarjan, recursion-detection, termination]

# Dependency graph
requires:
  - phase: 05-milestone-prep (v0.1)
    provides: "Existing Contracts struct, VcKind enum, CallGraph, spec_attribute macro helper"
provides:
  - "#[decreases(expr)] proc macro for termination measures"
  - "Contracts.decreases: Option<SpecExpr> field"
  - "VcKind::Termination variant with diagnostics support"
  - "RecursiveGroup type with contains() and is_mutual()"
  - "CallGraph::detect_recursion() using petgraph tarjan_scc"
affects: [06-02, 06-03, driver-extraction, diagnostics]

# Tech tracking
tech-stack:
  added: [petgraph 0.8.3]
  patterns: [SCC-based recursion detection, self-loop check for direct recursion]

key-files:
  created: []
  modified:
    - crates/macros/src/lib.rs
    - crates/analysis/src/ir.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/call_graph.rs
    - crates/analysis/Cargo.toml
    - crates/driver/src/diagnostics.rs
    - crates/driver/src/callbacks.rs

key-decisions:
  - "Reused existing spec_attribute helper for #[decreases] -- same doc attribute encoding pattern"
  - "petgraph 0.8 for SCC analysis -- mature, well-tested, minimal dependency surface"
  - "Self-loop check for direct recursion: tarjan_scc returns size-1 SCCs for ALL nodes, only self-edge nodes are recursive"

patterns-established:
  - "Termination annotation: #[decreases(expr)] encodes as doc attribute rust_fv::decreases::EXPR"
  - "Recursion detection: CallGraph::detect_recursion() -> Vec<RecursiveGroup>"
  - "RecursiveGroup distinguishes direct (is_mutual=false) vs mutual (is_mutual=true) recursion"

# Metrics
duration: 25min
completed: 2026-02-12
---

# Phase 6 Plan 1: Recursive Function Infrastructure Summary

**#[decreases(expr)] proc macro, Contracts.decreases field, VcKind::Termination, and petgraph SCC-based recursion detection with RecursiveGroup type**

## Performance

- **Duration:** 25 min
- **Started:** 2026-02-12T07:42:37Z
- **Completed:** 2026-02-12T08:08:03Z
- **Tasks:** 2
- **Files modified:** 18

## Accomplishments
- Added `#[decreases(expr)]` proc macro using the shared `spec_attribute` helper (same pattern as requires/ensures/invariant)
- Extended `Contracts` struct with `decreases: Option<SpecExpr>` field for termination measures
- Added `VcKind::Termination` variant with full diagnostics support (description + fix suggestion)
- Added petgraph 0.8 dependency and implemented `CallGraph::detect_recursion()` using Tarjan's SCC algorithm
- Created `RecursiveGroup` type correctly handling both direct recursion (self-loops) and mutual recursion (multi-node SCCs)
- 14 new tests, 1755 total tests passing, 0 warnings

## Task Commits

Each task was committed atomically:

1. **Task 1: Add #[decreases] macro, IR extension, and VcKind::Termination** - `9a513a1` (feat)
2. **Task 2: Add petgraph dependency and SCC-based recursion detection** - `47c1ae0` (feat)

_Note: TDD tasks -- tests written first (RED), then implementation (GREEN), then refactor._

## Files Created/Modified
- `crates/macros/src/lib.rs` - Added `#[decreases(expr)]` proc macro + 4 tests
- `crates/analysis/src/ir.rs` - Added `decreases: Option<SpecExpr>` to Contracts + 2 tests
- `crates/analysis/src/vcgen.rs` - Added `VcKind::Termination` variant + 1 test
- `crates/analysis/src/call_graph.rs` - Added `RecursiveGroup`, `detect_recursion()` + 10 tests
- `crates/analysis/Cargo.toml` - Added `petgraph = "0.8"` dependency
- `crates/driver/src/diagnostics.rs` - Added Termination description + fix suggestion + 2 tests
- `crates/driver/src/callbacks.rs` - Added decreases extraction from doc attributes + vc_kind_to_string
- `crates/driver/src/cache.rs` - Added `decreases: None` to existing Contracts constructions
- Various test files (10) - Added `decreases: None` to all Contracts struct literals

## Decisions Made
- Reused `spec_attribute` helper for `#[decreases]` -- identical encoding pattern as requires/ensures/invariant, zero code duplication
- petgraph 0.8 chosen over manual Tarjan implementation -- battle-tested, minimal API surface needed
- Self-loop check essential for correctness: `tarjan_scc` returns size-1 SCCs for ALL nodes; only nodes with self-edges are truly directly recursive (pitfall #3 from research)

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Added decreases: None to all existing Contracts struct constructions**
- **Found during:** Task 1 (adding decreases field to Contracts)
- **Issue:** ~100+ explicit `Contracts { ... }` constructions across test files, bench files, driver, and analysis crate became compilation errors after adding the new field
- **Fix:** Mechanically added `decreases: None` to all existing Contracts struct literals across 12 files
- **Files modified:** contract_db.rs, monomorphize.rs, cache.rs, callbacks.rs, + 8 test/bench files
- **Verification:** `cargo test --workspace` passes all 1755 tests
- **Committed in:** 9a513a1 (Task 1 commit)

**2. [Rule 3 - Blocking] Updated driver callbacks for new Contracts field and VcKind variant**
- **Found during:** Task 1 (adding VcKind::Termination)
- **Issue:** `vc_kind_to_string` match and `extract_contracts` in callbacks.rs needed updates for exhaustive matching
- **Fix:** Added Termination case to vc_kind_to_string, decreases extraction to extract_contracts, HirContracts struct
- **Files modified:** crates/driver/src/callbacks.rs
- **Verification:** `cargo build --workspace` compiles cleanly
- **Committed in:** 9a513a1 (Task 1 commit)

**3. [Rule 3 - Blocking] Added petgraph::visit::EdgeRef import for self-loop detection**
- **Found during:** Task 2 (implementing detect_recursion)
- **Issue:** `target()` method on edge references requires `EdgeRef` trait in scope
- **Fix:** Added `use petgraph::visit::EdgeRef;` import
- **Files modified:** crates/analysis/src/call_graph.rs
- **Verification:** All 31 call_graph tests pass
- **Committed in:** 47c1ae0 (Task 2 commit)

---

**Total deviations:** 3 auto-fixed (all Rule 3 - blocking issues)
**Impact on plan:** All auto-fixes were mechanical/necessary for compilation. No scope creep.

## Issues Encountered
None -- plan executed smoothly after addressing compilation blockers.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- All infrastructure for recursive function verification is in place
- Plan 06-02 can proceed with termination VC generation using `Contracts.decreases` and `CallGraph::detect_recursion()`
- Plan 06-03 can proceed with encoding and diagnostics using `VcKind::Termination`

## Self-Check: PASSED

- All 8 key files verified present
- Commit 9a513a1 verified in git history
- Commit 47c1ae0 verified in git history
- 1755 tests pass, 0 failures, 0 warnings

---
*Phase: 06-recursive-functions, Plan: 01*
*Completed: 2026-02-12*
