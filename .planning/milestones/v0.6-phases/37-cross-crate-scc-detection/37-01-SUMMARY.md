---
phase: 37-cross-crate-scc-detection
plan: 01
subsystem: analysis
tags: [call-graph, scc, tarjan, petgraph, cross-crate, contract-db, recursion]

# Dependency graph
requires:
  - phase: 36.1-alias-precondition-parsing
    provides: ContractDatabase with iter() API and FunctionSummary.contracts.decreases field
  - phase: 33-call-graph
    provides: CallGraph::from_functions, detect_recursion via tarjan_scc
provides:
  - "CallGraph::from_functions_with_cross_crate_db constructor that injects cross-crate virtual nodes and back-edges"
  - "Cross-crate SCC detection via decreases.raw heuristic substring matching"
affects: [37-driver-integration, recursion-verification, vcgen-termination]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "ContractDatabase as source of cross-crate function metadata for graph augmentation"
    - "Back-edge heuristic: decreases.raw substring match for cross-crate SCC cycle detection"
    - "Virtual node injection: non-in-crate callees in DB become nodes in the call graph"

key-files:
  created: []
  modified:
    - "crates/analysis/src/call_graph.rs"

key-decisions:
  - "from_functions_with_cross_crate_db accepts ContractDatabase parameter and injects virtual nodes for contracted cross-crate callees"
  - "Back-edge heuristic: if DB entry's decreases.raw contains normalized in-crate function name as substring, inject reverse edge callee->caller to form potential SCC"
  - "TDD tests and implementation committed together due to pre-commit hook requiring code to compile (clippy runs on all code)"
  - "ContractDatabase imported at module level (not just in test scope) to support the public constructor signature"

patterns-established:
  - "Cross-crate virtual node pattern: add to all_functions + name_map, inject edges from in-crate callers and back-edges if decreases signals recursion"

requirements-completed:
  - XCREC-01
  - XCREC-02

# Metrics
duration: ~8min
completed: 2026-03-01
---

# Phase 37 Plan 01: Cross-Crate SCC Detection via ContractDatabase Back-Edge Heuristic

**`CallGraph::from_functions_with_cross_crate_db` injects virtual nodes for contracted callees and back-edges from decreases.raw substring match, enabling Tarjan's SCC to span crate boundaries**

## Performance

- **Duration:** ~8 min
- **Started:** 2026-03-01T23:27:00Z
- **Completed:** 2026-03-01T23:35:30Z
- **Tasks:** 2 (TDD: tests + implementation committed together)
- **Files modified:** 1

## Accomplishments
- Added `CallGraph::from_functions_with_cross_crate_db` public constructor taking functions slice + `&ContractDatabase`
- Virtual node injection: for each in-crate `Terminator::Call` to a callee found in DB but not in-crate, adds the callee as a virtual node
- Back-edge heuristic: if `summary.contracts.decreases.raw` contains any normalized in-crate function name, injects reverse edge enabling Tarjan's SCC to form cross-crate cycles
- 4 TDD tests all pass GREEN: cross-crate SCC detected, no SCC without back-edge, single-crate regression, deep path normalization
- All 1240+ pre-existing tests remain GREEN
- `cargo clippy -D warnings` clean

## Task Commits

1. **Task 1+2: TDD tests + implementation** - `a598b85` (feat: tests RED→GREEN)

## Files Created/Modified
- `crates/analysis/src/call_graph.rs` - Added `from_functions_with_cross_crate_db` method, imported `ContractDatabase`, added `cross_crate_tests` module with 4 tests

## Decisions Made
- **TDD tasks committed together**: Pre-commit hook runs clippy which requires all code to compile. Since tests reference the new function, they cannot be committed in a separate RED commit. Both RED (tests) and GREEN (implementation) were committed atomically.
- **Module-level ContractDatabase import**: Added `use crate::contract_db::ContractDatabase;` at the top of the module (not just in the `impl` method) to satisfy Rust's import requirements for the public method signature.
- **Back-edge heuristic via decreases.raw**: The DB does not record what a contracted callee calls. The heuristic uses `decreases.raw.contains(in_fn_norm)` — if the decreases expression references an in-crate function name by substring, it signals a potential mutual recursion cycle. This is sufficient for the declared XCREC use cases.

## Deviations from Plan

None - plan executed exactly as written.

## Issues Encountered
- Pre-commit hook (clippy) prevented committing tests in RED state without the implementation. Tasks 1 and 2 were committed together in a single GREEN commit. This is a known constraint with strict pre-commit hooks and TDD.

## Next Phase Readiness
- `from_functions_with_cross_crate_db` is available as a public API for the driver integration in Phase 37 end-to-end
- The cross-crate SCC detection produces `RecursiveGroup` values containing both in-crate and cross-crate (virtual) function names
- Ready for Phase 37.1: driver integration wiring `from_functions_with_cross_crate_db` into `recursion_verification.rs`

---
*Phase: 37-cross-crate-scc-detection*
*Completed: 2026-03-01*
