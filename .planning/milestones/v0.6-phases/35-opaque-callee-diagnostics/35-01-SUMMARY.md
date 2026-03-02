---
phase: 35-opaque-callee-diagnostics
plan: 01
subsystem: formal-verification
tags: [rust, vcgen, diagnostics, vckind, opaque-callee, v060, v061]

# Dependency graph
requires:
  - phase: 34-cross-function-pointer-aliasing
    provides: generate_call_site_vcs structure, ContractDatabase, FunctionSummary with alias_preconditions
provides:
  - VcKind::OpaqueCallee variant (V060 warning — safe context uncontracted callee)
  - VcKind::OpaqueCalleeUnsafe variant (V061 error — unsafe context uncontracted callee)
  - generate_call_site_vcs None-arm emits always-SAT diagnostic VC instead of silently skipping
  - diagnostics.rs severity routing: OpaqueCallee → Warning, OpaqueCalleeUnsafe → Error
  - callbacks.rs vc_kind_to_string + OpaqueCallee excluded from failure push path
affects:
  - 35-02-PLAN (integration tests, end-to-end V060/V061 emission validation)
  - 36-infer-summary (callee contract inference will reduce OpaqueCallee emission)

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Always-SAT diagnostic VC pattern: SetLogic(QF_BV) + Assert(BoolLit(true)) + CheckSat, vc_kind carries diagnostic classification"
    - "Deduplication via seen_opaque HashSet keyed on (callee_name:vc_kind_debug) prevents multiple OpaqueCallee VCs per callee per function"
    - "Unsafe context escalation: func.is_unsafe_fn || unsafe_blocks.iter().any(|b| b.block_index == call_site.block_idx)"
    - "OpaqueCallee SAT = diagnostic fired (warning only), excluded from failure push path in callbacks.rs"

key-files:
  created: []
  modified:
    - crates/analysis/src/vcgen.rs
    - crates/analysis/tests/interprocedural_tests.rs
    - crates/driver/src/diagnostics.rs
    - crates/driver/src/callbacks.rs

key-decisions:
  - "OpaqueCallee diagnostic VC is always-SAT (BoolLit(true)) — SAT result means 'diagnostic fired', not 'verification failed'"
  - "OpaqueCallee SAT excluded from failure push in callbacks.rs; OpaqueCalleeUnsafe SAT IS a failure (remains in push path)"
  - "Deduplication emits at most one OpaqueCallee diagnostic per unique (callee_name, vc_kind) pair per function to avoid noise"
  - "test_call_without_contracts_treated_as_opaque updated: old behavior was silent skip, new behavior is OpaqueCallee VC emission"
  - "None contract_db still skips call-site processing entirely (no OpaqueCallee); Some(&empty_db) emits OpaqueCallee diagnostics"

patterns-established:
  - "Always-SAT diagnostic VC: use for informational/warning-level diagnostics that must surface without blocking verification"
  - "vc_kind_description + suggest_fix + vc_kind_to_string all updated atomically when adding new VcKind variants"

requirements-completed: [OPAQUE-01, OPAQUE-02]

# Metrics
duration: 18min
completed: 2026-02-28
---

# Phase 35 Plan 01: Opaque Callee Diagnostics (V060/V061) Summary

**VcKind::OpaqueCallee and OpaqueCalleeUnsafe variants replace silent skip with always-SAT diagnostic VCs for uncontracted callees, routed to Warning/Error severity through diagnostics.rs and callbacks.rs**

## Performance

- **Duration:** 18 min
- **Started:** 2026-02-28T12:27:13Z
- **Completed:** 2026-02-28T12:45:00Z
- **Tasks:** 3 (TDD RED+GREEN for vcgen, TDD RED+GREEN for driver, full verification pass)
- **Files modified:** 4

## Accomplishments

- Added `VcKind::OpaqueCallee` (V060 warning) and `VcKind::OpaqueCalleeUnsafe` (V061 error) to the enum
- Replaced `None => { tracing::debug!(...); continue; }` arm in `generate_call_site_vcs` with always-SAT diagnostic VC emission, with unsafe context detection and deduplication
- Wired severity dispatch (OpaqueCallee → Warning, OpaqueCalleeUnsafe → Error), `vc_kind_description`, `suggest_fix`, `vc_kind_to_string`, and SAT exclusion from failure push path
- 13 new unit tests across vcgen (6) and driver (7), all GREEN

## Task Commits

1. **Task 1+2 (RED+GREEN): VcKind variants + vcgen None-arm + interprocedural test fix** - `7a84c69` (feat)
2. **Task 1+2 (driver wiring): diagnostics.rs + callbacks.rs severity/vc_kind_to_string/SAT** - `82f6f3b` (feat)

## Files Created/Modified

- `crates/analysis/src/vcgen.rs` - Added OpaqueCallee/OpaqueCalleeUnsafe variants; replaced None-arm with always-SAT VC; deduplication via seen_opaque HashSet; 6 new unit tests
- `crates/analysis/tests/interprocedural_tests.rs` - Updated test_call_without_contracts_treated_as_opaque to assert OpaqueCallee VC emission (not silent skip)
- `crates/driver/src/diagnostics.rs` - vc_kind_description entries, suggest_fix entries, OpaqueCallee added to Warning severity branch; 5 new tests
- `crates/driver/src/callbacks.rs` - vc_kind_to_string entries for opaque_callee/opaque_callee_unsafe; OpaqueCallee excluded from failure push; 2 new tests

## Decisions Made

- Always-SAT diagnostic VC pattern: `SetLogic("QF_BV") + Assert(BoolLit(true)) + CheckSat` with vc_kind carrying diagnostic classification — mirrors existing DataRaceFreedom pattern
- Deduplication via `seen_opaque: HashSet<String>` keyed on `"callee_name:vc_kind_debug"` — prevents duplicate warnings for multiple call paths to the same uncontracted callee
- OpaqueCallee excluded from failure push in callbacks.rs (SAT = diagnostic fired, warning only); OpaqueCalleeUnsafe SAT IS a verification failure and stays in failure list
- `None` contract_db skips call-site processing entirely; `Some(&empty_db)` emits OpaqueCallee diagnostics — this is correct behavior, the test was updated to assert the new intent

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Updated existing test asserting silent-skip behavior**
- **Found during:** Task 3 (full test suite)
- **Issue:** `test_call_without_contracts_treated_as_opaque` in `interprocedural_tests.rs` asserted zero call-site VCs for uncontracted callee — this was the old behavior that this plan intentionally replaced
- **Fix:** Updated test assertions to verify OpaqueCallee VC is emitted (not empty), callee name appears in description, and None contract_db still produces no OpaqueCallee VCs
- **Files modified:** `crates/analysis/tests/interprocedural_tests.rs`
- **Verification:** All tests pass after update
- **Committed in:** `7a84c69` (Task 1 commit)

---

**Total deviations:** 1 auto-fixed (Rule 1 - Bug — test asserting obsolete behavior)
**Impact on plan:** Required fix. The old test was testing the exact behavior we are replacing. Update was the correct response.

## Issues Encountered

None — implementation followed plan exactly. The always-SAT VC pattern was already established by DataRaceFreedom and only required minor adaptation.

## Next Phase Readiness

- Plan 35-01 complete: OpaqueCallee/OpaqueCalleeUnsafe diagnostic VCs are emitted correctly
- Plan 35-02 (integration tests, end-to-end V060/V061) can proceed: it will test the full cargo verify pipeline producing V060/V061 output
- Phase 36 (infer_summary) context: the more uncontracted callees get contracts inferred, the fewer OpaqueCallee VCs will fire

---
*Phase: 35-opaque-callee-diagnostics*
*Completed: 2026-02-28*
