---
phase: 36-summary-contract-inference
plan: 02
subsystem: analysis
tags: [rust, formal-verification, json-output, contract-inference, serde, integration-tests]

# Dependency graph
requires:
  - phase: 36-summary-contract-inference
    plan: 01
    provides: "is_inferred flag on FunctionSummary, OpaqueCallee suppression in vcgen, infer_summary proc-macro"
  - phase: 35-opaque-callee-diagnostics
    provides: "VcKind::OpaqueCallee diagnostic pattern, ContractDatabase, FunctionSummary"
provides:
  - "InferredSummary struct in json_output.rs with callee and contract fields"
  - "inferred_summaries: Option<Vec<InferredSummary>> field on JsonVerificationReport with skip_serializing_if"
  - "ContractDatabase::iter() method for iterating all (name, summary) pairs"
  - "callbacks.rs wiring: collects is_inferred entries from contract_db into JSON report"
  - "Integration tests: test_infer_summary_suppresses_opaque_callee, test_infer_summary_no_suppression_without_flag"
  - "JSON serialization tests: test_inferred_summaries_json_field"
  - "OPAQUE-03 requirement fully satisfied"
affects: [phase-37-cross-crate-recursion, any phase using JsonVerificationReport]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "skip_serializing_if = Option::is_none for optional JSON fields (field absent when None, not null)"
    - "contract_db.iter().filter(|(_, s)| s.is_inferred) pattern for collecting inferred summaries"
    - "if inferred.is_empty() { None } else { Some(inferred) } pattern for Option population"

key-files:
  created: []
  modified:
    - crates/driver/src/json_output.rs
    - crates/driver/src/callbacks.rs
    - crates/analysis/src/contract_db.rs
    - crates/analysis/src/vcgen.rs

key-decisions:
  - "inferred_summaries omitted entirely (None) when no infer_summary callees — skip_serializing_if ensures field absent rather than null or empty array"
  - "contract string hardcoded as 'pure: reads nothing, writes nothing' for conservative inference — consistent with Phase 36-01 semantic"
  - "ContractDatabase::iter() added as public API — minimal change enabling callbacks.rs to enumerate all entries without exposing HashMap directly"
  - "test_infer_summary_no_suppression_without_flag uses empty contract_db (callee absent) rather than is_inferred=false — mirrors real-world behavior where unannotated callees are simply missing from DB"

patterns-established:
  - "JSON report observability pattern: optional top-level arrays use Option<Vec<T>> with skip_serializing_if"
  - "Integration test naming: test_infer_summary_* for Phase 36 regression guard"

requirements-completed: [OPAQUE-03]

# Metrics
duration: 0min
completed: 2026-02-28
---

# Phase 36 Plan 02: Summary Contract Inference — JSON Observability Summary

**`inferred_summaries` JSON field added to verification report with `InferredSummary{callee, contract}` struct, callbacks.rs wiring from contract_db.iter(), and 3 integration tests confirming suppression behavior and field stability**

## Performance

- **Duration:** Continuation (all code already committed in prior session)
- **Started:** 2026-02-28
- **Completed:** 2026-02-28
- **Tasks:** 2 of 2
- **Files modified:** 4

## Accomplishments

- Added `InferredSummary { callee: String, contract: String }` struct to `json_output.rs` with `Serialize, Deserialize, Debug, Clone, PartialEq` derives
- Added `inferred_summaries: Option<Vec<InferredSummary>>` field to `JsonVerificationReport` with `#[serde(skip_serializing_if = "Option::is_none")]` so field is fully absent (not null) when no infer_summary callees exist
- Added `ContractDatabase::iter()` method returning `impl Iterator<Item = (&String, &FunctionSummary)>`
- Wired `inferred_summaries` population in `callbacks.rs` JSON report build by iterating contract_db, filtering `is_inferred == true`, and constructing `InferredSummary` entries
- Added 6 tests in `json_output.rs` covering None-absent, Some-present, roundtrip, multiple entries, and the named `test_inferred_summaries_json_field` integration test
- Added 3 tests in `contract_db.rs` covering iter() on empty DB, iter() yielding all entries, and the `filter(is_inferred)` pattern
- Added `test_infer_summary_suppresses_opaque_callee` and `test_infer_summary_no_suppression_without_flag` in `vcgen.rs`
- All 212+ workspace tests pass; `cargo clippy --workspace -- -D warnings` clean

## Task Commits

Each task was committed atomically:

1. **Task 1: Add InferredSummary struct and inferred_summaries field to JSON report** - `9438fd0` (feat)
2. **Task 2: Wire inferred_summaries into callbacks.rs JSON build and write integration tests** - `4e8e453` (feat)

## Files Created/Modified

- `crates/driver/src/json_output.rs` — Added `InferredSummary` struct, `inferred_summaries` field on `JsonVerificationReport`, and 6 serialization tests
- `crates/driver/src/callbacks.rs` — Added `contract_db.iter().filter(is_inferred)` → `inferred_summaries` wiring in JSON report construction
- `crates/analysis/src/contract_db.rs` — Added `iter()` method and 3 tests demonstrating the filter pattern
- `crates/analysis/src/vcgen.rs` — Added `test_infer_summary_suppresses_opaque_callee` and `test_infer_summary_no_suppression_without_flag` integration tests

## Decisions Made

- `inferred_summaries` is omitted entirely when no infer_summary callees (not null, not empty array) — `skip_serializing_if = "Option::is_none"` enforces this cleanly
- `contract` string hardcoded as `"pure: reads nothing, writes nothing"` — consistent with conservative inference semantic established in Phase 36-01
- `ContractDatabase::iter()` exposes the underlying `HashMap::iter()` as a public method — minimal invasive change
- `test_infer_summary_no_suppression_without_flag` uses empty contract_db (callee absent) rather than `is_inferred=false` — accurately reflects real-world behavior

## Deviations from Plan

None — plan executed exactly as written. All artifacts were already committed in a prior session as part of Phase 36-01/36-02 work.

## Issues Encountered

None.

## User Setup Required

None — no external service configuration required.

## Next Phase Readiness

- OPAQUE-03 fully satisfied: `#[verifier::infer_summary]` suppresses OpaqueCallee VCs and appears in `inferred_summaries` JSON field
- Phase 37 (cross-crate recursion, XCREC) is ready to proceed
- Cross-crate MIR availability for Tarjan's SCC across crate boundaries remains a noted concern for Phase 37 planning

---
*Phase: 36-summary-contract-inference*
*Completed: 2026-02-28*
