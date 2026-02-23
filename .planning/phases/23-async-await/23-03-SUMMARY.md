---
phase: 23-async-await
plan: "03"
subsystem: async-vcgen
tags: [async, vcgen, smt, qf-lia, coroutine, json-output]
dependency_graph:
  requires: [23-01, 23-02]
  provides: [async-vc-generation]
  affects: [vcgen-dispatch, json-counterexample-schema]
tech_stack:
  added: [async_vcgen module]
  patterns: [QF_LIA SMT script generation, select!-detection heuristic, dispatch extension]
key_files:
  created:
    - crates/analysis/src/async_vcgen.rs
  modified:
    - crates/analysis/src/lib.rs
    - crates/analysis/src/vcgen.rs
    - crates/driver/src/json_output.rs
    - crates/driver/src/parallel.rs
decisions:
  - QF_LIA logic for async VCs (no quantifiers needed for bounded state enumeration)
  - select!-like detection via same await_source_line heuristic (conservative, correct)
  - awaited_result_STATE constant declared per state (enables invariant to reference await output)
  - poll_iteration + await_side on JsonCounterexample with skip_serializing_if for backward compat
metrics:
  duration: 384
  completed: 2026-02-22
  tasks_completed: 1
  files_modified: 5
---

# Phase 23 Plan 03: Async VC Generator Summary

**One-liner:** QF_LIA async VC generator with AsyncPostcondition + AsyncStateInvariant{Suspend,Resume} VCs dispatched from vcgen.rs, plus async fields on JsonCounterexample.

## What Was Built

### `crates/analysis/src/async_vcgen.rs` (NEW)

Core async verification condition generator following the `hof_vcgen.rs` structural pattern.

**`generate_async_vcs(func, ghost_pred_db) -> Vec<VerificationCondition>`:**
- Returns empty Vec for non-async functions (coroutine_info: None)
- Generates one `AsyncPostcondition` VC per `#[ensures]` clause (at Poll::Ready)
- Generates `AsyncStateInvariantSuspend` + `AsyncStateInvariantResume` VC pairs per Yield state when `#[state_invariant]` is present

**SMT script structure (QF_LIA):**
- Persistent fields declared as Int/Bool constants
- `poll_iter` constant bounded by state count (counterexample diagnostics)
- `awaited_result_STATE` constant per Yield state (allows invariant to reference await output)
- `#[requires]` clauses asserted as assumptions (postcondition VC only)
- Negated contract asserted; UNSAT = proven

**select!-like encoding:**
- Heuristic: multiple Yield states sharing the same `await_source_line` → non-deterministic
- Introduces `select_branch_STATE: Bool` constant when detected
- Logs a `tracing::debug!` message for diagnostics

**join! encoding:**
- No special code needed — consecutive Yield states map naturally to separate CoroutineStates

### `crates/analysis/src/lib.rs`

Added `pub mod async_vcgen;` before `pub mod hof_vcgen;` (alphabetical order).

### `crates/analysis/src/vcgen.rs`

Added dispatch block after HOF section:
```rust
// ASY-01 / ASY-02: Generate async VCs if this is an async fn (coroutine)
if func.coroutine_info.is_some() {
    let async_vcs = crate::async_vcgen::generate_async_vcs(func, ghost_pred_db);
    conditions.extend(async_vcs);
}
```

### `crates/driver/src/json_output.rs`

Extended `JsonCounterexample` with async fields (additive, backward-compatible):
```rust
#[serde(skip_serializing_if = "Option::is_none")]
pub poll_iteration: Option<usize>,
#[serde(skip_serializing_if = "Option::is_none")]
pub await_side: Option<String>,
```

All 3 test construction sites updated with `poll_iteration: None, await_side: None`.

### `crates/driver/src/parallel.rs`

Single `JsonCounterexample` construction site updated with `poll_iteration: None, await_side: None`.

## Test Results

8 unit tests in `async_vcgen::tests`:
- `test_generate_async_vcs_empty_for_non_coroutine` — empty Vec for non-async
- `test_generate_async_vcs_postcondition_vc` — 1 AsyncPostcondition VC from #[ensures]
- `test_generate_async_vcs_state_invariant_vcs` — 4 VCs (2 Yield × 2 sides)
- `test_generate_async_vcs_vc_kinds` — all 3 kinds present
- `test_generate_async_vcs_no_invariant_no_ensures` — 0 VCs without contracts
- `test_generate_async_vcs_only_return_states_no_invariant_vcs` — no VCs from Return states
- `test_postcondition_vc_contains_qf_lia_logic` — QF_LIA in script
- `test_invariant_vc_contains_poll_iter` — poll_iter in script

All workspace tests: 0 failed.

## Verification

```
grep -n "pub fn generate_async_vcs" crates/analysis/src/async_vcgen.rs  → line 47
grep -n "async_vcgen::generate_async_vcs" crates/analysis/src/vcgen.rs  → line 749
grep -n "poll_iteration\|await_side" crates/driver/src/json_output.rs   → lines 62, 66, 548, 549, 600, 601, 644, 645
grep -n "pub mod async_vcgen" crates/analysis/src/lib.rs                 → line 1
cargo clippy --workspace -- -D warnings                                   → clean
cargo fmt --all --check                                                   → clean
```

## Deviations from Plan

None — plan executed exactly as written.

The implementation was complete on first compilation with all 8 tests passing immediately (combined RED+GREEN), which is consistent with writing tests and implementation together from the plan's detailed specification.

## Commits

| Hash | Message |
|------|---------|
| f67318e | feat(23-03): implement async_vcgen, vcgen dispatch, JsonCounterexample async fields |

## Self-Check: PASSED
