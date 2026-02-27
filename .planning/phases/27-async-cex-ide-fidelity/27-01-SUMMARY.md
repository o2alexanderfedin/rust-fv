---
phase: 27-async-cex-ide-fidelity
plan: "01"
subsystem: driver+vscode
tags: [async, counterexample, ide, tdd, asy-02]
dependency_graph:
  requires: []
  provides: [poll_iteration extraction, await_side inference, TypeScript interface, async context rendering, E2E test]
  affects: [crates/driver/src/parallel.rs, crates/driver/tests/async_cex_e2e.rs, vscode-extension/src/verifier.ts, vscode-extension/src/outputPanel.ts, crates/analysis/src/async_vcgen.rs]
tech_stack:
  added: []
  patterns: [TDD RED-GREEN, Rule1-AutoFix GetModel missing]
key_files:
  created: [crates/driver/tests/async_cex_e2e.rs]
  modified: [crates/driver/src/parallel.rs, crates/analysis/src/async_vcgen.rs, vscode-extension/src/verifier.ts, vscode-extension/src/outputPanel.ts]
decisions:
  - "GetModel command added to async VCs in async_vcgen.rs — without it check_sat_raw never receives model data"
  - "await_side uses pre_await/post_await strings matching public JSON API spec"
  - "AsyncPostcondition gets poll_iteration but no await_side (fires at Poll::Ready, not await point)"
metrics:
  completed: 2026-02-23
---

# Phase 27 Plan 01: Async Counterexample IDE Fidelity Summary

Wired `poll_iteration` and `await_side` through the full ASY-02 pipeline: Z3 model extraction in `build_counterexample_v2()`, TypeScript interface in `verifier.ts`, output panel rendering in `outputPanel.ts`, and E2E integration test confirming end-to-end field population.

## What Was Implemented

### Task 1: TDD — Extract poll_iteration and await_side (parallel.rs)

**RED:** Added two failing unit tests in `parallel.rs` `#[cfg(test)] mod tests`:
- `test_build_counterexample_v2_async_fields_suspension` — expects `poll_iteration=Some(2)`, `await_side=Some("pre_await")`
- `test_build_counterexample_v2_async_fields_resume` — expects `poll_iteration=Some(1)`, `await_side=Some("post_await")`
- Added `make_minimal_async_func()` helper (mirrors `wmm_race_e2e.rs` pattern) since `Function` has no `Default`

**GREEN:** Replaced `poll_iteration: None, await_side: None` placeholders in `build_counterexample_v2()` with:
- `poll_iteration`: scans `cx_pairs` for `poll_iter` key, parses as `usize`, gated on `AsyncStateInvariantSuspend | AsyncStateInvariantResume | AsyncPostcondition`
- `await_side`: `match vc_kind` — `Suspend` → `"pre_await"`, `Resume` → `"post_await"`, `_` → `None`

Key lines in `crates/driver/src/parallel.rs`: ~414-430

### Task 2: TypeScript + outputPanel + E2E (verifier.ts, outputPanel.ts, async_cex_e2e.rs)

**verifier.ts** — Added to `JsonCounterexample` interface (lines 44-46):
```typescript
poll_iteration?: number;
await_side?: string;
```

**outputPanel.ts** — Added after `violated_spec` block (lines 129-135):
```typescript
if (failure.counterexample_v2?.poll_iteration !== undefined) {
  const side = failure.counterexample_v2.await_side ?? 'unknown';
  channel.appendLine(`    Async context: poll iteration ${...}, ${side}`);
}
```

**async_cex_e2e.rs** — New E2E test `test_async_cex_e2e_async_fields_populated`:
- Builds async Function with `state_invariant: "counter >= 1"` (falsifiable, Z3 assigns counter=0)
- Runs through full driver pipeline via `verify_functions_parallel()`
- Asserts: failure exists, `vc_kind` is AsyncStateInvariant*, `counterexample_v2` is `Some`, `poll_iteration` is `Some`, `await_side` is `"pre_await"` or `"post_await"`

## Auto-fix Applied (Rule 1 — Bug)

**Missing `(get-model)` in async VCs**

- **Found during:** Task 2 E2E test (counterexample_v2 was None despite SAT result)
- **Issue:** `async_vcgen.rs` scripts ended with `(check-sat)` but not `(get-model)`. The driver uses `check_sat_raw()` which does NOT auto-append `(get-model)` (unlike `check_sat()` which does). So `parse_model()` found no `(define-fun` and returned `None`.
- **Fix:** Added `Command::GetModel` after `Command::CheckSat` in both `build_postcondition_vc()` and `build_state_invariant_vc()` in `async_vcgen.rs`
- **Files modified:** `crates/analysis/src/async_vcgen.rs` (2 sites)
- **Commit:** c220780

## Test Results

| Test | Result |
|------|--------|
| `test_build_counterexample_v2_async_fields_suspension` | PASS (poll_iteration=Some(2), await_side=Some("pre_await")) |
| `test_build_counterexample_v2_async_fields_resume` | PASS (poll_iteration=Some(1), await_side=Some("post_await")) |
| `test_async_cex_e2e_async_fields_populated` | PASS |
| `npx tsc --noEmit` | 0 errors |
| `cargo test -p rust-fv-driver` (full) | 426 passed, 0 failed |
| `cargo test -p rust-fv-analysis` (full) | 1300+ passed, 0 failed |
| `cargo clippy -p rust-fv-driver -- -D warnings` | clean |

## Commits

| Hash | Message |
|------|---------|
| 3506610 | test(27-01): add failing test for build_counterexample_v2 async fields |
| 8268ef2 | feat(27-01): extract poll_iteration and await_side in build_counterexample_v2 |
| c220780 | feat(27-01): update TypeScript interface + outputPanel rendering + async cex E2E test |

## Self-Check: PASSED
