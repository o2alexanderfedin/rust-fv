---
phase: 26-wmm03-race-detection-fix
plan: "02"
subsystem: driver
tags: [weak-memory, diagnostics, e2e-test, wmm03, concurrency]
dependency_graph:
  requires: [26-01]
  provides: [WMM-03 E2E proof, WeakMemoryRace UX]
  affects: [crates/driver/src/diagnostics.rs, crates/driver/tests/wmm_race_e2e.rs]
tech_stack:
  added: []
  patterns: [litmus-function pattern for IR construction, driver E2E test pattern]
key_files:
  created:
    - crates/driver/tests/wmm_race_e2e.rs
  modified:
    - crates/driver/src/diagnostics.rs
decisions:
  - "Follow ghost_predicate_e2e.rs VerificationTask struct pattern (name/ir_func/contract_db/ghost_pred_db fields)"
  - "Use Function.atomic_ops (not statements) with ConcurrencyConfig.verify_concurrency=true to trigger RC11 VCs"
  - "Atomic ops on thread_id=1 require one ThreadSpawn entry (0..max_thread range)"
metrics:
  duration: 317
  completed: "2026-02-23"
  tasks: 2
  files: 2
---

# Phase 26 Plan 02: WMM-03 Diagnostics UX and E2E Test Summary

**One-liner:** WeakMemoryRace added to diagnostics suggest_fix() and bounded-concurrency warning; E2E driver test proves Relaxed race surfaces end-to-end via verify_functions_parallel.

## Tasks Completed

| Task | Name | Commit | Files |
|------|------|--------|-------|
| 1 | Complete diagnostics.rs error UX for WeakMemoryRace | 96938b6 | crates/driver/src/diagnostics.rs |
| 2 | E2E driver integration test — Relaxed race surfaces as failure | 3805445 | crates/driver/tests/wmm_race_e2e.rs |

## What Was Built

### Task 1: diagnostics.rs WeakMemoryRace UX

Two additive changes to `crates/driver/src/diagnostics.rs`:

1. **`suggest_fix()` arm** (line 530): `VcKind::WeakMemoryRace => Some("Weak memory data race: use Release/Acquire ordering instead of Relaxed...")` explaining the problem (Relaxed = no ordering guarantees) with actionable remediation (Release/Acquire or Mutex).

2. **Bounded concurrency warning** (line 202): Added `|| failure.vc_kind == VcKind::WeakMemoryRace` to the condition in `report_text_only()`, ensuring WeakMemoryRace failures trigger the same bounded-concurrency warning as DataRaceFreedom, LockInvariant, Deadlock, and ChannelSafety.

### Task 2: wmm_race_e2e.rs E2E Integration Test

Created `crates/driver/tests/wmm_race_e2e.rs` with `test_relaxed_race_surfaces_as_driver_failure`:

- Builds `Function` with `atomic_ops`: two Relaxed stores to location "x" on thread 0 and thread 1
- Uses `ConcurrencyConfig { verify_concurrency: true, ... }` to enable RC11 VC generation
- Includes one `ThreadSpawn` entry for thread_id=1 (the spawned thread)
- Creates `VerificationTask` with the correct struct fields matching actual API
- Calls `verify_functions_parallel(vec![task], &mut cache, 1, false, false)`
- Asserts `results` contains at least one entry with `verified=false` and `vc_kind=VcKind::WeakMemoryRace`
- Test passes in 0.03s (Z3 available)

Key deviation from plan template: Plan showed a simplified `VerificationTask` struct and `verify_functions_parallel` API that did not match the actual codebase. Used `ghost_predicate_e2e.rs` as the authoritative reference (per plan instruction), resulting in the correct field layout: `name`, `ir_func`, `contract_db`, `ghost_pred_db`, `cache_key`, `mir_hash`, `contract_hash`, `dependencies`, `invalidation_decision`, `source_locations`.

## Verification Results

- `cargo clippy -p rust-fv-analysis -p rust-fv-driver`: 0 errors
- `cargo test -p rust-fv-analysis --test weak_memory_litmus`: 9/9 passed
- `cargo test -p rust-fv-driver --test wmm_race_e2e`: 1/1 passed
- `cargo test -p rust-fv-analysis -p rust-fv-driver`: all tests passed, 0 failures

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Plan template used wrong VerificationTask API**
- **Found during:** Task 2 (before writing the file, per plan's own instruction to read reference files)
- **Issue:** Plan showed `VerificationTask { function: func, cache: Arc::new(VcCache::new(&cache_dir)), invalidation: InvalidationDecision { ... }, ... }` which doesn't match the actual struct with fields `name`, `ir_func`, `contract_db`, `ghost_pred_db`, `cache_key`, `mir_hash`, `contract_hash`, `dependencies`, `invalidation_decision`, `source_locations`.
- **Fix:** Read `ghost_predicate_e2e.rs` as instructed by the plan itself, then used the correct struct layout. Also read `parallel.rs` to confirm `verify_functions_parallel` signature takes `(&mut VcCache, usize, bool, bool)` not `Arc<VcCache>`.
- **Files modified:** `crates/driver/tests/wmm_race_e2e.rs`
- **Commit:** 3805445

**2. [Rule 3 - Blocking] Plan showed Statement::AtomicStore which doesn't exist**
- **Found during:** Task 2 research (plan's own instruction to verify IR struct field names)
- **Issue:** Plan's code template used `Statement::AtomicStore(AtomicOp { ... })` but the actual IR uses `Function.atomic_ops: Vec<AtomicOp>` (not embedded in statements). Statements are `Assign`, `Nop`, etc.
- **Fix:** Placed atomic ops in `Function.atomic_ops` with `ConcurrencyConfig.verify_concurrency=true` following the `make_litmus_function` pattern from `weak_memory_litmus.rs`.
- **Files modified:** `crates/driver/tests/wmm_race_e2e.rs`
- **Commit:** 3805445

**3. [Rule 1 - Format] rustfmt reformatted multi-line format! in assert**
- **Found during:** Task 2 pre-commit hook
- **Fix:** Ran `cargo fmt` — format!("...{} {:?}", r.verified, r.vc_location.vc_kind) collapsed to single line.
- **Commit:** 3805445 (re-committed after format fix)

## WMM-03 Requirements — All 4 Criteria Satisfied

1. WeakMemoryRace VC body has race-existence constraints (not Assert(BoolLit(false))) — verified by rc11.rs (Plan 26-01)
2. Driver pipeline interprets SAT as race error — verified by `test_relaxed_race_surfaces_as_driver_failure` (this plan)
3. `test_relaxed_data_race_detected` asserts Z3 SAT — verified by weak_memory_litmus test (Plan 26-01)
4. E2E integration test proves race error surfaces end-to-end — verified by `wmm_race_e2e.rs` (this plan)

## Self-Check: PASSED

- diagnostics.rs: FOUND
- wmm_race_e2e.rs: FOUND
- 26-02-SUMMARY.md: FOUND
- Commit 96938b6: FOUND
- Commit 3805445: FOUND
