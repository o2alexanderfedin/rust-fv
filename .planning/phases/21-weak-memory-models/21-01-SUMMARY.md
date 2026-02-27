---
phase: 21-weak-memory-models
plan: 01
subsystem: concurrency
tags: [rc11, weak-memory, smt-encoding, ir-extension, vcgen]
dependency_graph:
  requires: []
  provides: [rc11-primitives, thread_id-on-AtomicOp, WeakMemory-VcKind-variants]
  affects: [vcgen, ir, concurrency/mod]
tech_stack:
  added: [QF_LIA integer arithmetic for mo ordering, RC11 formal model encoding]
  patterns: [bounded SMT encoding, integer modification order positions, functional rf constraints]
key_files:
  created:
    - crates/analysis/src/concurrency/rc11.rs
  modified:
    - crates/analysis/src/ir.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/concurrency/mod.rs
    - crates/analysis/tests/concurrency_verification.rs
    - crates/driver/src/callbacks.rs
    - crates/driver/src/diagnostics.rs
decisions:
  - "Use Term::IntLt for QF_LIA mo comparison (not Term::BvSLt) — correct for integer mo positions"
  - "encode_fr takes store_s2 as explicit parameter (not inside store_events) — cleaner API"
  - "thread_id defaults to 0 at all existing construction sites — backward compatible"
metrics:
  duration_seconds: 452
  completed_date: "2026-02-20"
  tasks_completed: 2
  files_changed: 6
---

# Phase 21 Plan 01: RC11 Weak Memory Foundation Summary

RC11 SMT encoding foundation with mo/rf/sw/fr primitives using QF_LIA integer arithmetic, thread_id on AtomicOp, and three WeakMemory* VcKind variants.

## What Was Built

### Task 1: IR Extension and VcKind Variants (commit aaf156b)

Extended `AtomicOp` struct in `ir.rs` with:
- `pub thread_id: usize` — identifies which thread performs each atomic op (0 = main)

Extended `VcKind` enum in `vcgen.rs` with three new variants:
- `WeakMemoryCoherence` — RC11 coherence check (hb;eco? irreflexive)
- `WeakMemoryRace` — conflicting Relaxed accesses without ordering
- `WeakMemoryAtomicity` — RMW atomicity under RC11 (rmw ∩ (rb;mo) = ∅)

Updated all 14 AtomicOp construction sites across:
- `crates/analysis/src/ir.rs` (2 test sites)
- `crates/analysis/src/vcgen.rs` (2 test sites)
- `crates/analysis/tests/concurrency_verification.rs` (12 sites)

Added WeakMemory* match arms in exhaustive matches:
- `crates/driver/src/callbacks.rs` — `vc_kind_to_string()`
- `crates/driver/src/diagnostics.rs` — `vc_kind_description()`

### Task 2: RC11 SMT Encoding Module (commit 24e6cea)

Created `crates/analysis/src/concurrency/rc11.rs` (467 lines) implementing 11 public functions:

1. `declare_mo_order(event_id)` — `(declare-fun mo_order_N () Int)`
2. `declare_rf(load, store)` — `(declare-fun rf_L_S () Bool)`
3. `assert_mo_total_order(events)` — distinctness constraints for strict total order
4. `assert_rf_functional(load, stores)` — at-least-one + at-most-one rf constraints
5. `is_release(ordering)` — Release/AcqRel/SeqCst predicate
6. `is_acquire(ordering)` — Acquire/AcqRel/SeqCst predicate
7. `encode_sw(store, store_ord, load, load_ord)` — synchronizes-with as rf when release+acquire
8. `encode_fr(load, store_s2, store_events)` — from-read using `IntLt(mo_order_s1, mo_order_s2)`
9. `coherence_check(i, j, hb_i_j, eco_j_i)` — `(assert (not (and hb eco)))`
10. `weak_memory_smt_logic()` — returns `"QF_LIA"`
11. `has_non_seqcst_atomics(func)` — gate: any non-SeqCst atomic op

Added `pub mod rc11` and re-exports to `concurrency/mod.rs`.

## Verification Results

- `cargo build -p rust-fv-analysis`: 0 errors
- `cargo test -p rust-fv-analysis --lib`: 1174 passed, 0 failed (25 new RC11 tests)
- `cargo clippy -p rust-fv-analysis -- -D warnings`: 0 errors
- WeakMemoryCoherence matches in vcgen.rs: 3
- rc11.rs line count: 467 (> 150 minimum)
- thread_id in ir.rs: 3 occurrences

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 2 - Missing Critical Functionality] Added WeakMemory* match arms in driver crate**
- **Found during:** Task 1 commit (pre-commit hook)
- **Issue:** Non-exhaustive match patterns in `callbacks.rs` and `diagnostics.rs` after adding new VcKind variants
- **Fix:** Added match arms for `WeakMemoryCoherence`, `WeakMemoryRace`, `WeakMemoryAtomicity` in both files
- **Files modified:** `crates/driver/src/callbacks.rs`, `crates/driver/src/diagnostics.rs`
- **Commit:** aaf156b (included in Task 1 commit)

**2. [Rule 1 - Bug] Applied rustfmt to rc11.rs before commit**
- **Found during:** Task 2 commit (pre-commit hook)
- **Issue:** rustfmt reformatted `declare_rf` multi-line body to single line, and collapsed import list
- **Fix:** Applied `cargo fmt` to normalize formatting
- **Files modified:** `crates/analysis/src/concurrency/rc11.rs`

## Self-Check: PASSED

- FOUND: crates/analysis/src/concurrency/rc11.rs
- FOUND: crates/analysis/src/ir.rs
- FOUND: crates/analysis/src/vcgen.rs
- FOUND: crates/analysis/src/concurrency/mod.rs
- FOUND commit: aaf156b (Task 1)
- FOUND commit: 24e6cea (Task 2)
