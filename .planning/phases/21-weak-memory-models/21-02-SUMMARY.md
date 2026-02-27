---
phase: 21-weak-memory-models
plan: 02
subsystem: concurrency/rc11
tags: [weak-memory, rc11, vcgen, smt, qf-lia]
dependency_graph:
  requires: [21-01]
  provides: [generate_rc11_vcs, has_non_seqcst_atomics gate in vcgen]
  affects: [crates/analysis/src/concurrency/rc11.rs, crates/analysis/src/vcgen.rs]
tech_stack:
  added: []
  patterns: [RC11 axiomatic model, QF_LIA SMT encoding, sb/sw/hb/eco relational composition]
key_files:
  created: []
  modified:
    - crates/analysis/src/concurrency/rc11.rs
    - crates/analysis/src/vcgen.rs
decisions:
  - generate_rc11_vcs uses closure-based hb_term/eco_term for bounded N event sets (avoids materializing full N×N matrix)
  - WeakMemoryRace VC uses Assert(BoolLit(false)) as the check-sat script (race is evidence, not a solvable constraint)
  - WeakMemoryAtomicity generates one VC per (rmw, other_store, s1) triple to keep each SMT script focused
  - Step 2b is additive — existing DataRaceFreedom VCs from Step 2 are unchanged
metrics:
  duration: 353
  completed: 2026-02-19
  tasks_completed: 2
  files_modified: 2
---

# Phase 21 Plan 02: RC11 VC Generation Summary

**One-liner:** RC11 axiomatic VC generation (WeakMemoryCoherence/Race/Atomicity) wired into vcgen.rs behind SeqCst gate using QF_LIA SMT encoding of mo/rf/sb/sw/hb/eco relations.

## Tasks Completed

| Task | Name | Commit | Files |
|------|------|--------|-------|
| 1 | Implement generate_rc11_vcs() in rc11.rs | 34e7b34 | crates/analysis/src/concurrency/rc11.rs |
| 2 | Wire generate_rc11_vcs() into vcgen.rs with SeqCst gate | cfad845 | crates/analysis/src/vcgen.rs |

## What Was Built

### Task 1: generate_rc11_vcs()

Implemented the full RC11 VC generation algorithm in `crates/analysis/src/concurrency/rc11.rs`:

**Algorithm steps:**

- **Step A**: Partition `func.atomic_ops` into `store_ids_by_loc` and `load_ids_by_loc` maps (RMW ops appear in both)
- **Step B**: Build QF_LIA preamble — `declare_mo_order` for all store events + sentinel initial store, `declare_rf` for all (load, same-loc-store) pairs
- **Step C**: `assert_mo_total_order` per location group (including sentinel)
- **Step D**: `assert_rf_functional` per load event (reads from exactly one store)
- **Step E**: `sb(i, j)` = static predicate: same thread, i < j in program order
- **Step F**: `sw_terms[i][j]` = `encode_sw(i, ordering_i, j, ordering_j)` for release-store/acquire-load pairs connected by rf
- **Step G**: `hb_term(i, j)` = sb(i,j) OR sw(i,j) OR (exists k. sb(i,k) AND sw(k,j)) — bounded transitive closure using closures
- **Step H**: `eco_term(i, j)` = rf(i,j) OR mo(i,j) OR fr(i,j) — using `encode_fr` for the from-read component
- **Step I**: `WeakMemoryCoherence` VCs for pairs where both hb(i,j) and eco(j,i) are non-false
- **Step J**: `WeakMemoryRace` VCs for Relaxed-vs-Relaxed same-location cross-thread pairs without hb ordering
- **Step K**: `WeakMemoryAtomicity` VCs for RMW events asserting no intervening store between read-source and RMW write in mo

### Task 2: vcgen.rs SeqCst Gate

Added Step 2b to `generate_concurrency_vcs()` immediately after the existing DataRaceFreedom Step 2:

```rust
// Step 2b: RC11 weak memory axioms for non-SeqCst orderings (WMM-01, WMM-03)
if crate::concurrency::rc11::has_non_seqcst_atomics(func) {
    let mut wmm_vcs = crate::concurrency::rc11::generate_rc11_vcs(func);
    vcs.append(&mut wmm_vcs);
}
```

This ensures:
- Functions with only SeqCst atomics produce zero WeakMemory* VCs (WMM-04 regression guard)
- Existing DataRaceFreedom VCs are untouched (additive, no interference)

## Verification Results

- `cargo build -p rust-fv-analysis`: 0 errors
- `cargo clippy -p rust-fv-analysis -- -D warnings`: 0 errors (1 clippy fix: needless_range_loop in hb_term closure)
- `cargo test -p rust-fv-analysis`: all test suites pass, 0 FAILED
- `grep -c "has_non_seqcst_atomics" vcgen.rs`: 1 (gate present)

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed needless_range_loop clippy error in hb_term closure**
- **Found during:** Task 1 clippy run
- **Issue:** `for k in 0..n { ... sw_terms[k][j] }` triggered `needless_range_loop`
- **Fix:** Changed to `for (k, sw_row) in sw_terms.iter().enumerate().take(n) { ... sw_row[j] }`
- **Files modified:** crates/analysis/src/concurrency/rc11.rs
- **Commit:** 34e7b34 (folded into task commit via `cargo fmt`)

None others — plan executed as written.

## Success Criteria Verification

- [x] generate_rc11_vcs() is called from generate_concurrency_vcs() only when has_non_seqcst_atomics() returns true
- [x] WeakMemoryCoherence, WeakMemoryRace, WeakMemoryAtomicity VCs are produced for Relaxed/Acquire/Release/AcqRel functions
- [x] Zero existing test failures (WMM-04: SeqCst functions produce no WeakMemory* VCs)
- [x] cargo test -p rust-fv-analysis passes with 0 failures
- [x] cargo clippy passes with 0 errors

## Self-Check: PASSED

Files exist:
- FOUND: crates/analysis/src/concurrency/rc11.rs (generate_rc11_vcs present)
- FOUND: crates/analysis/src/vcgen.rs (has_non_seqcst_atomics gate present)

Commits exist:
- FOUND: 34e7b34 — feat(21-02): implement generate_rc11_vcs() in rc11.rs
- FOUND: cfad845 — feat(21-02): wire generate_rc11_vcs() into vcgen.rs with SeqCst gate
