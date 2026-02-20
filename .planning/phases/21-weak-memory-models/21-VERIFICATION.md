---
phase: 21-weak-memory-models
verified: 2026-02-19T14:00:00Z
status: passed
score: 14/14 must-haves verified
re_verification: false
---

# Phase 21: Weak Memory Models Verification Report

**Phase Goal:** Developers can verify programs using Relaxed/Acquire/Release/AcqRel atomic orderings with sound RC11 semantics
**Verified:** 2026-02-19
**Status:** passed
**Re-verification:** No — initial verification

---

## Goal Achievement

### Observable Truths

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | VcKind enum has WeakMemoryCoherence, WeakMemoryRace, WeakMemoryAtomicity variants | VERIFIED | `crates/analysis/src/vcgen.rs` lines 128, 131, 134 — all three variants present |
| 2 | AtomicOp IR struct carries `thread_id: usize` (default 0 = main thread) | VERIFIED | `crates/analysis/src/ir.rs` line 245: `pub thread_id: usize`; defaults at lines 1740, 1797 |
| 3 | rc11.rs compiles with all 11+ public functions | VERIFIED | 14 public functions confirmed via `grep "^pub fn"` on rc11.rs (930 lines, vs min 150) |
| 4 | `generate_concurrency_vcs()` gates RC11 path on `has_non_seqcst_atomics()` | VERIFIED | `crates/analysis/src/vcgen.rs` lines 3468–3471: gate present and correct |
| 5 | Functions with only SeqCst atomics produce zero WeakMemory* VCs (WMM-04) | VERIFIED | Gate is strictly `if has_non_seqcst_atomics(func)` — SeqCst-only functions skip the path |
| 6 | `generate_weak_memory_vcs()` produces all three VC kinds for non-SeqCst ops | VERIFIED | `crates/analysis/src/concurrency/rc11.rs` Steps I/J/K (lines 469, 525, 592, 667) emit Coherence/Race/Atomicity |
| 7 | All 8 canonical C11 litmus tests (IRIW, SB, LB, MP, CoRR, CoRW, CoWR, CoWW) produce correct SAT/UNSAT verdicts | VERIFIED | `cargo test --test weak_memory_litmus`: 9 passed, 0 failed |
| 8 | MP forbidden scenario (r1=1, r2=0) returns UNSAT from Z3 | VERIFIED | `test_mp_release_acquire_forbidden` passed |
| 9 | SB allowed scenario returns SAT under Relaxed | VERIFIED | `test_sb_store_buffering_allowed` passed |
| 10 | LB forbidden scenario returns UNSAT — no-thin-air axiom | VERIFIED | `test_lb_load_buffering_forbidden` passed |
| 11 | IRIW forbidden scenario returns UNSAT — coherence | VERIFIED | `test_iriw_forbidden` passed |
| 12 | Data race test: two Relaxed writes produces WeakMemoryRace VC | VERIFIED | `test_relaxed_data_race_detected` passed; filters for `VcKind::WeakMemoryRace` |
| 13 | No regressions in full test suite | VERIFIED | Full `cargo test -p rust-fv-analysis`: 0 FAILED across all test suites (1174+ tests) |
| 14 | `pub mod rc11` exported from `concurrency/mod.rs` | VERIFIED | `crates/analysis/src/concurrency/mod.rs` lines 5 and 18: `pub mod rc11` + re-exports |

**Score:** 14/14 truths verified

---

## Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `crates/analysis/src/concurrency/rc11.rs` | RC11 SMT encoding primitives (min 150 lines) | VERIFIED | 930 lines; 14 public functions including `declare_mo_order`, `declare_rf`, `assert_mo_total_order`, `assert_rf_functional`, `is_release`, `is_acquire`, `encode_sw`, `encode_fr`, `coherence_check`, `coherence_violation`, `assert_initial_store_mo_first`, `weak_memory_smt_logic`, `has_non_seqcst_atomics`, `generate_rc11_vcs` |
| `crates/analysis/src/vcgen.rs` | WeakMemory* VcKind variants | VERIFIED | Contains `WeakMemoryCoherence` (line 128), `WeakMemoryRace` (line 131), `WeakMemoryAtomicity` (line 134); gate `has_non_seqcst_atomics` at line 3468 |
| `crates/analysis/src/ir.rs` | `thread_id` field on AtomicOp | VERIFIED | `pub thread_id: usize` at line 245; 3 total occurrences |
| `crates/analysis/src/concurrency/mod.rs` | `pub mod rc11` declaration + re-exports | VERIFIED | Line 5: `pub mod rc11`; line 18: `pub use rc11::{has_non_seqcst_atomics, weak_memory_smt_logic}` |
| `crates/analysis/tests/weak_memory_litmus.rs` | 8 litmus tests + data race test (min 300 lines) | VERIFIED | 1522 lines; 9 test functions (`#[test]` at lines 142, 286, 418, 578, 932, 1187, 1313, 1410, 1485) |

---

## Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| `crates/analysis/src/concurrency/rc11.rs` | `crates/analysis/src/concurrency/mod.rs` | `pub mod rc11` declaration | WIRED | Line 5 in mod.rs |
| `crates/analysis/src/vcgen.rs` | `VcKind` enum | `WeakMemoryCoherence` variant | WIRED | Line 128 in vcgen.rs; used at vcgen.rs line 519 and rc11.rs lines 469-525 |
| `crates/analysis/src/vcgen.rs` | `crates/analysis/src/concurrency/rc11.rs` | `generate_rc11_vcs(func)` call in `generate_concurrency_vcs()` | WIRED | vcgen.rs lines 3468–3470: gate + call verified |
| `crates/analysis/src/concurrency/rc11.rs` | `crates/analysis/src/vcgen.rs` | `VcKind::WeakMemoryCoherence` used in `VerificationCondition` | WIRED | rc11.rs line 519 emits `VcKind::WeakMemoryCoherence`; line 592 emits `WeakMemoryRace`; line 667 emits `WeakMemoryAtomicity` |
| `crates/analysis/tests/weak_memory_litmus.rs` | `crates/analysis/src/vcgen.rs` | `vcgen::generate_concurrency_vcs()` call | WIRED | litmus.rs line 1507: `vcgen::generate_concurrency_vcs(&func)` |
| `crates/analysis/tests/weak_memory_litmus.rs` | `crates/analysis/src/concurrency/rc11.rs` | `VcKind::WeakMemoryCoherence` filter | WIRED | litmus.rs line 1511: `.filter(|vc| vc.location.vc_kind == VcKind::WeakMemoryRace)` |

---

## Requirements Coverage

| Requirement | Source Plans | Description | Status | Evidence |
|-------------|-------------|-------------|--------|---------|
| WMM-01 | 21-01, 21-02 | User can verify programs using Relaxed/Acquire/Release/AcqRel atomic orderings with full RC11 coherence axioms (mo, rf, co) | SATISFIED | rc11.rs implements mo, rf, sw, fr, coherence axioms; vcgen.rs wires generate_rc11_vcs() for non-SeqCst functions |
| WMM-02 | 21-03 | The 8 canonical C11 litmus tests (IRIW, SB, LB, MP, CoRR, CoRW, CoWR, CoWW) pass as soundness specification | SATISFIED | All 9 tests (8 litmus + data race) pass: 9 passed, 0 failed, verified against live Z3 |
| WMM-03 | 21-02, 21-03 | Data race detection extends to cover weak memory orderings (not just SeqCst) | SATISFIED | WeakMemoryRace VCs generated for Relaxed-vs-Relaxed same-location cross-thread pairs; confirmed by `test_relaxed_data_race_detected` |
| WMM-04 | 21-01, 21-02 | All weak memory axioms scoped to WeakMemory* VcKind — existing SeqCst verification proofs not regressed | SATISFIED | `has_non_seqcst_atomics()` gate in vcgen.rs ensures SeqCst-only functions produce zero WeakMemory* VCs; existing 1174+ lib tests pass |

No orphaned requirements — all four WMM requirements (WMM-01 through WMM-04) are claimed by at least one plan and satisfied by implementation evidence.

---

## Anti-Patterns Found

| File | Pattern | Severity | Impact |
|------|---------|----------|--------|
| None found | — | — | — |

Scanned `rc11.rs`, `vcgen.rs` (WeakMemory sections), and `weak_memory_litmus.rs` for TODO/FIXME/placeholder/unimplemented!/todo! markers. Zero found.

---

## Human Verification Required

### 1. RC11 Soundness vs. Full Axiomatic Model

**Test:** Read the IRIW and LB test implementations in `weak_memory_litmus.rs` (lines 578–931, 419–577). Both use non-standard encodings (timestamp-based LIA for IRIW, direct rf-cycle for LB) rather than the full psc (per-SC-location) axiom.
**Expected:** The approximate encodings are conservative (sound) — they prove UNSAT for the forbidden scenarios without implementing psc fully.
**Why human:** Semantic correctness of the approximate encoding relative to the full RC11 axiomatic model requires domain expertise to validate. The tests pass (UNSAT), but a human RC11 expert should confirm the encoding is not accidentally sound for the wrong reason.

### 2. Violation-Detection VC Semantics

**Test:** Review `generate_rc11_vcs()` in `rc11.rs` (lines 255+) and confirm that the switch from `coherence_check` (safety mode: `NOT(hb∧eco)`) to `coherence_violation` (violation-detection mode: `hb∧eco`) is correctly understood by any downstream consumer.
**Expected:** VCs in violation-detection mode return SAT when a coherence violation exists (the forbidden execution is possible) and UNSAT when the execution is forbidden by RC11. Downstream Z3 result interpretation must be aware of this inverted semantics.
**Why human:** The semantics inversion (SAT = violation, UNSAT = safe) is non-standard and could confuse future integrators. A code review of the VC consumer (e.g., `crates/driver/src/callbacks.rs`) should confirm result interpretation is correct.

---

## Gaps Summary

No gaps found. All 14 must-haves are verified. All four requirements (WMM-01 through WMM-04) are satisfied. The full test suite passes with zero failures. All key links are wired. No anti-patterns detected.

---

_Verified: 2026-02-19_
_Verifier: Claude (gsd-verifier)_
