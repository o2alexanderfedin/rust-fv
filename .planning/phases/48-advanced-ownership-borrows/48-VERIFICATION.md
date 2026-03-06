---
phase: 48-advanced-ownership-borrows
verified: 2026-03-06T04:00:00Z
status: passed
score: 5/5 must-haves verified
re_verification:
  previous_status: gaps_found
  previous_score: 4/5
  gaps_closed:
    - "A function using the two-phase borrow pattern vec.push(vec.len()) verifies successfully -- no false positive conflict VC"
  gaps_remaining: []
  regressions: []
---

# Phase 48: Advanced Ownership & Borrows Verification Report

**Phase Goal:** RefCell interior mutability is tracked as ghost state, two-phase borrows and partial struct moves are modeled, disjoint field borrows are verified, and trigger inference no longer proposes datatype selector symbols
**Verified:** 2026-03-06T04:00:00Z
**Status:** passed
**Re-verification:** Yes -- after gap closure (Plan 48-04 closed COMPL-13 MIR converter gap)

## Goal Achievement

### Observable Truths

| # | Truth | Status | Evidence |
|---|-------|--------|----------|
| 1 | A function calling cell.borrow() when borrow_mut() is outstanding generates a BorrowConflict VC that Z3 resolves as SAT | VERIFIED | `generate_refcell_vcs` in vcgen.rs:5137; 11 unit tests pass |
| 2 | A function using the two-phase borrow pattern vec.push(vec.len()) verifies successfully -- no false positive conflict VC | VERIFIED | mir_converter.rs:273 detects TwoPhaseBorrow, sets BorrowPhase::Reserved; line 312 activates at call sites; borrow_conflict.rs:131 skips Reserved; 5 analysis tests + 3 E2E tests all pass |
| 3 | A function that partially moves a struct field and then reads a different field verifies successfully; reading the moved field generates UseAfterPartialMove VC | VERIFIED | `generate_partial_move_vcs` in vcgen.rs:4972 with FieldMoveTracker; 6 unit tests pass |
| 4 | A function taking &mut s.x and &s.y simultaneously verifies with disjointness confirmed; &mut s.x and &s.x produces BorrowConflict | VERIFIED | `are_borrows_field_disjoint` in borrow_conflict.rs:69; 6 unit tests pass |
| 5 | Quantifier trigger inference never proposes a datatype selector symbol as a trigger candidate | VERIFIED | `is_datatype_symbol` filter in encode_quantifier.rs:242; 7 unit tests pass |

**Score:** 5/5 truths verified

### Required Artifacts

| Artifact | Expected | Status | Details |
|----------|----------|--------|---------|
| `crates/analysis/src/encode_quantifier.rs` | is_datatype_symbol filter | VERIFIED | Function at line 242, filter at line 288 |
| `crates/analysis/src/ir.rs` | BorrowPhase enum, RefCellGhostState struct | VERIFIED | BorrowPhase at line 111, RefCellGhostState at line 618 |
| `crates/analysis/src/vcgen.rs` | BorrowConflict/UseAfterPartialMove VCs | VERIFIED | VcKind variants, generate_refcell_vcs, generate_partial_move_vcs, FieldMoveTracker |
| `crates/analysis/src/borrow_conflict.rs` | Two-phase skip, field disjointness | VERIFIED | BorrowPhase::Reserved skip at line 131, are_borrows_field_disjoint at line 69 |
| `crates/driver/src/mir_converter.rs` | TwoPhaseBorrow MIR detection, BorrowInfo population | VERIFIED | TwoPhaseBorrow detection at line 273, BorrowPhase::Reserved set at line 274, call-site activation at lines 294-317, wired to Function struct at line 350 |
| `crates/driver/src/diagnostics.rs` | V090/V091 codes | VERIFIED | V090 at line 572, V091 at line 578 |
| `crates/driver/src/callbacks.rs` | vc_kind_to_string mappings | VERIFIED | BorrowConflict at line 1696, UseAfterPartialMove at line 1697 |
| `crates/driver/tests/two_phase_borrow_e2e.rs` | E2E integration tests | VERIFIED | 141 lines, 3 tests, all pass |
| `crates/analysis/tests/trigger_filter_tests.rs` | Datatype symbol filtering tests | VERIFIED | 156 lines, 7 tests pass |
| `crates/analysis/tests/refcell_ghost_tests.rs` | RefCell ghost state tests | VERIFIED | 407 lines, 11 tests pass |
| `crates/analysis/tests/two_phase_borrow_tests.rs` | Two-phase borrow analysis tests | VERIFIED | 210 lines, 5 tests pass |
| `crates/analysis/tests/partial_move_tests.rs` | Partial move tests | VERIFIED | 235 lines, 6 tests pass |
| `crates/analysis/tests/borrow_splitting_tests.rs` | Borrow splitting tests | VERIFIED | 367 lines, 6 tests pass |

### Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| encode_quantifier.rs | find_trigger_candidates | is_datatype_symbol filter | WIRED | Filter at line 288 |
| diagnostics.rs | VcKind::BorrowConflict | V090 diagnostic code | WIRED | Line 572 |
| diagnostics.rs | VcKind::UseAfterPartialMove | V091 diagnostic code | WIRED | Line 578 |
| vcgen.rs | ir.rs | RefCellGhostState from Function.refcell_ghost_states | WIRED | Line 5147 |
| borrow_conflict.rs | ir.rs | BorrowPhase::Reserved check | WIRED | Line 131 |
| vcgen.rs | ir.rs | Projection::Field for move tracking | WIRED | FieldMoveTracker at lines 4889/4908/4935 |
| borrow_conflict.rs | ir.rs | Projection::Field for disjointness | WIRED | are_borrows_field_disjoint uses field_indices |
| mir_converter.rs | ir.rs | TwoPhaseBorrow populates BorrowPhase::Reserved | WIRED | Line 274 sets Reserved, line 350 wires borrow_infos into Function struct |
| mir_converter.rs | ir.rs | Call-site activation Reserved to Activated | WIRED | Lines 294-317 scan terminators and transition phase |

### Requirements Coverage

| Requirement | Source Plan | Description | Status | Evidence |
|-------------|------------|-------------|--------|----------|
| COMPL-08 | 48-01 | Quantifier trigger inference filters out datatype selector symbols | SATISFIED | is_datatype_symbol in encode_quantifier.rs; 7 tests pass |
| COMPL-09 | 48-02 | RefCell runtime borrow count tracked as ghost state with exclusivity VCs | SATISFIED | generate_refcell_vcs in vcgen.rs; 11 tests pass |
| COMPL-13 | 48-02, 48-04 | Two-phase borrowing modeled for method calls like vec.push(vec.len()) | SATISFIED | Analysis-level skip (5 tests) + MIR converter detection (3 E2E tests) -- full pipeline wired |
| COMPL-14 | 48-03 | Partial struct moves tracked per-field with use-after-partial-move VCs | SATISFIED | FieldMoveTracker + generate_partial_move_vcs; 6 tests pass |
| COMPL-16 | 48-03 | Borrow splitting allows simultaneous &mut s.x and &s.y verified as disjoint | SATISFIED | are_borrows_field_disjoint + extract_borrow_place; 6 tests pass |

### Anti-Patterns Found

| File | Line | Pattern | Severity | Impact |
|------|------|---------|----------|--------|
| (none found in phase 48 modified files) | - | - | - | - |

### Human Verification Required

### 1. End-to-end RefCell BorrowConflict detection

**Test:** Run `cargo verify` on a Rust file containing `RefCell::borrow()` after `borrow_mut()` and confirm V090 diagnostic is emitted
**Expected:** Verification failure with V090 diagnostic code
**Why human:** Requires a real Rust source file compiled through the full MIR pipeline; unit tests verify the analysis module in isolation

### 2. End-to-end two-phase borrow with real MIR

**Test:** Run `cargo verify` on a Rust file containing `vec.push(vec.len())` pattern
**Expected:** No false-positive BorrowConflict VC
**Why human:** E2E tests simulate MIR structure but do not exercise the full rustc MIR extraction path

### Gaps Summary

No gaps remain. The single gap from the initial verification (COMPL-13: MIR converter not populating BorrowPhase::Reserved) has been fully closed by Plan 48-04:

- `mir_converter.rs` now detects `BorrowKind::Mut { kind: TwoPhaseBorrow }` at line 273 and sets `BorrowPhase::Reserved`
- Reserved borrows transition to `BorrowPhase::Activated` at call site terminators (lines 294-317)
- The collected `borrow_infos` vec is wired into the `Function` struct at line 350
- 3 new E2E integration tests confirm the end-to-end behavior
- All 38 tests across 6 test files pass with no regressions

---

_Verified: 2026-03-06T04:00:00Z_
_Verifier: Claude (gsd-verifier)_
