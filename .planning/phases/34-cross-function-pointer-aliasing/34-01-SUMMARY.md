---
phase: 34-cross-function-pointer-aliasing
plan: 01
subsystem: analysis
tags: [formal-verification, smt, aliasing, pointer, heap-model, vcgen, spec-parser, contract-db]

# Dependency graph
requires: []
provides:
  - generate_alias_check_assertion(p, q) in heap_model.rs returning Term::Eq
  - generate_alias_check_assertion_from_terms(p, q) for pre-built SMT terms
  - VcKind::PointerAliasing variant in vcgen.rs for alias VC classification
  - alias(p, q) parse arm in spec_parser.rs convert_call()
  - AliasPrecondition struct with param_idx_a, param_idx_b, raw fields
  - alias_preconditions: Vec<AliasPrecondition> field on FunctionSummary
affects:
  - 34-cross-function-pointer-aliasing/34-02 (call-site alias VC injection)

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Alias-check assertion follows same shape as null_check_assertion: Term::Eq over Const terms"
    - "AliasPrecondition stored by parameter index (not name) to survive call-site substitution"
    - "VcKind enum extended with new variant; all existing match arms updated in callbacks.rs and diagnostics.rs"

key-files:
  created: []
  modified:
    - crates/analysis/src/heap_model.rs
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/spec_parser.rs
    - crates/analysis/src/contract_db.rs
    - crates/driver/src/callbacks.rs
    - crates/driver/src/diagnostics.rs
    - crates/analysis/benches/stress_bench.rs
    - crates/analysis/src/stdlib_contracts/types.rs
    - crates/analysis/src/stdlib_contracts/option.rs
    - crates/analysis/src/stdlib_contracts/result.rs
    - crates/analysis/src/stdlib_contracts/vec.rs
    - crates/analysis/src/stdlib_contracts/hashmap.rs
    - crates/analysis/src/stdlib_contracts/iterator.rs
    - crates/analysis/src/stdlib_contracts/string.rs
    - crates/analysis/src/stdlib_contracts/override_check.rs
    - crates/analysis/tests/interprocedural_tests.rs
    - crates/analysis/tests/ownership_tests.rs
    - crates/analysis/tests/sep_logic_integration.rs
    - crates/analysis/tests/stdlib_override_test.rs

key-decisions:
  - "generate_alias_check_assertion mirrors generate_null_check_assertion pattern: returns Term::Eq(Const(p), Const(q)) — same shape as existing heap model helpers"
  - "AliasPrecondition stores parameter indices (not names) so Plan 02 call-site injection survives argument substitution"
  - "alias(p, q) parse arm returns Some(Term::Eq) directly from spec_parser via generate_alias_check_assertion_from_terms — no intermediate representation"
  - "alias_preconditions defaults to vec![] on all existing FunctionSummary sites — zero-cost for callee functions without alias specs"

patterns-established:
  - "Alias check SMT pattern: Term::Eq(Const(p), Const(q)) — SAT means aliasing violation found"
  - "FunctionSummary extension: new field alias_preconditions with empty vec default for backward compatibility"
  - "VcKind variant addition: requires updating vc_kind_to_string in callbacks.rs and vc_kind_description in diagnostics.rs"

requirements-completed: [ALIAS-01, ALIAS-02]

# Metrics
duration: 12min
completed: 2026-02-28
---

# Phase 34 Plan 01: Cross-Function Pointer Aliasing Core Infrastructure Summary

**SMT alias-check assertion helper, VcKind::PointerAliasing variant, alias(p,q) spec_parser arm, and AliasPrecondition/FunctionSummary extension wired as Plan 02 call-site injection foundation**

## Performance

- **Duration:** ~12 min
- **Started:** 2026-02-28T10:52:00Z
- **Completed:** 2026-02-28T11:04:10Z
- **Tasks:** 1 (TDD: RED + GREEN + REFACTOR combined)
- **Files modified:** 19

## Accomplishments

- Added `generate_alias_check_assertion("p", "q")` to `heap_model.rs` returning `Term::Eq(Const("p"), Const("q"))` — SAT semantics match aliasing violation detection
- Added `generate_alias_check_assertion_from_terms(p, q)` used by `spec_parser` when converting `alias(p, q)` annotation expressions
- Added `VcKind::PointerAliasing` after `MemorySafety` in `vcgen.rs` with full match arm coverage in `callbacks.rs` and `diagnostics.rs`
- Added `"alias"` parse arm in `spec_parser.rs` `convert_call()` with arity validation (rejects wrong-arity calls with tracing warn)
- Added `AliasPrecondition { param_idx_a, param_idx_b, raw }` struct and `alias_preconditions: Vec<AliasPrecondition>` field to `FunctionSummary`
- Updated all `FunctionSummary` construction sites across 19 files with `alias_preconditions: vec![]`
- All 9 new tests pass; all 1211+ existing tests remain GREEN

## Task Commits

1. **Task 1: Full TDD cycle (RED+GREEN+REFACTOR)** - `ed3aeb1` (feat)

## Files Created/Modified

- `crates/analysis/src/heap_model.rs` - Added `generate_alias_check_assertion` and `generate_alias_check_assertion_from_terms` with 3 new unit tests
- `crates/analysis/src/vcgen.rs` - Added `VcKind::PointerAliasing` variant; updated `FunctionSummary` construction sites in tests
- `crates/analysis/src/spec_parser.rs` - Added `"alias"` parse arm in `convert_call()`; added `make_alias_func()` helper and 4 new tests
- `crates/analysis/src/contract_db.rs` - Added `AliasPrecondition` struct; added `alias_preconditions` field to `FunctionSummary`; added 2 new tests
- `crates/driver/src/callbacks.rs` - Added `VcKind::PointerAliasing => "pointer_aliasing"` match arm; updated `FunctionSummary` construction
- `crates/driver/src/diagnostics.rs` - Added `VcKind::PointerAliasing => "pointer aliasing violation"` match arm
- `crates/analysis/benches/stress_bench.rs` - Updated 3 `FunctionSummary` construction sites with `alias_preconditions: vec![]`
- `crates/analysis/src/stdlib_contracts/*.rs` - Updated all `FunctionSummary` construction sites (hashmap, iterator, option, override_check, result, string, types, vec)
- `crates/analysis/tests/*.rs` - Updated `FunctionSummary` construction sites in interprocedural, ownership, sep_logic, stdlib_override tests

## Decisions Made

- `generate_alias_check_assertion` mirrors `generate_null_check_assertion` pattern: returns `Term::Eq(Const(p), Const(q))` — same shape keeps heap_model helpers consistent
- `AliasPrecondition` stores parameter indices (not names) so Plan 02 call-site injection survives argument substitution correctly
- `alias(p, q)` parse arm returns `Some(Term::Eq)` directly via `generate_alias_check_assertion_from_terms` — no intermediate representation needed
- `alias_preconditions` defaults to `vec![]` on all existing construction sites — zero-cost for callee functions without alias specs

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Fixed missing alias_preconditions field in bench and stdlib files**
- **Found during:** Task 1 (commit attempt triggered clippy pre-commit hook)
- **Issue:** `stress_bench.rs` and 16 other files with `FunctionSummary` struct literals were missing the new `alias_preconditions` field, causing compile error E0063
- **Fix:** Added `alias_preconditions: vec![]` to all `FunctionSummary` construction sites in stdlib_contracts, tests, benches, and driver files
- **Files modified:** 15 additional files beyond the 4 plan targets
- **Verification:** `cargo clippy -p rust-fv-analysis --benches -- -D warnings` passes; all tests GREEN
- **Committed in:** ed3aeb1 (combined with main implementation)

---

**Total deviations:** 1 auto-fixed (Rule 3 - blocking compilation error in bench/stdlib/driver files)
**Impact on plan:** Necessary propagation of struct field addition to all construction sites. No scope creep — all fixes are mechanical `alias_preconditions: vec![]` additions.

## Issues Encountered

None beyond the auto-fixed missing field propagation.

## User Setup Required

None - no external service configuration required.

## Self-Check: PASSED

- `ed3aeb1` exists in git log: confirmed
- `crates/analysis/src/heap_model.rs` contains `generate_alias_check_assertion`: confirmed
- `crates/analysis/src/vcgen.rs` contains `PointerAliasing`: confirmed
- `crates/analysis/src/spec_parser.rs` contains `"alias"` arm: confirmed
- `crates/analysis/src/contract_db.rs` contains `AliasPrecondition`: confirmed
- All 9 new alias tests GREEN: confirmed
- All 1211+ existing tests GREEN: confirmed

## Next Phase Readiness

- Plan 02 (call-site alias VC injection) can proceed immediately
- `AliasPrecondition` structs and `alias_preconditions` field ready for Plan 02 to consume at call boundaries
- `generate_alias_check_assertion_from_terms` ready for Plan 02 to generate VCs with substituted argument terms
- `VcKind::PointerAliasing` ready for Plan 02 VC classification and diagnostic reporting

---
*Phase: 34-cross-function-pointer-aliasing*
*Completed: 2026-02-28*
