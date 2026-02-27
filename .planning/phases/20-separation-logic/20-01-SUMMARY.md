---
phase: 20-separation-logic
plan: 01
subsystem: formal-verification
tags: [separation-logic, smt, pts_to, heap-model, smtlib, spec-parser]

# Dependency graph
requires:
  - phase: 19-counterexample-generation
    provides: IR Function/Local/Ty types and spec_parser infrastructure used here
provides:
  - sep_logic::declare_sep_heap() — 3 SMT commands for HeapVal sort + sep_heap + perm arrays
  - sep_logic::declare_heapval_accessor() — accessor fun heapval_as_bvN for HeapVal coercion
  - sep_logic::encode_pts_to() — pts_to(p, v) encoded as And([Select(perm,p), Eq(heapval_as_bvN(Select(sep_heap,p)), v)])
  - sep_logic::sep_logic_smt_logic() — returns QF_AUFBV or AUFBV based on quantifier presence
  - sep_logic::extract_pts_to_footprint() — recursive footprint walker for frame rule (Plan 03)
  - spec_parser: pts_to() recognized in convert_call and routed to encode_pts_to()
  - spec_parser: resolve_pointee_bits() helper maps RawPtr param type to bit width
affects: [20-02-plan, 20-03-plan, 20-04-plan]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Separation heap as two SMT arrays: sep_heap (Array Addr HeapVal) and perm (Array Addr Bool)"
    - "HeapVal is an uninterpreted sort; heapval_as_bvN coerces to bitvector for comparison"
    - "pts_to footprint extraction via structural term walk (first arm Select(perm,ptr) pattern)"
    - "resolve_pointee_bits uses let-chain syntax for collapsed if patterns (clippy compliant)"

key-files:
  created:
    - crates/analysis/src/sep_logic.rs
  modified:
    - crates/analysis/src/lib.rs
    - crates/analysis/src/spec_parser.rs

key-decisions:
  - "Separate heap domain (not byte-array model) avoids conflict with heap_model.rs"
  - "Default pointee_bits is 64 (conservative) when type cannot be resolved from param list"
  - "perm array is Bool (not fractional permissions) — sufficient for ownership in plan 01 scope"
  - "sep_logic_smt_logic returns QF_AUFBV for pts_to-only VCs (no frame forall needed yet)"

patterns-established:
  - "sep_logic functions are pure encoders — no state, no I/O, easy to test in isolation"
  - "pts_to arm in convert_call follows same early-return pattern as old/implies/forall/exists"

requirements-completed: [SEP-01]

# Metrics
duration: 10min
completed: 2026-02-19
---

# Phase 20 Plan 01: Separation Heap Domain and pts_to Encoder Summary

**SMT separation heap (HeapVal sort + sep_heap/perm arrays) and pts_to(p, v) spec predicate wired into spec_parser with pointee bit-width resolution**

## Performance

- **Duration:** 10 min
- **Started:** 2026-02-19T20:37:03Z
- **Completed:** 2026-02-19T20:47:00Z
- **Tasks:** 2
- **Files modified:** 3

## Accomplishments

- Created `sep_logic.rs` with 5 public functions: `declare_sep_heap`, `declare_heapval_accessor`, `encode_pts_to`, `sep_logic_smt_logic`, `extract_pts_to_footprint`
- Wired `pts_to()` recognition into `spec_parser::convert_call()` with `resolve_pointee_bits()` helper for type-directed bit-width selection
- All 5 unit tests pass (3 sep_logic + 2 pts_to parser tests), zero clippy warnings

## Task Commits

Both tasks were committed together as part of prior phase 20 preparatory work and a single pre-commit hook execution:

1. **Task 1: Create sep_logic.rs with sep_heap domain and pts_to encoder** - already committed in prior phase 20 work (sep_logic.rs, pub mod sep_logic in lib.rs)
2. **Task 2: Wire pts_to into spec_parser convert_call + declare pub mod in lib.rs** - `37070f3` (feat: pts_to arm, resolve_pointee_bits, unit tests in spec_parser.rs)

**Plan metadata:** (docs commit follows)

## Files Created/Modified

- `crates/analysis/src/sep_logic.rs` - Separation heap domain: HeapVal sort, sep_heap/perm arrays, pts_to encoder, SMT logic selector, footprint walker
- `crates/analysis/src/lib.rs` - Added `pub mod sep_logic;` module declaration
- `crates/analysis/src/spec_parser.rs` - Added `"pts_to"` match arm in `convert_call`, `resolve_pointee_bits()` helper, two unit tests (`test_pts_to_parse_basic`, `test_pts_to_wrong_arity`)

## Decisions Made

- Default pointee_bits to 64 when the pointer type cannot be resolved from the parameter list — conservative fallback that avoids silent 32-bit truncation on 64-bit pointers
- `perm` uses Bool (not fractional permissions or bitvector counts) — sufficient for Plan 01 ownership semantics; Plan 03 may revisit for concurrency
- `sep_logic_smt_logic(false)` returns `"QF_AUFBV"` because no frame forall is emitted until Plan 03

## Deviations from Plan

None - plan executed exactly as written. Both `sep_logic.rs` and the `spec_parser.rs` pts_to arm matched the spec in the plan document.

## Issues Encountered

- `rustfmt` required let-chain style (`if cond && let Pat = expr`) for `resolve_pointee_bits` inner loop — pre-commit hook enforced this automatically

## User Setup Required

None - no external service configuration required.

## Next Phase Readiness

- `sep_logic` module is fully ready for Plan 02 (ghost predicate integration) and Plan 03 (frame rule with `extract_pts_to_footprint`)
- `encode_pts_to` callable from any VCGen path that encounters a raw pointer spec assertion
- No blockers for Plans 02-04

---
*Phase: 20-separation-logic*
*Completed: 2026-02-19*
