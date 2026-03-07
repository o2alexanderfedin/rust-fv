---
phase: 50-stdlib-ptr-mem-unsafe-boundary
plan: 01
subsystem: stdlib-contracts
tags: [ptr, mem, unsafe, alignment, overlap, swap, replace, stdlib]

# Dependency graph
requires:
  - phase: 49-cross-crate-interop
    provides: StdlibContractRegistry pattern and loader infrastructure
provides:
  - "std::ptr contracts: read, write, copy, copy_nonoverlapping, swap, replace, drop_in_place, null, null_mut"
  - "std::mem contracts: swap, replace, forget, size_of, align_of"
  - "Overlap and alignment preconditions for unsafe ptr operations"
  - "Value exchange postconditions for mem::swap and mem::replace"
affects: [54-stdlib-contracts-batch-i, 55-stdlib-contracts-batch-ii]

# Tech tracking
tech-stack:
  added: []
  patterns: [ptr-alignment-precondition, overlap-check-precondition, value-exchange-postcondition]

key-files:
  created:
    - crates/analysis/src/stdlib_contracts/ptr.rs
    - crates/analysis/src/stdlib_contracts/mem.rs
    - crates/analysis/tests/ptr_contracts_test.rs
    - crates/analysis/tests/mem_contracts_test.rs
  modified:
    - crates/analysis/src/stdlib_contracts/mod.rs
    - crates/analysis/src/stdlib_contracts/loader.rs

key-decisions:
  - "Ptr contracts use SpecExpr-level alignment checks (addr % align_of::<T>() == 0) matching existing contract pattern"
  - "copy_nonoverlapping overlap check uses no_overlap(src, dst, count * size_of::<T>()) spec function"
  - "mem::swap single postcondition combines both exchange assertions (*a == old(*b) && *b == old(*a))"
  - "mem::forget modeled as no-op with postcondition 'true' (destructor skip)"
  - "size_of/align_of are pure with result > 0 postcondition"

patterns-established:
  - "Alignment precondition pattern: param % align_of::<T>() == 0"
  - "Overlap precondition pattern: no_overlap(src, dst, count * size)"
  - "Value exchange postcondition: *a == old(*b) && *b == old(*a)"

requirements-completed: [COMPL-23, COMPL-24]

# Metrics
duration: 2172s
completed: 2026-03-07
---

# Phase 50 Plan 01: Ptr/Mem Stdlib Contracts Summary

**14 stdlib contracts for std::ptr (9) and std::mem (5) with overlap/alignment preconditions and value-exchange postconditions, auto-loaded via StdlibContractRegistry**

## Performance

- **Duration:** 2172s (~36 min)
- **Started:** 2026-03-07T01:03:10Z
- **Completed:** 2026-03-07T01:39:22Z
- **Tasks:** 1
- **Files modified:** 6

## Accomplishments
- 9 ptr contracts with alignment preconditions (read, write, copy, copy_nonoverlapping, swap, replace, drop_in_place, null, null_mut)
- 5 mem contracts with value semantics (swap exchange, replace return-old, forget no-op, size_of/align_of positive)
- copy_nonoverlapping has both overlap AND alignment preconditions
- Zero-config activation via loader.rs wiring into StdlibContractRegistry
- 19 comprehensive tests (9 ptr + 10 mem) covering registration, preconditions, postconditions, purity

## Task Commits

Each task was committed atomically:

1. **Task 1: Create ptr.rs and mem.rs stdlib contract modules** - `c83936d` (feat)

_Note: TDD RED phase tests were created first but committed together with GREEN implementation due to pre-commit hook requiring compilation._

## Files Created/Modified
- `crates/analysis/src/stdlib_contracts/ptr.rs` - 9 ptr contracts with alignment/overlap preconditions
- `crates/analysis/src/stdlib_contracts/mem.rs` - 5 mem contracts with value exchange postconditions
- `crates/analysis/src/stdlib_contracts/mod.rs` - Added pub mod ptr and pub mod mem declarations
- `crates/analysis/src/stdlib_contracts/loader.rs` - Wired register_ptr_contracts and register_mem_contracts
- `crates/analysis/tests/ptr_contracts_test.rs` - 9 tests for ptr contract registration and preconditions
- `crates/analysis/tests/mem_contracts_test.rs` - 10 tests for mem contract registration and postconditions

## Decisions Made
- Used SpecExpr-level contracts (raw strings) following vec.rs pattern rather than direct SMT Term construction
- copy_nonoverlapping overlap check uses a `no_overlap(src, dst, count * size_of::<T>())` spec function for clarity
- mem::swap combines both exchange assertions into a single postcondition for atomicity
- mem::forget postcondition is literal "true" (destructor skip modeled as no-op)
- size_of and align_of marked as `is_pure: true` since they're compile-time constants

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Fixed pre-existing ir.rs test compilation errors**
- **Found during:** Task 1 (commit attempt)
- **Issue:** 13 Function struct constructors in ir.rs tests missing `maybeuninit_ghost_states` field (added by plan 50-02 which ran concurrently)
- **Fix:** Added `maybeuninit_ghost_states: vec![]` to all 13 Function constructors in ir.rs test code
- **Files modified:** crates/analysis/src/ir.rs
- **Verification:** `cargo clippy --all-targets --all-features -- -D warnings` passes
- **Committed in:** c83936d (part of task commit)

---

**Total deviations:** 1 auto-fixed (1 blocking)
**Impact on plan:** Fix was necessary to pass pre-commit hook. No scope creep.

## Issues Encountered
None beyond the pre-existing compilation issue documented above.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- ptr and mem contracts are registered and available via load_default_contracts()
- Ready for Phase 50 plans 02-04 (unsafe boundary analysis, async model)
- Pattern established for future stdlib contract modules (alignment, overlap, value exchange)

## Self-Check: PASSED

All 6 created/modified files verified present. Commit c83936d verified in git log.

---
*Phase: 50-stdlib-ptr-mem-unsafe-boundary*
*Completed: 2026-03-07*
