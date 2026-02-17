---
phase: 18-bv2int-optimization
plan: 02
subsystem: analysis
tags: [bv2int, smt, differential-testing, equivalence, caching, vcgen, encoding-mode]

# Dependency graph
requires:
  - phase: 18-01
    provides: EncodingMode enum, is_bv2int_eligible, encode_type_with_mode, encode_binop_with_mode from bv2int.rs
  - phase: 14-incremental-verification
    provides: VcCache, CacheEntry, CacheEntry fields (mir_hash, contract_hash, etc.)
provides:
  - EquivalenceResult struct with timing fields (bitvec_time_ms, bv2int_time_ms, speedup_factor, counterexample)
  - test_encoding_equivalence function for running both encodings and comparing outcomes
  - format_equivalence_result for human-readable "Xms / Yms (Z.Zx faster/slower)" output
  - SolverInterface trait for dependency-injection in tests (no binary required)
  - VcOutcome enum (Unsat, Sat(Option<String>), Unknown) for VC results
  - CacheEntry extended with bv2int_equiv_tested, bv2int_bitvec_time_ms, bv2int_int_time_ms, bv2int_speedup fields
  - store_equivalence_result / get_equivalence_result methods on CacheEntry
  - generate_vcs_with_mode in vcgen.rs: mode-aware VC generation (QF_BV vs QF_LIA/QF_NIA)
affects: [18-03-cli-integration, vcgen, driver]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "SolverInterface trait for differential testing -- injectable mock solver avoids real binary in unit tests"
    - "CycleMockSolver uses Cell<usize> for interior mutability in immutable trait method context"
    - "generate_vcs_with_mode delegates to generate_vcs when Bitvector mode -- zero code duplication"
    - "func_has_multiplication scan selects QF_NIA vs QF_LIA at script rewrite time"
    - "replace_script_logic replaces set-logic command in generated SMT scripts post-hoc"

key-files:
  created:
    - crates/analysis/src/differential.rs
  modified:
    - crates/analysis/src/lib.rs
    - crates/analysis/src/vcgen.rs
    - crates/driver/src/cache.rs
    - crates/driver/src/invalidation.rs
    - crates/driver/src/parallel.rs
    - crates/driver/tests/incremental_correctness.rs
    - crates/driver/src/bench_incremental.rs

key-decisions:
  - "SolverInterface trait defined in differential.rs (not solver crate) -- keeps differential testing self-contained, no binary dependency for unit tests"
  - "VcOutcome::Sat carries Option<String> model -- enables richer counterexample messages when model text available"
  - "generate_vcs_with_mode delegates to generate_vcs for Bitvector mode -- zero code duplication, guaranteed parity"
  - "Logic replaced post-hoc (replace_script_logic) rather than threading logic selection through all VC generators -- minimal invasive change"
  - "bv2int fields use #[serde(default)] -- backward-compatible with cache entries from before Phase 18"
  - "CacheEntry derives Default -- enables ..Default::default() in struct literals, required by all callers after new fields added"

patterns-established:
  - "Pattern: SolverInterface trait for injectable solvers -- used by test_encoding_equivalence, testable without Z3 binary"
  - "Pattern: post-hoc script logic replacement -- scripts generated with QF_BV then logic swapped to QF_LIA/QF_NIA in one pass"
  - "Pattern: ..Default::default() in CacheEntry literals -- required when adding new fields to non-exhaustive structs"

requirements-completed: [PERF-06]

# Metrics
duration: 7min
completed: 2026-02-17
---

# Phase 18 Plan 02: Differential Testing and Equivalence Caching Summary

**Differential testing engine with SolverInterface trait, EquivalenceResult timing struct, CacheEntry bv2int fields, and mode-aware VCGen for QF_LIA/QF_NIA encoding**

## Performance

- **Duration:** 7 min
- **Started:** 2026-02-17T03:53:24Z
- **Completed:** 2026-02-17T04:00:32Z
- **Tasks:** 1
- **Files modified:** 8

## Accomplishments

- Created `differential.rs` (480 lines, 13 tests) with `EquivalenceResult`, `test_encoding_equivalence`, `format_equivalence_result`, `SolverInterface` trait, `VcOutcome` enum
- Extended `CacheEntry` in `cache.rs` with 4 bv2int fields (`bv2int_equiv_tested`, timing, speedup), `store_equivalence_result`/`get_equivalence_result` methods, 7 new tests covering store/retrieve/backward-compat/persistence
- Added `generate_vcs_with_mode` to `vcgen.rs`: full mode-aware VC generation with post-hoc QF_BV->QF_LIA/QF_NIA logic substitution
- Registered `pub mod differential` in `lib.rs`
- All 13 differential tests and 55 cache tests pass; clippy clean; fmt clean

## Task Commits

Each task was committed atomically:

1. **Task 1: differential testing + equivalence caching** - `8864386` (feat)

## Files Created/Modified

- `crates/analysis/src/differential.rs` - New module: EquivalenceResult, test_encoding_equivalence, format_equivalence_result, SolverInterface trait, VcOutcome enum (480 lines, 13 tests)
- `crates/analysis/src/lib.rs` - Added `pub mod differential`
- `crates/analysis/src/vcgen.rs` - Added generate_vcs_with_mode, collect_declarations_with_mode, func_has_multiplication, replace_script_logic helpers
- `crates/driver/src/cache.rs` - Extended CacheEntry with bv2int fields + Default derive + store/get methods + 7 new tests
- `crates/driver/src/invalidation.rs` - Added `..Default::default()` to CacheEntry struct literal
- `crates/driver/src/parallel.rs` - Added `..Default::default()` to CacheEntry struct literal
- `crates/driver/tests/incremental_correctness.rs` - Added `..Default::default()` to 5 CacheEntry struct literals
- `crates/driver/src/bench_incremental.rs` - Added `..Default::default()` to 7 CacheEntry struct literals

## Decisions Made

- `SolverInterface` trait lives in `differential.rs`, not `solver/` crate -- keeps equivalence testing self-contained, avoids requiring Z3 binary for unit tests
- `VcOutcome::Sat(Option<String>)` carries optional model text -- enables richer divergence messages when SAT model is available
- `generate_vcs_with_mode` delegates to `generate_vcs` for `EncodingMode::Bitvector` -- zero duplication, guaranteed parity
- Post-hoc logic replacement (replace_script_logic) swaps QF_BV to QF_LIA/QF_NIA after all VCs generated -- minimally invasive, no threading through 15+ generation functions

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Fixed CacheEntry struct literals in test/bench files after Default derive added**
- **Found during:** Task 1 (commit attempt)
- **Issue:** Pre-commit hook ran clippy on entire workspace. Adding `Default` derive to `CacheEntry` and new fields meant existing struct literals in `incremental_correctness.rs` (5 occurrences) and `bench_incremental.rs` (7 occurrences) failed to compile with E0063 "missing fields".
- **Fix:** Added `..Default::default()` to all 14 affected CacheEntry struct literals in the two files, plus `invalidation.rs` (1) and `parallel.rs` (1) which were caught by initial clippy pass.
- **Files modified:** `crates/driver/tests/incremental_correctness.rs`, `crates/driver/src/bench_incremental.rs`, `crates/driver/src/invalidation.rs`, `crates/driver/src/parallel.rs`
- **Verification:** `cargo clippy -- -D warnings` clean; `cargo fmt --check` clean; all tests pass
- **Committed in:** `8864386` (included in task commit)

---

**Total deviations:** 1 auto-fixed (Rule 3 - blocking struct literal compilation errors)
**Impact on plan:** Auto-fix required for commit to succeed. Adding Default derive to CacheEntry is the correct approach (enables `..Default::default()` idiom) -- the fix is minimal and correct for all callers.

## Issues Encountered

- Pre-commit hook compiles entire workspace including test files. Adding new fields to `CacheEntry` required updating all struct literal initializations across the workspace. Pattern established: always add `..Default::default()` to struct literals when extending cache/driver types.

## Next Phase Readiness

- Differential testing engine complete; 18-03 (CLI integration) can now call `test_encoding_equivalence` with real VCs from `generate_vcs_with_mode`
- `CacheEntry::store_equivalence_result` / `get_equivalence_result` ready for use in CLI orchestration
- `format_equivalence_result` ready for output formatting in 18-03

---
*Phase: 18-bv2int-optimization*
*Completed: 2026-02-17*
