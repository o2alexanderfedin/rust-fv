---
phase: 18-bv2int-optimization
plan: 01
subsystem: analysis
tags: [bv2int, smt, encoding, bitvector, integer-arithmetic, overflow, rust-rfc-0560]

# Dependency graph
requires:
  - phase: analysis
    provides: ir.rs (BinOp, Function, Rvalue, Statement, Ty), encode_sort.rs (encode_type, Sort), encode_term.rs (encode_binop, Term)
provides:
  - EncodingMode enum (Bitvector/Integer) for SMT encoding strategy selection
  - IneligibilityReason enum with actionable Display messages for developer output
  - is_bv2int_eligible function for conservative static analysis of function eligibility
  - encode_type_with_mode function for mode-aware Rust type -> SMT sort mapping
  - encode_binop_with_mode function for mode-aware binary operation encoding
  - wrap_overflow function for RFC 0560 wrapping arithmetic (signed ITE chain, unsigned modulo)
affects: [18-02-differential-testing, 18-03-cli-integration, vcgen, driver]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "Conservative applicability analysis: entire function rejected if ANY bitwise/shift op found (safety over precision)"
    - "Mode dispatch pattern: functions take EncodingMode and delegate vs. implement independently"
    - "Two's complement wrapping via ITE chain for signed, modulo for unsigned (RFC 0560 semantics)"
    - "no_bv2int attribute encoded as magic string in Contracts.requires (avoids new IR field)"

key-files:
  created:
    - crates/analysis/src/bv2int.rs
  modified:
    - crates/analysis/src/lib.rs
    - crates/solver/src/lib.rs
    - crates/solver/tests/z3_integration.rs

key-decisions:
  - "Entire function rejection for any bitwise/shift op (not per-expression) -- conservative, predictable, simpler"
  - "#[fv::no_bv2int] encoded as magic requires string '__fv_no_bv2int__' (avoids new IR field per Phase 14 lesson)"
  - "Signed wrapping uses ITE chain (ite (>= r 2^(N-1)) (- r 2^N) (ite (< r -2^(N-1)) (+ r 2^N) r))"
  - "Unsigned wrapping uses simple modulo: (mod result 2^N)"

patterns-established:
  - "Pattern 1: Mode-aware encoding functions follow delegate-or-implement -- EncodingMode::Bitvector delegates to existing encode_*, Integer implements inline"
  - "Pattern 2: Eligibility returns Result<(), IneligibilityReason> for structured error propagation with actionable messages"

requirements-completed: [PERF-05]

# Metrics
duration: 3min
completed: 2026-02-17
---

# Phase 18 Plan 01: bv2int Core Encoding Infrastructure Summary

**EncodingMode enum + conservative applicability analysis + RFC 0560 wrapping overflow guards for bv2int SMT optimization**

## Performance

- **Duration:** 3 min
- **Started:** 2026-02-17T03:25:07Z
- **Completed:** 2026-02-17T03:28:21Z
- **Tasks:** 1
- **Files modified:** 4

## Accomplishments

- Created `bv2int.rs` (876 lines) with complete EncodingMode, IneligibilityReason, eligibility analysis, and integer encoding
- All 5 bitwise/shift operations (BitAnd, BitOr, BitXor, Shl, Shr) correctly rejected with actionable location messages
- RFC 0560 wrapping overflow guards: unsigned via `mod result 2^N`, signed via nested ITE two's complement chain
- `#[fv::no_bv2int]` attribute detection via magic `__fv_no_bv2int__` marker in contracts (zero IR schema changes)
- 35 unit tests covering all behaviors (5 bitwise rejections, comparison acceptance, all arithmetic ops, overflow wrapping)

## Task Commits

Each task was committed atomically:

1. **Task 1: bv2int core implementation** - `94c04df` (feat)

## Files Created/Modified

- `crates/analysis/src/bv2int.rs` - New module: EncodingMode, IneligibilityReason, is_bv2int_eligible, encode_type_with_mode, encode_binop_with_mode, wrap_overflow (876 lines, 35 tests)
- `crates/analysis/src/lib.rs` - Already had `pub mod bv2int;` registered (no change needed)
- `crates/solver/src/lib.rs` - Added `SolverKind` to public re-exports
- `crates/solver/tests/z3_integration.rs` - Updated to use new `SolverConfig::new(kind, path)` signature

## Decisions Made

- Entire-function rejection strategy (vs per-expression): simpler, predictable, avoids complex bitvector/integer variable tracking
- `#[fv::no_bv2int]` stored as magic `__fv_no_bv2int__` string in `Contracts.requires` -- avoids adding a new field to the IR which would require updating 30+ test fixtures
- Wrapping overflow follows Rust RFC 0560 exactly: modulo for unsigned, two's complement ITE chain for signed

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Fixed pre-commit hook failure due to solver API changes**
- **Found during:** Task 1 (commit attempt)
- **Issue:** Unstaged changes in `crates/solver/src/config.rs` and `error.rs` changed `SolverConfig::new(path)` to `SolverConfig::new(kind, path)` and `SolverError::NotFound(path)` to `NotFound(kind, path)`. The pre-commit hook compiled the entire workspace including unstaged changes, causing z3_integration.rs to fail compilation.
- **Fix:** Updated `z3_integration.rs` to use `SolverConfig::new(SolverKind::Z3, path)` and `SolverError::NotFound(_kind, path)`. Added `SolverKind` to `solver/src/lib.rs` re-exports. Applied `cargo fmt` to resolve line-length formatting.
- **Files modified:** `crates/solver/tests/z3_integration.rs`, `crates/solver/src/lib.rs`
- **Verification:** `cargo clippy -- -D warnings` and `cargo fmt --check` both pass
- **Committed in:** `94c04df` (included in task commit)

---

**Total deviations:** 1 auto-fixed (Rule 3 - blocking pre-commit issue)
**Impact on plan:** Auto-fix was necessary for commit to succeed. Solver API changes were pre-existing in working tree from unrelated work (multiple-solvers feature). Fix is minimal and correct.

## Issues Encountered

- Pre-commit hook runs clippy on the entire workspace including unstaged changes. Unstaged solver changes broke integration tests. Fixed by updating tests to match new API.

## Next Phase Readiness

- bv2int core infrastructure complete; 18-02 (differential testing) can now use `is_bv2int_eligible` and `encode_binop_with_mode`
- 18-03 (CLI integration) can use `is_bv2int_eligible` for candidate detection and `EncodingMode` for user-controlled activation

---
*Phase: 18-bv2int-optimization*
*Completed: 2026-02-17*
