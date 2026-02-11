---
phase: 02-table-stakes-completion
plan: 05
subsystem: analysis, driver
tags: [syn, spec-parser, old-operator, cargo-verify, colored-output, field-access]

# Dependency graph
requires:
  - phase: 02-03
    provides: "AssertKind-based VCGen and assertion verification infrastructure"
  - phase: 02-04
    provides: "Aggregate type encoding for struct/tuple field access in specs"
provides:
  - "Full syn-based specification parser (parse_spec_expr) handling Rust expression syntax"
  - "old(expr) operator for pre-state references in postconditions"
  - "Struct/tuple field access in specifications (result.x, result.0)"
  - "cargo verify subcommand with colored per-function output (OK/FAIL/TIMEOUT)"
  - "cargo-verify binary target for cargo subcommand installation"
affects: [Phase 3, Phase 4]

# Tech tracking
tech-stack:
  added: [syn 2.0, colored 3.1]
  patterns:
    - "syn::parse_str for spec expression parsing with recursive AST walking"
    - "parse_spec fallback pattern: syn parser first, simple parser second"
    - "old() operator via in_old flag propagation through expression tree"
    - "cargo subcommand detection via args[1] == 'verify'"

key-files:
  created:
    - crates/analysis/src/spec_parser.rs
    - crates/analysis/tests/spec_parser_tests.rs
    - crates/driver/src/cargo_verify.rs
    - crates/driver/src/output.rs
  modified:
    - crates/analysis/Cargo.toml
    - crates/analysis/src/lib.rs
    - crates/analysis/src/vcgen.rs
    - crates/driver/Cargo.toml
    - crates/driver/src/main.rs
    - crates/driver/src/callbacks.rs

key-decisions:
  - "syn 2.0 with 'full' and 'parsing' features for complete Rust expression support"
  - "parse_spec fallback pattern: try syn parser first, fall back to parse_simple_spec for edge cases"
  - "old(expr) via in_old flag: recursively convert all variable refs to {name}_pre suffixed constants"
  - "Signedness inference from terms: check Const type, then App selector field type, then function heuristic"
  - "colored 3.1 for output formatting (minimal dependency, no proc-macro overhead)"
  - "Simpler cargo verify: invoke cargo check with RUSTC=driver instead of cargo_metadata dependency"
  - "Dual binary targets (rust-fv-driver + cargo-verify) sharing same main.rs entry point"

patterns-established:
  - "spec_parser::parse_spec_expr as primary spec parsing entry point"
  - "Fallback parse_spec wrapper for backward compatibility"
  - "output::FunctionResult for per-function verification status aggregation"
  - "cargo verify subcommand pattern: detect args[1], delegate to cargo_verify module"

# Metrics
duration: 11min
completed: 2026-02-11
---

# Phase 2 Plan 5: Spec Parser + Cargo Verify Summary

**Full syn-based spec parser with old() operator, field access, and cargo verify subcommand producing colored OK/FAIL/TIMEOUT per-function output**

## Performance

- **Duration:** 11 min
- **Started:** 2026-02-11T12:05:12Z
- **Completed:** 2026-02-11T12:16:02Z
- **Tasks:** 2
- **Files modified:** 10

## Accomplishments
- Full specification parser via syn handling arithmetic, comparisons, logical ops, field access, old() operator
- old(expr) correctly replaces all variable references with {name}_pre for pre-state snapshots
- Backward compatibility verified: all existing specs work through parse_spec fallback
- cargo verify subcommand with colored per-function output and --help/--timeout flags
- 36 integration tests + 32 unit tests for spec parser covering full syntax and backward compat
- All 399 workspace tests passing

## Task Commits

Each task was committed atomically:

1. **Task 1: Full specification parser using syn and old() operator** - `7fb8491` (feat)
2. **Task 2: cargo verify subcommand with colored output** - `39c7cfc` (feat)

## Files Created/Modified
- `crates/analysis/src/spec_parser.rs` - Full syn-based spec expression parser (460+ lines)
- `crates/analysis/tests/spec_parser_tests.rs` - 36 integration tests for spec parser
- `crates/driver/src/cargo_verify.rs` - cargo verify subcommand entry point and Cargo.toml parsing
- `crates/driver/src/output.rs` - Colored per-function verification output formatter
- `crates/analysis/Cargo.toml` - Added syn 2.0 dependency
- `crates/analysis/src/lib.rs` - Added spec_parser module declaration
- `crates/analysis/src/vcgen.rs` - Updated to use parse_spec (syn-first with fallback)
- `crates/driver/Cargo.toml` - Added colored 3.1 dependency and cargo-verify binary target
- `crates/driver/src/main.rs` - Added verify subcommand detection and module declarations
- `crates/driver/src/callbacks.rs` - Updated to use colored output with per-function grouping

## Decisions Made
1. **syn 2.0 with full+parsing features**: Covers all Rust expression syntax we need. visit feature skipped as we do manual recursive walking.
2. **parse_spec fallback pattern**: New syn parser is primary, old parse_simple_spec is fallback via `parse_spec()` wrapper. Zero risk of regression.
3. **old() via in_old flag**: Simple boolean flag propagated through recursive convert_expr. All variable references get `_pre` suffix when in_old=true.
4. **Skip cargo_metadata dependency**: Read crate name from Cargo.toml directly to avoid pulling in heavy transitive dependencies. Keeps disk footprint minimal.
5. **Dual binary targets**: Both rust-fv-driver and cargo-verify point to same main.rs. Args[1]="verify" triggers subcommand path.
6. **colored 3.1 over termcolor**: Simpler API, lightweight dependency chain.

## Deviations from Plan

None - plan executed exactly as written.

## Issues Encountered
None.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- Phase 2 (Table Stakes Completion) is now fully complete (all 5 plans done)
- All infrastructure ready for Phase 3 (DX and Robustness)
- 399+ tests passing across workspace, zero warnings
- cargo verify subcommand ready for end-user workflow testing

---
*Phase: 02-table-stakes-completion*
*Completed: 2026-02-11*

## Self-Check: PASSED

All key files verified present. All task commits verified in git log. All minimum line counts exceeded (spec_parser: 818, cargo_verify: 164, output: 116, spec_parser_tests: 503).
