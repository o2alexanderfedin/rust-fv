---
phase: 05-performance-and-polish
plan: 03
subsystem: diagnostics
tags: [error-reporting, json-output, ide-integration, user-experience]

dependency_graph:
  requires:
    - vcgen module with VcLocation metadata
    - solver module with counterexample extraction
  provides:
    - rustc-style diagnostics with fix suggestions
    - structured JSON output for IDE integration
    - VcKind classification for error categorization
  affects:
    - driver callbacks (verification pipeline)
    - cargo verify CLI (output format flag)

tech_stack:
  added:
    - ariadne 0.4 (rustc-style error reporting)
    - serde 1.0 (JSON serialization)
    - serde_json 1.0 (JSON output)
  patterns:
    - Diagnostic builder pattern (ariadne Report API)
    - Output format abstraction (Text vs Json)
    - Counterexample filtering (hide internal variables)

key_files:
  created:
    - crates/driver/src/diagnostics.rs (ariadne-based error reporting)
    - crates/driver/src/json_output.rs (structured JSON schema)
  modified:
    - crates/analysis/src/vcgen.rs (VcLocation with VcKind)
    - crates/driver/Cargo.toml (ariadne, serde deps)

decisions:
  - Use ariadne 0.4 for rustc-style diagnostics (mature, well-documented)
  - VcKind classification with 10 categories (Precondition, Postcondition, Overflow, DivisionByZero, ShiftBounds, Assertion, LoopInvariantInit/Preserve/Exit, PanicFreedom)
  - JSON to stdout, all other output to stderr (IDE integration best practice)
  - Fallback text diagnostics when source location unavailable (ariadne requires source file access)
  - Fix suggestions for common patterns (overflow, precondition, postcondition, loop invariants, division-by-zero)

metrics:
  duration: 12 minutes
  tasks_completed: 2
  commits: 2
  files_created: 2
  files_modified: 3
  completed_date: 2026-02-11
---

# Phase 05 Plan 03: Enhanced Diagnostics and JSON Output

**One-liner:** Ariadne-based rustc-style error diagnostics with VcKind classification, counterexample formatting, fix suggestions, and structured JSON output for IDE integration.

## Objectives

Polish verification error messages to guide developers to fixes using rustc-style diagnostics and add structured JSON output for IDE integration (TOOL-05 requirement).

**Success Criteria:**
- Verification failures include source location (when available), failed property, and counterexample
- Fix suggestions guide developers for common failure patterns
- --output-format json produces structured JSON for IDE integration
- Existing colored text output remains the default and is enhanced with diagnostics

## Implementation Summary

### Task 1: Enhanced VcLocation and ariadne diagnostics

**Enhanced VcLocation structure:**
- Added `vc_kind: VcKind` field with 10 classification categories
- Added `contract_text: Option<String>` to capture failing spec
- Added `source_file` and `source_line` for source location (populated by driver)

**VcKind enum covers:**
- Precondition / Postcondition
- Loop invariant (Init / Preserve / Exit)
- Overflow / DivisionByZero / ShiftBounds
- Assertion / PanicFreedom

**Diagnostics module:**
- `report_verification_failure()` with dual output modes:
  - Ariadne-based rich reporting when source location available
  - Colored text fallback for current use (source info not yet populated by driver)
- `suggest_fix()` provides actionable advice for 7 common patterns
- `format_counterexample()` filters internal variables, converts bitvector values to decimal

**All VcLocation construction sites updated** in vcgen.rs:
- Overflow VCs: classified by operation (Add/Sub/Mul → Overflow, Div/Rem → DivisionByZero, Shl/Shr → ShiftBounds)
- Postcondition VCs: include contract text
- Precondition VCs (call sites): include contract text
- Loop invariant VCs (3 types): include invariant text
- Assertion VCs: classified as Assertion

### Task 2: JSON output and driver integration

**JSON output module:**
- `JsonVerificationReport` schema with functions, failures, summary
- `JsonFunctionResult` per-function with status ("ok"/"fail"/"timeout"), VC counts, failures
- `JsonFailure` with vc_kind, description, contract, source location, counterexample, suggestion
- `print_json_report()` outputs to stdout (stderr for progress)

**Driver integration:**
- `OutputFormat` enum (Text / Json) in callbacks
- `--output-format json` flag in cargo verify CLI
- `RUST_FV_OUTPUT_FORMAT` env var passed through pipeline
- Structured `VerificationFailure` collection during verification loop
- Counterexample extraction as Vec<(String, String)> from solver Model
- Progress messages suppressed in JSON mode (only JSON to stdout)
- Crate name extracted from TyCtxt for JSON report

**Dual output modes:**
- Text mode (default): Summary table + detailed diagnostics for each failure
- JSON mode: Structured report to stdout, all diagnostics/progress to stderr

## Verification

- `cargo build --workspace` compiles with ariadne, serde, serde_json dependencies
- `cargo test --workspace` passes all 498+ tests
- `cargo clippy --workspace -- -D warnings` produces zero warnings
- Diagnostics module has unit tests for counterexample formatting, fix suggestions, bitvector parsing

## Deviations from Plan

None - plan executed exactly as written.

## Integration Points

**Upstream dependencies:**
- VcGen module provides VcLocation with metadata
- Solver module provides counterexample Model

**Downstream consumers:**
- Driver callbacks integrate diagnostics into verification pipeline
- cargo verify CLI exposes --output-format flag
- Future: IDE/rust-analyzer can consume JSON output

**Future enhancements:**
- Populate source_file/source_line in driver using rustc Span API
- Enable full ariadne source-based error reporting
- Add more fix suggestions for additional VC kinds
- Support --output-format=sarif for static analysis tool integration

## Self-Check

Verifying created files exist:

```bash
[ -f "crates/driver/src/diagnostics.rs" ] && echo "FOUND" || echo "MISSING"
[ -f "crates/driver/src/json_output.rs" ] && echo "FOUND" || echo "MISSING"
```

Result: FOUND, FOUND

Verifying commits exist:

```bash
git log --oneline --grep="05-03"
```

Result:
- 27abf6c feat(05-03): add JSON output module for structured reporting
- 328f7a4 feat(05-03): add VcKind classification and ariadne-based diagnostics

## Self-Check: PASSED

All artifacts created, all commits present, all tests passing.
