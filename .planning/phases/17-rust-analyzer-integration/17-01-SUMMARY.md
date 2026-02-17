---
phase: 17-rust-analyzer-integration
plan: 01
subsystem: ide-integration
tags: [rust-analyzer, json-diagnostics, rustc-format, flycheck, ide]

# Dependency graph
requires:
  - phase: 16-vscode-extension
    provides: "VSCode extension with diagnostics, JSON output format"
provides:
  - "Rustc-compatible JSON diagnostic output (RustcDiagnostic types)"
  - "--message-format=json flag for cargo verify"
  - "--version flag for installation detection"
  - "JsonVerificationReport deserialization support"
affects: [17-02-PLAN, rust-analyzer-integration]

# Tech tracking
tech-stack:
  added: []
  patterns: ["rustc-compatible JSON diagnostic format", "subprocess stdout capture and conversion"]

key-files:
  created:
    - crates/driver/src/rustc_json.rs
  modified:
    - crates/driver/src/cargo_verify.rs
    - crates/driver/src/json_output.rs
    - crates/driver/src/main.rs

key-decisions:
  - "Combined Task 1 and Task 2 into single commit (clippy -D warnings requires used code)"
  - "Added Deserialize to all JSON output types for report parsing from captured stdout"
  - "parse_json_report_from_output uses balanced-brace extraction for robustness with cargo output prefix"

patterns-established:
  - "Rustc diagnostic format: one JSON object per stdout line with reason, message, spans"
  - "Message-format flag separate from output-format (IDE vs machine-readable)"

requirements-completed: [IDE-04, IDE-05]

# Metrics
duration: 7min
completed: 2026-02-17
---

# Phase 17 Plan 01: Rustc-Compatible JSON Diagnostics Summary

**Rustc-compatible JSON diagnostic output via --message-format=json for rust-analyzer flycheck integration**

## Performance

- **Duration:** 7 min (413s)
- **Started:** 2026-02-17T01:03:24Z
- **Completed:** 2026-02-17T01:10:17Z
- **Tasks:** 2
- **Files modified:** 4

## Accomplishments
- Created rustc_json module with RustcDiagnostic, RustcMessage, RustcSpan, RustcCode types matching rustc's JSON output format
- Implemented conversion from JsonVerificationReport to rustc-compatible diagnostics with inline counterexamples
- Added --message-format=json flag that captures subprocess stdout and emits rustc-format diagnostics
- Added --version flag for cargo-verify installation detection
- 20 new tests covering all diagnostic conversion and argument parsing scenarios

## Task Commits

Both tasks committed atomically (required for clippy compliance):

1. **Task 1+2: Rustc JSON diagnostics and --message-format flag** - `1ebe9ad` (feat)

**Plan metadata:** pending (docs: complete plan)

## Files Created/Modified
- `crates/driver/src/rustc_json.rs` - Rustc-compatible JSON diagnostic types and conversion logic
- `crates/driver/src/cargo_verify.rs` - --message-format flag parsing, stdout capture, rustc diagnostic emission
- `crates/driver/src/json_output.rs` - Added Deserialize derive for report parsing
- `crates/driver/src/main.rs` - Added mod rustc_json declaration

## Decisions Made
- Combined Tasks 1 and 2 into a single commit because clippy with -D warnings rejects unused code, making Task 1 impossible to commit alone
- Added Deserialize to JSON output types (non-breaking change) to enable parsing captured subprocess stdout
- Used balanced-brace JSON extraction in parse_json_report_from_output for robustness when cargo adds prefix output
- Summary diagnostic uses "note" level for all-pass and "warning" level for failures

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Added Deserialize derive to JSON output types**
- **Found during:** Task 2 (wiring --message-format flag)
- **Issue:** JsonVerificationReport and related types only had Serialize, but parsing captured stdout requires Deserialize
- **Fix:** Added `Deserialize` derive to all 5 JSON output types in json_output.rs
- **Files modified:** crates/driver/src/json_output.rs
- **Verification:** cargo test passes, cargo clippy clean
- **Committed in:** 1ebe9ad

**2. [Rule 3 - Blocking] Improved arg filtering for cargo check forwarding**
- **Found during:** Task 2 (arg forwarding)
- **Issue:** Original arg filtering used starts_with which doesn't properly skip value-bearing flags (e.g., --timeout 30 would skip --timeout but forward 30)
- **Fix:** Added skip_next pattern for flags with separate values (--message-format, --output-format, --timeout, --jobs)
- **Files modified:** crates/driver/src/cargo_verify.rs
- **Verification:** Existing tests still pass, new behavior correct
- **Committed in:** 1ebe9ad

---

**Total deviations:** 2 auto-fixed (2 blocking)
**Impact on plan:** Both auto-fixes necessary for correct operation. No scope creep.

## Issues Encountered
None - implementation followed plan with minor adjustments for clippy compliance.

## User Setup Required
None - no external service configuration required.

## Next Phase Readiness
- rustc-compatible JSON diagnostic output ready for rust-analyzer integration
- Plan 17-02 can now configure rust-analyzer's check.overrideCommand to use `cargo verify --message-format=json`
- All existing functionality unchanged (--output-format json still works independently)

---
*Phase: 17-rust-analyzer-integration*
*Completed: 2026-02-17*
