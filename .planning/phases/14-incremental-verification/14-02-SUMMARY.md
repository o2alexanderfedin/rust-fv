---
phase: 14-incremental-verification
plan: 02
subsystem: driver-output
tags: [incremental, ui, cache-management, timing, verbose]
dependency-graph:
  requires: [14-01-dual-hash-cache]
  provides: [status-output, timing-display, cache-cli]
  affects: [driver, cargo-verify, output]
tech-stack:
  added: []
  patterns: [invalidation-reason-mapping, per-function-metadata, verbose-mode]
key-files:
  created: []
  modified:
    - crates/driver/src/output.rs
    - crates/driver/src/callbacks.rs
    - crates/driver/src/cargo_verify.rs
    - crates/driver/src/cache.rs
decisions:
  - invalidation-reason-always-shown: "Invalidation reasons shown for all re-verified functions (not behind verbose flag)"
  - verbose-for-timing-only: "--verbose flag controls per-function timing display, not invalidation reasons"
  - skip-status-for-cache-hits: "Cached functions show [SKIP] status instead of [OK]"
  - total-timing-always-shown: "Total verification time shown in summary line when any functions were verified"
metrics:
  duration: 478s
  completed: 2026-02-15
---

# Phase 14 Plan 02: Per-Function Status Output and Cache Management Summary

**One-liner:** User-visible incremental verification with [SKIP] status, invalidation reasons, timing display, and `cargo verify clean` command.

## What Was Built

Completed the user-facing integration of incremental verification through enhanced output and cache management:

1. **Enhanced VerificationStatus Enum**
   - Added `Skipped` variant for cached results
   - [SKIP] status displayed in cyan for cached functions
   - Distinct visual feedback for cache hits vs. re-verification

2. **Per-Function Metadata System**
   - Added `FunctionMetadata` struct to store invalidation reasons and timing
   - Stores metadata from `VerificationTaskResult` during execution
   - Maps to human-readable strings for display

3. **Invalidation Reason Display**
   - Always shown for re-verified functions (not behind verbose flag)
   - Human-readable mappings:
     - `MirChanged` → "body changed"
     - `ContractChanged{dep}` → "contract of {dep} changed"
     - `Fresh` → "fresh run"
     - `CacheMiss` → "not in cache"
     - `Expired` → "cache expired"
   - Displayed as: `[OK] foo (3 VCs) -- Re-verifying: body changed`

4. **Timing Display**
   - Total timing always shown in summary when functions were verified
   - Per-function timing shown with `--verbose` flag
   - Format: `[OK] foo (3 VCs, 42ms) -- Re-verifying: body changed`
   - Summary format: `Summary: 2 OK, 1 SKIP, 0 FAIL (total: 156ms)`

5. **Cache Management CLI**
   - `cargo verify clean` subcommand to delete `target/verify-cache/`
   - Confirmation message after deletion
   - Gracefully handles non-existent cache directory
   - Updated usage documentation

6. **Verbose Mode**
   - `--verbose` or `-v` flag for detailed output
   - Passed via `RUST_FV_VERBOSE` environment variable
   - Enables per-function timing display
   - Does not hide invalidation reasons (always shown)

## Deviations from Plan

None - plan executed exactly as written.

## Implementation Details

### FunctionResult Enhancement

Extended `FunctionResult` struct with:
- `invalidation_reason: Option<String>` - Human-readable invalidation reason
- `duration_ms: Option<u64>` - Verification duration (None for cached)

### Metadata Propagation

```rust
struct FunctionMetadata {
    invalidation_reason: Option<InvalidationReason>,
    duration_ms: Option<u64>,
    from_cache: bool,
}
```

Stored in `VerificationCallbacks::func_metadata` HashMap, populated from `VerificationTaskResult`, and joined during `print_results`.

### Output Changes

Before:
```
  [OK]    max (3/3 VCs)
  [OK]    helper (2/2 VCs)
```

After:
```
  [OK]    max (3 VCs) -- Re-verifying: body changed
  [SKIP]  helper (cached)

Summary: 1 OK, 1 SKIP, 0 FAIL (total: 42ms)
```

With `--verbose`:
```
  [OK]    max (3 VCs, 42ms) -- Re-verifying: body changed
  [SKIP]  helper (cached)

Summary: 1 OK, 1 SKIP, 0 FAIL (total: 42ms)
```

### JSON Output

Extended JSON format to include:
- `"status": "skipped"` for cached functions
- `invalidation_reason` field (when present)
- `duration_ms` field (when present)

## Testing

**Coverage:** 317 tests total (added 13 new tests)

**New tests:**
- `test_print_verification_results_skipped` - Skipped status formatting
- `test_print_verification_results_with_timing` - Verbose timing display
- `test_print_verification_results_with_invalidation_reason` - Reason display
- `test_verification_status_skipped` - Skipped enum variant
- `test_parse_verbose_*` (6 tests) - Verbose flag parsing
- `test_clean_command_*` (3 tests) - Clean subcommand detection

**Verification:**
- ✅ All 317 tests pass
- ✅ Clippy clean (no warnings with `-D warnings`)
- ✅ Formatting correct (`cargo fmt --check`)

## Key Decisions

1. **Invalidation reasons always shown**: Unlike timing (which requires --verbose), invalidation reasons are always displayed for re-verified functions. This is the primary signal users need to understand why re-verification occurred.

2. **Verbose flag for timing only**: The `--verbose` flag controls per-function timing display, not invalidation reasons. This keeps the default output informative without overwhelming users.

3. **SKIP status for cache hits**: Cached functions show `[SKIP]` instead of `[OK]` to clearly distinguish between verified and cached results. This makes cache behavior visible and debuggable.

4. **Total timing always shown**: When any functions were verified (not all cached), the summary line shows total timing. This provides performance feedback without requiring a flag.

## CLI Changes

### New Subcommand

```bash
cargo verify clean
```

Deletes `target/verify-cache/` and confirms deletion.

### New Flag

```bash
cargo verify --verbose
cargo verify -v
```

Enables per-function timing display.

### Updated Usage

```
USAGE:
    cargo verify [OPTIONS]
    cargo verify clean

SUBCOMMANDS:
    clean    Delete verification cache (target/verify-cache/)

OPTIONS:
    --verbose, -v               Show per-function timing information
    ...
```

## Integration Points

**Current integration:**
- `output.rs`: Enhanced `VerificationStatus` and `FunctionResult`, updated `print_verification_results`
- `callbacks.rs`: Added `FunctionMetadata` storage, invalidation reason mapping, verbose flag handling
- `cargo_verify.rs`: Added `clean` subcommand, `--verbose` flag parsing, updated usage text
- `cache.rs`: Updated documentation to reference `target/verify-cache/`

**Future integration (next phases):**
- IDE integration: JSON output includes invalidation reasons and timing for editor displays
- Performance benchmarking: Timing data enables verification performance tracking

## Examples

### First Run (All New)

```
  [OK]    max (3 VCs) -- Re-verifying: not in cache
  [OK]    helper (2 VCs) -- Re-verifying: not in cache

Summary: 2 OK, 0 SKIP, 0 FAIL (total: 156ms)
```

### Second Run (All Cached)

```
  [SKIP]  max (cached)
  [SKIP]  helper (cached)

Summary: 0 OK, 2 SKIP, 0 FAIL
```

### After Modifying max() Body

```
  [OK]    max (3 VCs) -- Re-verifying: body changed
  [SKIP]  helper (cached)

Summary: 1 OK, 1 SKIP, 0 FAIL (total: 78ms)
```

### After Modifying helper() Contract

```
  [OK]    max (3 VCs) -- Re-verifying: contract of helper changed
  [OK]    helper (2 VCs) -- Re-verifying: body changed

Summary: 2 OK, 0 SKIP, 0 FAIL (total: 145ms)
```

### With --verbose Flag

```
  [OK]    max (3 VCs, 78ms) -- Re-verifying: body changed
  [SKIP]  helper (cached)

Summary: 1 OK, 1 SKIP, 0 FAIL (total: 78ms)
```

### Clean Command

```bash
$ cargo verify clean
Removed cache directory: target/verify-cache
```

## Performance Notes

- **Zero overhead for cached functions**: Skipped functions load results from disk without re-verification
- **Timing precision**: Millisecond-level timing helps identify slow verification conditions
- **Metadata storage**: HashMap lookup adds negligible overhead (~O(1) per function)
- **Verbose mode impact**: No performance impact - only affects display, not verification

## Next Steps

1. **Phase 14 Plan 03**: Benchmark incremental verification performance (target: <1s re-verification)
2. **Phase 14 Plan 04**: IDE integration using JSON output with invalidation metadata
3. **Phase 15**: Quantifier trigger diagnostics (leverage timing data for performance analysis)

## Self-Check: PASSED

**Files created:**
- None (all changes to existing files)

**Files modified:**
- ✅ `crates/driver/src/output.rs` has `Skipped` status, new `FunctionResult` fields, enhanced `print_verification_results`
- ✅ `crates/driver/src/callbacks.rs` has `FunctionMetadata`, invalidation reason mapping, verbose flag
- ✅ `crates/driver/src/cargo_verify.rs` has `clean` subcommand, `--verbose` flag, updated usage
- ✅ `crates/driver/src/cache.rs` documentation updated to `target/verify-cache/`

**Commits:**
- ✅ `17ceb1e` - Task 1 (cache directory documentation updates)
- ✅ `5df6245` - Task 2 (per-function status output, timing, cache management)

**Tests:**
- ✅ 317 tests pass (13 new tests for output, verbose, clean)
- ✅ Clippy clean
- ✅ Formatting correct

**Must-haves verification:**
- ✅ Every function shows status: verified/skipped/failed in output
- ✅ Invalidation reason displayed when re-verifying (always shown, not behind verbose)
- ✅ Total verification time shown in summary by default
- ✅ Per-function timing shown with --verbose flag
- ✅ --fresh flag bypasses cache without deleting files (implemented in 14-01)
- ✅ `cargo verify clean` subcommand deletes cache directory permanently
- ✅ Cache location is `target/verify-cache/` (not `target/rust-fv-cache/`)

**Output verification:**
- ✅ `[OK]`, `[SKIP]`, `[FAIL]` statuses display correctly
- ✅ Invalidation reasons shown as human-readable strings
- ✅ Timing shows in summary (always) and per-function (with --verbose)
- ✅ JSON output includes new fields (status: "skipped", invalidation_reason, duration_ms)

---

**Phase:** 14-incremental-verification
**Plan:** 02
**Completed:** 2026-02-15
**Duration:** 478 seconds (7 minutes 58 seconds)
**Tasks completed:** 2/2
**Tests added:** 13
**Files created:** 0
**Files modified:** 4
**Lines added:** ~550
