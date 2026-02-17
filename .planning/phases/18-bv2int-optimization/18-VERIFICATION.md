---
phase: 18-bv2int-optimization
verified: 2026-02-17T21:00:00Z
status: human_needed
score: 4/5 success criteria verified (5th needs human judgment)
re_verification: false
human_verification:
  - test: "Confirm that inline Rust doc comments and --help text satisfy the 'Documentation clearly explains when/how to use bv2int and known limitations' criterion"
    expected: "Either (a) the existing --help text + module-level doc comments in bv2int.rs are accepted as sufficient documentation, or (b) a separate user-facing doc file (docs/bv2int.md or similar) is needed"
    why_human: "The ROADMAP criterion says 'Documentation clearly explains when/how to use bv2int and known limitations' — this is ambiguous between a standalone docs file and inline help text. The help text covers activation, eligibility, and env vars. Module docs cover conservative analysis strategy. No docs/ file exists outside .planning/. A human must decide if this meets the bar."
---

# Phase 18: bv2int Optimization Verification Report

**Phase Goal:** Developer can enable bv2int optimization for arithmetic-heavy verification with proven equivalence and performance measurement
**Verified:** 2026-02-17T21:00:00Z
**Status:** human_needed
**Re-verification:** No — initial verification

## Goal Achievement

### Observable Truths (from ROADMAP.md Success Criteria)

| #  | Truth | Status | Evidence |
|----|-------|--------|---------|
| 1  | Developer can enable bv2int optimization via RUST_FV_BV2INT=1 environment variable | VERIFIED | `parse_bv2int_flag` in `cargo_verify.rs` line 320: falls back to `std::env::var("RUST_FV_BV2INT").map(|v| v == "1")`. Help text at line 526 documents it. CLI flag takes precedence (line 317-318). |
| 2  | Differential testing suite proves equivalence between bitvector and bv2int encodings across all test cases | VERIFIED | `crates/analysis/src/differential.rs` (480 lines, 13 tests): `test_encoding_equivalence` runs both encoding modes, compares SAT/UNSAT outcomes, returns `EquivalenceResult` with timing and divergence detection. Wired into `callbacks.rs` via `run_differential_test`. |
| 3  | Conservative applicability analysis restricts bv2int to arithmetic-only verification (no bitwise operations) | VERIFIED | `is_bv2int_eligible` in `bv2int.rs` lines 95-145: rejects any function containing `BinOp::BitAnd`, `BitOr`, `BitXor`, `Shl`, or `Shr` with actionable `IneligibilityReason` message. 5 distinct bitwise rejection tests pass. |
| 4  | Performance regression tests detect cases where bv2int causes slowdowns (>2x slower triggers warning) | VERIFIED | `check_slowdown_warning` in `output.rs` line 321-337: triggers when `speedup_factor < 1.0 / threshold` (default 2.0), i.e. bv2int strictly more than 2x slower. Threshold configurable via `--bv2int-threshold` or `RUST_FV_BV2INT_THRESHOLD`. Wired into `callbacks.rs` line 707-713. 6 unit tests. |
| 5  | Documentation clearly explains when/how to use bv2int and known limitations | UNCERTAIN | Help text in `cargo_verify.rs` lines 486-503, 525-529 covers activation, eligibility, QF_LIA/QF_NIA encoding, and env vars. Module-level doc comments in `bv2int.rs` lines 1-9 explain encoding modes, eligibility analysis, and conservative rejection strategy. No standalone user-facing doc file exists outside `.planning/`. Needs human judgment. |

**Score:** 4/5 truths verified (1 uncertain pending human assessment)

### Required Artifacts

| Artifact | Min Lines | Actual Lines | Status | Details |
|----------|-----------|--------------|--------|---------|
| `crates/analysis/src/bv2int.rs` | 150 | 876 | VERIFIED | Contains `EncodingMode` enum, `IneligibilityReason`, `is_bv2int_eligible`, `encode_type_with_mode`, `encode_binop_with_mode`, `wrap_overflow`. 35 unit tests. |
| `crates/analysis/src/differential.rs` | 100 | 480 | VERIFIED | Contains `EquivalenceResult`, `test_encoding_equivalence`, `format_equivalence_result`, `SolverInterface` trait, `VcOutcome` enum. 13 unit tests. |
| `crates/driver/src/cache.rs` | — | 1455 | VERIFIED | Extended with `bv2int_equiv_tested`, `bv2int_bitvec_time_ms`, `bv2int_int_time_ms`, `bv2int_speedup` fields (all `#[serde(default)]`). `store_equivalence_result`/`get_equivalence_result` methods present. 7 new tests. |
| `crates/driver/src/cargo_verify.rs` | — | 1507 | VERIFIED | `parse_bv2int_flag`, `parse_bv2int_report_flag`, `parse_bv2int_threshold` all present. Help text documents all flags and env vars. CLI precedence logic at lines 316-323. |
| `crates/driver/src/callbacks.rs` | — | 1196 | VERIFIED | `EncodingMode` used, `is_bv2int_eligible` called per-function. `run_differential_test` wires `generate_vcs_with_mode` + `test_encoding_equivalence`. `Z3SolverAdapter` implements `SolverInterface`. |
| `crates/driver/src/output.rs` | — | 811 | VERIFIED | `Bv2intFunctionReport`, `format_bv2int_timing`, `check_slowdown_warning`, `print_bv2int_report` all present. 20 integration tests. |
| `crates/driver/src/diagnostics.rs` | — | 2474 | VERIFIED | `report_bv2int_divergence` (V002) and `report_bv2int_ineligibility` (V003) present. 4 smoke tests. |

### Key Link Verification

| From | To | Via | Status | Details |
|------|----|-----|--------|---------|
| `cargo_verify.rs` | `callbacks.rs` | bv2int config passed as env vars | WIRED | `cargo_verify.rs` sets `RUST_FV_BV2INT`, `RUST_FV_BV2INT_REPORT`, `RUST_FV_BV2INT_THRESHOLD` env vars (lines 138-145); `callbacks.rs` reads them at lines 149-157 |
| `callbacks.rs` | `bv2int.rs` | `is_bv2int_eligible` per-function call | WIRED | `callbacks.rs` line 505: `rust_fv_analysis::bv2int::is_bv2int_eligible(ir_func)` |
| `callbacks.rs` | `differential.rs` | `run_differential_test` calls `test_encoding_equivalence` | WIRED | `callbacks.rs` line 866 calls `rust_fv_analysis::differential::test_encoding_equivalence`. `run_differential_test` at line 831. |
| `differential.rs` | `bv2int.rs` | `EncodingMode::Bitvector` and `EncodingMode::Integer` used in VC generation | WIRED | `generate_vcs_with_mode` called with both modes in `run_differential_test` |
| `differential.rs` | `vcgen.rs` | `generate_vcs_with_mode` called | WIRED | `callbacks.rs`:`run_differential_test` calls `rust_fv_analysis::vcgen::generate_vcs_with_mode` |
| `output.rs` | `callbacks.rs` | `format_bv2int_timing` and `check_slowdown_warning` called | WIRED | `callbacks.rs` lines 703, 707 call `output::format_bv2int_timing` and `output::check_slowdown_warning` |
| `cache.rs` | `differential.rs` | `bv2int_equiv_tested` fields store equivalence results | WIRED | `CacheEntry::store_equivalence_result` method present and called from callback pipeline |

### Requirements Coverage

| Requirement | Source Plans | Description | Status | Evidence |
|-------------|-------------|-------------|--------|---------|
| PERF-05 | 18-01, 18-03 | Developer can enable bv2int optimization for arithmetic-heavy verification via environment variable | SATISFIED in code — PENDING in tracker | `RUST_FV_BV2INT=1` activates bv2int mode. `cargo_verify.rs` line 320 reads env var. **Note: REQUIREMENTS.md still shows `[ ]` (Pending) — tracker not updated after implementation.** |
| PERF-06 | 18-02, 18-03 | bv2int differential testing ensures equivalence with bitvector encoding | SATISFIED in code — PENDING in tracker | `differential.rs` implements `test_encoding_equivalence` with timing and divergence detection. Cached via `CacheEntry` bv2int fields. **Note: REQUIREMENTS.md still shows `[ ]` (Pending) — tracker not updated after implementation.** |

### Anti-Patterns Found

No anti-patterns found in the phase artifacts. Scanned for `TODO`, `FIXME`, `PLACEHOLDER`, `unimplemented!`, `todo!`, empty return values, and stub implementations in all 7 key files — none detected.

The graceful degradation pattern (`run_differential_test` returns `(None, None, None)` when Z3 unavailable) is intentional, not a stub — it preserves correctness when the solver binary is absent.

### Human Verification Required

#### 1. Documentation Sufficiency Assessment

**Test:** Review the following documentation surfaces and determine if they collectively satisfy "Documentation clearly explains when/how to use bv2int and known limitations":

1. Run `cargo verify --help` and read the bv2int section
2. Read `crates/analysis/src/bv2int.rs` lines 1-95 (module doc + `EncodingMode` + `IneligibilityReason` + `is_bv2int_eligible` doc)
3. Confirm there is no standalone `docs/bv2int.md` or similar file outside `.planning/`

**Expected:** Either (a) the help text + module docs are accepted as sufficient, or (b) a separate user-facing documentation file is required.

**Why human:** "Documentation clearly explains when/how to use bv2int and known limitations" is inherently a quality judgment. The implementation provides:
- `--help` text covering: activation flags, env vars, eligibility concept (QF_LIA/QF_NIA), threshold configuration
- Module-level Rust doc comments: encoding mode explanation, conservative rejection strategy, ineligibility reasons with actionable messages
- Runtime per-function warnings explaining why a function was skipped (the "known limitations" surfaced dynamically)
- No separate `docs/bv2int.md` file exists

The sufficiency of inline docs + help text vs. a standalone user doc file is a product decision, not a code question.

## Gaps Summary

No implementation gaps found. All code artifacts are substantive, wired, and non-stub. The 4 programmatically-verifiable success criteria pass.

One item requires human judgment: whether the existing --help text and Rust doc comments constitute sufficient "Documentation" for success criterion 5, or whether a standalone user-facing docs file is required.

Additionally, REQUIREMENTS.md bookkeeping is stale: PERF-05 and PERF-06 both show `[ ]` (Pending) at lines 24-25 and 80-81, despite being implemented. This does not affect goal achievement but means the requirements tracker is out of sync with reality.

---

_Verified: 2026-02-17T21:00:00Z_
_Verifier: Claude (gsd-verifier)_
