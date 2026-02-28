---
phase: 36-summary-contract-inference
plan: 01
subsystem: analysis
tags: [formal-verification, proc-macro, vcgen, contract-inference, opaque-callee]

# Dependency graph
requires:
  - phase: 35-opaque-callee-diagnostics
    provides: V060/V061 OpaqueCallee diagnostic infrastructure used here for suppression
provides:
  - "#[verifier::infer_summary] proc-macro attribute embedding rust_fv::infer_summary doc marker"
  - "is_inferred: bool field on Contracts and FunctionSummary structs"
  - "Extraction of rust_fv::infer_summary doc attr in callbacks.rs extract_contracts"
  - "OpaqueCallee VC suppression in generate_call_site_vcs for is_inferred=true entries"
  - "Updated suggest_fix for OpaqueCallee mentioning #[verifier::infer_summary] as alternative"
affects: [37-cross-crate-recursion, vcgen, contract-db, diagnostics]

# Tech tracking
tech-stack:
  added: []
  patterns:
    - "infer_summary follows trusted_impl pattern — proc-macro embeds doc marker, driver scans it"
    - "is_inferred flag propagates: HirContracts -> ir::Contracts -> FunctionSummary -> vcgen early continue"
    - "Synthetic DB entry insertion: || contracts.is_inferred guard ensures empty-contract functions enter contract_db"

key-files:
  created: []
  modified:
    - "crates/macros/src/lib.rs"
    - "crates/analysis/src/ir.rs"
    - "crates/analysis/src/contract_db.rs"
    - "crates/driver/src/callbacks.rs"
    - "crates/analysis/src/vcgen.rs"
    - "crates/driver/src/diagnostics.rs"

key-decisions:
  - "infer_summary suppression via is_inferred flag on FunctionSummary — early continue in generate_call_site_vcs before has_requires check"
  - "Synthetic DB entry guard: || contracts.is_inferred added to existing OR-chain — minimal invasiveness"
  - "is_inferred propagation via doc-attr pattern matching rust_fv::infer_summary in extract_contracts (mirrors is_pure arm)"

patterns-established:
  - "Pattern: proc-macro embeds doc marker, driver scans doc attr in HIR, sets field on HirContracts, propagates to ir::Contracts and FunctionSummary"
  - "Pattern: is_inferred early-continue in generate_call_site_vcs before VC generation — safe skip for pure no-op callees"

requirements-completed: [OPAQUE-03]

# Metrics
duration: 35min
completed: 2026-02-28
---

# Phase 36 Plan 01: Summary Contract Inference Summary

**`#[verifier::infer_summary]` proc-macro with is_inferred flag propagation from HIR doc-attr through contract_db to vcgen OpaqueCallee suppression**

## Performance

- **Duration:** ~35 min
- **Started:** 2026-02-28T20:20:00Z
- **Completed:** 2026-02-28T20:59:46Z
- **Tasks:** 3 (2 TDD + 1 verification)
- **Files modified:** 33 (including stdlib_contracts, benches, test files for is_inferred: false propagation)

## Accomplishments
- `#[verifier::infer_summary]` proc-macro attribute registered in crates/macros/src/lib.rs, mirrors trusted_impl pattern, embeds `rust_fv::infer_summary` doc marker
- `is_inferred: bool` field added to `Contracts` struct in ir.rs and `FunctionSummary` struct in contract_db.rs
- `extract_contracts` in callbacks.rs now detects `rust_fv::infer_summary` doc attr and populates an entry in contract_db with `is_inferred=true` even when all other contract fields are empty
- `generate_call_site_vcs` in vcgen.rs short-circuits with `continue` for `is_inferred=true` callees — suppressing OpaqueCallee/OpaqueCalleeUnsafe diagnostic
- `suggest_fix` for OpaqueCallee in diagnostics.rs updated to mention `#[verifier::infer_summary]` as an alternative to full contracts
- Full workspace clippy (`-D warnings`) and test suite pass with zero failures

## Task Commits

Each task was committed atomically:

1. **Task 1: Add proc-macro and is_inferred flag** - `1b806fa` (feat)
2. **Task 2: RED tests for OpaqueCallee suppression** - `c78c006` (test)
3. **Task 2: Extract infer_summary in callbacks, suppress in vcgen, update suggest_fix** - `5f0d7f6` (feat)
4. **Task 3: Full build/clippy/test verification** - (no commit — verification only, workspace clean)

_Note: Task 1 required auto-fixing 30+ struct literal sites across stdlib_contracts, vcgen, benches, and test files to add is_inferred: false after the field was added to Contracts._

## Files Created/Modified
- `crates/macros/src/lib.rs` - Added infer_summary proc-macro and infer_summary_impl, plus unit tests
- `crates/analysis/src/ir.rs` - Added is_inferred: bool to Contracts struct with tests
- `crates/analysis/src/contract_db.rs` - Added is_inferred: bool to FunctionSummary with tests
- `crates/driver/src/callbacks.rs` - Added is_inferred to HirContracts, extraction arm for rust_fv::infer_summary, guard update, propagation to FunctionSummary
- `crates/analysis/src/vcgen.rs` - Added is_inferred early continue in generate_call_site_vcs, plus two new regression tests
- `crates/driver/src/diagnostics.rs` - Updated suggest_fix for OpaqueCallee to mention infer_summary
- 27 other files (stdlib_contracts, tests, benches) — added is_inferred: false to struct literals

## Decisions Made
- infer_summary suppression implemented as early `continue` in `generate_call_site_vcs` before `has_requires`/`has_alias_preconditions` checks — cleanest skip with no VC generation for inferred callees
- Synthetic DB entry guard uses `|| contracts.is_inferred` added to the existing OR-chain in `extract_contracts` — zero disruption to existing logic
- is_inferred propagation mirrors the is_pure field pattern throughout: HirContracts -> ir::Contracts -> FunctionSummary

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Fixed 30+ Contracts struct literal compilation errors**
- **Found during:** Task 1 (after adding is_inferred field to Contracts struct)
- **Issue:** Adding `is_inferred: bool` to Contracts caused compilation failures in all files that had explicit Contracts struct literals (stdlib_contracts, vcgen, monomorphize, recursion, async_vcgen, hof_vcgen, benches, and 15+ test files)
- **Fix:** Applied sed pattern to add `is_inferred: false` after `state_invariant: None,` in all affected files, then ran cargo fmt to normalize indentation
- **Files modified:** All stdlib_contracts modules, vcgen.rs, monomorphize.rs, recursion.rs, async_vcgen.rs, hof_vcgen.rs, stress_bench.rs, vcgen_bench.rs, and 15 test files in crates/analysis/tests/, plus driver/src/cache.rs and driver tests
- **Verification:** `cargo build --workspace` exits 0, `cargo test --workspace` all pass
- **Committed in:** 1b806fa (Task 1 commit)

---

**Total deviations:** 1 auto-fixed (Rule 1 - compilation errors from field addition)
**Impact on plan:** Necessary consequence of adding a new non-optional field to a widely-used struct. No scope creep — only added `is_inferred: false` at existing sites.

## Issues Encountered
- The pre-commit hook (rustfmt + clippy) revealed additional files missed by the initial sed pass (stress_bench.rs, vcgen_bench.rs, hof_closures.rs, async_vcgen.rs, hof_vcgen.rs, driver/src/cache.rs, driver test files) — required multiple fix rounds before the commit succeeded.

## Next Phase Readiness
- OPAQUE-03 requirement fulfilled: users can annotate callees with `#[verifier::infer_summary]` to avoid V060/V061 diagnostics
- Phase 37 (cross-crate recursion) can proceed — no blockers from Phase 36 Plan 01
- Regression guards in place: test_opaque_callee_vc_emitted_for_uncontracted_callee still passes (no annotation = still emits V060); test_no_opaque_callee_vc_for_inferred_summary_callee passes (annotated = no V060)

---
*Phase: 36-summary-contract-inference*
*Completed: 2026-02-28*
