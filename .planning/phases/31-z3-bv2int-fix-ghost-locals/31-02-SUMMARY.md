---
phase: 31-z3-bv2int-fix-ghost-locals
plan: "02"
subsystem: vcgen
tags: [bv2int, spec-int, smt-logic, e2e-tests, z3]
dependency_graph:
  requires:
    - "31-01"
  provides:
    - "uses_spec_int_types() detects as int/as nat in spec strings"
    - "E2E tests: test_unbounded_int_addition_no_overflow GREEN"
    - "E2E tests: test_unbounded_int_sum_formula GREEN"
  affects:
    - "crates/analysis/src/vcgen.rs"
    - "crates/analysis/tests/e2e_verification.rs"
tech_stack:
  added: []
  patterns:
    - "let closure for spec expression predicate scanning"
    - "let-chain collapsible-if for Option<SpecExpr> check"
    - "..Default::default() pattern for Contracts missing fields"
key_files:
  created: []
  modified:
    - "crates/analysis/src/vcgen.rs"
    - "crates/analysis/tests/e2e_verification.rs"
decisions:
  - "Extended uses_spec_int_types() with substring scan over spec expressions (contains 'as int' / 'as nat') after existing type-based checks — minimal change, no signature change"
  - "Used let-chain syntax for state_invariant Option check to satisfy clippy collapsible_if rule"
  - "Added all missing Function struct fields explicitly (no Default on Function, only Contracts has Default) — mirrors make_add_function() helper pattern"
metrics:
  duration: 288
  completed: "2026-02-26"
  tasks_completed: 2
  files_modified: 2
---

# Phase 31 Plan 02: Fix uses_spec_int_types() and Activate bv2int E2E Tests Summary

Extended `uses_spec_int_types()` in vcgen.rs to detect `"as int"`/`"as nat"` substrings in spec expression strings, enabling ALL logic selection for BV-typed functions with integer-cast specs; then activated the two corresponding E2E tests.

## Tasks Completed

| Task | Name | Commit | Files |
|------|------|--------|-------|
| 1 | Extend uses_spec_int_types() for spec string scanning | f062779 | crates/analysis/src/vcgen.rs |
| 2 | Un-comment bv2int E2E tests and fix struct initializers | 493933e | crates/analysis/tests/e2e_verification.rs |

## What Was Built

**Task 1: `uses_spec_int_types()` extension**

Added spec expression scanning after the existing type-based checks in `uses_spec_int_types()`. The new code scans all spec expressions in `func.contracts.requires`, `.ensures`, `.invariants`, and `.state_invariant` for the substrings `"as int"` or `"as nat"`. This covers the common case where a function uses BV IR types (I32, U64) but its spec asserts properties via integer arithmetic using `as int` casts.

The `phase04_bv2int_logic_selection` test (added in plan 31-01 as RED) is now GREEN.

**Task 2: Un-commented E2E tests**

Removed the `// TODO: ` prefix from all lines in the two blocked test functions in `e2e_verification.rs` (lines ~1518–1682). Fixed:
- Stray un-prefixed comment at original line 1595 (indented correctly)
- Missing `Function` struct fields (not deriveable as Default) — added all fields matching the `make_add_function()` helper pattern
- Missing `Contracts` struct fields — used `..Default::default()` (Contracts derives Default)

Both tests assert `(set-logic ALL)` and `bv2int` presence in generated SMT scripts and now pass GREEN.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Missing Function struct fields in un-commented tests**
- **Found during:** Task 2 — compile errors after un-commenting
- **Issue:** `Function` struct has 18+ fields; the commented-out tests only specified 7
- **Fix:** Added all missing fields (`generic_params`, `prophecies`, `lifetime_params`, `outlives_constraints`, `borrow_info`, `reborrow_chains`, `unsafe_blocks`, `unsafe_operations`, `unsafe_contracts`, `is_unsafe_fn`, `thread_spawns`, `atomic_ops`, `sync_ops`, `lock_invariants`, `concurrency_config`, `source_names`, `coroutine_info`) matching the existing `make_add_function()` pattern
- **Files modified:** crates/analysis/tests/e2e_verification.rs
- **Commit:** 493933e

**2. [Rule 1 - Bug] Stray unindented comment at original line 1595**
- **Found during:** Task 2 — the line `// Check that bv2int conversion is present` lacked the `// TODO:` prefix in the original file, so it remained at column 0 after un-commenting
- **Fix:** Indented to 8-space level matching surrounding code
- **Files modified:** crates/analysis/tests/e2e_verification.rs
- **Commit:** 493933e

**3. [Rule 2 - Auto-fix] Clippy collapsible_if for state_invariant check**
- **Found during:** Task 1 commit attempt
- **Issue:** Nested `if let Some(ref inv) = ... { if spec_uses_bv2int(inv) { return true; } }` triggers `clippy::collapsible_if`
- **Fix:** Used let-chain syntax: `if let Some(ref inv) = func.contracts.state_invariant && spec_uses_bv2int(inv) { return true; }`
- **Files modified:** crates/analysis/src/vcgen.rs
- **Commit:** f062779

## Verification Results

```
test phase04_bv2int_logic_selection ... ok          (vcgen_completeness29)
test test_unbounded_int_addition_no_overflow ... ok  (e2e_verification)
test test_unbounded_int_sum_formula ... ok           (e2e_verification)

Regressions: 0 (phase04_ghost_local_leaks_into_vc still RED — expected, fixed in plan 31-03)
cargo clippy: 0 errors
```

## Self-Check: PASSED

Files modified:
- FOUND: crates/analysis/src/vcgen.rs
- FOUND: crates/analysis/tests/e2e_verification.rs

Commits:
- FOUND: f062779
- FOUND: 493933e
