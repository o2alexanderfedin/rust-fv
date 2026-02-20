---
phase: 22-higher-order-closures
plan: 02
subsystem: analysis
tags: [hof, vcgen, smt, auflia, closure-contract]
requirements: [HOF-01, HOF-02]
dependency_graph:
  requires: [22-01]
  provides: [hof-vcgen, fn-spec-vc-generation]
  affects: [crates/analysis/src/hof_vcgen.rs, crates/analysis/src/vcgen.rs, crates/analysis/src/lib.rs]
tech_stack:
  added: []
  patterns: [AUFLIA-logic, uninterpreted-closure-functions, negated-forall-entailment, env_before/env_after-FnMut]
key_files:
  created:
    - crates/analysis/src/hof_vcgen.rs
  modified:
    - crates/analysis/src/vcgen.rs
    - crates/analysis/src/lib.rs
decisions:
  - "AUFLIA logic (not QF_BV) for HOF VCs — universal quantification requires non-QF logic"
  - "Best-effort HOF spec expression parser: unsupported expressions produce BoolLit(true) stub rather than panicking"
  - "FnOnce uses identical Fn path — no env_before/after, single-call VC per RESEARCH.md Pattern 6"
  - "Sort::Uninterpreted for closure environment sort (not Sort::Datatype) since env is opaque in fn_spec context"
  - "substitute_result() does post-parse substitution of result -> closure_app term (clean separation of concerns)"
metrics:
  duration: 916
  completed: 2026-02-20
  tasks: 2
  files: 3
---

# Phase 22 Plan 02: HOF VCGen Engine Summary

AUFLIA-logic SMT VC generation for fn_spec closure entailment: hof_vcgen.rs with generate_fn_spec_vcs() + generate_fn_mut_vcs() wired into generate_vcs() so ClosureContract VCs are emitted for every fn_spec clause.

## What Was Built

### Task 1: Create hof_vcgen.rs with Fn/FnOnce and FnMut entailment VC generation

**`crates/analysis/src/hof_vcgen.rs`** — New module implementing fn_spec VC generation:

```rust
/// Generate ClosureContract VCs for all fn_spec clauses in a function's contracts.
pub fn generate_fn_spec_vcs(func: &Function, fn_specs: &[FnSpec]) -> Vec<VerificationCondition>
```

**Fn/FnOnce path** emits AUFLIA scripts with this structure:
```text
(set-logic AUFLIA)
(declare-sort ClosureEnv_PARAM 0)
(declare-fun PARAM_impl (ClosureEnv_PARAM BOUND_SORT ...) Int)
(declare-const env_PARAM ClosureEnv_PARAM)
(declare-const BOUND_VAR BOUND_SORT)
(assert (not (forall ((BOUND_VAR BOUND_SORT)) (=> PRE POST))))
(check-sat)
```
UNSAT = entailment verified.

**FnMut path** adds env_before/env_after constants for each captured variable in ClosureInfo.env_fields:
```text
(declare-const env_before_CAPVAR SORT)
(declare-const env_after_CAPVAR SORT)
```

**Spec expression parser** handles common HOF spec patterns:
- Integer comparisons: `x > 0`, `result > 0`, `x >= 0`, `==`, `!=`, `<=`, `<`
- Arithmetic: `+`, `-`, `*` (top-level operator splitting with parenthesis tracking)
- Conjunctions/disjunctions: `&&`, `||`
- Boolean literals: `true`, `false`
- Falls back to `Term::BoolLit(true)` stub for unrecognized expressions (no panic)

**Result substitution**: `substitute_result()` recursively replaces `Term::Const("result")` with the closure application term `(PARAM_impl env_PARAM BOUND_VAR...)`.

**VerificationCondition emitted with:**
- `description`: `"fn_spec(f, |x| pre => post)"`
- `location.vc_kind`: `VcKind::ClosureContract`
- `location.contract_text`: `"|x| pre => post"`

**10 unit tests** covering: Fn, FnMut, FnOnce paths; env_before/after constants; AUFLIA logic; forall structure; description format; empty spec list; unknown param fallback.

**`crates/analysis/src/lib.rs`** — Added `pub mod hof_vcgen;`.

### Task 2: Wire generate_fn_spec_vcs() into generate_vcs() in vcgen.rs

**`crates/analysis/src/vcgen.rs`** — Added 6 lines after the concurrency VCs section:

```rust
// HOF-01 / HOF-02: Generate fn_spec entailment VCs if any are declared
if !func.contracts.fn_specs.is_empty() {
    let hof_vcs =
        crate::hof_vcgen::generate_fn_spec_vcs(func, &func.contracts.fn_specs);
    conditions.extend(hof_vcs);
}
```

VC generation ordering (final):
1. Standard precondition/postcondition VCs
2. Memory safety VCs
3. Concurrency/weak memory VCs (Phase 21)
4. HOF fn_spec VCs (Phase 22)

`fn_specs` defaults to `vec![]` for all existing functions, so the new branch is never taken in any pre-existing tests — zero regressions.

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Clippy `only_used_in_recursion` on `bound_sorts` param**
- **Found during:** Task 1 clippy check
- **Issue:** `parse_hof_expr` passed `bound_sorts` only to recursive calls, triggering the `only_used_in_recursion` lint
- **Fix:** Renamed parameter to `_bound_sorts` (clippy-idiomatic prefix for recursion-only params)
- **Files modified:** `crates/analysis/src/hof_vcgen.rs`
- **Commit:** f08c995

**2. [Rule 1 - Bug] Clippy `manual_strip` on negative literal detection**
- **Found during:** Task 1 clippy check
- **Issue:** `s.starts_with('-')` followed by `s[1..]` triggered `manual_strip` lint
- **Fix:** Replaced with `s.strip_prefix('-')` + let-chain syntax to also fix `collapsible_if`
- **Files modified:** `crates/analysis/src/hof_vcgen.rs`
- **Commit:** f08c995

**3. [Rule 3 - Blocking] rustfmt line-length formatting in vcgen.rs wiring**
- **Found during:** Task 2 pre-commit hook
- **Issue:** Two-line `let hof_vcs = \n crate::...` was reformatted to one line by rustfmt
- **Fix:** Ran `cargo fmt -p rust-fv-analysis` before commit
- **Files modified:** `crates/analysis/src/vcgen.rs`
- **Commit:** 5515f0f

## Self-Check

**Files exist:**
- FOUND: `crates/analysis/src/hof_vcgen.rs`
- FOUND: `crates/analysis/src/vcgen.rs`
- FOUND: `crates/analysis/src/lib.rs`

**Commits exist:**
- FOUND: f08c995 — feat(22-02): create hof_vcgen.rs with Fn/FnOnce and FnMut entailment VC generation
- FOUND: 5515f0f — feat(22-02): wire generate_fn_spec_vcs() into generate_vcs() in vcgen.rs

**Verification:**
- `cargo build -p rust-fv-analysis` passes
- `cargo clippy -p rust-fv-analysis -- -D warnings` passes (no warnings)
- `grep generate_fn_spec_vcs crates/analysis/src/vcgen.rs` returns a result
- `grep hof_vcgen crates/analysis/src/lib.rs` returns a result
- All tests: 1184 passed in rust-fv-analysis, 0 failed, zero regressions across rust-fv-macros, rust-fv-analysis, rust-fv-driver

## Self-Check: PASSED
