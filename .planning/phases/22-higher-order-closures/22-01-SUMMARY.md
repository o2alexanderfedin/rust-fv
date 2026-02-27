---
phase: 22-higher-order-closures
plan: 01
subsystem: macros+analysis+driver
tags: [hof, proc-macro, ir, extraction, fn-spec]
requirements: [HOF-01, HOF-02]
dependency_graph:
  requires: []
  provides: [fn_spec-macro, FnSpec-IR, fn_spec-extraction]
  affects: [crates/macros/src/lib.rs, crates/analysis/src/ir.rs, crates/driver/src/callbacks.rs]
tech_stack:
  added: []
  patterns: [proc_macro2-token-scanning, doc-attribute-encoding, HIR-extraction]
key_files:
  created: []
  modified:
    - crates/macros/src/lib.rs
    - crates/analysis/src/ir.rs
    - crates/driver/src/callbacks.rs
    - crates/analysis/src/recursion.rs
    - "crates/analysis/src/stdlib_contracts/*.rs (9 files)"
    - "crates/analysis/tests/*.rs (13 test files)"
    - "crates/driver/src/cache.rs"
    - "crates/driver/tests/incremental_correctness.rs"
decisions:
  - "Token-level fat-arrow scanning (not syn::parse_str) to handle => in fn_spec clauses — syn rejects fat-arrow as binary op"
  - "%% as pre/post separator to avoid :: collisions in expression content"
  - "Single form: (f, |x| pre => post) where first segment has no fat-arrow; multi form: each segment has PARAM => CLAUSE"
  - "extract_bound_vars/strip_bound_var_prefix as simple string helpers — no need for full syn parsing"
metrics:
  duration: 1719
  completed: 2026-02-20
  tasks: 2
  files: 32
---

# Phase 22 Plan 01: fn_spec Annotation Infrastructure Summary

fn_spec proc macro + FnSpec IR type + driver extraction: full triangle from `#[fn_spec(f, |x| pre => post)]` to `Contracts.fn_specs` parsed entries.

## What Was Built

### Task 1: fn_spec Proc Macro + FnSpec IR Type

**`crates/analysis/src/ir.rs`** — Added `FnSpec` struct and extended `Contracts`:
```rust
pub struct FnSpec {
    pub closure_param: String,
    pub pre: String,
    pub post: String,
    pub bound_vars: Vec<String>,
}

pub struct Contracts {
    // ... existing fields ...
    pub fn_specs: Vec<FnSpec>,  // new field, defaults to vec![]
}
```

**`crates/macros/src/lib.rs`** — Added `fn_spec` proc macro:
- Public `#[proc_macro_attribute]` entry `fn_spec` delegating to `fn_spec_impl`
- `fn_spec_impl` supports two forms:
  - Single: `(f, |x| pre => post)` — first comma-separated segment is the param
  - Multiple: `(f => |x| ..., g => |y| ...)` — each segment is `PARAM => CLAUSE`
- Token-level fat-arrow scanning (`=` followed by `>`) avoids syn parsing limitations
- Encodes as `rust_fv::fn_spec::PARAM::PRE%%POST` hidden doc attributes
- 6 unit tests covering both forms, error handling, and item preservation

### Task 2: Driver Extraction of fn_spec Doc Attributes

**`crates/driver/src/callbacks.rs`** — Extended `extract_contracts()`:
- Added `fn_specs: Vec<FnSpec>` to `HirContracts` intermediate struct
- Added `rust_fv::fn_spec::` branch in the doc attribute scanning loop
- Uses `split_once("::")` and `split_once("%%")` to parse PARAM and PRE%%POST
- Added `extract_bound_vars()` helper: extracts names from `|x: T, y: U|` prefix
- Added `strip_bound_var_prefix()` helper: returns pre-expression after `|vars|`
- Wired `fn_specs: contracts.fn_specs` into the final `Contracts` construction

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 1 - Bug] Collapsible-if clippy violations in fn_spec helpers**
- **Found during:** Task 1 clippy check
- **Issue:** Nested `if let` + `if` blocks in `contains_fat_arrow` and `find_fat_arrow_position` triggered `collapsible_if` clippy lint
- **Fix:** Converted to let-chain syntax (`&& let ... && condition`)
- **Files modified:** `crates/macros/src/lib.rs`
- **Commit:** 64a35be

**2. [Rule 3 - Blocking] 170+ Contracts struct literals missing fn_specs field**
- **Found during:** Task 1 (adding new field to Contracts struct)
- **Issue:** All explicit `Contracts { ... }` struct literals across the codebase failed to compile without the new `fn_specs` field
- **Fix:** Python script to add `fn_specs: vec![],` after every `decreases: None,` or `decreases: Some(...),` block in 32 files
- **Files modified:** All test files, stdlib_contracts/*.rs, benches, driver/cache.rs
- **Commit:** 64a35be

**3. [Rule 1 - Bug] Python script missed `decreases: None, // comment` pattern**
- **Found during:** Task 1 test compilation
- **Issue:** The Python script only matched lines ending exactly with `decreases: None,` — missed the case with inline comments
- **Fix:** Applied a more inclusive pattern match that catches `decreases: None` anywhere on the line
- **Files modified:** `crates/analysis/tests/recursion_verification.rs`
- **Commit:** 64a35be

**4. [Rule 1 - Bug] Python script injected fn_specs into commented-out code in e2e_verification.rs**
- **Found during:** `cargo fmt` formatting check
- **Issue:** Two `// TODO: decreases: None,` comment lines triggered the Python script, producing syntactically invalid `fn_specs:` lines at zero indentation
- **Fix:** Removed the two incorrect `fn_specs: vec![],` lines
- **Files modified:** `crates/analysis/tests/e2e_verification.rs`
- **Commit:** 64a35be

## Self-Check

**Files exist:**
- FOUND: `crates/analysis/src/ir.rs` (FnSpec struct, fn_specs field)
- FOUND: `crates/macros/src/lib.rs` (fn_spec proc macro, fn_spec_impl)
- FOUND: `crates/driver/src/callbacks.rs` (rust_fv::fn_spec:: extraction)

**Commits exist:**
- FOUND: 64a35be — feat(22-01): fn_spec proc macro, FnSpec IR type, and driver extraction

**Tests:**
- 1174 tests pass (0 failed, 0 regressions)
- 6 new fn_spec tests in rust-fv-macros
- clippy -D warnings clean on all three modified crates

## Self-Check: PASSED
