---
phase: 20-separation-logic
plan: "02"
subsystem: ghost-predicate-infrastructure
tags: [separation-logic, proc-macro, ghost-predicate, database]
dependency_graph:
  requires: []
  provides: [ghost_predicate_macro, GhostPredicateDatabase, ghost_pred_db_field]
  affects: [crates/macros, crates/analysis, crates/driver]
tech_stack:
  added: [GhostPredicateDatabase, GhostPredicate]
  patterns: [doc-attribute-serialization, database-as-struct-field]
key_files:
  created:
    - crates/analysis/src/ghost_predicate_db.rs
  modified:
    - crates/macros/src/lib.rs
    - crates/analysis/src/lib.rs
    - crates/driver/src/callbacks.rs
decisions:
  - "extract_ghost_predicates() as separate function (not modifying extract_contracts return type) — avoids call-site ripple effects"
  - "ghost_pred_db stored as pub field on VerificationCallbacks so Plan 03 can read self.ghost_pred_db during VC generation"
  - "let-chain collapsible-if pattern used for doc attribute matching to satisfy clippy -D warnings"
metrics:
  duration_seconds: 34
  tasks_completed: 2
  files_created: 1
  files_modified: 4
  completed_date: "2026-02-19"
---

# Phase 20 Plan 02: Ghost Predicate Infrastructure Summary

Ghost predicate proc-macro, GhostPredicateDatabase, and callbacks.rs extraction wired end-to-end using doc-attribute serialization pattern.

## Tasks Completed

| Task | Name | Commit | Files |
|------|------|--------|-------|
| 1 | Add #[ghost_predicate] proc-macro | 4031e46 | crates/macros/src/lib.rs, crates/analysis/src/sep_logic.rs |
| 2 | Create GhostPredicateDatabase and wire callbacks.rs | 37070f3 | ghost_predicate_db.rs, lib.rs, callbacks.rs, spec_parser.rs |

## What Was Built

### ghost_predicate proc-macro (crates/macros/src/lib.rs)

The `#[ghost_predicate]` proc-macro attribute serializes a function's parameter names and body as a hidden doc attribute using the format:

```
rust_fv::ghost_predicate::fn_name::param1,param2::body_tokens
```

The function itself is emitted unchanged for normal compilation. The doc attribute is `#[doc(hidden)]` to suppress rustdoc output. Tests verify the correct format string and param serialization.

### GhostPredicateDatabase (crates/analysis/src/ghost_predicate_db.rs)

```rust
pub struct GhostPredicate {
    pub param_names: Vec<String>,
    pub body_raw: String,
}

pub struct GhostPredicateDatabase {
    predicates: HashMap<String, GhostPredicate>,
}
```

API: `insert()`, `get()`, `contains()`, `len()`, `is_empty()`. Three unit tests cover insert/get, empty DB, and multiple predicates.

### callbacks.rs extraction (crates/driver/src/callbacks.rs)

- Added `ghost_pred_db: GhostPredicateDatabase` field on `VerificationCallbacks` (initialized in `new()` and `passthrough()`)
- Added `extract_ghost_predicates(tcx)` function that scans HIR body owners for `rust_fv::ghost_predicate::` doc attrs
- Uses `splitn(3, "::")` to parse name, params (comma-separated), and body_raw
- Called in `after_analysis()` before contract DB construction: `self.ghost_pred_db = extract_ghost_predicates(tcx)`

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 3 - Blocking] Fixed collapsible-if clippy errors in sep_logic.rs**
- **Found during:** Task 1 commit (pre-commit hook)
- **Issue:** sep_logic.rs (from Plan 01) had 4 nested if-let chains that clippy flagged as collapsible-if
- **Fix:** Converted to let-chain syntax: `if let Some(x) = foo() && let Bar(y) = x && y == "perm"`
- **Files modified:** crates/analysis/src/sep_logic.rs
- **Commit:** 4031e46

**2. [Rule 3 - Blocking] Fixed collapsible-if in extract_ghost_predicates**
- **Found during:** Task 2 clippy check
- **Issue:** New extract_ghost_predicates() used nested if-let pattern triggering clippy::collapsible_if
- **Fix:** Converted to let-chain: `if let Some(doc) = extract_doc_value(attr) && let Some(pred_spec) = doc.strip_prefix(...)`
- **Files modified:** crates/driver/src/callbacks.rs
- **Commit:** 37070f3

**3. [Rule 3 - Blocking] Fixed rustfmt formatting in spec_parser.rs**
- **Found during:** Task 2 commit (pre-commit hook)
- **Issue:** spec_parser.rs had pre-existing formatting deviations (line-break style)
- **Fix:** `cargo fmt -p rust-fv-analysis`
- **Files modified:** crates/analysis/src/spec_parser.rs
- **Commit:** 37070f3

## Verification Results

1. `cargo build -p rust-fv-macros` — 0 errors
2. `cargo build -p rust-fv-driver` — 0 errors
3. `cargo test -p rust-fv-macros -- test_ghost_predicate` — 2 tests pass
4. `cargo test -p rust-fv-analysis -- ghost_predicate_db` — 3 tests pass
5. `cargo clippy -p rust-fv-macros -p rust-fv-analysis -p rust-fv-driver -- -D warnings` — 0 warnings

## Self-Check: PASSED

- crates/analysis/src/ghost_predicate_db.rs: FOUND
- crates/macros/src/lib.rs ghost_predicate macro: FOUND (lines 232-253)
- ghost_pred_db field on VerificationCallbacks: FOUND
- Commits 4031e46 and 37070f3: FOUND
