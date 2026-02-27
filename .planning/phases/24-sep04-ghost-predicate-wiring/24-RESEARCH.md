# Phase 24: SEP-04 Ghost Predicate Production Wiring - Research

**Researched:** 2026-02-20
**Domain:** Rust driver pipeline wiring — threading `GhostPredicateDatabase` through `VerificationTask` into `generate_vcs()` and `parse_spec()`
**Confidence:** HIGH (all findings from direct source inspection of the actual codebase)

---

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| SEP-04 | User can define recursive heap predicates via `#[ghost_predicate]` (e.g. `linked_list(p, n)`) with bounded unfolding (depth 3) | Ghost predicate infrastructure fully built in Phase 20 but severed from production pipeline. Three surgical changes wire it end-to-end: add `ghost_pred_db` field to `VerificationTask`, pass it at construction, and switch `parse_spec()` to `parse_spec_expr_with_db`. |
</phase_requirements>

---

## Summary

Phase 20 built the complete `#[ghost_predicate]` infrastructure: `GhostPredicateDatabase` in `crates/analysis/src/ghost_predicate_db.rs`, `extract_ghost_predicates()` in `callbacks.rs`, and `parse_spec_expr_with_db()` in `spec_parser.rs`. The database is correctly populated from HIR doc attributes at `callbacks.rs:401`. However, it is never forwarded into the parallel verification pipeline: `VerificationTask` (defined at `parallel.rs:20-44`) has no `ghost_pred_db` field, the task-construction push at `callbacks.rs:631` omits it, and `verify_single()` calls `generate_vcs()` which internally calls the db-less `parse_spec()` at `vcgen.rs:3091-3093`.

The fix is three surgical changes: (1) add `ghost_pred_db: Arc<GhostPredicateDatabase>` to `VerificationTask`, (2) populate it at the push site in `callbacks.rs`, and (3) thread the database through `generate_vcs()` into `parse_spec()` so it calls `parse_spec_expr_with_db` instead of `parse_spec_expr`. A driver-level integration test using the `verify_functions_parallel` path (not the direct `parse_spec_expr_with_db` path) then validates the wiring end-to-end.

All three sub-problems are well-bounded. The existing `Arc<ContractDatabase>` pattern in `VerificationTask` serves as the exact template for adding `Arc<GhostPredicateDatabase>`. The `parse_spec_expr_with_db` API is stable and tested. The unit/integration test infrastructure in `crates/analysis/tests/sep_logic_integration.rs` provides a clear pattern for the new driver-level test.

**Primary recommendation:** Make the three surgical changes as described, then add a single driver-level integration test that calls `verify_functions_parallel()` with a function whose `#[requires]` spec contains a ghost predicate reference, asserting the VCs are UNSAT (predicate correctly expands).

---

## Standard Stack

### Core (all pre-existing in this codebase)

| Component | Location | Purpose | Status |
|-----------|----------|---------|--------|
| `GhostPredicateDatabase` | `crates/analysis/src/ghost_predicate_db.rs` | Maps predicate name → `GhostPredicate` (param_names, body_raw) | Built, stable |
| `GhostPredicate` | same | Holds formal params + raw body string | Built, stable |
| `extract_ghost_predicates(tcx)` | `crates/driver/src/callbacks.rs:401` | Extracts `#[ghost_predicate]` from HIR doc attrs → `GhostPredicateDatabase` | Built, working |
| `parse_spec_expr_with_db(spec, func, db)` | `crates/analysis/src/spec_parser.rs:46` | Parses spec expression with ghost predicate expansion to depth 3 | Built, stable |
| `VerificationTask` | `crates/driver/src/parallel.rs:21-44` | Per-function task struct carried into rayon threads | Missing `ghost_pred_db` |
| `generate_vcs(func, contract_db)` | `crates/analysis/src/vcgen.rs:224` | Generates all VCs for a function | Missing `ghost_pred_db` parameter |
| `parse_spec(spec, func)` | `crates/analysis/src/vcgen.rs:3091` | Private bridge to `parse_spec_expr` — must be switched to `parse_spec_expr_with_db` | Bug: calls db-less version |

### Supporting

| Component | Location | Purpose |
|-----------|----------|---------|
| `Arc<ContractDatabase>` in `VerificationTask` | `parallel.rs:27` | Exact template for adding `Arc<GhostPredicateDatabase>` — same pattern |
| `verify_single()` | `parallel.rs:222` | Calls `generate_vcs()` — only one call site to update |
| `verify_functions_parallel()` | `parallel.rs:82` | Entry point for driver-level integration test |
| `GHOST_PRED_EXPAND_DEPTH` | `spec_parser.rs` | Constant = 3, controls unfolding depth |

---

## Architecture Patterns

### Current Flow (broken — ghost_pred_db is severed)

```
callbacks.rs:after_analysis()
  ├── extract_ghost_predicates(tcx) → self.ghost_pred_db   [DB built here]
  ├── for each func:
  │     └── tasks.push(VerificationTask { ..., NO ghost_pred_db })  [SEVERED HERE]
  └── verify_functions_parallel(tasks, ...)
        └── verify_single(task)
              └── generate_vcs(&task.ir_func, Some(&task.contract_db))
                    └── parse_spec(spec, func)   [calls parse_spec_expr - db-less]
```

### Fixed Flow (after Phase 24)

```
callbacks.rs:after_analysis()
  ├── extract_ghost_predicates(tcx) → self.ghost_pred_db   [DB built here]
  ├── let ghost_pred_db = Arc::new(self.ghost_pred_db.clone())
  ├── for each func:
  │     └── tasks.push(VerificationTask { ..., ghost_pred_db: Arc::clone(&ghost_pred_db) })
  └── verify_functions_parallel(tasks, ...)
        └── verify_single(task)
              └── generate_vcs(&task.ir_func, Some(&task.contract_db), &task.ghost_pred_db)
                    └── parse_spec(spec, func, &ghost_pred_db)   [calls parse_spec_expr_with_db]
```

### Pattern 1: Arc<T> Sharing for Thread-Safe Shared Data

`VerificationTask` already uses `Arc<ContractDatabase>` for sharing the contract DB across rayon threads without cloning the full DB per function. Use the identical pattern:

```rust
// In callbacks.rs — after building ghost_pred_db
let ghost_pred_db_arc = Arc::new(self.ghost_pred_db.clone());

// In the task push loop
tasks.push(crate::parallel::VerificationTask {
    name: name.clone(),
    ir_func,
    contract_db: std::sync::Arc::new(contract_db.clone()),
    ghost_pred_db: Arc::clone(&ghost_pred_db_arc),  // NEW: same Arc pattern
    cache_key,
    mir_hash: *mir_hash,
    contract_hash: *contract_hash,
    dependencies,
    invalidation_decision,
    source_locations,
});
```

**Source:** Direct inspection of `crates/driver/src/callbacks.rs:631-641` and `crates/driver/src/parallel.rs:21-44`.

### Pattern 2: Extending `generate_vcs()` Signature

`generate_vcs()` is the public API entry. Three callers exist:

1. `crates/driver/src/parallel.rs:262` — `verify_single()` — MUST be updated
2. `crates/analysis/tests/sep_logic_integration.rs` — test file — `generate_vcs(&func, None)` calls
3. Any other crate consumers

Check for all callers and update to add `ghost_pred_db: &GhostPredicateDatabase` parameter. Alternatively, add a new `generate_vcs_with_db()` overload and leave `generate_vcs()` as a shim delegating to it with an empty DB — this is backward-compatible.

**Recommendation:** The backward-compatible shim approach:

```rust
// Keep existing signature as shim
pub fn generate_vcs(func: &Function, contract_db: Option<&ContractDatabase>) -> FunctionVCs {
    let empty_db = spec_parser::empty_ghost_db();
    generate_vcs_with_db(func, contract_db, &empty_db)
}

// New function with ghost_pred_db
pub fn generate_vcs_with_db(
    func: &Function,
    contract_db: Option<&ContractDatabase>,
    ghost_pred_db: &GhostPredicateDatabase,
) -> FunctionVCs {
    // ... same body as current generate_vcs but passes ghost_pred_db to parse_spec
}
```

This avoids touching test files that call `generate_vcs()` directly. The `verify_single()` in `parallel.rs` is then updated to call `generate_vcs_with_db`.

**Alternative:** Modify `generate_vcs()` signature directly. Requires updating all callers. More invasive but simpler.

### Pattern 3: Updating `parse_spec()` to Use DB

The private `parse_spec()` function at `vcgen.rs:3091` is called at 14 sites in `vcgen.rs`. Rather than threading `ghost_pred_db` through each intermediate function, the cleanest approach is:

1. Change `parse_spec()` signature to accept `&GhostPredicateDatabase`
2. Have `generate_vcs_with_db()` (or the updated `generate_vcs()`) pass `ghost_pred_db` into the internal helper

The 14 call sites of `parse_spec()` are all within `generate_contract_vcs()`, `generate_call_site_vcs()`, and similar functions that are already reachable from `generate_vcs()`. They must all receive the db.

**Minimum invasive approach:** Add `ghost_pred_db: &GhostPredicateDatabase` to `parse_spec()` and update all 14 internal call sites within vcgen.rs. This is internal to one file.

```rust
// Before (vcgen.rs:3091)
fn parse_spec(spec: &str, func: &Function) -> Option<Term> {
    let term = spec_parser::parse_spec_expr(spec, func)
        .or_else(|| parse_simple_spec(spec, func))?;
    match crate::encode_quantifier::annotate_quantifier(term) {
        Ok(annotated_term) => Some(annotated_term),
        Err(trigger_error) => { ... None }
    }
}

// After (vcgen.rs:3091)
fn parse_spec(spec: &str, func: &Function, ghost_pred_db: &GhostPredicateDatabase) -> Option<Term> {
    let term = spec_parser::parse_spec_expr_with_db(spec, func, ghost_pred_db)
        .or_else(|| parse_simple_spec(spec, func))?;
    match crate::encode_quantifier::annotate_quantifier(term) {
        Ok(annotated_term) => Some(annotated_term),
        Err(trigger_error) => { ... None }
    }
}
```

### Pattern 4: Driver-Level Integration Test

Existing integration tests in `crates/analysis/tests/sep_logic_integration.rs` call `parse_spec_expr_with_db()` directly. The gap is that they bypass the driver path. The new driver-level test must go through `verify_functions_parallel()`.

Pattern from `crates/driver/tests/incremental_correctness.rs` — build IR functions, create `VerificationTask` structs, call `verify_functions_parallel()`, assert results:

```rust
// New test in crates/driver/tests/ghost_predicate_e2e.rs (or parallel.rs tests)
#[test]
fn test_ghost_predicate_expands_via_driver_path() {
    // Build a GhostPredicateDatabase with "owned(p)" = "pts_to(p, 0)"
    let mut db = GhostPredicateDatabase::new();
    db.insert("owned".to_string(), GhostPredicate {
        param_names: vec!["p".to_string()],
        body_raw: "pts_to(p, 0)".to_string(),
    });

    // Build IR function with requires: "owned(p)"
    let func = build_ptr_func("test_ghost", "owned(p)", "");

    // Build VerificationTask with ghost_pred_db
    let task = VerificationTask {
        name: "test_ghost".to_string(),
        ir_func: func,
        contract_db: Arc::new(ContractDatabase::new()),
        ghost_pred_db: Arc::new(db),   // THE WIRED FIELD
        cache_key: [0u8; 32],
        mir_hash: [0u8; 32],
        contract_hash: [0u8; 32],
        dependencies: vec![],
        invalidation_decision: InvalidationDecision::verify(InvalidationReason::Fresh),
        source_locations: HashMap::new(),
    };

    let mut cache = VcCache::new(temp_dir());
    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

    // The owned(p) ghost predicate expands to pts_to(p, 0).
    // With no callee providing a heap model, VCs may return unknown or sat,
    // but critically must NOT panic and must produce at least one VC result.
    assert!(!results.is_empty(), "Driver path must produce results");
    // Verify the ghost predicate was processed (not silently dropped):
    // If ghost_pred_db was severed, parse_spec would return None for "owned(p)"
    // and no precondition VC would be generated.
    // The correct behavior: at least one VC with "precondition" in description.
    let has_pre_vc = results[0].results.iter().any(|r|
        r.condition.contains("precondition") || r.condition.contains("requires"));
    assert!(has_pre_vc, "Ghost predicate in requires must produce a precondition VC");
}
```

**Note:** The exact assertion depends on the sep_logic encoding behavior. If the test is fragile, assert on VC count (must be > 0) and non-panicking execution rather than specific UNSAT/SAT outcomes. Confirm with a failing test first (RED phase).

### Anti-Patterns to Avoid

- **Cloning GhostPredicateDatabase per function:** The DB is read-only during parallel verification. Use `Arc::clone()` not `.clone()` per task — same as `contract_db`.
- **Modifying `generate_vcs()` public signature directly without backward compatibility:** Many test files call `generate_vcs(&func, None)`. Prefer the shim approach.
- **Adding ghost_pred_db to functions that don't need it:** Only `parse_spec()` and its callers (within vcgen.rs) need the db. Do not add it to unrelated VcGen helpers.
- **Testing via `parse_spec_expr_with_db` directly (bypassing driver):** The existing Phase 20 tests already do this. The Phase 24 test MUST go through `verify_functions_parallel()` to prove the wiring is complete.

---

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Ghost pred expansion | Custom expansion logic | `parse_spec_expr_with_db()` in `spec_parser.rs:46` | Already implemented with depth-3 bounded unfolding and depth-exhaustion BoolLit(false) |
| Thread-safe DB sharing | Per-task DB clone | `Arc<GhostPredicateDatabase>` via `Arc::clone()` | Same pattern as `Arc<ContractDatabase>` already in `VerificationTask` |
| Empty DB for backward compat | Custom empty struct | `spec_parser::empty_ghost_db()` or `GhostPredicateDatabase::new()` | Existing utility |

---

## Common Pitfalls

### Pitfall 1: Modifying `generate_vcs()` Public Signature

**What goes wrong:** If you change `generate_vcs(func, contract_db)` to `generate_vcs(func, contract_db, ghost_pred_db)`, all call sites in test files break. Phase 20 integration tests at `crates/analysis/tests/sep_logic_integration.rs` call `vcgen::generate_vcs()` directly.

**How to avoid:** Use the shim pattern — keep `generate_vcs()` signature intact as a delegating wrapper to a new `generate_vcs_with_db()`. Only `verify_single()` in `parallel.rs` needs to call `generate_vcs_with_db()`.

**Warning signs:** Compilation errors in `sep_logic_integration.rs` test file.

### Pitfall 2: Missing `parse_spec()` Call Sites in vcgen.rs

**What goes wrong:** `parse_spec()` is called at 14 locations in `vcgen.rs` (lines 1456, 1553, 1683, 1714, 2006, 2032, 2067, 2168, 2425, 2467, 2537, 2621, 2633, and the definition at 3091). If only some are updated to pass `ghost_pred_db`, some spec expressions will silently use the db-less path.

**How to avoid:** After changing `parse_spec()` signature, the Rust compiler will flag ALL call sites that need updating. Let the compiler guide completeness. Grep for `parse_spec(` after the change to verify all sites.

**Warning signs:** Clippy passes but ghost predicates in certain contract positions (e.g., loop invariants vs. postconditions) don't expand.

### Pitfall 3: `Arc<GhostPredicateDatabase>` Not Created Before the Task Loop

**What goes wrong:** Creating `Arc::new(db.clone())` inside the per-function loop creates N Arc allocations for the same data. Must create once before the loop.

**How to avoid:** Create `let ghost_pred_db_arc = Arc::new(self.ghost_pred_db.clone())` once before the `for (name, ir_func, ...)` loop at `callbacks.rs:~461`, then use `Arc::clone(&ghost_pred_db_arc)` per task.

### Pitfall 4: Driver Test Bypassing the Critical Path

**What goes wrong:** Writing a test that calls `parse_spec_expr_with_db()` directly. This is what Phase 20 tests already do. Phase 24 success criterion 4 explicitly requires testing through the driver path.

**How to avoid:** The integration test MUST create a `VerificationTask` with the `ghost_pred_db` field and call `verify_functions_parallel()`. This is the only way to confirm the field is wired end-to-end.

### Pitfall 5: sep_logic VC Non-UNSAT without sep_heap Declarations

**What goes wrong:** A pts_to-based ghost predicate expanding in a spec may produce VCs that are SAT (not UNSAT) if the sep_heap array is not declared in the SMT script. The test assertion needs to match actual behavior.

**How to avoid:** Check whether `generate_vcs_with_db()` (or the updated `generate_vcs()`) also calls `has_sep_logic_spec()` and `prepend_sep_heap_decls()` when ghost predicates expand to pts_to. If the sep_heap declaration gate is based on syntactic substring check of the original spec string (not the expanded form), ghost predicate expansion may miss the sep_heap declaration injection. Verify this in `vcgen.rs` and add expansion-aware gate if needed.

**Warning signs:** VCs that reference `perm` or `sep_heap` terms but the SMT script has no `(declare-const sep_heap ...)` — Z3 returns an error rather than SAT/UNSAT.

---

## Code Examples

### Exact Current State: VerificationTask Struct

```rust
// Source: crates/driver/src/parallel.rs:21-44
#[derive(Clone)]
pub struct VerificationTask {
    pub name: String,
    pub ir_func: Function,
    pub contract_db: Arc<ContractDatabase>,
    pub cache_key: [u8; 32],
    pub mir_hash: [u8; 32],
    pub contract_hash: [u8; 32],
    pub dependencies: Vec<String>,
    pub invalidation_decision: crate::invalidation::InvalidationDecision,
    pub source_locations: std::collections::HashMap<(usize, usize), (String, usize, usize)>,
    // MISSING: ghost_pred_db: Arc<GhostPredicateDatabase>
}
```

### Exact Current State: generate_vcs() Signature

```rust
// Source: crates/analysis/src/vcgen.rs:224
pub fn generate_vcs(func: &Function, contract_db: Option<&ContractDatabase>) -> FunctionVCs {
    // ... 400+ lines ...
    // Internally calls parse_spec() at 14 sites
}
```

### Exact Current State: parse_spec() — The Bug

```rust
// Source: crates/analysis/src/vcgen.rs:3091-3111
fn parse_spec(spec: &str, func: &Function) -> Option<Term> {
    let term =
        spec_parser::parse_spec_expr(spec, func)  // BUG: db-less version
            .or_else(|| parse_simple_spec(spec, func))?;
    match crate::encode_quantifier::annotate_quantifier(term) {
        Ok(annotated_term) => Some(annotated_term),
        Err(trigger_error) => {
            tracing::error!("Trigger validation failed in function {}: {:?}", func.name, trigger_error);
            None
        }
    }
}
```

### Exact Current State: parse_spec_expr_with_db() Signature

```rust
// Source: crates/analysis/src/spec_parser.rs:46-51
pub fn parse_spec_expr_with_db(
    spec: &str,
    func: &Function,
    ghost_pred_db: &GhostPredicateDatabase,
) -> Option<Term> {
    parse_spec_expr_with_depth(spec, func, ghost_pred_db, GHOST_PRED_EXPAND_DEPTH)
}
```

### Exact Current State: Task Construction (callbacks.rs:631)

```rust
// Source: crates/driver/src/callbacks.rs:631-641
tasks.push(crate::parallel::VerificationTask {
    name: name.clone(),
    ir_func,
    contract_db: std::sync::Arc::new(contract_db.clone()),
    cache_key,
    mir_hash: *mir_hash,
    contract_hash: *contract_hash,
    dependencies,
    invalidation_decision,
    source_locations,
    // MISSING: ghost_pred_db
});
```

### Exact Current State: verify_single() Call to generate_vcs

```rust
// Source: crates/driver/src/parallel.rs:261-262
let mut func_vcs =
    rust_fv_analysis::vcgen::generate_vcs(&task.ir_func, Some(&task.contract_db));
    // MISSING: ghost_pred_db argument
```

### Existing Integration Test Pattern (for reference)

```rust
// Source: crates/analysis/tests/sep_logic_integration.rs:464-513
// This pattern is what Phase 20 tests do — bypasses driver path
let mut db = GhostPredicateDatabase::new();
db.insert("owned".to_string(), GhostPredicate {
    param_names: vec!["p".to_string()],
    body_raw: "pts_to(p, 0)".to_string(),
});
let term_depth3 = parse_spec_expr_with_db("owned(p)", &func, &db);
assert!(term_depth3.is_some());
assert!(matches!(&term_depth3.unwrap(), Term::And(_)));
```

### GhostPredicateDatabase Public API

```rust
// Source: crates/analysis/src/ghost_predicate_db.rs
impl GhostPredicateDatabase {
    pub fn new() -> Self { Self::default() }
    pub fn insert(&mut self, name: String, pred: GhostPredicate) { ... }
    pub fn get(&self, name: &str) -> Option<&GhostPredicate> { ... }
    pub fn contains(&self, name: &str) -> bool { ... }
    pub fn len(&self) -> usize { ... }
    pub fn is_empty(&self) -> bool { ... }
}
```

---

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| `parse_spec_expr()` (db-less) | `parse_spec_expr_with_db()` (with ghost pred expansion) | Phase 20-03 | Enables recursive heap predicate expansion; old version still present for backward compat |
| No ghost predicate tracking | `GhostPredicateDatabase` populated at `after_analysis()` | Phase 20-02 | DB exists and is correct — just not forwarded to pipeline |
| No ghost predicate in `VerificationTask` | Pending Phase 24 fix | Phase 24 | Will complete the wiring |

**Deprecated/outdated:**
- Calling `parse_spec_expr()` (db-less) in `parse_spec()` inside vcgen.rs: this was the pre-Phase-20 behavior; Phase 20 added the `_with_db` variant but failed to update the internal caller.

---

## Open Questions

1. **Does `has_sep_logic_spec()` check gate work for ghost predicates that expand to pts_to?**
   - What we know: `has_sep_logic_spec()` is a syntactic substring check for `"pts_to"` in the raw spec string. A raw spec of `"owned(p)"` does NOT contain `"pts_to"`.
   - What's unclear: If the gate is based on raw spec and not the expanded result, then when `owned(p)` expands to `pts_to(p, 0)`, the `sep_heap` declarations may not be injected, causing Z3 errors.
   - Recommendation: Before finalizing the plan, check `has_sep_logic_spec()` implementation and determine if it needs to be ghost-predicate-aware (e.g., check if any referenced ghost predicates in the spec transitively expand to pts_to). This may be an additional fix needed in Phase 24.

2. **Arc vs. direct reference for ghost_pred_db in generate_vcs_with_db?**
   - What we know: `generate_vcs()` takes `contract_db: Option<&ContractDatabase>` as a reference, not Arc. The Arc is held by `VerificationTask`.
   - What's unclear: Should `generate_vcs_with_db()` take `ghost_pred_db: &GhostPredicateDatabase` or `ghost_pred_db: Arc<GhostPredicateDatabase>`?
   - Recommendation: Use `&GhostPredicateDatabase` (reference) in the function signature, consistent with the `contract_db` pattern. The Arc stays in `VerificationTask`; `verify_single()` passes `&task.ghost_pred_db`.

3. **Test scope for driver-level integration test**
   - What we know: `verify_functions_parallel()` requires a real Z3 solver. `incremental_correctness.rs` operates at the IR/cache level without Z3.
   - What's unclear: Should the driver-level integration test require Z3 (like `sep_logic_integration.rs`) or be structured to run without Z3?
   - Recommendation: Follow the `sep_logic_integration.rs` pattern with `solver_or_skip()` — require Z3, but gracefully skip if not installed. The test must exercise the real solver path to prove the wiring.

---

## Sources

### Primary (HIGH confidence)

All findings from direct source inspection:

- `crates/driver/src/parallel.rs:20-44` — `VerificationTask` struct — no `ghost_pred_db` field confirmed
- `crates/driver/src/callbacks.rs:401` — `self.ghost_pred_db = extract_ghost_predicates(tcx)` — DB populated here
- `crates/driver/src/callbacks.rs:631-641` — Task construction — `ghost_pred_db` absent confirmed
- `crates/driver/src/parallel.rs:261-262` — `verify_single()` calls `generate_vcs()` without db
- `crates/analysis/src/vcgen.rs:224` — `generate_vcs()` signature — no ghost_pred_db param
- `crates/analysis/src/vcgen.rs:3091-3111` — `parse_spec()` calls db-less `parse_spec_expr`
- `crates/analysis/src/spec_parser.rs:46-51` — `parse_spec_expr_with_db()` signature and implementation
- `crates/analysis/src/ghost_predicate_db.rs` — Full `GhostPredicateDatabase` type
- `crates/analysis/tests/sep_logic_integration.rs:460-513` — Phase 20 test patterns for ghost pred expansion
- `crates/driver/tests/incremental_correctness.rs` — Driver-level test pattern using IR + `verify_functions_parallel`
- `.planning/v0.4-MILESTONE-AUDIT.md` — Audit finding confirming critical wiring gap

### Secondary (MEDIUM confidence)

- `.planning/STATE.md:77-86` — Accumulated decisions from Phase 20 that confirm the design intent

---

## Metadata

**Confidence breakdown:**
- Current broken state: HIGH — directly confirmed from source code inspection
- Fix approach: HIGH — derived from existing `Arc<ContractDatabase>` pattern in the same struct
- Integration test pattern: HIGH — `sep_logic_integration.rs` and `incremental_correctness.rs` provide exact templates
- Open question 1 (sep_heap gate): LOW — requires additional source inspection of `has_sep_logic_spec()` during planning

**Research date:** 2026-02-20
**Valid until:** 2026-03-20 (30 days — stable codebase, no external dependencies)
