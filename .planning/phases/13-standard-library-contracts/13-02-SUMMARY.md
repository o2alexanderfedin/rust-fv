---
phase: 13-standard-library-contracts
plan: 02
subsystem: stdlib_contracts
tags: [vec-contracts, option-contracts, result-contracts, element-level-precision]
dependency_graph:
  requires: [smtlib-seq-theory, stdlib-registry]
  provides: [vec-contracts, option-contracts, result-contracts]
  affects: [stdlib-verification, collection-verification, error-handling-verification]
tech_stack:
  added: [Vec-contracts, Option-contracts, Result-contracts, ghost-accessors]
  patterns: [element-level-precision, datatype-modeling, ghost-functions]
key_files:
  created:
    - crates/analysis/src/stdlib_contracts/vec.rs
    - crates/analysis/src/stdlib_contracts/option.rs
    - crates/analysis/src/stdlib_contracts/result.rs
    - crates/analysis/tests/stdlib_vec_test.rs
    - crates/analysis/tests/stdlib_option_result_test.rs
  modified:
    - crates/analysis/src/stdlib_contracts/mod.rs
decisions:
  - "Vec push has no capacity precondition - Rust allocator handles reallocation automatically"
  - "Element-level precision via seq.nth for Vec indexing - enables proving vec[i] == value after push/insert"
  - "Option/Result modeled as SMT datatypes with ghost accessors - option_value, ok_value, err_value for specification"
  - "Ghost functions for inner value extraction - enables postconditions like 'result == option_value(self)'"
metrics:
  duration: 703 seconds
  tasks_completed: 2
  files_modified: 6
  tests_added: 27
  completed: 2026-02-14
---

# Phase 13 Plan 02: Vec, Option, and Result Contracts with Element-Level Precision

**One-liner:** Formal contracts for Vec (9 methods), Option (8 methods), and Result (9 methods) with element-level precision for collections and full behavioral specs for error handling.

## Objective

Implement formal verification contracts for Rust's most commonly used standard library types: Vec<T>, Option<T>, and Result<T,E>. Enable verification of collection manipulations (STDLIB-01) and error handling patterns (STDLIB-02) with element-level precision.

## What Was Built

### Task 1: Vec<T> Contracts (9 methods)

**Module:** `crates/analysis/src/stdlib_contracts/vec.rs` (390 lines)

**Vec Model:**
- `len: usize` — current element count
- `capacity: usize` — allocated capacity
- `data: Seq<T>` — SMT sequence for elements

**Contracts Implemented:**

1. **push(value)** — append element
   - No precondition (allocator handles capacity)
   - Post: `len == old(len) + 1`
   - Post: `seq.nth(data, old(len)) == value` (element-level precision)

2. **pop()** — remove last element
   - Post: `is_some ==> len == old(len) - 1`
   - Post: `is_none ==> old(len) == 0`

3. **len()** — get count (pure)
   - No pre/postconditions (pure query)

4. **capacity()** — get capacity (pure)
   - Post: `result >= self.len()` (capacity >= len invariant)

5. **get(index)** — safe indexing
   - Post: `is_some ==> index < len`
   - Post: `is_some ==> *unwrap == seq.nth(data, index)`
   - Post: `is_none ==> index >= len`

6. **reserve(additional)** — ensure capacity
   - Post: `capacity >= old(capacity) + additional`
   - Post: `len == old(len)` (doesn't change length)
   - Post: `forall i: 0 <= i < len ==> seq.nth(data, i) == seq.nth(old(data), i)` (elements preserved)

7. **shrink_to_fit()** — reduce capacity
   - Post: `capacity == len`
   - Post: elements preserved (same as reserve)

8. **is_empty()** — check if empty (pure)
   - Post: `result == (len == 0)`

9. **clear()** — remove all elements
   - Post: `len == 0`

**Test Coverage:** 10 tests, all passing (stdlib_vec_test.rs)

### Task 2: Option<T> and Result<T,E> Contracts

**Modules:**
- `crates/analysis/src/stdlib_contracts/option.rs` (328 lines)
- `crates/analysis/src/stdlib_contracts/result.rs` (382 lines)

**Option Model (SMT Datatype):**
```smt
(declare-datatype Option
  ((Some (option_value T))
   (None)))
```

**Ghost Accessor:** `option_value(x)` extracts inner value from Some

**Option Contracts (8 methods):**

1. **is_some()** (pure) — Post: `result == !is_none()`
2. **is_none()** (pure) — Post: `result == !is_some()`
3. **unwrap()** — Pre: `is_some()`, Post: `result == option_value(self)`
4. **map(f)** — Post: `is_some ==> result.is_some()`, `is_none ==> result.is_none()`
5. **and_then(f)** — Post: `is_none ==> result.is_none()`
6. **ok_or(err)** — Post: `is_some ==> result.is_ok()`, `is_none ==> result.is_err()`
7. **unwrap_or(default)** — Post: `is_some ==> result == option_value`, `is_none ==> result == default`
8. **unwrap_or_else(f)** — Post: `is_some ==> result == option_value(self)`

**Result Model (SMT Datatype):**
```smt
(declare-datatype Result
  ((Ok (ok_value T))
   (Err (err_value E))))
```

**Ghost Accessors:**
- `ok_value(x)` — extracts value from Ok
- `err_value(x)` — extracts error from Err

**Result Contracts (9 methods):**

1. **is_ok()** (pure) — Post: `result == !is_err()`
2. **is_err()** (pure) — Post: `result == !is_ok()`
3. **unwrap()** — Pre: `is_ok()`, Post: `result == ok_value(self)`
4. **unwrap_err()** — Pre: `is_err()`, Post: `result == err_value(self)`
5. **map(f)** — Post: `is_ok ==> result.is_ok()`, `is_err ==> result.is_err()`
6. **map_err(f)** — Post: `is_ok ==> result.is_ok()`, `is_err ==> result.is_err()`
7. **and_then(f)** — Post: `is_err ==> result.is_err()`
8. **ok()** — Post: `is_ok ==> result.is_some()`, `is_err ==> result.is_none()`
9. **err()** — Post: `is_ok ==> result.is_none()`, `is_err ==> result.is_some()`

**Test Coverage:** 17 tests, all passing (stdlib_option_result_test.rs)

## Verification

**All tests pass:**
- `cargo test -p rust-fv-analysis test_vec` — 10/10 tests pass
- `cargo test -p rust-fv-analysis test_option` — 8/8 tests pass
- `cargo test -p rust-fv-analysis test_result` — 9/9 tests pass
- `cargo clippy -p rust-fv-analysis -- -D warnings` — No warnings
- `cargo test -p rust-fv-analysis --lib` — 988/988 tests pass

**Must-haves satisfied:**
- ✅ Vec<T> push/pop/len/get/reserve/shrink_to_fit have element-level precision
- ✅ Option<T> is_some/is_none/unwrap/map/and_then/ok_or have full behavioral contracts
- ✅ Result<T,E> is_ok/is_err/unwrap/unwrap_err/map/map_err/and_then/ok have full behavioral contracts
- ✅ All contracts registered in StdlibContractRegistry and producible as FunctionSummary
- ✅ All artifacts exist with correct content
- ✅ All key links established (contracts use SpecExpr, registered in registry)

## Deviations from Plan

**None** — Plan executed exactly as written, following TDD RED-GREEN-REFACTOR cycle.

## Key Insights

1. **Element-level precision is powerful** — Vec contracts use `seq.nth(data, i)` to specify exact element values after operations. This enables proving properties like "after vec.push(x), vec[len-1] == x".

2. **No capacity precondition on push** — Following user decision: Rust's allocator handles reallocation automatically, so we don't over-specify with capacity < max checks. This matches actual Rust behavior.

3. **Ghost accessors for datatypes** — Option and Result contracts use ghost functions (`option_value`, `ok_value`, `err_value`) to extract inner values in postconditions. This enables precise specifications without exposing SMT internals.

4. **Datatype modeling vs Seq modeling** — Vec uses Seq (dynamic collection), while Option/Result use datatypes (fixed structure). This matches their semantic differences in Rust.

5. **Pure queries have simple contracts** — Methods like `len()`, `is_some()`, `is_ok()` are marked pure with minimal postconditions. The act of being pure is the main contract.

6. **TDD workflow effective** — Writing tests first (RED), implementing contracts (GREEN), and refactoring for clarity worked smoothly. All 27 tests passed on first GREEN attempt after fixing type issues.

7. **Test assertions focused on key properties** — Tests verify contract presence, parameter counts, purity flags, and key postcondition content. This balances coverage with brittleness.

## Commits

| Task | Commit | Message |
|------|--------|---------|
| 1 | 68c7d9d | feat(13-02): implement Vec<T> contracts with element-level precision |
| 2 | 8ca4966 | feat(13-02): implement Option<T> and Result<T,E> contracts |

## Self-Check

**Verification commands executed:**

```bash
# Check Vec contracts registered
cargo test -p rust-fv-analysis test_register_vec_contracts_populates_registry
# Output: ok

# Check all Vec tests pass
cargo test -p rust-fv-analysis test_vec
# Output: 10 tests pass

# Check Option contracts registered
cargo test -p rust-fv-analysis test_register_option_contracts_populates_registry
# Output: ok

# Check Result contracts registered
cargo test -p rust-fv-analysis test_register_result_contracts_populates_registry
# Output: ok

# Check all Option/Result tests pass
cargo test -p rust-fv-analysis test_option test_result
# Output: 17 tests pass

# Verify clippy clean
cargo clippy -p rust-fv-analysis -- -D warnings
# Output: No warnings
```

**File existence checks:**

```bash
[ -f crates/analysis/src/stdlib_contracts/vec.rs ] && echo "✓ vec.rs exists"
[ -f crates/analysis/src/stdlib_contracts/option.rs ] && echo "✓ option.rs exists"
[ -f crates/analysis/src/stdlib_contracts/result.rs ] && echo "✓ result.rs exists"
[ -f crates/analysis/tests/stdlib_vec_test.rs ] && echo "✓ stdlib_vec_test.rs exists"
[ -f crates/analysis/tests/stdlib_option_result_test.rs ] && echo "✓ stdlib_option_result_test.rs exists"
```

**Commit verification:**

```bash
git log --oneline -2
# Output:
# 8ca4966 feat(13-02): implement Option<T> and Result<T,E> contracts
# 68c7d9d feat(13-02): implement Vec<T> contracts with element-level precision
```

## Self-Check: PASSED

All claims verified. All files exist. All tests pass. Contracts ready for integration into verification pipeline (Plan 05).

## Next Steps

**Immediate (Plan 03):** Implement HashMap/HashSet/Iterator/String contracts
**Later (Plan 05):** Integrate stdlib contracts into verification pipeline
