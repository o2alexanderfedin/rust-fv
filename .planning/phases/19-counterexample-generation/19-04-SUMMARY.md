---
phase: 19-counterexample-generation
plan: "04"
subsystem: driver/json-output
tags: [json, counterexample, typescript, schema, backward-compat]
dependency_graph:
  requires: [19-01, 19-02]
  provides: [structured-json-counterexample-schema, typescript-interfaces]
  affects: [vscode-extension, CI-tooling, IDE-integration]
tech_stack:
  added: []
  patterns: [additive-schema, backward-compat, struct-propagation]
key_files:
  created: []
  modified:
    - crates/driver/src/json_output.rs
    - crates/driver/src/callbacks.rs
    - crates/driver/src/diagnostics.rs
    - crates/driver/src/parallel.rs
    - crates/driver/src/rustc_json.rs
    - crates/driver/src/main.rs
    - vscode-extension/src/verifier.ts
decisions:
  - "Debug+Clone derives added to JsonCounterexample/JsonCexVariable/JsonCexValue/JsonLocation for Clone across VerificationResult and VerificationFailure propagation chains"
  - "counterexample_v2 populated in parallel.rs verify_single (where IR func data is available) via build_counterexample_v2() helper, not in callbacks.rs (no IR data there)"
  - "JsonFailure keeps both counterexample (flat, backward compat) and counterexample_v2 (rich schema) — additive approach"
  - "cex_render module added to main.rs mod declarations (was only in lib.rs, needed for binary targets)"
metrics:
  duration_seconds: 155
  completed_date: "2026-02-19"
  tasks_completed: 2
  tasks_total: 2
  files_modified: 7
---

# Phase 19 Plan 04: Structured JSON Counterexample Schema and TypeScript Interfaces Summary

Additive JSON schema extension adding `counterexample_v2` with typed variables (name, type, display, raw, initial, at_failure) and structured metadata (failing_location, vc_kind, violated_spec) alongside the existing flat `counterexample` field for backward compatibility. TypeScript interfaces in `verifier.ts` mirror the Rust schema exactly.

## What Was Built

### New JSON Schema (Rust)

`json_output.rs` has four new public types with `#[derive(Serialize, Deserialize, Debug, Clone)]`:

- `JsonCounterexample` — top-level structured counterexample with `variables`, `failing_location`, `vc_kind`, `violated_spec`
- `JsonCexVariable` — single variable with `name`, `type`, optional `display`/`raw` (single-value) or `initial`/`at_failure` (SSA multi-version)
- `JsonCexValue` — typed value pair: `display` (human string) and `raw` (JSON tree)
- `JsonLocation` — source position: `file`, `line`, `column`

`JsonFailure` now has:
```rust
pub counterexample: Option<Vec<JsonAssignment>>,  // kept — backward compat
pub counterexample_v2: Option<JsonCounterexample>, // new — rich schema
```

### Counterexample Population Pipeline

`parallel.rs` `verify_single` — on `SolverResult::Sat(model)`:
1. Raw model pairs go into `counterexample` (existing)
2. `build_counterexample_v2(cx_pairs, &vc.location, &task.ir_func)` calls `cex_render::render_counterexample` with IR locals/params for type dispatch
3. Maps `Vec<CexVariable>` → `Vec<JsonCexVariable>` → stored in `VerificationResult.counterexample_v2`

Propagation chain: `parallel.rs` → `VerificationResult.counterexample_v2` → `callbacks.rs` → `VerificationFailure.counterexample_v2` → `JsonFailure.counterexample_v2`

### TypeScript Interfaces (verifier.ts)

Added after `JsonAssignment`:
```typescript
export interface JsonCounterexample {
  variables: JsonCexVariable[];
  failing_location: JsonLocation;
  vc_kind: string;
  violated_spec?: string;
}

export interface JsonCexVariable {
  name: string;
  type: string;
  display?: string;
  raw?: unknown;
  initial?: JsonCexValue;
  at_failure?: JsonCexValue;
}

export interface JsonCexValue {
  display: string;
  raw: unknown;
}

export interface JsonLocation {
  file: string;
  line: number;
  column: number;
}
```

`JsonFailure` updated to include `counterexample_v2?: JsonCounterexample`.

### Example JSON Output (v2 schema)

```json
{
  "counterexample": [{"variable": "x", "value": "-1"}],
  "counterexample_v2": {
    "variables": [{
      "name": "x",
      "type": "i32",
      "display": "i32: -1",
      "raw": -1
    }],
    "failing_location": {"file": "src/lib.rs", "line": 5, "column": 1},
    "vc_kind": "precondition",
    "violated_spec": "x > 0"
  }
}
```

## Test Results

- `cargo test --package rust-fv-driver -- json_output`: 18 tests pass
- `cargo test --workspace`: All tests pass (417+ driver tests, full workspace)
- `cargo clippy --package rust-fv-driver -- -D warnings`: No warnings
- `npx tsc --noEmit` (vscode-extension): Compiles without errors

## Deviations from Plan

### Auto-fixed Issues

**1. [Rule 2 - Missing Functionality] counterexample_v2 field missing from test constructors**
- **Found during:** Task 1 — cargo test showed compilation errors
- **Issue:** `JsonFailure` struct had `counterexample_v2` field added (in prior 19-02 commit) but test literal constructors in `json_output.rs`, `rustc_json.rs` were missing the field
- **Fix:** Added `counterexample_v2: None` to all test `JsonFailure` struct literals
- **Files modified:** `json_output.rs`, `rustc_json.rs`

**2. [Rule 2 - Missing Functionality] counterexample_v2 not in VerificationResult/VerificationFailure**
- **Found during:** Task 1 — needed to propagate v2 through the pipeline
- **Issue:** `VerificationResult` and `VerificationFailure` were missing `counterexample_v2` field; `parallel.rs` didn't build it; `callbacks.rs` didn't propagate it
- **Fix:** Added field to both structs; added `build_counterexample_v2()` helper in `parallel.rs`; propagated through callbacks.rs
- **Files modified:** `callbacks.rs`, `diagnostics.rs`, `parallel.rs`

**3. [Rule 3 - Blocking] cex_render not in main.rs mod declarations**
- **Found during:** Task 1 — build error `unresolved import`
- **Issue:** `cex_render` module was declared in `lib.rs` only; `parallel.rs` (used by binary) couldn't find it
- **Fix:** Added `mod cex_render;` to `main.rs`
- **Files modified:** `main.rs`

**4. [Rule 2 - Missing Functionality] JsonCounterexample missing Debug+Clone derives**
- **Found during:** Task 1 — clone error on `Option<JsonCounterexample>`
- **Issue:** Struct needed `Clone` for propagation through `VerificationResult`
- **Fix:** Added `Debug, Clone` to all four new json_output structs
- **Files modified:** `json_output.rs`

## Self-Check: PASSED

Files exist:
- `crates/driver/src/json_output.rs` — FOUND
- `vscode-extension/src/verifier.ts` — FOUND
- `crates/driver/src/parallel.rs` — FOUND (build_counterexample_v2 present)

Commits exist:
- `e75f4ae` — FOUND (Task 1: json_output + callbacks + parallel + diagnostics fixes)
- `427bd46` — FOUND (Task 2: verifier.ts TypeScript interfaces)
