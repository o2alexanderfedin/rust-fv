# Phase 19: Counterexample Generation - Research

**Researched:** 2026-02-19
**Domain:** SMT model presentation, ariadne diagnostics, Rust name recovery, JSON schema extension
**Confidence:** HIGH

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

#### Variable Selection
- Show **all variables live at the point of failure** — not just spec-referenced ones; more context is better
- For variables reassigned during execution (SSA versions): show **both** the initial value and the value at failure, with labels distinguishing them (e.g., `(initial)` and `(at failure)`)
- **Ghost variables** (`#[ghost]`, spec-only vars) are **hidden** — they are spec-internal, showing them breaks abstraction for the developer
- **Loop induction variables** (e.g., `i`) are **always shown**, regardless of VC kind — the loop iteration where something went wrong is crucial context

#### Complex Type Display
- **Structs**: Fully recursive expansion — show all nested fields with no depth truncation
- **Vecs/slices/arrays**: Show all elements up to 10; beyond 10, truncate with `... (N more)` message
- **Enums**: Use **Rust Debug format** — mirror what `{:?}` would print (`Some(42)`, `Ok(Point { x: 3 })`) — familiar to all Rust developers
- **Raw pointers** (`*const T`, `*mut T`): Show **symbolic address + pointee value** — `ptr@0x1 -> i32: 42` — both the abstract heap address and what it points to in the SMT model

#### Ariadne Annotation Style
- Place counterexample labels **at each variable's use site** in the spec — secondary spans connecting value to its role in the failing spec
- **No cap** on inline labels — show all variables, even if there are many
- Label format: **`x: i32 = 5`** — Rust declaration syntax, reads like a let binding
- For variables with two values (initial + at-failure): use **two separate span labels** — one at the parameter declaration site labeled `(initial)`, one at the failing line labeled `(at failure)`

#### JSON Schema Design
- Top-level structure: **structured with metadata**:
  ```json
  {
    "counterexample": {
      "variables": [...],
      "failing_location": { "file": "...", "line": N, "column": N },
      "vc_kind": "postcondition",
      "violated_spec": "result >= 0"
    }
  }
  ```
- Complex value representation: **both display string and raw typed tree**:
  ```json
  {
    "name": "p",
    "type": "Point",
    "display": "Point { x: 3, y: -1 }",
    "raw": { "kind": "struct", "fields": [{ "name": "x", "type": "i32", "value": 3 }, { "name": "y", "type": "i32", "value": -1 }] }
  }
  ```
- **Include `violated_spec`**: the text of the `#[ensures]`/`#[assert]` clause that failed
- Variables with two values: **single entry with `initial` and `at_failure` sub-objects**:
  ```json
  {
    "name": "x",
    "type": "i32",
    "initial": { "display": "5", "raw": 5 },
    "at_failure": { "display": "7", "raw": 7 }
  }
  ```

### Claude's Discretion
- Exact ariadne color scheme and label styling
- Ordering of variables within the counterexample (spec-referenced first vs alphabetical vs declaration order)
- How to handle `!Send`/non-`Debug` types that the SMT model has a value for but Rust can't represent as a string easily
- Whether to show a summary header line (e.g., `counterexample found:`) before the ariadne output

### Deferred Ideas (OUT OF SCOPE)
None — discussion stayed within phase scope.
</user_constraints>

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| CEX-01 | User sees Rust variable names (not SSA names like `_param_x_1`) in counterexample output when verification fails | `body.var_debug_info` in `rustc_middle::mir::Body` maps MIR locals to source names; `mir_converter.rs` must be extended to collect this map and thread it through the IR |
| CEX-02 | User sees typed Rust values (e.g. `i32: 5`, `bool: false`) not raw hex bitvectors in counterexample output | `Local.ty` in the IR already carries `Ty`; existing `parse_bitvec_value` in `diagnostics.rs` handles hex→decimal; needs extension for structs, enums, Vec, raw pointers |
| CEX-03 | User sees counterexample values annotated at the failing source line via ariadne inline labels in terminal output | `ariadne 0.4.1` is already a dependency; `report_with_ariadne` in `diagnostics.rs` currently falls back to text; needs actual `Source::from(file_text)` + multi-label `Label::new` calls; `VcLocation.source_file/source_line` exist but are currently `None` from `mir_converter` |
| CEX-04 | Machine consumers receive structured `counterexample` field in `--output-format=json` output on verification failure | `json_output.rs` has `JsonFailure.counterexample: Option<Vec<JsonAssignment>>`; must be replaced/extended with the new structured schema from decisions; VSCode extension `verifier.ts` must be updated to match the new schema |
</phase_requirements>

## Summary

Phase 19 is a presentation-layer enhancement. The SMT solver already emits models as raw `(name, value_string)` pairs stored in `solver::Model`. The VCGen already tracks `VcLocation` with `contract_text` and `vc_kind`. What is missing are three things: (1) a mapping from SSA local indices (`_1`, `_2`) to Rust source names, (2) typed value rendering that handles the full Rust type tree, and (3) fully wired-up ariadne labels and a richer JSON schema to surface these rendered values.

The core work is in `crates/driver`: extend `mir_converter.rs` to harvest `body.var_debug_info` (rustc's source-name map for locals), extend `diagnostics.rs` to use the name map and typed rendering when building `VerificationFailure`, make `report_with_ariadne` actually read source files and place per-variable `Label` spans, and extend `json_output.rs` with the new `counterexample` block schema. All of these changes are confined to `driver` and the presentation path; `analysis` (VCGen, IR) is unchanged.

The ariadne path currently falls back to text because `source_file`/`source_line` in `VcLocation` are always `None` — that plumbing from `callbacks.rs` also needs to be completed as part of this phase so ariadne can read the actual source bytes.

**Primary recommendation:** Implement in this order: (1) name recovery via `var_debug_info` in `mir_converter`, (2) typed value rendering as a new `cex_render.rs` module in `driver`, (3) ariadne multi-label wiring in `diagnostics.rs`, (4) JSON schema extension in `json_output.rs`, (5) VSCode `verifier.ts` TypeScript types update.

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| ariadne | 0.4.1 | Source-annotated terminal diagnostics | Already in Cargo.toml; provides `Report`, `Label`, `Source` API |
| serde / serde_json | 1.0 | JSON serialization | Already in workspace dependencies |
| colored | 3.1 | ANSI color for text fallback | Already used in `diagnostics.rs` |
| rustc_middle::mir | nightly rustc | `var_debug_info`, `local_decls`, source spans | The only authoritative source of local→name mapping |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| rustc_span | nightly rustc | `Span` → `(file, line, col)` conversion | Extracting column info from MIR `SourceInfo` when ariadne needs byte offsets |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| ariadne inline labels | rustc's own `DiagnosticBuilder` | rustc diagnostics require being inside the compiler; we are in an after-analysis callback where we can use ariadne's standalone renderer |
| `var_debug_info` map | Heuristic regex on SSA names | `var_debug_info` is the correct rustc API; heuristics fail for shadowed variables and cannot recover struct field access chains |

**Installation:** No new dependencies needed — all required crates are already in `Cargo.toml` or the nightly rustc sysroot.

## Architecture Patterns

### Recommended Project Structure

New files to add inside `crates/driver/src/`:
```
crates/driver/src/
├── mir_converter.rs     # EXTEND: harvest var_debug_info → name map
├── cex_render.rs        # NEW: typed value rendering (CEX-01, CEX-02 logic)
├── diagnostics.rs       # EXTEND: ariadne multi-label wiring (CEX-03)
├── json_output.rs       # EXTEND: new counterexample schema (CEX-04)
└── callbacks.rs         # EXTEND: plumb name map + source location
```

### Pattern 1: SSA Name Recovery via `var_debug_info`

**What:** `rustc_middle::mir::Body::var_debug_info` is a `Vec<VarDebugInfo>` where each entry has `.name` (the source identifier) and `.value` (a `VarDebugInfoContents` which contains the `Place` or `Const` it maps to). For simple locals, `VarDebugInfoContents::Place(p)` gives you the local index.

**When to use:** In `mir_converter::convert_mir`, after building params and locals, iterate `body.var_debug_info` to build a `HashMap<usize, String>` from local index → source name. Store this map in the IR `Function` (add a `pub source_names: HashMap<String, String>` field mapping SSA name `"_1"` → `"x"`).

**Example:**
```rust
// In mir_converter.rs
use rustc_middle::mir::{VarDebugInfoContents};

let mut source_names: std::collections::HashMap<String, String> = HashMap::new();
for debug_info in &body.var_debug_info {
    if let VarDebugInfoContents::Place(place) = &debug_info.value {
        if place.projection.is_empty() {
            let ssa_name = format!("_{}", place.local.as_usize());
            source_names.insert(ssa_name, debug_info.name.to_string());
        }
    }
}
```

Confidence: HIGH — `var_debug_info` is the standard rustc API for this purpose, used by Miri, KANI, and Prusti.

### Pattern 2: Typed Value Rendering (`cex_render.rs`)

**What:** A new module that takes an SMT model assignment string + a `Ty` from the IR and produces both `display: String` and `raw: serde_json::Value`.

**Key rendering rules:**
- `Ty::Int(_)` or `Ty::Uint(_)`: Parse bitvector (`#xHEX`, `#bBIN`) → decimal signed/unsigned
- `Ty::Bool`: `"true"` / `"false"` directly
- `Ty::Struct { name, fields }`: recursively render each field; join as `StructName { field: val, ... }`
- `Ty::Enum { name, .. }`: Map SMT datatype constructor → Rust Debug format (`Some(42)`, `Ok(...)`)
- `Ty::RawPtr(inner)`: Show as `ptr@0xADDR -> TYPE: VALUE` using symbolic address from model
- `Ty::Array` / `Ty::Slice`: Collect up to 10 elements; emit `... (N more)` if beyond

**When to use:** Called from `diagnostics.rs` when building `VerificationFailure.counterexample` entries.

### Pattern 3: Ariadne Multi-Label Source Annotation

**What:** `ariadne 0.4` supports multiple `Label` per `Report`. Each label points to a byte-range `(file, start..end)` in the source and carries a message string.

**Constraint:** ariadne requires the source text as a `&str`. We must read the file at `VcLocation.source_file`. The current `report_with_ariadne` already has the skeleton but calls `report_text_only` as fallback because source text was not read.

**Key ariadne API (verified from codebase at `diagnostics.rs:8` and `Cargo.lock` ariadne 0.4.1):**
```rust
use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};

let source_text = std::fs::read_to_string(source_file)?;
let mut colors = ColorGenerator::new();
let mut report = Report::build(ReportKind::Error, source_file, byte_offset)
    .with_message("verification failed: postcondition not satisfied");

for (var_name, typed_value) in &counterexample_vars {
    if let Some(use_span) = find_var_span_in_spec(&source_text, source_line, var_name) {
        report = report.with_label(
            Label::new((source_file, use_span.clone()))
                .with_message(format!("{}: {} = {}", var_name, var_type, typed_value.display))
                .with_color(colors.next())
        );
    }
}
report.finish().eprint((source_file, Source::from(&source_text))).unwrap();
```

**Finding span positions:** The spec text (e.g., `result >= 0`) is in `VcLocation.contract_text`. A substring search within the source line suffices for finding variable use sites. For two-value variables, also search the parameter declaration line (line 1 of the function signature).

**When to use:** Only when both `source_file` exists as a readable path AND `source_line` is populated. Fall back to text-only for cases where source is unavailable (e.g., stdlib stubs).

### Pattern 4: Source Location Plumbing

**What:** `VcLocation.source_file` and `source_line` are currently `None` from `mir_converter`. The MIR `Statement.source_info.span` and `Terminator.source_info.span` carry `rustc_span::Span`. These must be resolved via `tcx.sess.source_map()` to get `(file_name, line)`.

**Where to add:** In `callbacks.rs` where `convert_mir` is called, pass `tcx` into a helper that post-processes the `VcLocation` list and fills in source info from the MIR statements.

### Pattern 5: JSON Schema Extension

**What:** Replace `json_output::JsonAssignment { variable: String, value: String }` with the richer schema while maintaining backward compatibility for the VSCode extension.

**Migration strategy:** Add the new `counterexample` top-level object inside `JsonFailure` as an additional optional field `counterexample_v2: Option<JsonCounterexample>`. Keep the old `counterexample: Option<Vec<JsonAssignment>>` for backward compatibility. The VSCode extension `verifier.ts` already only reads `counterexample` as `JsonAssignment[]`; update the TypeScript types to use the richer schema.

**New Rust types to add in `json_output.rs`:**
```rust
#[derive(Serialize, Deserialize)]
pub struct JsonCounterexample {
    pub variables: Vec<JsonCexVariable>,
    pub failing_location: JsonLocation,
    pub vc_kind: String,
    pub violated_spec: Option<String>,
}

#[derive(Serialize, Deserialize)]
pub struct JsonCexVariable {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    // For single-value variables:
    pub display: Option<String>,
    pub raw: Option<serde_json::Value>,
    // For two-value (SSA) variables:
    pub initial: Option<JsonCexValue>,
    pub at_failure: Option<JsonCexValue>,
}

#[derive(Serialize, Deserialize)]
pub struct JsonCexValue {
    pub display: String,
    pub raw: serde_json::Value,
}

#[derive(Serialize, Deserialize)]
pub struct JsonLocation {
    pub file: String,
    pub line: usize,
    pub column: usize,
}
```

### Anti-Patterns to Avoid
- **Hardcoding `_1` = first param, `_2` = second param:** MIR local numbering is not stable. Always use `var_debug_info` for name recovery.
- **Parsing Z3 model text with regex:** The model string is `"k = v, k2 = v2"` (from `callbacks.rs:48`). Parse it by splitting on `", "` — but this breaks for values containing commas (e.g., struct values). Switch to structured model representation instead.
- **Reading source files from `diagnostics.rs`:** File I/O in the diagnostic module couples presentation to file system. Pass source text as a parameter from the call site in `callbacks.rs` where the file path is known.
- **Mutable static for ghost variable filtering:** Ghost detection must use `Local.is_ghost` from the IR, not string-matching on names.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Local → source name mapping | String regex on `_1`, `_2` | `body.var_debug_info` | Handles shadowing, closures, inline expansion |
| Byte offset from line/col | Manual line counting | `tcx.sess.source_map().lookup_char_pos(span.lo())` | Handles multi-byte UTF-8, CRLF |
| Ariadne source read | Custom `std::fs::read_to_string` in diagnostics | Pass source text from caller | Keeps diagnostics testable without file system |
| SMT bitvector parsing | Custom hex parser | Extend existing `parse_bitvec_value` | Already handles `#x` and `#b` prefix formats |

**Key insight:** The rustc compiler already computed and stored all source location information; `var_debug_info` and `source_map` surface it without any re-analysis.

## Common Pitfalls

### Pitfall 1: Struct Model Values from Z3
**What goes wrong:** Z3's `(get-model)` for a struct type returns something like `(Point (mk-Point 3 (- 1)))` or similar datatype constructor syntax, not a flat assignment. The current `Model` stores `assignments: Vec<(String, String)>` where values are raw Z3 strings.
**Why it happens:** Z3 encodes structs as SMT-LIB datatypes; the model output mirrors that encoding.
**How to avoid:** The `cex_render.rs` module must know the SMT sort encoding for each Rust type (from `encode_sort.rs` in `analysis`). Parse the Z3 constructor application by matching against the sort's constructor name.
**Warning signs:** Display showing `(mk-Point 3 (- 1))` instead of `Point { x: 3, y: -1 }` in output.

### Pitfall 2: SSA Versions and Initial/At-Failure
**What goes wrong:** VCGen uses path-condition encoding, not explicit SSA versioning. Variables reassigned in branches appear as the same SMT constant `x` with a single value in the model. However, if VCGen emits distinct SMT constants per assignment (e.g., `x_init` vs `x` at failure point), the model will have multiple entries.
**Why it happens:** Need to verify exactly how VCGen names variables across reassignments — whether it uses `_1_0`, `_1_1` versioning or ITE encoding.
**How to avoid:** Read `vcgen.rs` `PathAssignment` handling to confirm naming scheme. If ITE encoding is used (single constant), the initial value may not be recoverable from the model — in that case, label as single-value only.
**Warning signs:** No `_init` suffixed variables in the Z3 model despite reassignment in the spec.

### Pitfall 3: Source File Path Resolution
**What goes wrong:** `VcLocation.source_file` (when populated) may be a relative path or a rustc span path that doesn't resolve from the current working directory.
**Why it happens:** rustc's `SourceMap` stores paths relative to the workspace root.
**How to avoid:** Use `tcx.sess.source_map().lookup_char_pos(span.lo()).file.name` and resolve against the workspace root from `CARGO_MANIFEST_DIR` env var.
**Warning signs:** `std::fs::read_to_string` returning `NotFound` for a path that looks valid.

### Pitfall 4: VSCode Extension Schema Breakage
**What goes wrong:** The VSCode extension `verifier.ts` parses `failure.counterexample` as `JsonAssignment[]`. Adding a new nested `counterexample` object under a different key or changing the existing field's type will silently break the extension.
**Why it happens:** TypeScript optional fields swallow missing keys; incorrect type changes cause runtime errors at `.variable` / `.value` access.
**How to avoid:** Keep the existing `counterexample: Option<Vec<JsonAssignment>>` field for the flat representation. Add the richer schema as a new sibling field (e.g., `counterexample_v2` or nest inside `counterexample` as `{ variables: [...] }`). Update `verifier.ts` TypeScript interfaces in the same PR.
**Warning signs:** VSCode diagnostic panel showing `undefined` for variable names.

### Pitfall 5: Model String Parsing Fragility
**What goes wrong:** `callbacks.rs:663-674` re-parses the counterexample from the string `"k = v, k2 = v2"` by splitting on `", "`. Struct values contain commas and spaces, breaking the split.
**Why it happens:** The counterexample is currently serialized as a flat string in `VerificationResult.counterexample: Option<String>`.
**How to avoid:** Change `VerificationResult.counterexample` from `Option<String>` to `Option<Vec<(String, String)>>` so the model is passed as structured pairs. This requires updating the `Z3SolverAdapter` in `callbacks.rs` to stop serializing the model to a string.
**Warning signs:** Variable names appearing as `"k = v"` (the whole pair) instead of just `"k"`.

## Code Examples

Verified patterns from codebase inspection:

### Current State: Model Serialization in callbacks.rs (lines 43-55)
```rust
// CURRENT — loses structure:
Ok(rust_fv_solver::SolverResult::Sat(model)) => {
    let model_str = model.map(|m| {
        m.assignments
            .iter()
            .map(|(k, v)| format!("{k} = {v}"))
            .collect::<Vec<_>>()
            .join(", ")
    });
    VcOutcome::Sat(model_str)
}
```

### Target State: Structured Model Pass-Through
```rust
// TARGET — preserves structure:
Ok(rust_fv_solver::SolverResult::Sat(model)) => {
    let assignments = model.map(|m| m.assignments.clone());
    VcOutcome::Sat(assignments)  // requires VcOutcome enum change
}
```

### Current Ariadne Skeleton in diagnostics.rs (already compiled)
```rust
use ariadne::{ColorGenerator, Label, Report, ReportKind};
// ariadne 0.4.1 is at version with Source::from(&str) API

let mut colors = ColorGenerator::new();
let report = Report::build(ReportKind::Error, source_file, offset)
    .with_message(...)
    .with_label(
        Label::new((source_file, offset..offset + 1))
            .with_message(failure.message.clone())
            .with_color(color),
    );
// Currently falls back to report_text_only — needs Source::from wiring
```

### var_debug_info Access Pattern (rustc nightly API)
```rust
// In mir_converter.rs — body.var_debug_info is Vec<VarDebugInfo<'tcx>>
use rustc_middle::mir::VarDebugInfoContents;
for info in &body.var_debug_info {
    match &info.value {
        VarDebugInfoContents::Place(place) if place.projection.is_empty() => {
            let idx = place.local.as_usize();
            source_names.insert(format!("_{idx}"), info.name.to_string());
        }
        _ => {} // ignore composite / const debug info
    }
}
```

### Ghost Variable Filtering (using existing IR field)
```rust
// Local.is_ghost is already set in ir.rs lines 380-401
// Filter ghost vars when building counterexample display:
let visible_locals: Vec<&Local> = func.locals.iter()
    .chain(func.params.iter())
    .filter(|l| !l.is_ghost)
    .collect();
```

## State of the Art

| Old Approach | Current Approach | Impact |
|--------------|------------------|--------|
| `counterexample: Option<String>` flat | `counterexample: Option<Vec<JsonAssignment>>` | Exists; needs to become `JsonCounterexample` block |
| `format_counterexample` heuristic filter | Filter via `Local.is_ghost` + `var_debug_info` name map | Correctness improvement |
| ariadne fallback to text | ariadne with actual source + multi-label spans | CEX-03 requirement |
| `_1 = #x0000002a` in output | `x: i32 = 42` with type | CEX-01 + CEX-02 requirement |

**Currently incomplete:**
- `VcLocation.source_file` / `source_line` are always `None` from `mir_converter`: no source location plumbing from MIR spans yet
- `report_with_ariadne` falls back to `report_text_only` unconditionally (line 95 of `diagnostics.rs`)
- `VerificationResult.counterexample` is `Option<String>` — loses structure; re-parsed with fragile split at `callbacks.rs:664`
- `ir::Local.is_ghost` is set correctly by macros but `mir_converter` always sets `is_ghost: false` (line 27, 37, 52) — ghost detection must be wired

## Open Questions

1. **SSA Versioning Scheme in VCGen**
   - What we know: VCGen uses `PathAssignment` with `path_condition` + ITE encoding for branches
   - What's unclear: Does VCGen emit distinct SMT constants for a variable reassigned in a loop (e.g., `x_0`, `x_1`) or does it use ITE over a single `x`?
   - Recommendation: Read `vcgen.rs` around `encode_assign` to confirm; if ITE, initial value cannot be recovered from model and the "initial / at failure" distinction only applies to function parameters vs their value at the failing assertion

2. **Column Information for Ariadne Byte Offsets**
   - What we know: ariadne `Label::new((file, start..end))` needs byte offsets, not line numbers; `source_line` gives line but not column
   - What's unclear: Is column info available from the MIR `SourceInfo.span`?
   - Recommendation: Use `tcx.sess.source_map().lookup_char_pos(span.lo()).col.to_usize()` to get column; store as `source_column: Option<usize>` in `VcLocation`; for ariadne, compute byte offset as line-start + column

3. **Ghost Variable Detection in mir_converter**
   - What we know: `Local.is_ghost` field exists in IR; `mir_converter.rs` always sets it to `false`; `#[ghost]` macro emits a doc attribute (`doc = "rust_fv::ghost"`)
   - What's unclear: How to detect ghost locals during MIR conversion — the `#[ghost]` attribute is on the function/item, not on the MIR local decl
   - Recommendation: In `callbacks.rs`, after HIR attribute extraction, build a set of ghost function names; mark any local that comes from a call to a ghost function as ghost in the IR

4. **SMT Model Struct Value Format**
   - What we know: `encode_sort.rs` uses `collect_datatype_declarations` to encode structs as SMT datatypes; Z3 model output for datatypes uses constructor application syntax
   - What's unclear: Exact Z3 model string format for `Point { x: 3, y: -1 }` — is it `(mk-Point 3 (- 1))` or similar?
   - Recommendation: Write a quick integration test in `solver/tests` to observe actual Z3 model output for a struct-typed variable before implementing the parser in `cex_render.rs`

## Sources

### Primary (HIGH confidence)
- Codebase inspection: `crates/driver/src/mir_converter.rs` — confirmed `var_debug_info` not yet used
- Codebase inspection: `crates/driver/src/diagnostics.rs:8,38-96` — confirmed ariadne 0.4.1 present, `report_with_ariadne` falls back to text
- Codebase inspection: `crates/driver/src/json_output.rs` — confirmed current flat `JsonAssignment` schema
- Codebase inspection: `crates/driver/src/callbacks.rs:43-55, 663-674` — confirmed model serialized to string and re-parsed
- Codebase inspection: `crates/analysis/src/ir.rs:376-401` — confirmed `Local.is_ghost` field exists
- Codebase inspection: `vscode-extension/src/verifier.ts` — confirmed TypeScript interface for current schema
- `Cargo.lock`: ariadne version 0.4.1 confirmed

### Secondary (MEDIUM confidence)
- rustc MIR documentation pattern: `body.var_debug_info` as standard local→name API (used by Miri, KANI, and Prusti — well-established pattern in the Rust verification ecosystem)
- ariadne 0.4 multi-label pattern: `Label::new` + `Report::with_label` chaining, confirmed by codebase usage at `diagnostics.rs:67-70`

### Tertiary (LOW confidence)
- Z3 SMT model format for datatype constructors: assumed from general Z3 knowledge; must be verified with an integration test before implementing struct rendering

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH — all libraries already present in Cargo.toml; rustc API is established
- Architecture: HIGH — all touch points identified from direct code inspection
- Pitfalls: HIGH — pitfalls are directly observable from current code (string serialization, ariadne fallback, etc.)
- SSA versioning open question: MEDIUM — requires reading vcgen.rs in detail

**Research date:** 2026-02-19
**Valid until:** 2026-03-19 (30 days; stack is stable, rustc nightly API may drift slightly)
