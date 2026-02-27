# Phase 25: VSCode Counterexample v2 Integration - Research

**Researched:** 2026-02-20
**Domain:** TypeScript VSCode extension — counterexample display, JSON schema consumption
**Confidence:** HIGH

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| CEX-02 | User sees typed Rust values (e.g. `i32: 5`, `bool: false`) not raw hex bitvectors in counterexample output | `counterexample_v2` in `JsonFailure` already carries typed `display` strings (e.g. `"i32: -1"`); `diagnostics.ts` and `outputPanel.ts` must read from `failure.counterexample_v2.variables` instead of legacy `failure.counterexample` flat list |
| CEX-04 | Machine consumers receive structured `counterexample` field in `--output-format=json` output on verification failure | Rust side complete (Phase 19-04). IDE gap: `diagnostics.ts` and `outputPanel.ts` still read the flat legacy field; wiring them to `counterexample_v2` closes this IDE consumer gap |
</phase_requirements>

## Summary

Phase 25 is a narrow TypeScript-only wiring task. Phase 19-04 already built the complete `counterexample_v2` infrastructure end-to-end: the Rust backend populates `JsonFailure.counterexample_v2` with typed variables (name, type, display string, raw JSON), and `verifier.ts` already has the TypeScript interfaces (`JsonCounterexample`, `JsonCexVariable`, `JsonCexValue`, `JsonLocation`) declared and typed. The gap is that `diagnostics.ts` and `outputPanel.ts` still read `failure.counterexample` (the legacy flat `JsonAssignment[]`) and ignore `failure.counterexample_v2`.

The change is two functions in two files:

1. `diagnostics.ts` `createDiagnostic()`: upgrade the counterexample section to prefer `counterexample_v2` (displaying `varname: type = display` for each variable) with graceful fallback to legacy `counterexample` when `counterexample_v2` is absent.
2. `outputPanel.ts` `formatFailedFunction()`: same preference logic — prefer `counterexample_v2.variables` with typed rendering, fallback to legacy.

No new dependencies. No schema changes. No Rust changes. TypeScript compiles without errors today (`npx tsc --noEmit` passes clean). The task is purely presentation-layer wiring within the extension.

**Primary recommendation:** Wire `counterexample_v2` into `diagnostics.ts` and `outputPanel.ts` with typed rendering and legacy fallback. Single plan, two files, one helper function.

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| TypeScript | ^5.3.0 | Extension language | Already in `package.json` devDependencies |
| vscode API | ^1.85.0 | `vscode.Diagnostic`, `vscode.OutputChannel` | Already used throughout |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| (none new) | — | — | No new npm packages needed |

**Installation:** No new dependencies. All required types are already declared in `verifier.ts`.

## Architecture Patterns

### Current File Structure (files to modify)
```
vscode-extension/src/
├── verifier.ts          # DONE in Phase 19-04: JsonCounterexample interfaces declared
├── diagnostics.ts       # MODIFY: wire counterexample_v2 in createDiagnostic()
└── outputPanel.ts       # MODIFY: wire counterexample_v2 in formatFailedFunction()
```

### Pattern 1: Prefer-v2-with-legacy-fallback

**What:** A helper function that accepts `failure: JsonFailure` and returns a pre-formatted array of display lines. It checks `counterexample_v2` first, and falls back to the legacy `counterexample` flat list if v2 is absent.

**When to use:** Called from both `createDiagnostic()` (for the vscode.Diagnostic message string) and `formatFailedFunction()` (for the output panel).

**Example:**
```typescript
// In diagnostics.ts — preferred rendering helper
import { JsonFailure, JsonCexVariable } from './verifier';

function renderCounterexampleLines(failure: JsonFailure): string[] {
  // Prefer typed v2 schema
  if (failure.counterexample_v2 && failure.counterexample_v2.variables.length > 0) {
    return failure.counterexample_v2.variables.map(renderTypedVariable);
  }
  // Fallback to legacy flat assignments
  if (failure.counterexample && failure.counterexample.length > 0) {
    return failure.counterexample.map((a) => `${a.variable} = ${a.value}`);
  }
  return [];
}

function renderTypedVariable(v: JsonCexVariable): string {
  // Single-value variable: "x: i32 = 5"
  if (v.display !== undefined) {
    return `${v.name}: ${v.type} = ${v.display}`;
  }
  // SSA two-value variable: "x: i32 = 5 (initial) → 7 (at failure)"
  if (v.initial && v.at_failure) {
    return `${v.name}: ${v.type} = ${v.initial.display} (initial) → ${v.at_failure.display} (at failure)`;
  }
  // Only initial (parameter that wasn't mutated)
  if (v.initial) {
    return `${v.name}: ${v.type} = ${v.initial.display}`;
  }
  return `${v.name}: ${v.type} = (unknown)`;
}
```

**Confidence:** HIGH — schema shape confirmed from `verifier.ts` and `19-04-SUMMARY.md`.

### Pattern 2: diagnostics.ts createDiagnostic() — upgrade counterexample section

**Current code (lines 66-68 of `diagnostics.ts`):**
```typescript
if (failure.counterexample && failure.counterexample.length > 0) {
  message += `\nCounterexample: ${formatCounterexample(failure.counterexample)}`;
}
```

**Target code:**
```typescript
const cexLines = renderCounterexampleLines(failure);
if (cexLines.length > 0) {
  message += `\nCounterexample:\n  ${cexLines.join('\n  ')}`;
}
```

The existing `formatCounterexample` export can be kept for backward compatibility (used by any callers) or updated to delegate to the new helper. The `renderCounterexampleLines` helper is the new internal entry point.

### Pattern 3: outputPanel.ts formatFailedFunction() — upgrade counterexample section

**Current code (lines 114-120 of `outputPanel.ts`):**
```typescript
if (failure.counterexample && failure.counterexample.length > 0) {
  channel.appendLine('    Counterexample:');
  for (const assignment of failure.counterexample) {
    channel.appendLine(`      ${assignment.variable} = ${assignment.value}`);
  }
}
```

**Target code:**
```typescript
const cexLines = renderCounterexampleLines(failure);
if (cexLines.length > 0) {
  channel.appendLine('    Counterexample:');
  for (const line of cexLines) {
    channel.appendLine(`      ${line}`);
  }
}
```

**Where to put `renderTypedVariable` and `renderCounterexampleLines`:** Either in `diagnostics.ts` with a re-export, or in a new `cexFormat.ts` utility module. Since both `diagnostics.ts` and `outputPanel.ts` need it, extracting to a `cexFormat.ts` module avoids a circular import and follows DRY. Alternatively, duplicate the two small helpers in each file if a new module feels over-engineered for 15 lines of code — YAGNI applies here.

**Recommendation:** Inline the helpers in `diagnostics.ts` (which already imports `JsonAssignment`) and import `renderCounterexampleLines` into `outputPanel.ts`. This keeps new file count at zero and avoids over-engineering.

### Pattern 4: violated_spec in output panel

The `counterexample_v2.violated_spec` field (optional string) contains the text of the failing `#[ensures]`/`#[assert]`. Currently the output panel shows `failure.contract` for this purpose. `violated_spec` is more specific (it is the exact spec clause, not the full contract string). The output panel can optionally show it:

```typescript
if (failure.counterexample_v2?.violated_spec) {
  channel.appendLine(`    Violated spec: ${failure.counterexample_v2.violated_spec}`);
}
```

This is an enhancement, not required by the success criteria, but adds value at zero cost since the field is already in the JSON.

### Anti-Patterns to Avoid

- **Remove legacy `failure.counterexample` branch entirely:** Do not delete the legacy fallback. The success criteria explicitly require graceful fallback when `counterexample_v2` is absent (e.g., older cargo verify binary without v2 support, or timeout cases where no model was found).
- **Access `counterexample_v2.variables` without null-check:** TypeScript strict mode is enabled (`"strict": true` in tsconfig.json). The `counterexample_v2` field is optional (`?`). Access must be guarded: `failure.counterexample_v2 && failure.counterexample_v2.variables.length > 0` or use optional chaining `failure.counterexample_v2?.variables ?? []`.
- **Importing vscode in a pure utility helper:** If extracting to `cexFormat.ts`, do not import `vscode` — keep it as a pure TypeScript module so it can be unit-tested without the VSCode runtime.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Type-aware rendering logic | Custom type parser in TS | Read `v.display` (pre-rendered by Rust `cex_render.rs`) | Rust side already does type dispatch; `display` is the human string; TypeScript only formats it for presentation |
| JSON schema parsing | Manual field access chains | TypeScript interfaces already in `verifier.ts` | Full type safety with zero extra code |

**Key insight:** The hard work (SMT bitvector → typed Rust value) is already done in Rust's `cex_render.rs`. The TypeScript layer only needs to pick up the pre-rendered `display` string and format it for the output panel. This is purely a string formatting task.

## Common Pitfalls

### Pitfall 1: Optional chaining with `length` check
**What goes wrong:** `failure.counterexample_v2.variables.length > 0` throws if `counterexample_v2` is `undefined`.
**Why it happens:** TypeScript optional field — field may be absent when solver found no model (UNSAT or timeout).
**How to avoid:** `failure.counterexample_v2 && failure.counterexample_v2.variables.length > 0` or `(failure.counterexample_v2?.variables.length ?? 0) > 0`.
**Warning signs:** TypeScript strict-mode error at compile time: "Object is possibly undefined."

### Pitfall 2: Missing the `initial`-only case
**What goes wrong:** Rendering code only handles `display` (single-value) and `initial`+`at_failure` (two-value), but forgets the `initial`-only case.
**Why it happens:** A function parameter that was never mutated gets an `initial` sub-object but no `at_failure`. Accessing `v.at_failure.display` throws if `at_failure` is undefined.
**How to avoid:** Handle all three cases: `display`-only, `initial`+`at_failure`, `initial`-only (see `renderTypedVariable` example above).
**Warning signs:** `[FAIL]` in output panel showing `(unknown)` for function parameters that definitely have values.

### Pitfall 3: formatCounterexample export breakage
**What goes wrong:** `formatCounterexample` is exported from `diagnostics.ts` (line 92). If it is removed or its signature is changed, any external consumers break at compile time.
**Why it happens:** Phase 19-04 kept it for backward compatibility.
**How to avoid:** Keep `formatCounterexample(assignments: JsonAssignment[]): string` export unchanged. Add new rendering logic alongside it, not in place of it.
**Warning signs:** TypeScript compile error: "Property 'formatCounterexample' does not exist on module."

### Pitfall 4: TypeScript tsc not in PATH
**What goes wrong:** `npx tsc --noEmit` reports "command not found" or "tsc: not found" in some environments.
**Why it happens:** Node/npm not in PATH for the shell running the verification.
**How to avoid:** Use `cd /Users/alexanderfedin/Projects/hapyy/rust-fv/vscode-extension && npx tsc --noEmit` — `npx` finds the local devDependency TypeScript. Confirmed to work (clean output on current codebase).
**Warning signs:** `npx: not found` — fallback: `./node_modules/.bin/tsc --noEmit`.

## Code Examples

Verified patterns from direct codebase inspection:

### Current JsonFailure interface in verifier.ts (Phase 19-04 output)
```typescript
// Source: vscode-extension/src/verifier.ts lines 22-31
export interface JsonFailure {
  vc_kind: string;
  description: string;
  contract?: string;
  source_file?: string;
  source_line?: number;
  counterexample?: JsonAssignment[];        // keep — backward compat
  counterexample_v2?: JsonCounterexample;   // new — rich schema
  suggestion?: string;
}
```

### Current JsonCexVariable in verifier.ts (Phase 19-04 output)
```typescript
// Source: vscode-extension/src/verifier.ts lines 47-58
export interface JsonCexVariable {
  name: string;
  type: string;
  display?: string;
  raw?: unknown;
  initial?: JsonCexValue;
  at_failure?: JsonCexValue;
}
```

### Example counterexample_v2 JSON (from 19-04-SUMMARY.md)
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

### Current counterexample rendering in diagnostics.ts (to be upgraded)
```typescript
// Source: vscode-extension/src/diagnostics.ts lines 66-68
if (failure.counterexample && failure.counterexample.length > 0) {
  message += `\nCounterexample: ${formatCounterexample(failure.counterexample)}`;
}

// Source: vscode-extension/src/diagnostics.ts lines 92-96
export function formatCounterexample(assignments: JsonAssignment[]): string {
  return assignments
    .map((a) => `${a.variable} = ${a.value}`)
    .join(', ');
}
```

### Current counterexample rendering in outputPanel.ts (to be upgraded)
```typescript
// Source: vscode-extension/src/outputPanel.ts lines 114-120
if (failure.counterexample && failure.counterexample.length > 0) {
  channel.appendLine('    Counterexample:');
  for (const assignment of failure.counterexample) {
    channel.appendLine(`      ${assignment.variable} = ${assignment.value}`);
  }
}
```

## State of the Art

| Old Approach | Current Approach | Impact |
|--------------|------------------|--------|
| `failure.counterexample` flat list (`variable`, `value` raw strings) | `failure.counterexample_v2.variables` with `display` typed strings | CEX-02/CEX-04 IDE gap — this phase closes it |
| `formatCounterexample`: `x = #x0000002a` style | `renderTypedVariable`: `x: i32 = 42` style | Readable, type-annotated, developer-familiar format |

**Already complete (Phase 19-04, no changes needed):**
- Rust `json_output.rs`: `JsonCounterexample`, `JsonCexVariable`, `JsonCexValue`, `JsonLocation` structs
- Rust `parallel.rs`: `build_counterexample_v2()` populates v2 from `cex_render::render_counterexample`
- TypeScript `verifier.ts`: All four interfaces declared, `JsonFailure.counterexample_v2` typed

**This phase closes (IDE consumer gap):**
- `diagnostics.ts`: Still reads legacy `failure.counterexample` (flat, untyped values)
- `outputPanel.ts`: Still reads legacy `failure.counterexample` (flat, untyped values)

## Open Questions

1. **Single-function helper vs new utility module**
   - What we know: Both `diagnostics.ts` and `outputPanel.ts` need identical rendering logic; `diagnostics.ts` is imported by `extension.ts`; `outputPanel.ts` is independently imported
   - What's unclear: Whether to extract `renderCounterexampleLines` to a new `cexFormat.ts` or to put it in `diagnostics.ts` with cross-import to `outputPanel.ts`
   - Recommendation: Put helpers in `diagnostics.ts` (it already imports `JsonAssignment`; add `JsonCexVariable` import from `verifier`); import and re-use in `outputPanel.ts`. Zero new files, follows YAGNI.

2. **`violated_spec` display in output panel**
   - What we know: `counterexample_v2.violated_spec` contains the failing spec text; `failure.contract` also exists and may overlap
   - What's unclear: Whether `violated_spec` duplicates `failure.contract` or adds new information
   - Recommendation: Check if `failure.contract` is always populated when `violated_spec` is; if so, `violated_spec` display is additive enhancement. Include it in output panel for completeness — adds one line, zero risk.

## Sources

### Primary (HIGH confidence)
- Direct codebase inspection: `vscode-extension/src/diagnostics.ts` — confirmed legacy counterexample reading at lines 66-68, 92-96
- Direct codebase inspection: `vscode-extension/src/outputPanel.ts` — confirmed legacy counterexample reading at lines 114-120
- Direct codebase inspection: `vscode-extension/src/verifier.ts` — confirmed `JsonFailure.counterexample_v2` typed, all v2 interfaces present (Phase 19-04 output)
- `.planning/phases/19-counterexample-generation/19-04-SUMMARY.md` — confirmed complete v2 pipeline, TypeScript compiles clean
- `vscode-extension/tsconfig.json` — confirmed `"strict": true`, ES2022 target, commonjs module
- `vscode-extension/package.json` — confirmed `"lint": "tsc --noEmit"`, no test runner configured

### Secondary (MEDIUM confidence)
- `npx tsc --noEmit` run confirmed: zero errors on current codebase (TypeScript extension compiles clean)

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH — no new dependencies; all interfaces already declared
- Architecture: HIGH — exact lines to change identified from direct code inspection
- Pitfalls: HIGH — TypeScript strict mode enforces null-safety; fallback pattern is explicit success criterion

**Research date:** 2026-02-20
**Valid until:** 2026-03-20 (30 days; TypeScript and VSCode API are stable; schema is frozen from Phase 19)
