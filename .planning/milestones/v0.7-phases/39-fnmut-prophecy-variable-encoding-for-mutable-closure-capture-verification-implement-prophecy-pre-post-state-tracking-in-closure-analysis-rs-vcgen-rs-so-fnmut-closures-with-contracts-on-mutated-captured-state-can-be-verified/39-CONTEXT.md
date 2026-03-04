# Phase 39: FnMut Prophecy Variable Encoding - Context

**Gathered:** 2026-03-02
**Status:** Ready for planning

<domain>
## Phase Boundary

Implement SMT prophecy variable encoding for mutable captured state in FnMut closures.
Specifically: extend `closure_analysis.rs` and `vcgen.rs` so that when a FnMut closure
captures a variable mutably, the VCGen emits pre/post prophecy variable declarations
and resolution constraints — enabling contracts like `#[ensures(count == old(count) + 1)]`
on functions that take or construct FnMut closures with mutated captured state.

**Out of scope:** Per-call-site chained prophecy tracking (multi-call state sequences),
FnOnce / Fn closure prophecy (neither mutates captures in the same way), async closures.

</domain>

<decisions>
## Implementation Decisions

### Mutability annotation in ClosureInfo.env_fields

- Add a `CaptureMode` enum: `ByMove | ByRef | ByMutRef`
- Change `env_fields` from `Vec<(String, Ty)>` to `Vec<(String, Ty, CaptureMode)>` in `ir.rs`
- Rationale: mirrors Rust's actual closure capture analysis; allows precise detection of which
  fields need prophecy variables vs. which are immutably captured. Inferring from `FnMut` alone
  over-approximates and forces unnecessary prophecy declarations for immutable captures.
- All existing callers that construct `ClosureInfo` use `env_fields: vec![...]` — they must be
  updated with `CaptureMode::ByMove` as the default for backwards-compatibility in tests.

### Prophecy granularity

- One prophecy pair per mutable-captured env field per closure (global pre/post per function).
- Naming convention (mirrors existing `encode_prophecy.rs`):
  - `{field_name}_initial` — captured value at closure-invocation entry
  - `{field_name}_prophecy` — predicted final value at closure-invocation return
- Resolution constraint: `(assert (= {field_name}_final {field_name}_prophecy))` at return.
- Rationale: simpler, consistent with how `detect_prophecies` handles `&mut T` params; per-call
  chaining is deferred to a later phase when multi-call closure verification is needed.

### Contract reference syntax

- Reuse existing `old()` operator: `old(count)` in an `#[ensures]` resolves to `count_initial`
- In postcondition context (not inside `old()`), env field name `count` resolves to `count_prophecy`
- This is exactly parallel to how `*_1` → `_1_prophecy` and `old(*_1)` → `_1_initial` works today
- No new syntax needed in `spec_parser.rs` — the existing `in_old` flag and postcondition context
  variable resolution already handle this pattern once the prophecy variables are declared.

### Data structure reuse

- Extend existing `ProphecyInfo` struct in `ir.rs` to add `closure_name: Option<String>`:
  - `None` → regular `&mut T` parameter prophecy (existing behavior)
  - `Some(name)` → closure env field prophecy (new behavior)
- Add `detect_closure_prophecies(closure_info: &ClosureInfo) -> Vec<ProphecyInfo>` in `encode_prophecy.rs`
  to mirror `detect_prophecies(func: &Function)`.
- Reuse `prophecy_declarations` and `prophecy_resolutions` unchanged — they operate on `Vec<ProphecyInfo>`
  and don't care about `closure_name`.
- In `vcgen.rs`, call `detect_closure_prophecies` for each FnMut closure info found by
  `closure_analysis::extract_closure_info`, and integrate the resulting declarations alongside
  regular declarations.

### Claude's Discretion

- Exact placement of closure prophecy declarations within the SMT script (before or after
  regular parameter declarations is fine — order doesn't matter to Z3).
- How to update existing test helper constructors for `ClosureInfo` (add `CaptureMode::ByMove`
  as the third element of each `env_fields` tuple).
- Whether to add a convenience `ClosureInfo::new_fnmut(...)` constructor helper.

</decisions>

<code_context>
## Existing Code Insights

### Reusable Assets

- `encode_prophecy::ProphecyInfo`: Can be extended with `closure_name: Option<String>` to cover
  closure env field prophecies without duplicating the struct.
- `encode_prophecy::prophecy_declarations(prophecies: &[ProphecyInfo]) -> Vec<Command>`: Can be
  reused as-is once `detect_closure_prophecies` produces a `Vec<ProphecyInfo>`.
- `encode_prophecy::prophecy_resolutions(...)`: Same — reuse unchanged.
- `encode_prophecy::detect_prophecies(func: &Function)`: The new `detect_closure_prophecies` mirrors
  this function, scanning `ClosureInfo.env_fields` for `CaptureMode::ByMutRef` entries.
- `closure_analysis::extract_closure_info(func)`: Already finds all `ClosureInfo` in a function —
  just needs to be called before prophecy detection in `vcgen.rs`.

### Established Patterns

- `CaptureMode` enum: Follow the `ClosureTrait` pattern (same file `ir.rs`) — `#[derive(Debug, Clone, PartialEq, Eq)]`.
- Prophecy variable naming: `{param}_initial` / `{param}_prophecy` — consistent with `ProphecyInfo.initial_var` / `.prophecy_var` naming.
- SMT variable declaration sequence: declare-const initial, declare-const prophecy, assert initial = current-value (see `prophecy_declarations`).
- Test construction: All IR tests construct `Function` with `prophecies: vec![]` — new closure prophecy tests should add prophecy entries to `ClosureInfo` instead of `Function.prophecies`.

### Integration Points

- `crates/analysis/src/ir.rs`: Add `CaptureMode` enum; update `ClosureInfo.env_fields` type.
- `crates/analysis/src/encode_prophecy.rs`: Add `closure_name: Option<String>` to `ProphecyInfo`;
  add `detect_closure_prophecies(closure_info: &ClosureInfo) -> Vec<ProphecyInfo>` function.
- `crates/analysis/src/vcgen.rs`: In declaration collection phase, after calling
  `closure_analysis::extract_closure_info`, call `detect_closure_prophecies` for each FnMut
  closure and append prophecy declarations.
- `crates/analysis/src/closure_analysis.rs`: No structural changes needed — `extract_closure_info`
  already works; only the `ClosureInfo` struct itself changes.
- `crates/driver/src/mir_converter.rs`: When converting MIR closure captures, populate
  `CaptureMode` appropriately (ByMutRef for `CaptureBy::Ref` with mutability, ByMove for
  `CaptureBy::Value`, etc.).

</code_context>

<specifics>
## Specific Ideas

- The test `test_vcgen_fnmut_closure_prophecy` in `vcgen.rs` currently has a placeholder comment
  "For now, just verify VCs are generated without errors" — Phase 39 should upgrade this to
  assert that the VC script actually contains `declare-const count_initial` and
  `declare-const count_prophecy` when `env_fields` includes a `ByMutRef` captured field.
- The `ProphecyInfo.deref_level` field (added for nested `&mut &mut T`) is not relevant for
  closure captures — set it to `0` for all closure env field prophecies.

</specifics>

<deferred>
## Deferred Ideas

- Per-call-site chained prophecy tracking (state₀ → state₁ → state₂ per invocation) — future phase
- FnOnce closure pre/post state (consume semantics are different) — separate phase
- Async closure (coroutine) captured state tracking — separate phase
- `spec_parser.rs` awareness of `closure.field` dot-access syntax in contracts — deferred;
  current flat naming (`count_initial`, `count_prophecy`) avoids need for struct-access syntax

</deferred>

---

*Phase: 39-fnmut-prophecy*
*Context gathered: 2026-03-02 via codebase analysis (discuss-phase)*
