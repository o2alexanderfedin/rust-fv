# Phase 42: Phase 39 Production Wiring (Ty::Closure from Real MIR) - Context

**Gathered:** 2026-03-03
**Status:** Ready for planning

<domain>
## Phase Boundary

Wire `mir_converter.rs` to emit `Ty::Closure` variants from real rustc MIR closure lowering so
the Phase 39 prophecy machinery is reachable from the production driver pipeline.

Specifically:
1. `convert_ty()` currently has a wildcard arm that maps `TyKind::Closure` → `Ty::Named(...)`.
   This must be fixed to produce `Ty::Closure(Box<ClosureInfo>)` when a closure type is encountered.
2. `CaptureMode` must be populated correctly: `ByMutRef` for mutable-reference captures,
   `ByMove` otherwise — not always defaulting to `ByMove`.

This phase does NOT add new prophecy logic — Phase 39 already implemented that. The only work
is connecting `TyKind::Closure` in rustc's MIR to `ir::Ty::Closure` in our IR.

**Out of scope:** New prophecy encoding, new contract syntax, async closures, multi-call chaining.

</domain>

<decisions>
## Implementation Decisions

### Claude's Discretion

All implementation strategy decisions are delegated to Claude. This follows the Phase 38 precedent
(identical wiring-only phase) where the same delegation was made.

Key technical decisions Claude should resolve:

- **tcx threading strategy**: `convert_ty(ty)` is a standalone function without `TyCtxt`. The cleanest
  approach (per existing pattern in `convert_generic_params`) is to introduce a new
  `convert_closure_ty(tcx, def_id, args)` helper that accepts `tcx` and is called from inside
  `convert_mir` when `TyKind::Closure` is encountered, while leaving the plain `convert_ty`
  unchanged for non-closure types. This avoids touching all call sites.

- **CaptureMode detection**: Use `tcx.closure_captures(def_id)` which returns `&[CapturedPlace<'tcx>]`
  with a `CaptureInfo` field containing `capture_kind: UpvarCapture`. Map `UpvarCapture::ByRef`
  with `BorrowKind::Mut { .. }` to `CaptureMode::ByMutRef`, and `UpvarCapture::ByValue` /
  `ByRef` with shared borrow → `CaptureMode::ByMove` / `CaptureMode::ByRef`.

- **ClosureInfo completeness**: Extract env_fields (upvar name + type + CaptureMode) at minimum.
  Also extract params and return_ty from `args.as_closure().sig()` if available without panics.
  Use `ClosureTrait::FnMut` when the closure MIR body is discovered; fall back to `FnMut` as
  default since this phase targets FnMut prophecy wiring.

- **Fallback behavior**: If `tcx.closure_captures()` fails or returns no captures, build a
  `ClosureInfo` with empty `env_fields` (rather than falling back to `Ty::Named`) so the
  prophecy machinery is still reachable even if no prophecy variables are generated.

- **Integration test**: Add an end-to-end driver-level integration test (in
  `crates/driver/tests/` or existing `integration_tests.rs`) that runs a real FnMut closure
  with `#[ensures(count == old(count) + 1)]` through `cargo verify` and asserts PASS.
  A failing case (contract violated) should also be tested.

</decisions>

<code_context>
## Existing Code Insights

### Reusable Assets

- `convert_mir(tcx, local_def_id, body, contracts)` in `mir_converter.rs:111`: Already receives
  `tcx`. The `TyKind::Closure` case should be handled inside this function, calling a new
  `convert_closure_ty(tcx, def_id, args)` helper inline.
- `convert_generic_params(tcx, def_id)` in `mir_converter.rs:57`: Exact pattern to follow —
  accepts `tcx` as first param, used inside `convert_mir`. New closure helper should mirror this.
- `ir::CaptureMode` enum (`ir.rs:29`): Already has `ByMove | ByRef | ByMutRef`. Populated with
  `ByMove` as default in all existing tests.
- `ir::ClosureInfo.env_fields: Vec<(String, Ty, CaptureMode)>` (`ir.rs:310`): The target struct.
  Already used in Phase 39 tests with manually constructed captures.
- Phase 39 tests in `vcgen.rs` and `encode_prophecy.rs`: These construct `ClosureInfo` manually
  with `CaptureMode::ByMutRef`. The production converter must produce the same structure.

### Established Patterns

- `convert_ty()` is a public pure function (no tcx). Keep it that way — closures are the only
  type that need tcx, so the divergence happens at the `TyKind::Closure` arm inside `convert_mir`.
- `body.local_decls[mir::Local::ZERO].ty` → `convert_ty(...)` pattern: Used for return type and
  all locals. When this encounters a closure type, `convert_ty` currently emits `Ty::Named`.
  The fix replaces that arm specifically inside `convert_mir`'s local conversion loops.
- Error handling: Other `convert_*` functions skip on failure, never panic. Closure extraction
  should follow: if `tcx.closure_captures(def_id)` unavailable, produce `ClosureInfo` with
  `env_fields: vec![]` rather than panicking.

### Integration Points

- `mir_converter.rs:511` — `convert_ty`: Add `ty::TyKind::Closure(def_id, args)` arm that calls
  `convert_closure_ty(...)`. But since `tcx` is unavailable here, the new arm in `convert_ty`
  should remain as `Ty::Named` — the real fix lives in `convert_mir`'s local conversion logic
  where `tcx` is available.
- `mir_converter.rs:124,143,161` — Local conversion inside `convert_mir`: These are the sites
  where closure types appear for params/locals. Add a check: if `decl.ty.is_closure()`, call
  `convert_closure_ty(tcx, ...)` instead of `convert_ty(decl.ty)`.
- `ir.rs:ClosureInfo`: No changes needed — struct already has correct shape from Phase 39.
- `crates/driver/tests/` — Integration test file for end-to-end verification.

</code_context>

<specifics>
## Specific Ideas

- The Phase 39 integration test `test_fnmut_prophecy_production_pipeline` may already exist as
  a placeholder — check `tests/` for an existing test file to extend rather than create new.
- `tcx.closure_captures(def_id)` returns `&[&rustc_middle::ty::CapturedPlace<'tcx>]` — each
  has `.var_ident` (name) and `.info.capture_kind` (UpvarCapture). The upvar type comes from
  `.place.ty(tcx).ty`.
- The `UpvarCapture` enum has `ByValue` and `ByRef(BorrowKind)`. Map:
  - `ByValue` → `CaptureMode::ByMove`
  - `ByRef(BorrowKind::MutBorrow)` → `CaptureMode::ByMutRef`
  - `ByRef(_)` → `CaptureMode::ByRef`

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope.

</deferred>

---

*Phase: 42-phase-39-production-wiring*
*Context gathered: 2026-03-03 via codebase analysis (discuss-phase)*
