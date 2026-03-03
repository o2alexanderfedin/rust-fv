---
phase: generics-fix
verified_at: "2026-03-02"
status: verified_with_gaps
score: 3/4
gaps_resolved_by: ["40-generics-verification-completion"]
---

# Phase Verification: generics-fix

**Phase goal:** Fix the generics verification gap — populate `generic_params` from
`tcx.generics_of(def_id)` in the MIR converter and route generic functions through
the parametric axiom path.

**Verification date:** 2026-03-02 (after Phase 40 completion)

**Score:** 3/4 truths VERIFIED in generics-fix; remaining gaps closed by Phase 40.

---

## Must-Haves Verification

### Truth 1: A generic function fn max<T: Ord>(a: T, b: T) -> T with contracts generates VCs when run through the driver pipeline

**Status:** VERIFIED

**Evidence:**
- `crates/driver/tests/generics_driver_e2e.rs`: test `generic_ir_function_produces_nonempty_results_when_generic_params_populated` — passes, confirming VCs are generated
- `crates/analysis/tests/generics_e2e.rs`: test `parametric_axioms_fire_for_generic_function` — passes
- Commit `24214ed`: `convert_generic_params()` in `mir_converter.rs` extracts type params from `tcx.generics_of(def_id)`; `generate_vcs_with_db` branch at `vcgen.rs:299-313` fires when `generic_params` is non-empty

**Note:** The VCs generated use real Ord axioms (DeclareSort + DeclareFun) after Phase 40-01 fixes `trait_bounds_as_smt_assumptions()`.

---

### Truth 2: The IR Function.generic_params is populated with type parameter names and trait bounds for generic functions

**Status:** VERIFIED

**Evidence:**
- `crates/driver/src/mir_converter.rs`: `convert_generic_params(tcx, def_id)` function (added in commit `24214ed`) iterates `tcx.generics_of(def_id).own_params`, filters `GenericParamDefKind::Type`, extracts trait bounds from `tcx.predicates_of(def_id)`, and returns `Vec<ir::GenericParam>`
- `convert_mir()` uses `generic_params: convert_generic_params(tcx, def_id)` instead of `vec![]`
- No `generic_params: vec![]` in the production code path

---

### Truth 3: The parametric axiom branch in generate_vcs_with_db fires for driver-produced IR (not just manual IR in tests)

**Status:** VERIFIED (routing) / PARTIAL (axiom content — fixed by Phase 40-01)

**Evidence:**
- `crates/analysis/src/vcgen.rs:299-313`: `if !func.generic_params.is_empty()` branch — fires when `mir_converter.rs` populates `generic_params`
- **Routing confirmed VERIFIED:** The branch fires for driver-produced IR because `convert_generic_params` now populates `generic_params`
- **Axiom content was PARTIAL in generics-fix:** `trait_bounds_as_smt_assumptions()` returned `vec![Term::BoolLit(true)]` for every bound — vacuous axioms
- **Axiom content fixed by Phase 40-01:** `trait_bounds_as_smt_assumptions()` now returns `Vec<Command>` with `DeclareSort("T", 0)`, `DeclareFun("T_le", ...)`, and `Assert` axioms for reflexivity and totality

**Resolution:** GENERICS-01 is fully satisfied after Phase 40-01.

---

### Truth 4: All existing tests continue to pass after the changes

**Status:** VERIFIED

**Evidence:**
- `cargo test --workspace` exits 0 (per generics-fix-01-SUMMARY.md)
- 0 failures across all packages after commit `24214ed`
- `cargo clippy --workspace`: 0 errors
- `cargo fmt --check`: no diff

---

## GENERICS Requirements

### GENERICS-01: Generic functions verified against real trait bound constraints

**Status in generics-fix:** PARTIAL — routing works, axiom content was vacuous (BoolLit(true))
**Status after Phase 40-01:** SATISFIED — `trait_bounds_as_smt_assumptions()` emits `DeclareSort`, `DeclareFun`, and `Assert` axioms for Ord/PartialOrd bounds

**Evidence (generics-fix):**
- Routing: `vcgen.rs:299-313` branch fires for driver-produced generic IR
- Gap: `monomorphize.rs:306-317` returned `BoolLit(true)` for all bounds

**Evidence (Phase 40-01 closure):**
- `monomorphize.rs`: `trait_bounds_as_smt_assumptions()` returns `Vec<Command>` with real SMT commands
- `vcgen.rs`: caller updated to `declarations.extend(assumptions)` (no more Assert-wrapping)
- New tests: `test_trait_bounds_as_smt_assumptions_ord_emits_real_commands` (unit), `ord_generic_smt_script_contains_declare_sort` (integration)

---

### GENERICS-02: generate_vcs_monomorphized called from parallel.rs verify_single() with MonomorphizationRegistry threaded through VerificationTask

**Status in generics-fix:** DEFERRED — explicitly noted in generics-fix-01-SUMMARY.md
**Status after Phase 40-02:** SATISFIED — registry threaded through VerificationTask; routing wired in verify_single()

**Evidence (generics-fix deferral):**
- generics-fix-01-SUMMARY.md: "GENERICS-02 deferred — requires call-site registry not yet available"
- `parallel.rs`: only a debug log for generic functions; `generate_vcs_monomorphized` not called

**Evidence (Phase 40-02 closure):**
- `parallel.rs`: `VerificationTask.monomorphization_registry: Arc<MonomorphizationRegistry>` field added
- `parallel.rs:verify_single()`: routes to `generate_vcs_monomorphized` when `is_generic() && !registry.get_instantiations().is_empty()`
- `callbacks.rs`: populates `monomorphization_registry: Arc::new(MonomorphizationRegistry::new())`
- New test: `monomorphized_path_fires_when_registry_has_instantiation` — registry populated with T -> i32, VCs produced

---

## Audit Blocker Clearance

**Original blocker (v0.1-MILESTONE-AUDIT.md):** generics-fix phase had no VERIFICATION.md — marked "UNVERIFIED (BLOCKER)"

**Resolution:** This VERIFICATION.md documents what generics-fix achieved and what Phase 40 completed. The two-phase resolution:
1. **generics-fix:** Routing infrastructure — generic_params populated from tcx, parametric branch activated
2. **Phase 40-01:** Real axioms — trait_bounds_as_smt_assumptions returns Vec<Command> with DeclareSort/DeclareFun/Assert
3. **Phase 40-02:** Registry wiring — MonomorphizationRegistry threaded through VerificationTask; generate_vcs_monomorphized routed

**Blocker status:** CLEARED

---

## Tech Debt Remaining

- `MonomorphizationRegistry` populated with empty registry in production (callbacks.rs) — call-site analysis to populate registry from real rustc MIR is Phase 42 scope
- `CaptureMode` always defaults to ByMove (Phase 42 / Phase 39 production wiring)
