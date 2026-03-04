---
phase: generics-fix
plan: 01
type: tdd
wave: 1
depends_on: []
files_modified:
  - crates/analysis/tests/generics_e2e.rs
  - crates/driver/tests/generics_driver_e2e.rs
  - crates/driver/src/mir_converter.rs
  - crates/driver/src/parallel.rs
autonomous: true
requirements:
  - GENERICS-01
  - GENERICS-02

must_haves:
  truths:
    - "A generic function fn max<T: Ord>(a: T, b: T) -> T with contracts generates VCs when run through the driver pipeline"
    - "The IR Function.generic_params is populated with type parameter names and trait bounds for generic functions"
    - "The parametric axiom branch in generate_vcs_with_db fires for driver-produced IR (not just manual IR in tests)"
    - "All existing tests continue to pass after the changes"
  artifacts:
    - path: "crates/analysis/tests/generics_e2e.rs"
      provides: "Analysis-layer E2E tests for generic function VC generation (parametric path)"
      exports: []
    - path: "crates/driver/tests/generics_driver_e2e.rs"
      provides: "Driver-layer E2E tests exercising VerificationTask with generic IR"
      exports: []
    - path: "crates/driver/src/mir_converter.rs"
      provides: "Populated generic_params in convert_mir() via tcx.generics_of(def_id)"
      exports: ["convert_mir"]
    - path: "crates/driver/src/parallel.rs"
      provides: "Routing to generate_vcs_monomorphized when generic_params is non-empty"
      exports: ["verify_functions_parallel"]
  key_links:
    - from: "crates/driver/src/mir_converter.rs:convert_mir"
      to: "crates/analysis/src/ir.rs:Function.generic_params"
      via: "tcx.generics_of(def_id).own_params iteration"
      pattern: "tcx\\.generics_of"
    - from: "crates/driver/src/parallel.rs:verify_single"
      to: "crates/analysis/src/vcgen.rs:generate_vcs_monomorphized"
      via: "ir_func.is_generic() check"
      pattern: "generate_vcs_monomorphized|is_generic"
---

<objective>
Fix the generics verification gap: populate generic_params in the MIR converter and route
generic functions through the correct VC generation path in the driver.

Purpose: Generic functions with contracts (e.g., fn max<T: Ord>(a: T, b: T) -> T) currently
produce no trait-bound axioms because generic_params is always empty at the driver level.
The parametric axiom branch in generate_vcs_with_db (vcgen.rs:290-298) is dead code in
production. This fix activates it by extracting type parameters from tcx.generics_of().

Output:
  - Failing tests demonstrating the gap (RED phase)
  - mir_converter.rs populating generic_params (GREEN phase)
  - parallel.rs routing to generate_vcs_monomorphized for generic functions (GREEN phase)
  - All existing tests passing (REFACTOR/verify phase)
</objective>

<execution_context>
Follow TDD: RED -> GREEN -> REFACTOR. Write failing tests first. Implement minimally. Verify.
</execution_context>

<context>
@/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/mir_converter.rs
@/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/parallel.rs
@/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/ir.rs
@/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/vcgen.rs
@/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/monomorphize.rs
@/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/tests/ghost_predicate_e2e.rs
@/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/tests/e2e_verification.rs

<interfaces>
<!-- Key types extracted from the codebase. Use these directly. -->

From crates/analysis/src/ir.rs:
```rust
pub struct GenericParam {
    pub name: String,
    pub trait_bounds: Vec<String>,
}

pub struct Function {
    pub generic_params: Vec<GenericParam>,
    // ... other fields
}

impl Function {
    pub fn is_generic(&self) -> bool {
        !self.generic_params.is_empty()
    }
}
```

From crates/analysis/src/vcgen.rs (line 246, 1032):
```rust
pub fn generate_vcs_with_db(
    func: &Function,
    contract_db: Option<&ContractDatabase>,
    ghost_pred_db: &GhostPredicateDatabase,
) -> FunctionVCs;

pub fn generate_vcs_monomorphized(
    func: &Function,
    registry: &crate::monomorphize::MonomorphizationRegistry,
    contract_db: Option<&ContractDatabase>,
) -> Vec<FunctionVCs>;
```

From crates/analysis/src/monomorphize.rs:
```rust
pub struct MonomorphizationRegistry { ... }
impl MonomorphizationRegistry {
    pub fn new() -> Self;
    pub fn register(&mut self, func_name: &str, inst: TypeInstantiation);
    pub fn get_instantiations(&self, func_name: &str) -> &[TypeInstantiation];
}
```

From crates/driver/src/parallel.rs (verify_single, line 225):
```rust
// Current call (always generate_vcs_with_db):
let mut func_vcs = rust_fv_analysis::vcgen::generate_vcs_with_db(
    &task.ir_func,
    Some(&task.contract_db),
    &task.ghost_pred_db,
);

// Target: route based on is_generic()
```

From crates/driver/src/mir_converter.rs (convert_mir, line 128):
```rust
// Current (line 136): generic_params: vec![]
// Target: extract from tcx.generics_of(def_id)
```

rustc API for generics (nightly-2026-02-11):
```rust
// tcx.generics_of(def_id) -> &ty::Generics
// .own_params: &[ty::GenericParamDef]
// Each GenericParamDef:
//   .name: rustc_span::symbol::Symbol  -> .as_str()
//   .kind: ty::GenericParamDefKind
//     GenericParamDefKind::Type { .. } -> is a type parameter
//     GenericParamDefKind::Lifetime { .. } -> skip (already in lifetime_params)
//     GenericParamDefKind::Const { .. } -> skip (const generics)
//
// Trait bounds on a type param come from tcx.predicates_of(def_id).predicates
// Each predicate: (ty::Clause, Span)
// clause.as_trait_clause() -> Option<ty::PolyTraitPredicate>
// trait_pred.skip_binder().trait_ref.def_id -> DefId of the trait
// tcx.def_path_str(trait_def_id) -> "std::cmp::Ord", "core::cmp::Ord", etc.
// Extract the short name by splitting on "::" and taking the last segment.
```
</interfaces>
</context>

<tasks>

<task type="auto" tdd="true">
  <name>Task 1: RED - Write failing tests for generic_params extraction and routing</name>
  <files>
    crates/analysis/tests/generics_e2e.rs
    crates/driver/tests/generics_driver_e2e.rs
  </files>
  <behavior>
    Analysis-layer tests (generics_e2e.rs):
    - Test 1 (parametric_axioms_fire_for_generic_function): Build a Function with
      generic_params=[GenericParam { name: "T", trait_bounds: ["Ord"] }], params _1 and _2
      with Ty::Generic("T"), return_local _0 with Ty::Generic("T"), body that returns
      Rvalue::Use(Operand::Copy(_1)). Add ensures contract "_0 == _1". Call
      generate_vcs_with_db. Assert conditions is non-empty (trait bound axiom branch fires,
      postcondition VC is generated). This test PASSES with existing code because the
      analysis layer already handles generic_params — it documents the existing behavior.

    - Test 2 (empty_generic_params_produces_no_axiom_assumptions): Same function but with
      generic_params: vec![]. Assert that conditions count is the same as when generic_params
      is populated (demonstrating that empty generic_params is valid but produces no axioms).
      This is a correctness documentation test.

    Driver-layer tests (generics_driver_e2e.rs):
    - Test 3 (generic_ir_function_routes_through_vcs_with_db_when_generic_params_populated):
      Build a VerificationTask with a Function where generic_params contains
      GenericParam { name: "T", trait_bounds: ["Ord"] }, params _1/_2 Ty::Generic("T"),
      return _0 Ty::Generic("T"), body assigns _0 = _1, ensures "_0 == _1".
      Call verify_functions_parallel with this task (1 thread, fresh).
      Assert results.len() == 1 AND results[0].results is non-empty.
      This test FAILS initially if parallel.rs does not handle generic functions correctly.

    - Test 4 (generic_function_with_empty_generic_params_still_verifies): Same as test 3
      but generic_params: vec![]. Must also produce non-empty results. Confirms no regression.

    All tests use the same helper pattern as ghost_predicate_e2e.rs:
      - temp_cache_dir() for isolation
      - VcCache::new(cache_dir)
      - InvalidationDecision::verify(InvalidationReason::Fresh)
      - verify_functions_parallel(vec![task], &mut cache, 1, false, false)
  </behavior>
  <action>
    Create crates/analysis/tests/generics_e2e.rs with the analysis-layer tests.
    Create crates/driver/tests/generics_driver_e2e.rs with the driver-layer tests.

    For generics_e2e.rs, import:
      use rust_fv_analysis::ir::*;
      use rust_fv_analysis::vcgen;
      use rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase;

    For generics_driver_e2e.rs, follow the exact pattern from
    crates/driver/tests/ghost_predicate_e2e.rs:
      - Same imports (rust_fv_driver::parallel, rust_fv_driver::cache, etc.)
      - Same temp_cache_dir helper
      - Make a make_generic_test_func(generic_params: Vec<GenericParam>) -> Function helper
        that builds the max-like function body (bb0: _0 = _1, Return)
        with ensures "_0 == _1" contract
      - make_generic_task(func: Function) -> VerificationTask (same as make_task in ghost test)

    Run tests to confirm RED state:
      cargo test --package rust-fv-analysis --test generics_e2e 2>&1 | tail -20
      cargo test --package rust-fv-driver --test generics_driver_e2e 2>&1 | tail -20

    Tests 1, 2, 4 should PASS (analysis layer works, empty generic_params works).
    Test 3 should PASS too since generate_vcs_with_db handles generic_params already.
    The RED state is in the DRIVER integration (mir_converter never populates generic_params
    in real usage), which is tested by the integration test pipeline tests — not by unit tests.

    After writing tests, confirm they compile and identify which pass/fail:
      cargo test --package rust-fv-driver --test generics_driver_e2e -- --nocapture 2>&1 | tail -30
  </action>
  <verify>
    <automated>cargo test --package rust-fv-analysis --test generics_e2e 2>&1 | tail -20 && cargo test --package rust-fv-driver --test generics_driver_e2e 2>&1 | tail -20</automated>
  </verify>
  <done>
    Both test files exist and compile. Tests document expected behavior:
    generic function with non-empty generic_params produces non-empty VCs via driver path.
    Tests pass or clearly document what must change in implementation tasks.
  </done>
</task>

<task type="auto" tdd="true">
  <name>Task 2: GREEN - Populate generic_params in mir_converter.rs</name>
  <files>
    crates/driver/src/mir_converter.rs
  </files>
  <behavior>
    - convert_generic_params() helper: takes tcx + def_id, returns Vec<GenericParam>
    - For each param in tcx.generics_of(def_id).own_params that is GenericParamDefKind::Type:
        * Extract name via param.name.as_str().to_string()
        * Extract trait bounds from tcx.predicates_of(def_id).predicates:
          - For each (predicate, _span) where clause.as_trait_clause() is Some:
            - Get trait_ref.def_id
            - Get the short name: tcx.def_path_str(trait_def_id).split("::").last().unwrap_or("").to_string()
            - Skip "Sized" (always implied, adds no verification value)
            - Collect into trait_bounds: Vec<String>
        * Build GenericParam { name, trait_bounds }
    - Call convert_generic_params() in convert_mir() and use the result instead of vec![]

    Trait bound extraction detail:
      tcx.predicates_of(def_id).predicates is &[(ty::Clause<'tcx>, Span)]
      clause.as_trait_clause() returns Option<ty::PolyTraitPredicate<'tcx>>
      On the PolyTraitPredicate, call .skip_binder() to get TraitPredicate
      .trait_ref.def_id gives the DefId of the trait
      Only include bounds where .trait_ref.self_ty() is Ty::Param(p) and p.name == param.name
      This filters to bounds that apply to THIS type parameter specifically.

    Keep the implementation simple and robust:
      - If tcx.generics_of(def_id) panics for some def_id, catch with a guard:
        the function signature already takes def_id as LocalDefId so this is safe.
      - Only extract GenericParamDefKind::Type params (skip Lifetime, Const).
      - Name collision with existing lifetime_params is not possible (different kind).
  </behavior>
  <action>
    Edit crates/driver/src/mir_converter.rs:

    1. Add a new private function after build_source_names:
    ```rust
    /// Extract generic type parameters from a function's generics.
    ///
    /// Calls tcx.generics_of(def_id) to enumerate type parameters, then
    /// tcx.predicates_of(def_id) to extract trait bounds for each.
    ///
    /// Lifetime and const generic parameters are skipped — lifetimes are
    /// handled separately in lifetime_params, and const generics are not
    /// supported in the verification IR.
    ///
    /// "Sized" bounds are filtered out as they are always implied and
    /// add no verification value.
    fn convert_generic_params(
        tcx: TyCtxt<'_>,
        def_id: rustc_hir::def_id::DefId,
    ) -> Vec<ir::GenericParam> {
        use rustc_middle::ty::GenericParamDefKind;

        let generics = tcx.generics_of(def_id);
        let predicates = tcx.predicates_of(def_id);

        generics
            .own_params
            .iter()
            .filter_map(|param| {
                if !matches!(param.kind, GenericParamDefKind::Type { .. }) {
                    return None;
                }
                let param_name = param.name.as_str().to_string();

                // Collect trait bounds that apply to this specific type parameter.
                let trait_bounds: Vec<String> = predicates
                    .predicates
                    .iter()
                    .filter_map(|(clause, _span)| {
                        let trait_pred = clause.as_trait_clause()?.skip_binder();
                        // Only include bounds on THIS parameter (self_ty == Param(param_name))
                        if let ty::TyKind::Param(p) = trait_pred.trait_ref.self_ty().kind() {
                            if p.name.as_str() != param_name {
                                return None;
                            }
                        } else {
                            return None;
                        }
                        let trait_name = tcx
                            .def_path_str(trait_pred.trait_ref.def_id)
                            .split("::")
                            .last()
                            .unwrap_or("")
                            .to_string();
                        // Skip Sized — always implied, adds no verification value
                        if trait_name == "Sized" {
                            return None;
                        }
                        Some(trait_name)
                    })
                    .collect();

                Some(ir::GenericParam {
                    name: param_name,
                    trait_bounds,
                })
            })
            .collect()
    }
    ```

    2. In convert_mir(), replace `generic_params: vec![]` with:
    ```rust
    generic_params: convert_generic_params(tcx, def_id),
    ```

    Run clippy and rustfmt after editing:
      cd /Users/alexanderfedin/Projects/hapyy/rust-fv && cargo clippy --package rust-fv-driver -p rust-fv-driver 2>&1 | grep -E "error|warning" | head -30
      cargo fmt --package rust-fv-driver 2>&1

    Run driver unit tests:
      cargo test --package rust-fv-driver --lib 2>&1 | tail -20
  </action>
  <verify>
    <automated>cd /Users/alexanderfedin/Projects/hapyy/rust-fv && cargo test --package rust-fv-driver --lib 2>&1 | tail -20 && cargo clippy --package rust-fv-driver 2>&1 | grep "^error" | wc -l</automated>
  </verify>
  <done>
    convert_generic_params() function exists in mir_converter.rs.
    convert_mir() uses it instead of vec![].
    cargo clippy produces zero errors for rust-fv-driver.
    All driver lib unit tests pass.
  </done>
</task>

<task type="auto" tdd="true">
  <name>Task 3: GREEN - Route generic functions to generate_vcs_monomorphized in parallel.rs + full test suite</name>
  <files>
    crates/driver/src/parallel.rs
  </files>
  <behavior>
    - In verify_single(), check ir_func.is_generic() before calling generate_vcs_with_db
    - If is_generic() is true:
        * Build a MonomorphizationRegistry with a fallback: since no call-site instantiation
          data is available in the driver yet (the registry is not threaded through
          VerificationTask), use generate_vcs_with_db as the existing parametric path
          (trait bound axioms from generic_params will now fire because generic_params is
          populated by Task 2)
        * This means: for now, is_generic() functions continue using generate_vcs_with_db
          because the parametric axiom approach in vcgen.rs:290-298 IS correct and will
          now actually fire with real generic_params data
        * The generate_vcs_monomorphized path requires a populated MonomorphizationRegistry
          which requires call-site analysis — that is a separate future task
        * Document this decision in a code comment: "Generic functions verified via
          parametric axioms (trait bound assumptions injected per vcgen.rs:290-298).
          Monomorphization-based verification (generate_vcs_monomorphized) requires
          call-site instantiation tracking — tracked in tech_debt."

    IMPORTANT: The key fix in Task 2 (populating generic_params) already activates the
    parametric branch in generate_vcs_with_db. Task 3's scope is:
      1. Add a clear comment in verify_single() documenting the routing decision
      2. Add a tracing::debug! log when a generic function is detected
      3. Confirm the driver e2e tests now pass with the Task 2 fix in place

    After the Task 2 fix, re-run all integration tests:
      cargo test --package rust-fv-driver 2>&1 | tail -30
      cargo test --package rust-fv-analysis 2>&1 | tail -30

    If any tests fail due to generate_vcs_with_db behavior changes for generic functions,
    investigate and fix. Document the fix in the SUMMARY.

    Run full test suite:
      cargo test --workspace 2>&1 | tail -40
  </behavior>
  <action>
    Edit crates/driver/src/parallel.rs in verify_single() at line ~264:

    Before the call to generate_vcs_with_db, add:
    ```rust
    // Generic function routing:
    // Functions with non-empty generic_params are verified via the parametric axiom
    // approach in generate_vcs_with_db (vcgen.rs lines 285-298 inject trait bound
    // assumptions for each generic parameter). This is activated by mir_converter.rs
    // populating generic_params from tcx.generics_of().
    //
    // The monomorphization path (generate_vcs_monomorphized) requires a populated
    // MonomorphizationRegistry with call-site instantiation data. That requires
    // call-site analysis (type-checking the caller body), which is not yet threaded
    // through VerificationTask. Tracked in tech_debt as GENERICS-02.
    if task.ir_func.is_generic() {
        tracing::debug!(
            function = %task.name,
            generic_params = ?task.ir_func.generic_params.iter().map(|gp| &gp.name).collect::<Vec<_>>(),
            "Verifying generic function via parametric axiom path"
        );
    }
    ```

    Keep the generate_vcs_with_db call unchanged (it now works correctly because
    generic_params is populated by Task 2).

    Run the full driver test suite including integration tests:
      cargo test --package rust-fv-driver 2>&1 | tail -30

    Run the generics-specific driver e2e tests:
      cargo test --package rust-fv-driver --test generics_driver_e2e -- --nocapture 2>&1 | tail -30

    Run the full workspace test suite:
      cargo test --workspace 2>&1 | grep -E "FAILED|error\[" | head -20

    Run clippy on the whole workspace:
      cargo clippy --workspace 2>&1 | grep "^error" | head -20

    Run rustfmt check:
      cargo fmt --check 2>&1 | head -20
  </action>
  <verify>
    <automated>cd /Users/alexanderfedin/Projects/hapyy/rust-fv && cargo test --workspace 2>&1 | tail -20</automated>
  </verify>
  <done>
    parallel.rs has a clear comment documenting the generic routing decision.
    tracing::debug! fires when a generic function is encountered.
    All workspace tests pass (cargo test --workspace exits 0).
    cargo clippy --workspace produces zero errors.
    cargo fmt --check produces no diff.
    The generics_driver_e2e tests confirm generic functions produce non-empty VC results.
  </done>
</task>

</tasks>

<verification>
After all three tasks complete, verify:

1. Generic param extraction:
   ```
   grep -n "convert_generic_params\|generic_params:" \
     /Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/mir_converter.rs
   ```
   Must show: convert_generic_params function definition AND its use in ir::Function construction.

2. No hardcoded empty vec in convert_mir:
   ```
   grep -n "generic_params: vec!\[\]" \
     /Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/mir_converter.rs
   ```
   Must return NO results (the hardcoded vec![] is gone).

3. Parametric branch is now live:
   The vcgen.rs:290 branch (`if !func.generic_params.is_empty()`) fires for
   driver-produced IR because mir_converter.rs now populates generic_params.

4. Full test suite:
   ```
   cd /Users/alexanderfedin/Projects/hapyy/rust-fv && cargo test --workspace
   ```
   Must exit 0.

5. New test files exist:
   - /Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/tests/generics_e2e.rs
   - /Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/tests/generics_driver_e2e.rs
</verification>

<success_criteria>
1. Function.generic_params is populated for all generic functions processed by the driver.
   A function `fn max<T: Ord>(a: T, b: T) -> T` produces
   `generic_params: [GenericParam { name: "T", trait_bounds: ["Ord"] }]`.

2. The parametric axiom branch in vcgen.rs (lines 285-298) now fires for driver-produced
   generic functions (previously dead code, now activated).

3. All existing tests pass: cargo test --workspace exits 0.

4. New tests in generics_e2e.rs and generics_driver_e2e.rs document and verify the behavior.

5. The code is clean: cargo clippy --workspace has zero errors, cargo fmt --check passes.
</success_criteria>

<output>
After completion, create `/Users/alexanderfedin/Projects/hapyy/rust-fv/.planning/phases/generics-fix/generics-fix-01-SUMMARY.md` with:
- What was implemented
- Files modified and what changed in each
- Test results (cargo test --workspace output summary)
- Any deferred items (MonomorphizationRegistry population from call-sites)
- Commit hash
</output>
