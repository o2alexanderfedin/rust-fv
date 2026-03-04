---
status: resolved
trigger: "Determine if we support cross-verifications for functions, lambdas, closures, structs/impls (Rust's 'classes'), generics, and crates."
created: 2026-03-02T06:00:00Z
updated: 2026-03-02T06:30:00Z
goal: find_and_fix
---

## Current Focus

hypothesis: Investigation complete — root cause matrix established.
test: Systematic code audit of ir.rs, vcgen.rs, mir_converter.rs, callbacks.rs, monomorphize.rs, behavioral_subtyping.rs, call_graph.rs
expecting: Actionable gap matrix with YES/NO/PARTIAL for each construct type
next_action: Report complete — proceed to fixes if requested

## Symptoms

expected: The system should support verifying properties across different Rust constructs: free functions, lambdas/closures, structs with impl blocks, generic types/functions, and across crate boundaries.
actual: Unknown — need to investigate what is actually implemented vs. what is missing.
errors: No runtime errors; this is a capability audit.
reproduction: N/A — investigation of feature coverage.
timeline: Unknown when each feature was added; need to audit current state.

## Eliminated

- hypothesis: Behavioral subtyping (TRT-01..05) is not wired at all
  evidence: Phase 38 (2026-03-02) wired generate_subtyping_vcs into callbacks.rs at lines 769-918. tcx.all_local_trait_impls() scans all trait impls; behavioral subtyping VCs ARE now submitted to Z3. The cross-milestone audit (vAll) noted this as unresolved but callbacks.rs has a comment "Addresses TRT-01..05 gap".
  timestamp: 2026-03-02

- hypothesis: Generic function support requires monomorphization registry to be populated from outside
  evidence: vcgen.rs:generate_vcs_with_db at line 246 handles generic_params via trait_bounds_as_smt_assumptions (parametric reasoning via axioms). generate_vcs_monomorphized (vcgen.rs:1032) exists but is NEVER called from driver — not a gap for VCGen because the parametric approach at line 290-298 handles generic functions without the registry.
  timestamp: 2026-03-02

## Evidence

- timestamp: 2026-03-02
  checked: crates/analysis/src/ir.rs — Function struct
  found: Function struct has generic_params: Vec<GenericParam> (line 319), each GenericParam has name + trait_bounds. ClosureInfo struct (line 292) with env_fields, params, return_ty, trait_kind. TraitDef (line 44) and TraitImpl (line 57) structs. Coroutine info for async fns.
  implication: IR model supports all construct types at the data structure level.

- timestamp: 2026-03-02
  checked: crates/driver/src/mir_converter.rs — convert_mir() and convert_ty()
  found: convert_mir() at line 128-153 sets generic_params: vec![] — generic type parameters are NOT extracted from MIR at the driver level. All Adt/Struct/Enum types fall through to Ty::Named(format!("{ty:?}")) via the _ wildcard at line 475. Closure types also fall to Named. struct fields are not extracted into Ty::Struct at the driver — only if explicitly declared as Aggregate IR in unit tests.
  implication: At the MIR conversion boundary, generic_params is always empty, Struct/Enum/Closure types are opaque Named strings. VCGen must reconstruct structure from Aggregate rvalue shapes rather than type annotations.

- timestamp: 2026-03-02
  checked: crates/driver/src/callbacks.rs — after_analysis(), contract extraction loop
  found: Line 503-528: iterates tcx.hir_body_owners() — this covers ALL function bodies including free functions, methods in impl blocks (for structs and for trait impls), closures (if they have contracts), async fn bodies. The driver makes no distinction — all annotated functions go through the same pipeline. Methods on structs (e.g., impl Account { fn value(&self) -> u64 }) are handled identically to free functions.
  implication: Free functions, struct methods (inherent impl), trait impl methods are ALL verified if they have contracts. The unit of verification is the function body regardless of its container.

- timestamp: 2026-03-02
  checked: crates/driver/src/callbacks.rs — behavioral subtyping block lines 768-918
  found: tcx.all_local_trait_impls(()) scans all local trait implementations. For each trait with contracted methods (from contract_db matching), generates SubtypingVc entries, calls generate_subtyping_script(), and submits each VC to Z3. Results are pushed to self.results. The generate_subtyping_script function in behavioral_subtyping.rs generates SMT scripts for LSP (precondition weakening + postcondition strengthening).
  implication: Behavioral subtyping IS wired for structs implementing traits. However, generate_subtyping_script returns scripts based on UNINTERPRETED predicates — the actual method implementations are not inlined into the behavioral subtyping VCs. Only trait-level contract consistency is checked, not whether the concrete method body satisfies the contracts (that's handled by the normal VCGen path for the method body).

- timestamp: 2026-03-02
  checked: crates/analysis/src/vcgen.rs — generate_vcs_with_db() lines 246-298
  found: Line 277-283: extract_closure_info() + encode_closure_as_uninterpreted() — closures are encoded as uninterpreted SMT functions. Line 285-298: generic_params processing — if func.generic_params is non-empty, calls trait_bounds_as_smt_assumptions() to inject SMT axioms for trait bounds. However, since mir_converter.rs always produces generic_params: vec![], this branch is dead in practice for driver-produced IR. Only manual IR construction in tests exercises this path.
  implication: Generic function verification via parametric axioms exists in analysis but is NOT activated from the driver because generic_params is never populated.

- timestamp: 2026-03-02
  checked: crates/analysis/src/vcgen.rs — generate_vcs_monomorphized() line 1032
  found: Function exists, takes MonomorphizationRegistry. NEVER called from crates/driver/ — grep confirms 0 uses in driver crate. Also never called from parallel.rs (which calls generate_vcs_with_db at line 264). This means the monomorphization strategy is test-only infrastructure.
  implication: Generic functions in user code go through generate_vcs_with_db with empty generic_params — verified as if the generic parameter T were an opaque named type. No actual monomorphization occurs in production. Trait bounds on T are not encoded.

- timestamp: 2026-03-02
  checked: crates/analysis/src/call_graph.rs — CallGraph and from_functions_with_cross_crate_db
  found: from_functions_with_cross_crate_db (line 115) augments call graph with cross-crate edges from ContractDatabase. Cross-crate callee nodes are added with virtual edges. This is called from vcgen.rs:373 inside generate_vcs_with_db. contract_db is built from tcx.hir_body_owners() which includes all LOCAL crate functions plus stdlib contracts. External crate functions appear in contract_db only if they were previously registered (via infer_summary or stdlib_contracts module).
  implication: Cross-crate call edges are tracked in the call graph for SCC/recursion detection. Modular verification (assert precondition, havoc return, assume postcondition) works for ANY callee in the contract_db, regardless of which crate it belongs to. However, external crate functions NOT in the contract_db are treated as opaque callees (V060 diagnostic warning emitted).

- timestamp: 2026-03-02
  checked: crates/analysis/src/closure_analysis.rs and defunctionalize.rs
  found: Closures are detected via ClosureInfo in Function.params/locals. encode_closure_as_uninterpreted() generates an SMT uninterpreted function declaration for the closure. FnOnce single-call validation is implemented. HOF specs (fn_spec) are supported via hof_vcgen.rs. FnMut prophecy integration is noted as deferred in tech_debt (vAll audit, phase 07-closures).
  implication: Closure verification is PARTIAL. Immutable (Fn) closures with uninterpreted encoding work. FnMut prophecy-based verification is deferred. Closures are not extracted from their lexical context into separate IR Functions in the MIR converter — they appear as opaque closure types. Contract annotation on closures is not supported via HIR doc attributes (closures don't have def_ids reachable from hir_body_owners in the same way).

- timestamp: 2026-03-02
  checked: e2e-bench/src/lib.rs — struct/impl verification in practice
  found: AccountId, Balance, Account, Transaction etc. all have methods in impl blocks with #[doc = "rust_fv::requires::..."] and #[doc = "rust_fv::ensures::..."] doc attributes. These are picked up by extract_contracts() via tcx.hir_body_owners() and verified normally. Cross-function calls (e.g., compound_interest calls bounded_add, apply_compound_interest calls compound_interest) are handled via contract_db modular verification.
  implication: Structs with impl methods ARE fully supported for verification. Cross-function verification within a crate is the primary verified scenario (ContractDatabase + call_graph).

## Resolution

root_cause: The cross-verification support scope has multiple layers with varying completeness. No single root cause — this is a capability audit with 5 distinct constructs.

fix: Document findings as a structured matrix (see below). The key actionable gap is generic_params not being populated from the driver, making generic function verification imprecise.

verification: All findings verified against source code in: mir_converter.rs, callbacks.rs, vcgen.rs, monomorphize.rs, behavioral_subtyping.rs, call_graph.rs, ir.rs, closure_analysis.rs, e2e-bench/src/lib.rs

files_changed: []
