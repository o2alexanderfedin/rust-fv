/// Verification callbacks for the rustc driver.
///
/// Implements `rustc_driver::Callbacks` to hook into the compilation
/// pipeline at `after_analysis`, where we have access to:
/// - HIR (for reading annotations/contracts)
/// - MIR (for semantic analysis)
/// - Full type information
/// - Borrow checker results
use rustc_driver::Callbacks;
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;

use crate::diagnostics;
use crate::json_output;
use crate::mir_converter;
use crate::output;

/// Output format for verification results.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutputFormat {
    /// Colored text output (default)
    Text,
    /// Structured JSON output
    Json,
}

/// Result of verifying a single function.
#[derive(Debug)]
pub struct VerificationResult {
    pub function_name: String,
    pub condition: String,
    pub verified: bool,
    pub counterexample: Option<String>,
    #[allow(dead_code)] // Used for future diagnostics enhancement
    pub vc_location: rust_fv_analysis::vcgen::VcLocation,
}

/// Callbacks that perform verification after analysis.
pub struct VerificationCallbacks {
    /// Whether verification is enabled
    enabled: bool,
    /// Collected results
    results: Vec<VerificationResult>,
    /// Output format (Text or Json)
    output_format: OutputFormat,
    /// Structured failure information for diagnostics
    failures: Vec<diagnostics::VerificationFailure>,
    /// Crate name (extracted during after_analysis)
    crate_name: Option<String>,
    /// Number of parallel verification threads
    jobs: usize,
    /// Force re-verification bypassing cache
    fresh: bool,
    /// Apply formula simplification before solver submission
    use_simplification: bool,
    /// Whether to disable stdlib contracts
    no_stdlib_contracts: bool,
    /// Enable verbose output with per-function timing
    #[allow(dead_code)] // Will be used in Task 2
    verbose: bool,
}

impl VerificationCallbacks {
    /// Create callbacks with verification enabled.
    pub fn new(output_format: OutputFormat, jobs: usize, fresh: bool) -> Self {
        // Check for --no-stdlib-contracts environment variable
        let no_stdlib_contracts = std::env::var("RUST_FV_NO_STDLIB_CONTRACTS").is_ok();

        // Check for --verbose flag
        let verbose = std::env::var("RUST_FV_VERBOSE").is_ok();

        Self {
            enabled: true,
            results: Vec::new(),
            output_format,
            failures: Vec::new(),
            crate_name: None,
            jobs,
            fresh,
            use_simplification: true, // Default: enable simplification
            no_stdlib_contracts,
            verbose,
        }
    }

    /// Create callbacks that just pass through (no verification).
    pub fn passthrough() -> Self {
        Self {
            enabled: false,
            results: Vec::new(),
            output_format: OutputFormat::Text,
            failures: Vec::new(),
            crate_name: None,
            jobs: 1,
            fresh: false,
            use_simplification: true,
            no_stdlib_contracts: false,
            verbose: false,
        }
    }

    /// Print verification results to stderr using colored output.
    ///
    /// Groups per-VC results by function name and produces a single
    /// per-function line with OK/FAIL/TIMEOUT status.
    pub fn print_results(&self) {
        let crate_name = self.crate_name.as_deref().unwrap_or("unknown");
        // Group results by function name
        let mut func_map: std::collections::HashMap<String, Vec<&VerificationResult>> =
            std::collections::HashMap::new();
        for result in &self.results {
            func_map
                .entry(result.function_name.clone())
                .or_default()
                .push(result);
        }

        // Convert to FunctionResult entries
        let mut func_results: Vec<output::FunctionResult> = func_map
            .into_iter()
            .map(|(name, vcs)| {
                let vc_count = vcs.len();
                let verified_count = vcs.iter().filter(|r| r.verified).count();
                let all_ok = verified_count == vc_count;

                // Collect first failure message
                let fail_msg = vcs.iter().find(|r| !r.verified).map(|r| {
                    let mut msg = r.condition.clone();
                    if let Some(cx) = &r.counterexample {
                        msg.push_str(&format!(" (counterexample: {cx})"));
                    }
                    msg
                });

                let status = if all_ok {
                    output::VerificationStatus::Ok
                } else if vcs
                    .iter()
                    .any(|r| r.condition.contains("unknown") || r.condition.contains("timeout"))
                {
                    output::VerificationStatus::Timeout
                } else {
                    output::VerificationStatus::Fail
                };

                output::FunctionResult {
                    name,
                    status,
                    message: fail_msg,
                    vc_count,
                    verified_count,
                }
            })
            .collect();

        // Sort by name for deterministic output
        func_results.sort_by(|a, b| a.name.cmp(&b.name));

        match self.output_format {
            OutputFormat::Text => {
                // Print summary table
                output::print_verification_results(&func_results);

                // Print detailed diagnostics for each failure
                for failure in &self.failures {
                    diagnostics::report_verification_failure(failure);
                }
            }
            OutputFormat::Json => {
                // Build JSON report
                let json_functions: Vec<json_output::JsonFunctionResult> = func_results
                    .iter()
                    .map(|fr| {
                        let status_str = match fr.status {
                            output::VerificationStatus::Ok => "ok",
                            output::VerificationStatus::Fail => "fail",
                            output::VerificationStatus::Timeout => "timeout",
                        };

                        // Collect failures for this function
                        let failures: Vec<json_output::JsonFailure> = self
                            .failures
                            .iter()
                            .filter(|f| f.function_name == fr.name)
                            .map(|f| json_output::JsonFailure {
                                vc_kind: vc_kind_to_string(&f.vc_kind),
                                description: f.message.clone(),
                                contract: f.contract_text.clone(),
                                source_file: f.source_file.clone(),
                                source_line: f.source_line,
                                counterexample: f.counterexample.as_ref().map(|cx| {
                                    cx.iter()
                                        .map(|(k, v)| json_output::JsonAssignment {
                                            variable: k.clone(),
                                            value: v.clone(),
                                        })
                                        .collect()
                                }),
                                suggestion: diagnostics::suggest_fix(&f.vc_kind),
                            })
                            .collect();

                        json_output::JsonFunctionResult {
                            name: fr.name.clone(),
                            status: status_str.to_string(),
                            vc_count: fr.vc_count,
                            verified_count: fr.verified_count,
                            failures,
                        }
                    })
                    .collect();

                let summary = json_output::JsonSummary {
                    total: func_results.len(),
                    ok: func_results
                        .iter()
                        .filter(|r| r.status == output::VerificationStatus::Ok)
                        .count(),
                    fail: func_results
                        .iter()
                        .filter(|r| r.status == output::VerificationStatus::Fail)
                        .count(),
                    timeout: func_results
                        .iter()
                        .filter(|r| r.status == output::VerificationStatus::Timeout)
                        .count(),
                };

                let report = json_output::JsonVerificationReport {
                    crate_name: crate_name.to_string(),
                    functions: json_functions,
                    summary,
                };

                json_output::print_json_report(&report);
            }
        }
    }
}

impl Callbacks for VerificationCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        if !self.enabled {
            return rustc_driver::Compilation::Continue;
        }

        // Extract crate name
        self.crate_name = Some(tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string());

        // Only print progress messages in Text mode (suppress in JSON mode)
        if self.output_format == OutputFormat::Text {
            eprintln!("[rust-fv] Running formal verification...");
        }

        // Extract contracts from HIR attributes
        let contracts_map = extract_contracts(tcx);

        // Build the contract database for inter-procedural verification
        let mut contract_db = rust_fv_analysis::contract_db::ContractDatabase::new();
        for (&local_def_id, contracts) in &contracts_map {
            let def_id = local_def_id.to_def_id();
            let name = tcx.def_path_str(def_id);
            let mir = tcx.optimized_mir(def_id);

            // Extract param names and types from MIR
            let params: Vec<_> = mir
                .args_iter()
                .map(|local| {
                    let decl = &mir.local_decls[local];
                    (
                        format!("_{}", local.as_usize()),
                        mir_converter::convert_ty(decl.ty),
                    )
                })
                .collect();

            let return_ty =
                mir_converter::convert_ty(mir.local_decls[rustc_middle::mir::Local::ZERO].ty);

            contract_db.insert(
                name,
                rust_fv_analysis::contract_db::FunctionSummary {
                    contracts: contracts.clone(),
                    param_names: params.iter().map(|(n, _)| n.clone()).collect(),
                    param_types: params.iter().map(|(_, t)| t.clone()).collect(),
                    return_ty,
                },
            );
        }

        // Load stdlib contracts unless disabled
        if !self.no_stdlib_contracts {
            let stdlib_registry =
                rust_fv_analysis::stdlib_contracts::loader::load_default_contracts();
            stdlib_registry.merge_into(&mut contract_db);
        }

        // Determine cache directory (target/verify-cache/)
        let cache_dir = std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
        let cache_path = std::path::PathBuf::from(cache_dir).join("verify-cache");

        // Load cache
        let mut cache = crate::cache::VcCache::new(cache_path);
        cache.load();

        // Note: --fresh no longer clears cache, it just bypasses it for this run
        // Cache files remain on disk for future runs

        // Collect all functions to verify
        let mut func_infos = Vec::new();

        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            let name = tcx.def_path_str(def_id);

            // Check if this function has any contracts
            let contracts = contracts_map.get(&local_def_id);
            let has_contracts =
                contracts.is_some_and(|c| !c.requires.is_empty() || !c.ensures.is_empty());

            // Skip functions without contracts
            if !has_contracts {
                continue;
            }

            // Get the optimized MIR
            let mir = tcx.optimized_mir(def_id);

            // Convert rustc MIR to our IR
            let ir_func = mir_converter::convert_mir(
                tcx,
                local_def_id,
                mir,
                contracts.cloned().unwrap_or_default(),
            );

            func_infos.push((name.clone(), ir_func));
        }

        // Build call graph
        let call_graph = rust_fv_analysis::call_graph::CallGraph::from_functions(
            &func_infos
                .iter()
                .map(|(n, f)| (n.clone(), f))
                .collect::<Vec<_>>(),
        );

        // Compute per-function hashes and dependencies
        let mut func_hashes = std::collections::HashMap::new();
        for (name, ir_func) in &func_infos {
            let ir_debug = format!("{:?}", ir_func);
            let mir_hash = crate::cache::VcCache::compute_mir_hash(name, &ir_debug);
            let contract_hash = crate::cache::VcCache::compute_contract_hash(name, &ir_func.contracts);
            func_hashes.insert(name.clone(), (mir_hash, contract_hash));
        }

        // Determine which functions have changed contracts
        let all_funcs_with_hashes: Vec<_> = func_hashes
            .iter()
            .map(|(name, (_mir_hash, contract_hash))| (name.clone(), *contract_hash))
            .collect();
        let changed_contracts = call_graph.changed_contract_functions(
            &all_funcs_with_hashes,
            |func_name: &str| {
                let contracts = rust_fv_analysis::ir::Contracts::default();
                #[allow(deprecated)]
                let key = crate::cache::VcCache::compute_key(func_name, &contracts, "");
                cache.get(&key).map(|entry| entry.contract_hash)
            },
        );

        // Build verification tasks with invalidation decisions
        let mut tasks = Vec::new();
        for (name, ir_func) in func_infos {
            let (mir_hash, contract_hash) = func_hashes.get(&name).unwrap();

            // Compute legacy cache key for backward compatibility
            let ir_debug = format!("{:?}", ir_func);
            #[allow(deprecated)]
            let cache_key = crate::cache::VcCache::compute_key(&name, &ir_func.contracts, &ir_debug);

            // Get direct dependencies
            let dependencies = call_graph.direct_callees(&name);

            // Decide whether to verify this function
            let invalidation_decision = crate::invalidation::decide_verification(
                &cache,
                &name,
                *mir_hash,
                *contract_hash,
                self.fresh,
                &changed_contracts,
                &dependencies,
            );

            tasks.push(crate::parallel::VerificationTask {
                name: name.clone(),
                ir_func,
                contract_db: std::sync::Arc::new(contract_db.clone()),
                cache_key,
                mir_hash: *mir_hash,
                contract_hash: *contract_hash,
                dependencies,
                invalidation_decision,
            });
        }

        // Sort tasks by topological order for bottom-up verification
        let topo_order = call_graph.topological_order();

        // Sort tasks by topological order
        tasks.sort_by_key(|task| {
            topo_order
                .iter()
                .position(|n| n == &task.name)
                .unwrap_or(usize::MAX)
        });

        if self.output_format == OutputFormat::Text {
            eprintln!(
                "[rust-fv] Verifying {} functions ({} parallel threads)...",
                tasks.len(),
                self.jobs
            );
        }

        // Run parallel verification
        let task_results = crate::parallel::verify_functions_parallel(
            tasks,
            &mut cache,
            self.jobs,
            self.fresh,
            self.use_simplification,
        );

        // Collect results and failures
        for task_result in task_results {
            for result in task_result.results {
                // Build structured failure if this VC failed
                if !result.verified
                    && result.vc_location.vc_kind != rust_fv_analysis::vcgen::VcKind::Postcondition
                {
                    // Parse counterexample string back into map
                    let counterexample = result.counterexample.as_ref().map(|cx_str| {
                        cx_str
                            .split(", ")
                            .filter_map(|s| {
                                let parts: Vec<_> = s.split(" = ").collect();
                                if parts.len() == 2 {
                                    Some((parts[0].to_string(), parts[1].to_string()))
                                } else {
                                    None
                                }
                            })
                            .collect()
                    });

                    self.failures.push(diagnostics::VerificationFailure {
                        function_name: result.function_name.clone(),
                        vc_kind: result.vc_location.vc_kind.clone(),
                        contract_text: result.vc_location.contract_text.clone(),
                        source_file: result.vc_location.source_file.clone(),
                        source_line: result.vc_location.source_line,
                        counterexample,
                        message: result.condition.clone(),
                    });
                }

                self.results.push(result);
            }
        }

        rustc_driver::Compilation::Stop // stop before codegen — we only verify, don't compile
    }
}

/// Contract information extracted from HIR attributes.
#[derive(Debug, Clone, Default)]
struct HirContracts {
    requires: Vec<String>,
    ensures: Vec<String>,
    invariants: Vec<String>,
    is_pure: bool,
    decreases: Option<String>,
}

/// Extract contracts from HIR doc attributes.
///
/// Our proc macros store specs as `#[doc = "rust_fv::requires::SPEC"]`.
/// We scan all function items for these hidden doc attributes.
fn extract_contracts(
    tcx: TyCtxt<'_>,
) -> std::collections::HashMap<rustc_hir::def_id::LocalDefId, rust_fv_analysis::ir::Contracts> {
    let mut map = std::collections::HashMap::new();

    for local_def_id in tcx.hir_body_owners() {
        let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
        let attrs = tcx.hir_attrs(hir_id);

        let mut contracts = HirContracts::default();

        for attr in attrs {
            if let Some(doc) = extract_doc_value(attr) {
                if let Some(spec) = doc.strip_prefix("rust_fv::requires::") {
                    contracts.requires.push(spec.to_string());
                } else if let Some(spec) = doc.strip_prefix("rust_fv::ensures::") {
                    contracts.ensures.push(spec.to_string());
                } else if let Some(spec) = doc.strip_prefix("rust_fv::invariant::") {
                    contracts.invariants.push(spec.to_string());
                } else if let Some(spec) = doc.strip_prefix("rust_fv::decreases::") {
                    contracts.decreases = Some(spec.to_string());
                } else if doc == "rust_fv::pure" {
                    contracts.is_pure = true;
                }
            }
        }

        if !contracts.requires.is_empty()
            || !contracts.ensures.is_empty()
            || !contracts.invariants.is_empty()
            || contracts.is_pure
            || contracts.decreases.is_some()
        {
            map.insert(
                local_def_id,
                rust_fv_analysis::ir::Contracts {
                    requires: contracts
                        .requires
                        .into_iter()
                        .map(|raw| rust_fv_analysis::ir::SpecExpr { raw })
                        .collect(),
                    ensures: contracts
                        .ensures
                        .into_iter()
                        .map(|raw| rust_fv_analysis::ir::SpecExpr { raw })
                        .collect(),
                    invariants: contracts
                        .invariants
                        .into_iter()
                        .map(|raw| rust_fv_analysis::ir::SpecExpr { raw })
                        .collect(),
                    is_pure: contracts.is_pure,
                    decreases: contracts
                        .decreases
                        .map(|raw| rust_fv_analysis::ir::SpecExpr { raw }),
                },
            );
        }
    }

    map
}

/// Extract the string value from a `#[doc = "..."]` attribute.
///
/// In nightly 1.95.0, `Attribute` is an enum with `Parsed` and `Unparsed` variants.
/// Doc comments become `Parsed(AttributeKind::DocComment { .. })`.
/// `#[doc = "..."]` may be either parsed or unparsed.
/// We use the `doc_str()` and `value_str()` methods from `AttributeExt`.
fn extract_doc_value(attr: &rustc_hir::Attribute) -> Option<String> {
    // Case 1: Doc comments (/// or /**/) parsed into AttributeKind::DocComment
    if let Some(symbol) = attr.doc_str() {
        return Some(symbol.to_string());
    }
    // Case 2: #[doc = "..."] that remains as Unparsed
    if attr.has_name(rustc_span::sym::doc)
        && let Some(value) = attr.value_str()
    {
        return Some(value.to_string());
    }
    None
}

/// Convert VcKind to a JSON-friendly string.
fn vc_kind_to_string(vc_kind: &rust_fv_analysis::vcgen::VcKind) -> String {
    use rust_fv_analysis::vcgen::VcKind;
    match vc_kind {
        VcKind::Precondition => "precondition",
        VcKind::Postcondition => "postcondition",
        VcKind::LoopInvariantInit => "loop_invariant_init",
        VcKind::LoopInvariantPreserve => "loop_invariant_preserve",
        VcKind::LoopInvariantExit => "loop_invariant_exit",
        VcKind::Overflow => "overflow",
        VcKind::DivisionByZero => "division_by_zero",
        VcKind::ShiftBounds => "shift_bounds",
        VcKind::Assertion => "assertion",
        VcKind::PanicFreedom => "panic_freedom",
        VcKind::Termination => "termination",
        VcKind::ClosureContract => "closure_contract",
        VcKind::BehavioralSubtyping => "behavioral_subtyping",
        VcKind::BorrowValidity => "borrow_validity",
        VcKind::MemorySafety => "memory_safety",
        VcKind::FloatingPointNaN => "floating_point_nan",
        VcKind::DataRaceFreedom => "data_race_freedom",
        VcKind::LockInvariant => "lock_invariant",
        VcKind::Deadlock => "deadlock",
        VcKind::ChannelSafety => "channel_safety",
    }
    .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_fv_analysis::vcgen::VcKind;

    // --- OutputFormat tests ---

    #[test]
    fn test_output_format_text() {
        let fmt = OutputFormat::Text;
        assert_eq!(fmt, OutputFormat::Text);
    }

    #[test]
    fn test_output_format_json() {
        let fmt = OutputFormat::Json;
        assert_eq!(fmt, OutputFormat::Json);
    }

    #[test]
    fn test_output_format_ne() {
        assert_ne!(OutputFormat::Text, OutputFormat::Json);
    }

    #[test]
    fn test_output_format_clone() {
        let fmt = OutputFormat::Json;
        let cloned = fmt;
        assert_eq!(fmt, cloned);
    }

    #[test]
    fn test_output_format_debug() {
        assert_eq!(format!("{:?}", OutputFormat::Text), "Text");
        assert_eq!(format!("{:?}", OutputFormat::Json), "Json");
    }

    // --- VerificationCallbacks::new tests ---

    #[test]
    fn test_callbacks_new_text() {
        let cb = VerificationCallbacks::new(OutputFormat::Text, 4, false);
        assert!(cb.enabled);
        assert_eq!(cb.output_format, OutputFormat::Text);
        assert_eq!(cb.jobs, 4);
        assert!(!cb.fresh);
        assert!(cb.results.is_empty());
        assert!(cb.failures.is_empty());
        assert!(cb.crate_name.is_none());
        assert!(cb.use_simplification);
    }

    #[test]
    fn test_callbacks_new_json() {
        let cb = VerificationCallbacks::new(OutputFormat::Json, 8, true);
        assert!(cb.enabled);
        assert_eq!(cb.output_format, OutputFormat::Json);
        assert_eq!(cb.jobs, 8);
        assert!(cb.fresh);
    }

    #[test]
    fn test_callbacks_new_single_job() {
        let cb = VerificationCallbacks::new(OutputFormat::Text, 1, false);
        assert_eq!(cb.jobs, 1);
    }

    // --- VerificationCallbacks::passthrough tests ---

    #[test]
    fn test_callbacks_passthrough() {
        let cb = VerificationCallbacks::passthrough();
        assert!(!cb.enabled);
        assert_eq!(cb.output_format, OutputFormat::Text);
        assert_eq!(cb.jobs, 1);
        assert!(!cb.fresh);
        assert!(cb.results.is_empty());
        assert!(cb.failures.is_empty());
        assert!(cb.crate_name.is_none());
        assert!(cb.use_simplification);
        assert!(!cb.verbose);
    }

    #[test]
    fn test_callbacks_verbose_flag() {
        // Verbose is false by default
        let cb = VerificationCallbacks::new(OutputFormat::Text, 4, false);
        assert!(!cb.verbose);

        // Test with RUST_FV_VERBOSE set
        unsafe {
            std::env::set_var("RUST_FV_VERBOSE", "1");
        }
        let cb_verbose = VerificationCallbacks::new(OutputFormat::Json, 2, true);
        assert!(cb_verbose.verbose);
        unsafe {
            std::env::remove_var("RUST_FV_VERBOSE");
        }
    }

    // --- vc_kind_to_string tests ---

    #[test]
    fn test_vc_kind_to_string_precondition() {
        assert_eq!(vc_kind_to_string(&VcKind::Precondition), "precondition");
    }

    #[test]
    fn test_vc_kind_to_string_postcondition() {
        assert_eq!(vc_kind_to_string(&VcKind::Postcondition), "postcondition");
    }

    #[test]
    fn test_vc_kind_to_string_loop_invariant_init() {
        assert_eq!(
            vc_kind_to_string(&VcKind::LoopInvariantInit),
            "loop_invariant_init"
        );
    }

    #[test]
    fn test_vc_kind_to_string_loop_invariant_preserve() {
        assert_eq!(
            vc_kind_to_string(&VcKind::LoopInvariantPreserve),
            "loop_invariant_preserve"
        );
    }

    #[test]
    fn test_vc_kind_to_string_loop_invariant_exit() {
        assert_eq!(
            vc_kind_to_string(&VcKind::LoopInvariantExit),
            "loop_invariant_exit"
        );
    }

    #[test]
    fn test_vc_kind_to_string_overflow() {
        assert_eq!(vc_kind_to_string(&VcKind::Overflow), "overflow");
    }

    #[test]
    fn test_vc_kind_to_string_division_by_zero() {
        assert_eq!(
            vc_kind_to_string(&VcKind::DivisionByZero),
            "division_by_zero"
        );
    }

    #[test]
    fn test_vc_kind_to_string_shift_bounds() {
        assert_eq!(vc_kind_to_string(&VcKind::ShiftBounds), "shift_bounds");
    }

    #[test]
    fn test_vc_kind_to_string_assertion() {
        assert_eq!(vc_kind_to_string(&VcKind::Assertion), "assertion");
    }

    #[test]
    fn test_vc_kind_to_string_panic_freedom() {
        assert_eq!(vc_kind_to_string(&VcKind::PanicFreedom), "panic_freedom");
    }

    #[test]
    fn test_vc_kind_to_string_termination() {
        assert_eq!(vc_kind_to_string(&VcKind::Termination), "termination");
    }

    #[test]
    fn test_vc_kind_to_string_closure_contract() {
        assert_eq!(
            vc_kind_to_string(&VcKind::ClosureContract),
            "closure_contract"
        );
    }

    #[test]
    fn test_vc_kind_to_string_behavioral_subtyping() {
        assert_eq!(
            vc_kind_to_string(&VcKind::BehavioralSubtyping),
            "behavioral_subtyping"
        );
    }

    #[test]
    fn test_vc_kind_to_string_borrow_validity() {
        assert_eq!(
            vc_kind_to_string(&VcKind::BorrowValidity),
            "borrow_validity"
        );
    }

    #[test]
    fn test_vc_kind_to_string_memory_safety() {
        assert_eq!(vc_kind_to_string(&VcKind::MemorySafety), "memory_safety");
    }

    #[test]
    fn test_vc_kind_to_string_floating_point_nan() {
        assert_eq!(
            vc_kind_to_string(&VcKind::FloatingPointNaN),
            "floating_point_nan"
        );
    }

    // --- VerificationResult tests (struct construction) ---

    #[test]
    fn test_verification_result_construction() {
        let result = VerificationResult {
            function_name: "test_fn".to_string(),
            condition: "postcondition: result > 0".to_string(),
            verified: true,
            counterexample: None,
            vc_location: rust_fv_analysis::vcgen::VcLocation {
                function: "test_fn".to_string(),
                block: 0,
                statement: 0,
                source_file: None,
                source_line: None,
                contract_text: None,
                vc_kind: VcKind::Postcondition,
            },
        };
        assert_eq!(result.function_name, "test_fn");
        assert!(result.verified);
        assert!(result.counterexample.is_none());
    }

    #[test]
    fn test_verification_result_with_counterexample() {
        let result = VerificationResult {
            function_name: "div".to_string(),
            condition: "division by zero".to_string(),
            verified: false,
            counterexample: Some("b = 0".to_string()),
            vc_location: rust_fv_analysis::vcgen::VcLocation {
                function: "div".to_string(),
                block: 1,
                statement: 2,
                source_file: Some("src/lib.rs".to_string()),
                source_line: Some(42),
                contract_text: Some("b != 0".to_string()),
                vc_kind: VcKind::DivisionByZero,
            },
        };
        assert!(!result.verified);
        assert_eq!(result.counterexample.as_deref(), Some("b = 0"));
        assert_eq!(
            result.vc_location.source_file.as_deref(),
            Some("src/lib.rs")
        );
        assert_eq!(result.vc_location.source_line, Some(42));
    }

    // --- print_results with no results should not panic ---

    #[test]
    fn test_print_results_empty() {
        let cb = VerificationCallbacks::passthrough();
        cb.print_results(); // Should not panic
    }
}
