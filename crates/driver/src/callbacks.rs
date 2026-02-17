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

use rust_fv_analysis::differential::{SolverInterface, VcOutcome};
use rust_fv_smtlib::script::Script;

use crate::diagnostics;
use crate::json_output;
use crate::mir_converter;
use crate::output;

/// Adapter that wraps the Z3 CLI solver to implement `SolverInterface`.
///
/// Used by `test_encoding_equivalence` to run both bitvector and integer
/// VCs through the same solver and compare outcomes.
struct Z3SolverAdapter {
    solver: rust_fv_solver::Z3Solver,
}

impl Z3SolverAdapter {
    /// Create a new adapter, returning None if the solver cannot be initialized.
    fn try_new() -> Option<Self> {
        rust_fv_solver::Z3Solver::with_default_config()
            .ok()
            .map(|solver| Self { solver })
    }
}

impl SolverInterface for Z3SolverAdapter {
    fn check(&self, script: &Script) -> VcOutcome {
        let script_text = script.to_string();
        match self.solver.check_sat_raw(&script_text) {
            Ok(rust_fv_solver::SolverResult::Unsat) => VcOutcome::Unsat,
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
            Ok(rust_fv_solver::SolverResult::Unknown(_)) | Err(_) => VcOutcome::Unknown,
        }
    }
}

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

/// Metadata for per-function verification.
#[derive(Debug, Clone)]
struct FunctionMetadata {
    invalidation_reason: Option<crate::invalidation::InvalidationReason>,
    duration_ms: Option<u64>,
    from_cache: bool,
}

/// Per-function bv2int result collected during verification.
#[derive(Debug, Clone)]
pub struct Bv2intFunctionRecord {
    /// Function name
    pub func_name: String,
    /// Whether the function was eligible for bv2int
    pub eligible: bool,
    /// Reason ineligible (None if eligible)
    pub skip_reason: Option<String>,
    /// Whether bv2int encoding was actually used
    pub bv2int_used: bool,
    /// Bitvector encoding time in ms (Some when timing available)
    pub bitvec_time_ms: Option<u64>,
    /// Integer encoding time in ms (Some when timing available)
    pub bv2int_time_ms: Option<u64>,
    /// Speedup factor (bv_time / int_time; >1.0 means faster with bv2int)
    pub speedup_factor: Option<f64>,
}

/// Callbacks that perform verification after analysis.
pub struct VerificationCallbacks {
    /// Whether verification is enabled
    enabled: bool,
    /// Collected results
    results: Vec<VerificationResult>,
    /// Per-function metadata (invalidation reasons, timing)
    func_metadata: std::collections::HashMap<String, FunctionMetadata>,
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
    verbose: bool,
    /// Enable bv2int optimization mode
    bv2int_enabled: bool,
    /// Show bv2int summary report after verification
    bv2int_report: bool,
    /// Slowdown warning threshold (warn when bv2int is >N times slower)
    bv2int_threshold: f64,
    /// Per-function bv2int results (populated when bv2int_enabled or bv2int_report)
    bv2int_records: Vec<Bv2intFunctionRecord>,
}

impl VerificationCallbacks {
    /// Create callbacks with verification enabled.
    pub fn new(output_format: OutputFormat, jobs: usize, fresh: bool) -> Self {
        // Check for --no-stdlib-contracts environment variable
        let no_stdlib_contracts = std::env::var("RUST_FV_NO_STDLIB_CONTRACTS").is_ok();

        // Check for --verbose flag
        let verbose = std::env::var("RUST_FV_VERBOSE").is_ok();

        // Check for bv2int flags (set by cargo_verify via env vars)
        let bv2int_enabled = std::env::var("RUST_FV_BV2INT")
            .map(|v| v == "1")
            .unwrap_or(false);
        let bv2int_report = std::env::var("RUST_FV_BV2INT_REPORT")
            .map(|v| v == "1")
            .unwrap_or(false);
        let bv2int_threshold = std::env::var("RUST_FV_BV2INT_THRESHOLD")
            .ok()
            .and_then(|v| v.parse::<f64>().ok())
            .unwrap_or(2.0);

        Self {
            enabled: true,
            results: Vec::new(),
            func_metadata: std::collections::HashMap::new(),
            output_format,
            failures: Vec::new(),
            crate_name: None,
            jobs,
            fresh,
            use_simplification: true, // Default: enable simplification
            no_stdlib_contracts,
            verbose,
            bv2int_enabled,
            bv2int_report,
            bv2int_threshold,
            bv2int_records: Vec::new(),
        }
    }

    /// Create callbacks that just pass through (no verification).
    pub fn passthrough() -> Self {
        Self {
            enabled: false,
            results: Vec::new(),
            func_metadata: std::collections::HashMap::new(),
            output_format: OutputFormat::Text,
            failures: Vec::new(),
            crate_name: None,
            jobs: 1,
            fresh: false,
            use_simplification: true,
            no_stdlib_contracts: false,
            verbose: false,
            bv2int_enabled: false,
            bv2int_report: false,
            bv2int_threshold: 2.0,
            bv2int_records: Vec::new(),
        }
    }

    /// Print verification results to stderr using colored output.
    ///
    /// Groups per-VC results by function name and produces a single
    /// per-function line with OK/FAIL/TIMEOUT/SKIP status.
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

                // Get metadata for this function
                let metadata = self.func_metadata.get(&name);
                let is_cached = metadata.map(|m| m.from_cache).unwrap_or(false);
                let duration_ms = metadata.and_then(|m| m.duration_ms);

                // Map invalidation reason to human-readable string
                let invalidation_reason = metadata.and_then(|m| {
                    m.invalidation_reason.as_ref().map(|reason| {
                        use crate::invalidation::InvalidationReason;
                        match reason {
                            InvalidationReason::MirChanged => "body changed".to_string(),
                            InvalidationReason::ContractChanged { dependency } => {
                                format!("contract of {} changed", dependency)
                            }
                            InvalidationReason::Fresh => "fresh run".to_string(),
                            InvalidationReason::CacheMiss => "not in cache".to_string(),
                            InvalidationReason::Expired => "cache expired".to_string(),
                        }
                    })
                });

                // Collect first failure message
                let fail_msg = vcs.iter().find(|r| !r.verified).map(|r| {
                    let mut msg = r.condition.clone();
                    if let Some(cx) = &r.counterexample {
                        msg.push_str(&format!(" (counterexample: {cx})"));
                    }
                    msg
                });

                let status = if is_cached {
                    output::VerificationStatus::Skipped
                } else if all_ok {
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
                    invalidation_reason,
                    duration_ms,
                }
            })
            .collect();

        // Sort by name for deterministic output
        func_results.sort_by(|a, b| a.name.cmp(&b.name));

        match self.output_format {
            OutputFormat::Text => {
                // Print summary table with verbose flag
                output::print_verification_results(&func_results, self.verbose);

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
                            output::VerificationStatus::Skipped => "skipped",
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
            let contract_hash =
                crate::cache::VcCache::compute_contract_hash(name, &ir_func.contracts);
            func_hashes.insert(name.clone(), (mir_hash, contract_hash));
        }

        // Determine which functions have changed contracts
        let all_funcs_with_hashes: Vec<_> = func_hashes
            .iter()
            .map(|(name, (_mir_hash, contract_hash))| (name.clone(), *contract_hash))
            .collect();
        let changed_contracts =
            call_graph.changed_contract_functions(&all_funcs_with_hashes, |func_name: &str| {
                let contracts = rust_fv_analysis::ir::Contracts::default();
                #[allow(deprecated)]
                let key = crate::cache::VcCache::compute_key(func_name, &contracts, "");
                cache.get(&key).map(|entry| entry.contract_hash)
            });

        // Perform bv2int eligibility analysis and differential testing when enabled.
        // When --bv2int-report requested without --bv2int: emit candidate list.
        // When --bv2int enabled: check per-function eligibility, emit warnings for
        // ineligible functions, and record equivalence results.
        if self.bv2int_enabled || self.bv2int_report {
            for (name, ir_func) in &func_infos {
                match rust_fv_analysis::bv2int::is_bv2int_eligible(ir_func) {
                    Ok(()) => {
                        // Eligible — run differential test if bv2int enabled and solver available
                        let (bitvec_time_ms, bv2int_time_ms, speedup_factor) =
                            if self.bv2int_enabled {
                                run_differential_test(name, ir_func, &contract_db)
                            } else {
                                (None, None, None)
                            };

                        // Report divergence if detected (speedup None with divergence logged)
                        self.bv2int_records.push(Bv2intFunctionRecord {
                            func_name: name.clone(),
                            eligible: true,
                            skip_reason: None,
                            bv2int_used: self.bv2int_enabled,
                            bitvec_time_ms,
                            bv2int_time_ms,
                            speedup_factor,
                        });
                    }
                    Err(reason) => {
                        // Ineligible — emit warning when bv2int explicitly requested
                        if self.bv2int_enabled && self.output_format == OutputFormat::Text {
                            diagnostics::report_bv2int_ineligibility(name, &reason.to_string());
                        }
                        self.bv2int_records.push(Bv2intFunctionRecord {
                            func_name: name.clone(),
                            eligible: false,
                            skip_reason: Some(reason.to_string()),
                            bv2int_used: false,
                            bitvec_time_ms: None,
                            bv2int_time_ms: None,
                            speedup_factor: None,
                        });
                    }
                }
            }

            // When --bv2int-report is requested without --bv2int: print candidate list
            if self.bv2int_report && !self.bv2int_enabled {
                let eligible: Vec<&str> = self
                    .bv2int_records
                    .iter()
                    .filter(|r| r.eligible)
                    .map(|r| r.func_name.as_str())
                    .collect();
                let ineligible: Vec<(&str, &str)> = self
                    .bv2int_records
                    .iter()
                    .filter(|r| !r.eligible)
                    .map(|r| (r.func_name.as_str(), r.skip_reason.as_deref().unwrap_or("")))
                    .collect();

                eprintln!();
                eprintln!("[rust-fv] bv2int candidates (eligible based on static analysis):");
                if eligible.is_empty() {
                    eprintln!("  (no eligible functions found)");
                } else {
                    eprintln!("  eligible: {}", eligible.join(", "));
                    eprintln!(
                        "  (use --bv2int to enable: cargo verify --bv2int {})",
                        eligible.join(", ")
                    );
                }
                if !ineligible.is_empty() {
                    eprintln!("  ineligible:");
                    for (name, reason) in &ineligible {
                        eprintln!("    {}: {}", name, reason);
                    }
                }
                eprintln!();
            }
        }

        // Build verification tasks with invalidation decisions
        let mut tasks = Vec::new();
        for (name, ir_func) in func_infos.into_iter() {
            let (mir_hash, contract_hash) = func_hashes.get(&name).unwrap();

            // Compute legacy cache key for backward compatibility
            let ir_debug = format!("{:?}", ir_func);
            #[allow(deprecated)]
            let cache_key =
                crate::cache::VcCache::compute_key(&name, &ir_func.contracts, &ir_debug);

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
            // Store per-function metadata
            self.func_metadata.insert(
                task_result.name.clone(),
                FunctionMetadata {
                    invalidation_reason: task_result.invalidation_reason.clone(),
                    duration_ms: task_result.duration_ms,
                    from_cache: task_result.from_cache,
                },
            );

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

        // Emit bv2int timing info and report when --bv2int is active
        if self.bv2int_enabled && self.output_format == OutputFormat::Text {
            for record in &self.bv2int_records {
                if record.eligible
                    && record.bv2int_used
                    && let (Some(bv_ms), Some(int_ms)) =
                        (record.bitvec_time_ms, record.bv2int_time_ms)
                {
                    // Use output module's formatted timing display
                    eprintln!(
                        "{}",
                        output::format_bv2int_timing(&record.func_name, bv_ms, int_ms)
                    );
                    // Check and emit slowdown warning
                    let speedup = record.speedup_factor.unwrap_or(1.0);
                    if let Some(warning) = output::check_slowdown_warning(
                        &record.func_name,
                        speedup,
                        self.bv2int_threshold,
                    ) {
                        eprintln!("{warning}");
                    }
                }
            }
        }

        // Emit full bv2int report table when --bv2int-report is set with --bv2int
        if self.bv2int_report && self.bv2int_enabled && self.output_format == OutputFormat::Text {
            crate::output::print_bv2int_report(&self.bv2int_records);
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

/// Run differential equivalence test for a single eligible function.
///
/// Generates VCs in both bitvector and integer modes, then runs them
/// through Z3 to compare outcomes and collect timing.
///
/// Returns `(bitvec_time_ms, bv2int_time_ms, speedup_factor)` when a solver
/// is available, or `(None, None, None)` when Z3 is not found.
fn run_differential_test(
    name: &str,
    ir_func: &rust_fv_analysis::ir::Function,
    contract_db: &rust_fv_analysis::contract_db::ContractDatabase,
) -> (Option<u64>, Option<u64>, Option<f64>) {
    use rust_fv_analysis::bv2int::EncodingMode;

    // Try to create a solver; gracefully degrade when Z3 is unavailable.
    let Some(adapter) = Z3SolverAdapter::try_new() else {
        return (None, None, None);
    };

    // Generate VCs in both modes
    let bv_vcs = rust_fv_analysis::vcgen::generate_vcs_with_mode(
        ir_func,
        Some(contract_db),
        EncodingMode::Bitvector,
    );
    let int_vcs = rust_fv_analysis::vcgen::generate_vcs_with_mode(
        ir_func,
        Some(contract_db),
        EncodingMode::Integer,
    );

    let bv_scripts: Vec<_> = bv_vcs
        .conditions
        .iter()
        .map(|vc| vc.script.clone())
        .collect();
    let int_scripts: Vec<_> = int_vcs
        .conditions
        .iter()
        .map(|vc| vc.script.clone())
        .collect();

    let result = rust_fv_analysis::differential::test_encoding_equivalence(
        name,
        &bv_scripts,
        &int_scripts,
        &adapter,
    );

    if !result.equivalent {
        let bv_str = if result.bitvec_time_ms > 0 {
            "SAT/UNSAT"
        } else {
            "unknown"
        };
        let int_str = if result.bv2int_time_ms > 0 {
            "SAT/UNSAT"
        } else {
            "unknown"
        };
        diagnostics::report_bv2int_divergence(
            name,
            bv_str,
            int_str,
            result.counterexample.as_deref(),
        );
        // Return timing even for divergent results (useful for analysis)
        return (
            Some(result.bitvec_time_ms),
            Some(result.bv2int_time_ms),
            Some(result.speedup_factor),
        );
    }

    (
        Some(result.bitvec_time_ms),
        Some(result.bv2int_time_ms),
        Some(result.speedup_factor),
    )
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
