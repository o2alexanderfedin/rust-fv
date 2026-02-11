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

use crate::mir_converter;
use crate::output;

/// Result of verifying a single function.
#[derive(Debug)]
pub struct VerificationResult {
    pub function_name: String,
    pub condition: String,
    pub verified: bool,
    pub counterexample: Option<String>,
}

/// Callbacks that perform verification after analysis.
pub struct VerificationCallbacks {
    /// Whether verification is enabled
    enabled: bool,
    /// Collected results
    results: Vec<VerificationResult>,
}

impl VerificationCallbacks {
    /// Create callbacks with verification enabled.
    pub fn new() -> Self {
        Self {
            enabled: true,
            results: Vec::new(),
        }
    }

    /// Create callbacks that just pass through (no verification).
    pub fn passthrough() -> Self {
        Self {
            enabled: false,
            results: Vec::new(),
        }
    }

    /// Print verification results to stderr using colored output.
    ///
    /// Groups per-VC results by function name and produces a single
    /// per-function line with OK/FAIL/TIMEOUT status.
    pub fn print_results(&self) {
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

        output::print_verification_results(&func_results);
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

        eprintln!("[rust-fv] Running formal verification...");

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

        // Find the Z3 solver
        let solver = match rust_fv_solver::Z3Solver::with_default_config() {
            Ok(s) => s,
            Err(e) => {
                eprintln!("[rust-fv] Error: Could not find Z3 solver: {e}");
                return rustc_driver::Compilation::Continue;
            }
        };

        // Iterate over all function bodies
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            let name = tcx.def_path_str(def_id);

            // Check if this function has any contracts
            let contracts = contracts_map.get(&local_def_id);
            let has_contracts =
                contracts.is_some_and(|c| !c.requires.is_empty() || !c.ensures.is_empty());

            // Skip functions without contracts (for now)
            if !has_contracts {
                continue;
            }

            eprintln!("[rust-fv] Verifying: {name}");

            // Get the optimized MIR
            let mir = tcx.optimized_mir(def_id);

            // Convert rustc MIR to our IR
            let ir_func = mir_converter::convert_mir(
                tcx,
                local_def_id,
                mir,
                contracts.cloned().unwrap_or_default(),
            );

            // Generate verification conditions with inter-procedural support
            let func_vcs = rust_fv_analysis::vcgen::generate_vcs(&ir_func, Some(&contract_db));

            // Check each VC with Z3
            for vc in &func_vcs.conditions {
                let script_text = vc.script.to_string();
                match solver.check_sat_raw(&script_text) {
                    Ok(rust_fv_solver::SolverResult::Unsat) => {
                        self.results.push(VerificationResult {
                            function_name: name.clone(),
                            condition: vc.description.clone(),
                            verified: true,
                            counterexample: None,
                        });
                    }
                    Ok(rust_fv_solver::SolverResult::Sat(model)) => {
                        let cx = model.map(|m| {
                            m.assignments
                                .iter()
                                .map(|(k, v)| format!("{k} = {v}"))
                                .collect::<Vec<_>>()
                                .join(", ")
                        });
                        self.results.push(VerificationResult {
                            function_name: name.clone(),
                            condition: vc.description.clone(),
                            verified: false,
                            counterexample: cx,
                        });
                    }
                    Ok(rust_fv_solver::SolverResult::Unknown(reason)) => {
                        self.results.push(VerificationResult {
                            function_name: name.clone(),
                            condition: format!("{} (unknown: {reason})", vc.description),
                            verified: false,
                            counterexample: None,
                        });
                    }
                    Err(e) => {
                        self.results.push(VerificationResult {
                            function_name: name.clone(),
                            condition: format!("{} (error: {e})", vc.description),
                            verified: false,
                            counterexample: None,
                        });
                    }
                }
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
                } else if doc == "rust_fv::pure" {
                    contracts.is_pure = true;
                }
            }
        }

        if !contracts.requires.is_empty()
            || !contracts.ensures.is_empty()
            || !contracts.invariants.is_empty()
            || contracts.is_pure
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
