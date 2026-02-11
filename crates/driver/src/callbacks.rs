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

    /// Print verification results to stderr.
    pub fn print_results(&self) {
        if self.results.is_empty() {
            eprintln!("[rust-fv] No verification conditions generated.");
            return;
        }

        let total = self.results.len();
        let verified = self.results.iter().filter(|r| r.verified).count();
        let failed = total - verified;

        eprintln!("\n[rust-fv] Verification Results:");
        eprintln!("  Total conditions: {total}");
        eprintln!("  Verified: {verified}");
        eprintln!("  Failed: {failed}");
        eprintln!();

        for result in &self.results {
            let status = if result.verified { "OK" } else { "FAIL" };
            eprintln!(
                "  [{status}] {}: {}",
                result.function_name, result.condition
            );
            if let Some(cx) = &result.counterexample {
                eprintln!("        Counterexample: {cx}");
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

        eprintln!("[rust-fv] Running formal verification...");

        // Extract contracts from HIR attributes
        let contracts_map = extract_contracts(tcx);

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

            // Generate verification conditions
            let func_vcs = rust_fv_analysis::vcgen::generate_vcs(&ir_func);

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
                } else if doc == "rust_fv::pure" {
                    contracts.is_pure = true;
                }
            }
        }

        if !contracts.requires.is_empty() || !contracts.ensures.is_empty() || contracts.is_pure {
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
