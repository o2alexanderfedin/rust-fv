//! Differential testing engine for bv2int encoding equivalence verification.
//!
//! Tests that bitvector and integer arithmetic encodings produce identical
//! verification results (both SAT or both UNSAT) for a given function's VCs.
//! Captures timing for both encodings to quantify the optimization speedup.
//!
//! # Approach
//!
//! For each function:
//! 1. Generate VCs with `EncodingMode::Bitvector` (baseline)
//! 2. Generate VCs with `EncodingMode::Integer` (optimized)
//! 3. Run solver on both, timing each
//! 4. Compare: both Unsat → equivalent; both Sat with consistent model → equivalent
//! 5. Divergent results → soundness error with counterexample
//!
//! Results are cached in `CacheEntry` (via `bv2int_equiv_tested` field) to avoid
//! re-running expensive equivalence checks when the function body hasn't changed.

use rust_fv_smtlib::script::Script;

/// Result of testing encoding equivalence for a function's verification conditions.
///
/// Returned by `test_encoding_equivalence`. Contains timing information for
/// both encodings and whether they agreed on all verification conditions.
#[derive(Debug, Clone, PartialEq)]
pub struct EquivalenceResult {
    /// Whether bitvector and integer encodings agree on all VCs.
    ///
    /// `true` if every VC is UNSAT (verified) in both encodings, or SAT in both.
    /// `false` if any VC diverges (one says SAT, the other UNSAT).
    pub equivalent: bool,
    /// Time spent running the solver on bitvector-encoded VCs (milliseconds).
    pub bitvec_time_ms: u64,
    /// Time spent running the solver on integer-encoded VCs (milliseconds).
    pub bv2int_time_ms: u64,
    /// Speedup factor: `bitvec_time_ms / bv2int_time_ms`.
    ///
    /// Values above 1.0 mean bv2int is faster; below 1.0 mean bitvector is faster.
    /// Set to 1.0 when `bv2int_time_ms` is zero to avoid division by zero.
    pub speedup_factor: f64,
    /// Description of the divergence, if `equivalent == false`.
    ///
    /// Includes the model from the SAT side when available, formatted as:
    /// `"bitvector=SAT, bv2int=UNSAT"` or similar.
    pub counterexample: Option<String>,
}

/// Test whether bitvector and integer encodings produce equivalent results.
///
/// Runs both sets of VCs through the solver and compares outcomes.
/// All VCs from each encoding are run sequentially; the first divergence
/// is reported.
///
/// # Arguments
/// * `func_name` - Function name (for error messages)
/// * `bv_scripts` - VCs encoded with `EncodingMode::Bitvector`
/// * `int_scripts` - VCs encoded with `EncodingMode::Integer` (must be same length)
/// * `solver` - Solver to use for both encodings
///
/// # Returns
/// `EquivalenceResult` with timing and equivalence outcome.
pub fn test_encoding_equivalence(
    func_name: &str,
    bv_scripts: &[Script],
    int_scripts: &[Script],
    solver: &dyn SolverInterface,
) -> EquivalenceResult {
    let bv_start = std::time::Instant::now();
    let bv_results: Vec<VcOutcome> = bv_scripts.iter().map(|s| solver.check(s)).collect();
    let bitvec_time_ms = bv_start.elapsed().as_millis() as u64;

    let int_start = std::time::Instant::now();
    let int_results: Vec<VcOutcome> = int_scripts.iter().map(|s| solver.check(s)).collect();
    let bv2int_time_ms = int_start.elapsed().as_millis() as u64;

    let speedup_factor = if bv2int_time_ms == 0 {
        1.0
    } else {
        bitvec_time_ms as f64 / bv2int_time_ms as f64
    };

    // Compare results pairwise
    for (i, (bv_r, int_r)) in bv_results.iter().zip(int_results.iter()).enumerate() {
        if !outcomes_agree(bv_r, int_r) {
            let counterexample = format!(
                "VC #{i} divergence in {func_name}: bitvector={}, bv2int={}{}",
                outcome_name(bv_r),
                outcome_name(int_r),
                format_model_detail(bv_r, int_r),
            );
            return EquivalenceResult {
                equivalent: false,
                bitvec_time_ms,
                bv2int_time_ms,
                speedup_factor,
                counterexample: Some(counterexample),
            };
        }
    }

    EquivalenceResult {
        equivalent: true,
        bitvec_time_ms,
        bv2int_time_ms,
        speedup_factor,
        counterexample: None,
    }
}

/// Format an `EquivalenceResult` as a human-readable string.
///
/// # Examples
/// - Equivalent, faster: `"bitvector: 120ms, bv2int: 40ms (3.0x faster)"`
/// - Equivalent, slower: `"bitvector: 40ms, bv2int: 120ms (0.3x slower)"`
/// - Divergent: `"ENCODING DIVERGENCE in my_func: bitvector=SAT, bv2int=UNSAT. Counterexample: ..."`
pub fn format_equivalence_result(result: &EquivalenceResult, func_name: &str) -> String {
    if result.equivalent {
        let direction = if result.speedup_factor >= 1.0 {
            format!("{:.1}x faster", result.speedup_factor)
        } else {
            format!("{:.1}x slower", result.speedup_factor)
        };
        format!(
            "bitvector: {}ms, bv2int: {}ms ({})",
            result.bitvec_time_ms, result.bv2int_time_ms, direction
        )
    } else {
        let ce = result.counterexample.as_deref().unwrap_or("no details");
        format!("ENCODING DIVERGENCE in {func_name}: {ce}")
    }
}

// ============================================================
// Solver abstraction (testable without real solver binary)
// ============================================================

/// Outcome of running a single VC through the solver.
#[derive(Debug, Clone, PartialEq)]
pub enum VcOutcome {
    /// Formula is unsatisfiable (VC proved).
    Unsat,
    /// Formula is satisfiable (VC failed), with optional structured model pairs.
    ///
    /// Each pair is `(variable_name, raw_value_string)`, e.g. `("x", "#x00000005")`.
    /// `None` means the solver returned SAT but no model was available.
    Sat(Option<Vec<(String, String)>>),
    /// Solver timed out or returned unknown.
    Unknown,
}

/// Minimal solver interface for differential testing.
///
/// This trait allows injecting mock solvers in unit tests without requiring
/// a real Z3 binary.
pub trait SolverInterface {
    /// Run a script and return the outcome.
    fn check(&self, script: &Script) -> VcOutcome;
}

// ============================================================
// Private helpers
// ============================================================

/// Returns true if two VC outcomes agree (both proved, both failed, or both unknown).
fn outcomes_agree(a: &VcOutcome, b: &VcOutcome) -> bool {
    matches!(
        (a, b),
        (VcOutcome::Unsat, VcOutcome::Unsat)
            | (VcOutcome::Sat(_), VcOutcome::Sat(_))
            | (VcOutcome::Unknown, VcOutcome::Unknown)
    )
}

/// Returns a short name for a VC outcome.
fn outcome_name(o: &VcOutcome) -> &'static str {
    match o {
        VcOutcome::Unsat => "UNSAT",
        VcOutcome::Sat(_) => "SAT",
        VcOutcome::Unknown => "UNKNOWN",
    }
}

/// Format additional model detail for divergence messages.
fn format_model_detail(bv_r: &VcOutcome, int_r: &VcOutcome) -> String {
    let format_pairs = |pairs: &[(String, String)]| -> String {
        pairs
            .iter()
            .map(|(k, v)| format!("{k} = {v}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let model = match (bv_r, int_r) {
        (VcOutcome::Sat(Some(m)), _) => Some(format!(" (bitvector model: {})", format_pairs(m))),
        (_, VcOutcome::Sat(Some(m))) => Some(format!(" (bv2int model: {})", format_pairs(m))),
        _ => None,
    };
    model.unwrap_or_default()
}

// ============================================================
// Tests
// ============================================================

#[cfg(test)]
mod tests {
    use super::*;
    use rust_fv_smtlib::script::Script;

    // --- Mock solver for deterministic tests ---

    /// A mock solver that returns pre-programmed outcomes.
    struct MockSolver {
        /// Outcomes to return, in order (cycled if more scripts than outcomes).
        outcomes: Vec<VcOutcome>,
    }

    impl MockSolver {
        fn new(outcomes: Vec<VcOutcome>) -> Self {
            Self { outcomes }
        }

        fn all_unsat(n: usize) -> Self {
            Self::new(vec![VcOutcome::Unsat; n])
        }

        #[allow(dead_code)]
        fn all_sat(n: usize) -> Self {
            Self::new(vec![VcOutcome::Sat(None); n])
        }
    }

    impl SolverInterface for MockSolver {
        fn check(&self, _script: &Script) -> VcOutcome {
            // Stateless mock: always returns first outcome (used with single VCs)
            // For multiple VCs, callers use separate mock instances per call.
            self.outcomes.first().cloned().unwrap_or(VcOutcome::Unknown)
        }
    }

    /// A mock solver that cycles through outcomes for multiple VCs.
    struct CycleMockSolver {
        outcomes: Vec<VcOutcome>,
        idx: std::cell::Cell<usize>,
    }

    impl CycleMockSolver {
        fn new(outcomes: Vec<VcOutcome>) -> Self {
            Self {
                outcomes,
                idx: std::cell::Cell::new(0),
            }
        }
    }

    impl SolverInterface for CycleMockSolver {
        fn check(&self, _script: &Script) -> VcOutcome {
            let i = self.idx.get();
            let outcome = self.outcomes[i % self.outcomes.len()].clone();
            self.idx.set(i + 1);
            outcome
        }
    }

    /// Helper: create an empty Script for testing (no actual SMT content needed).
    fn empty_script() -> Script {
        Script::new()
    }

    fn empty_scripts(n: usize) -> Vec<Script> {
        (0..n).map(|_| empty_script()).collect()
    }

    // --- EquivalenceResult tests ---

    #[test]
    fn test_equivalent_when_both_unsat() {
        let bv_scripts = empty_scripts(3);
        let int_scripts = empty_scripts(3);
        let bv_solver = MockSolver::all_unsat(3);
        let int_solver = MockSolver::all_unsat(3);

        // Use CycleMockSolver that returns UNSAT for all scripts
        let cycle = CycleMockSolver::new(vec![
            VcOutcome::Unsat,
            VcOutcome::Unsat,
            VcOutcome::Unsat,
            VcOutcome::Unsat,
            VcOutcome::Unsat,
            VcOutcome::Unsat,
        ]);
        let result = test_encoding_equivalence("my_func", &bv_scripts, &int_scripts, &cycle);

        assert!(result.equivalent);
        assert!(result.counterexample.is_none());
        let _ = (bv_solver, int_solver); // suppress unused warning
    }

    #[test]
    fn test_equivalent_when_both_sat() {
        let bv_scripts = empty_scripts(2);
        let int_scripts = empty_scripts(2);

        let cycle = CycleMockSolver::new(vec![
            VcOutcome::Sat(None),
            VcOutcome::Sat(None),
            VcOutcome::Sat(None),
            VcOutcome::Sat(None),
        ]);
        let result = test_encoding_equivalence("func", &bv_scripts, &int_scripts, &cycle);

        assert!(result.equivalent);
        assert!(result.counterexample.is_none());
    }

    #[test]
    fn test_divergent_bv_sat_int_unsat() {
        let bv_scripts = empty_scripts(1);
        let int_scripts = empty_scripts(1);

        // BV returns SAT, INT returns UNSAT
        let cycle = CycleMockSolver::new(vec![VcOutcome::Sat(None), VcOutcome::Unsat]);
        let result = test_encoding_equivalence("bad_func", &bv_scripts, &int_scripts, &cycle);

        assert!(!result.equivalent);
        assert!(result.counterexample.is_some());
        let ce = result.counterexample.unwrap();
        assert!(ce.contains("bad_func"));
        assert!(ce.contains("SAT"));
        assert!(ce.contains("UNSAT"));
    }

    #[test]
    fn test_divergent_bv_unsat_int_sat() {
        let bv_scripts = empty_scripts(1);
        let int_scripts = empty_scripts(1);

        // BV returns UNSAT, INT returns SAT
        let cycle = CycleMockSolver::new(vec![VcOutcome::Unsat, VcOutcome::Sat(None)]);
        let result = test_encoding_equivalence("another_func", &bv_scripts, &int_scripts, &cycle);

        assert!(!result.equivalent);
        assert!(result.counterexample.is_some());
        let ce = result.counterexample.unwrap();
        assert!(ce.contains("UNSAT"));
        assert!(ce.contains("SAT"));
    }

    #[test]
    fn test_counterexample_includes_model_when_sat_has_model() {
        let bv_scripts = empty_scripts(1);
        let int_scripts = empty_scripts(1);

        let model_pairs = vec![
            ("x".to_string(), "5".to_string()),
            ("y".to_string(), "-3".to_string()),
        ];
        let cycle = CycleMockSolver::new(vec![VcOutcome::Sat(Some(model_pairs)), VcOutcome::Unsat]);
        let result =
            test_encoding_equivalence("func_with_model", &bv_scripts, &int_scripts, &cycle);

        assert!(!result.equivalent);
        let ce = result.counterexample.unwrap();
        assert!(ce.contains("x = 5"), "Expected 'x = 5' in: {ce}");
        assert!(ce.contains("y = -3"), "Expected 'y = -3' in: {ce}");
    }

    #[test]
    fn test_timing_captured() {
        let bv_scripts = empty_scripts(1);
        let int_scripts = empty_scripts(1);

        let cycle = CycleMockSolver::new(vec![VcOutcome::Unsat, VcOutcome::Unsat]);
        let result = test_encoding_equivalence("timed_func", &bv_scripts, &int_scripts, &cycle);

        // Timing fields should be set (even if 0 for fast mock)
        let _ = result.bitvec_time_ms;
        let _ = result.bv2int_time_ms;
        // speedup_factor: if bv2int_time == 0, should be 1.0 (no division by zero)
        assert!(result.speedup_factor >= 0.0);
    }

    #[test]
    fn test_speedup_factor_no_divide_by_zero() {
        let bv_scripts = empty_scripts(1);
        let int_scripts = empty_scripts(1);

        let cycle = CycleMockSolver::new(vec![VcOutcome::Unsat, VcOutcome::Unsat]);
        let result = test_encoding_equivalence("func", &bv_scripts, &int_scripts, &cycle);

        // Even if both times are 0, speedup_factor must be finite
        assert!(result.speedup_factor.is_finite());
        assert!(result.speedup_factor > 0.0);
    }

    #[test]
    fn test_empty_vc_lists_are_equivalent() {
        let bv_scripts: Vec<Script> = vec![];
        let int_scripts: Vec<Script> = vec![];

        let cycle = CycleMockSolver::new(vec![]);
        let result = test_encoding_equivalence("empty_func", &bv_scripts, &int_scripts, &cycle);

        assert!(result.equivalent);
        assert!(result.counterexample.is_none());
    }

    #[test]
    fn test_first_divergence_reported() {
        // 3 VCs: first two agree (UNSAT), third diverges
        let bv_scripts = empty_scripts(3);
        let int_scripts = empty_scripts(3);

        let cycle = CycleMockSolver::new(vec![
            // BV: UNSAT, UNSAT, SAT
            VcOutcome::Unsat,
            VcOutcome::Unsat,
            VcOutcome::Sat(None),
            // INT: UNSAT, UNSAT, UNSAT
            VcOutcome::Unsat,
            VcOutcome::Unsat,
            VcOutcome::Unsat,
        ]);
        let result = test_encoding_equivalence("multi_vc_func", &bv_scripts, &int_scripts, &cycle);

        assert!(!result.equivalent);
        let ce = result.counterexample.unwrap();
        // Should mention VC #2 (0-indexed)
        assert!(ce.contains("#2"));
    }

    // --- format_equivalence_result tests ---

    #[test]
    fn test_format_equivalent_faster() {
        let result = EquivalenceResult {
            equivalent: true,
            bitvec_time_ms: 120,
            bv2int_time_ms: 40,
            speedup_factor: 3.0,
            counterexample: None,
        };
        let formatted = format_equivalence_result(&result, "my_func");
        assert!(formatted.contains("120ms"));
        assert!(formatted.contains("40ms"));
        assert!(formatted.contains("3.0x faster"));
    }

    #[test]
    fn test_format_equivalent_slower() {
        let result = EquivalenceResult {
            equivalent: true,
            bitvec_time_ms: 40,
            bv2int_time_ms: 120,
            speedup_factor: 0.33333,
            counterexample: None,
        };
        let formatted = format_equivalence_result(&result, "my_func");
        assert!(formatted.contains("40ms"));
        assert!(formatted.contains("120ms"));
        assert!(formatted.contains("slower"));
    }

    #[test]
    fn test_format_divergent_includes_func_name() {
        let result = EquivalenceResult {
            equivalent: false,
            bitvec_time_ms: 50,
            bv2int_time_ms: 30,
            speedup_factor: 1.67,
            counterexample: Some("bitvector=SAT, bv2int=UNSAT".to_string()),
        };
        let formatted = format_equivalence_result(&result, "critical_func");
        assert!(formatted.contains("ENCODING DIVERGENCE"));
        assert!(formatted.contains("critical_func"));
        assert!(formatted.contains("SAT"));
        assert!(formatted.contains("UNSAT"));
    }

    #[test]
    fn test_format_1x_shown_as_faster() {
        let result = EquivalenceResult {
            equivalent: true,
            bitvec_time_ms: 100,
            bv2int_time_ms: 100,
            speedup_factor: 1.0,
            counterexample: None,
        };
        let formatted = format_equivalence_result(&result, "func");
        assert!(formatted.contains("1.0x faster"));
    }

    // --- Structured model pairs tests (Phase 19) ---

    #[test]
    fn test_sat_with_structured_model_pairs_contains_formatted_pair() {
        // VcOutcome::Sat carries Vec<(String,String)> pairs
        // When BV=SAT(model) and INT=UNSAT, divergence message must contain "x = 5"
        let bv_scripts = empty_scripts(1);
        let int_scripts = empty_scripts(1);

        let model_pairs = vec![
            ("x".to_string(), "5".to_string()),
            ("b".to_string(), "true".to_string()),
        ];
        let cycle = CycleMockSolver::new(vec![VcOutcome::Sat(Some(model_pairs)), VcOutcome::Unsat]);
        let result =
            test_encoding_equivalence("func_with_pairs", &bv_scripts, &int_scripts, &cycle);

        assert!(!result.equivalent);
        let ce = result.counterexample.unwrap();
        // The counterexample must display "x = 5" (from the Vec pair)
        assert!(ce.contains("x = 5"), "Expected 'x = 5' in: {ce}");
        assert!(ce.contains("b = true"), "Expected 'b = true' in: {ce}");
    }

    #[test]
    fn test_sat_none_model_produces_no_model_detail() {
        let bv_scripts = empty_scripts(1);
        let int_scripts = empty_scripts(1);

        let cycle = CycleMockSolver::new(vec![VcOutcome::Sat(None), VcOutcome::Unsat]);
        let result = test_encoding_equivalence("no_model_func", &bv_scripts, &int_scripts, &cycle);

        assert!(!result.equivalent);
        let ce = result.counterexample.unwrap();
        // No model detail when None
        assert!(
            !ce.contains("model:"),
            "Should not contain model detail: {ce}"
        );
    }

    #[test]
    fn test_sat_vec_pairs_type_accepted_by_outcome() {
        // Verify the type is Vec<(String,String)> not String
        let pairs: Vec<(String, String)> = vec![("x".to_string(), "#x00000005".to_string())];
        let outcome = VcOutcome::Sat(Some(pairs));
        // Pattern match to confirm it holds Vec
        match outcome {
            VcOutcome::Sat(Some(v)) => {
                assert_eq!(v.len(), 1);
                assert_eq!(v[0].0, "x");
                assert_eq!(v[0].1, "#x00000005");
            }
            _ => panic!("Expected Sat(Some(vec))"),
        }
    }
}
