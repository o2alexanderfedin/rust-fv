//! Shared verification result types used across driver modules.
//!
//! Extracted into a separate module so they can be exported from the library crate
//! (`lib.rs`) for integration testing without pulling in rustc internal dependencies.

use crate::json_output::JsonCounterexample;
use rust_fv_analysis::vcgen::VcLocation;

/// Result of verifying a single verification condition.
#[derive(Debug, Clone)]
pub struct VerificationResult {
    pub function_name: String,
    pub condition: String,
    pub verified: bool,
    /// Structured counterexample as `(variable_name, raw_value)` pairs.
    /// `None` if the VC was verified (or no model was available).
    pub counterexample: Option<Vec<(String, String)>>,
    /// Structured counterexample v2 with typed variables and metadata.
    /// Populated when solver returns SAT with model and IR type info is available.
    pub counterexample_v2: Option<JsonCounterexample>,
    #[allow(dead_code)] // Used for future diagnostics enhancement
    pub vc_location: VcLocation,
}
