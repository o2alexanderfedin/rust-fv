/// Structured JSON output for verification results.
///
/// Enables IDE/rust-analyzer integration by producing machine-readable
/// verification results via --output-format json.
use serde::Serialize;

/// Complete verification report in JSON format.
#[derive(Serialize)]
pub struct JsonVerificationReport {
    pub crate_name: String,
    pub functions: Vec<JsonFunctionResult>,
    pub summary: JsonSummary,
}

/// Per-function verification result in JSON format.
#[derive(Serialize)]
pub struct JsonFunctionResult {
    pub name: String,
    /// "ok", "fail", "timeout"
    pub status: String,
    pub vc_count: usize,
    pub verified_count: usize,
    pub failures: Vec<JsonFailure>,
}

/// A single verification failure in JSON format.
#[derive(Serialize)]
pub struct JsonFailure {
    /// "precondition", "postcondition", "overflow", etc.
    pub vc_kind: String,
    pub description: String,
    pub contract: Option<String>,
    pub source_file: Option<String>,
    pub source_line: Option<usize>,
    pub counterexample: Option<Vec<JsonAssignment>>,
    pub suggestion: Option<String>,
}

/// Variable assignment in a counterexample.
#[derive(Serialize)]
pub struct JsonAssignment {
    pub variable: String,
    pub value: String,
}

/// Summary of all verification results.
#[derive(Serialize)]
pub struct JsonSummary {
    pub total: usize,
    pub ok: usize,
    pub fail: usize,
    pub timeout: usize,
}

/// Print a JSON verification report to stdout.
///
/// IMPORTANT: JSON output MUST go to stdout only (not stderr).
/// All progress/warnings go to stderr when JSON mode is active.
pub fn print_json_report(report: &JsonVerificationReport) {
    match serde_json::to_string_pretty(report) {
        Ok(json) => println!("{}", json), // stdout for JSON
        Err(e) => {
            eprintln!("[rust-fv] Error serializing JSON report: {}", e);
        }
    }
}
