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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_json_summary_serialization() {
        let summary = JsonSummary {
            total: 10,
            ok: 7,
            fail: 2,
            timeout: 1,
        };
        let json = serde_json::to_string(&summary).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed["total"], 10);
        assert_eq!(parsed["ok"], 7);
        assert_eq!(parsed["fail"], 2);
        assert_eq!(parsed["timeout"], 1);
    }

    #[test]
    fn test_json_assignment_serialization() {
        let assignment = JsonAssignment {
            variable: "x".to_string(),
            value: "42".to_string(),
        };
        let json = serde_json::to_string(&assignment).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed["variable"], "x");
        assert_eq!(parsed["value"], "42");
    }

    #[test]
    fn test_json_failure_serialization_minimal() {
        let failure = JsonFailure {
            vc_kind: "overflow".to_string(),
            description: "arithmetic overflow possible".to_string(),
            contract: None,
            source_file: None,
            source_line: None,
            counterexample: None,
            suggestion: None,
        };
        let json = serde_json::to_string(&failure).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed["vc_kind"], "overflow");
        assert_eq!(parsed["description"], "arithmetic overflow possible");
        assert!(parsed["contract"].is_null());
        assert!(parsed["source_file"].is_null());
        assert!(parsed["source_line"].is_null());
        assert!(parsed["counterexample"].is_null());
        assert!(parsed["suggestion"].is_null());
    }

    #[test]
    fn test_json_failure_serialization_full() {
        let failure = JsonFailure {
            vc_kind: "precondition".to_string(),
            description: "precondition not satisfied".to_string(),
            contract: Some("x > 0".to_string()),
            source_file: Some("src/lib.rs".to_string()),
            source_line: Some(42),
            counterexample: Some(vec![
                JsonAssignment {
                    variable: "x".to_string(),
                    value: "-1".to_string(),
                },
                JsonAssignment {
                    variable: "y".to_string(),
                    value: "0".to_string(),
                },
            ]),
            suggestion: Some("Add bounds check".to_string()),
        };
        let json = serde_json::to_string(&failure).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed["vc_kind"], "precondition");
        assert_eq!(parsed["contract"], "x > 0");
        assert_eq!(parsed["source_file"], "src/lib.rs");
        assert_eq!(parsed["source_line"], 42);
        assert_eq!(parsed["counterexample"].as_array().unwrap().len(), 2);
        assert_eq!(parsed["suggestion"], "Add bounds check");
    }

    #[test]
    fn test_json_function_result_serialization() {
        let result = JsonFunctionResult {
            name: "my_func".to_string(),
            status: "ok".to_string(),
            vc_count: 3,
            verified_count: 3,
            failures: vec![],
        };
        let json = serde_json::to_string(&result).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed["name"], "my_func");
        assert_eq!(parsed["status"], "ok");
        assert_eq!(parsed["vc_count"], 3);
        assert_eq!(parsed["verified_count"], 3);
        assert_eq!(parsed["failures"].as_array().unwrap().len(), 0);
    }

    #[test]
    fn test_json_function_result_with_failures() {
        let result = JsonFunctionResult {
            name: "bad_func".to_string(),
            status: "fail".to_string(),
            vc_count: 2,
            verified_count: 1,
            failures: vec![JsonFailure {
                vc_kind: "postcondition".to_string(),
                description: "postcondition not proven".to_string(),
                contract: Some("result > 0".to_string()),
                source_file: None,
                source_line: None,
                counterexample: None,
                suggestion: Some("Check return paths".to_string()),
            }],
        };
        let json = serde_json::to_string(&result).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed["status"], "fail");
        assert_eq!(parsed["failures"].as_array().unwrap().len(), 1);
        assert_eq!(parsed["failures"][0]["vc_kind"], "postcondition");
    }

    #[test]
    fn test_json_verification_report_serialization() {
        let report = JsonVerificationReport {
            crate_name: "my_crate".to_string(),
            functions: vec![
                JsonFunctionResult {
                    name: "func_a".to_string(),
                    status: "ok".to_string(),
                    vc_count: 2,
                    verified_count: 2,
                    failures: vec![],
                },
                JsonFunctionResult {
                    name: "func_b".to_string(),
                    status: "fail".to_string(),
                    vc_count: 3,
                    verified_count: 1,
                    failures: vec![JsonFailure {
                        vc_kind: "overflow".to_string(),
                        description: "arithmetic overflow".to_string(),
                        contract: None,
                        source_file: None,
                        source_line: None,
                        counterexample: None,
                        suggestion: None,
                    }],
                },
            ],
            summary: JsonSummary {
                total: 2,
                ok: 1,
                fail: 1,
                timeout: 0,
            },
        };
        let json = serde_json::to_string_pretty(&report).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed["crate_name"], "my_crate");
        assert_eq!(parsed["functions"].as_array().unwrap().len(), 2);
        assert_eq!(parsed["summary"]["total"], 2);
        assert_eq!(parsed["summary"]["ok"], 1);
        assert_eq!(parsed["summary"]["fail"], 1);
        assert_eq!(parsed["summary"]["timeout"], 0);
    }

    #[test]
    fn test_json_report_empty_functions() {
        let report = JsonVerificationReport {
            crate_name: "empty_crate".to_string(),
            functions: vec![],
            summary: JsonSummary {
                total: 0,
                ok: 0,
                fail: 0,
                timeout: 0,
            },
        };
        let json = serde_json::to_string(&report).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed["functions"].as_array().unwrap().len(), 0);
        assert_eq!(parsed["summary"]["total"], 0);
    }
}
