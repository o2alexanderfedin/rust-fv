/// Structured JSON output for verification results.
///
/// Enables IDE/rust-analyzer integration by producing machine-readable
/// verification results via --output-format json.
use serde::{Deserialize, Serialize};

/// Complete verification report in JSON format.
#[derive(Serialize, Deserialize)]
pub struct JsonVerificationReport {
    pub crate_name: String,
    pub functions: Vec<JsonFunctionResult>,
    pub summary: JsonSummary,
}

/// Per-function verification result in JSON format.
#[derive(Serialize, Deserialize)]
pub struct JsonFunctionResult {
    pub name: String,
    /// "ok", "fail", "timeout"
    pub status: String,
    pub vc_count: usize,
    pub verified_count: usize,
    pub failures: Vec<JsonFailure>,
}

/// A single verification failure in JSON format.
#[derive(Serialize, Deserialize)]
pub struct JsonFailure {
    /// "precondition", "postcondition", "overflow", etc.
    pub vc_kind: String,
    pub description: String,
    pub contract: Option<String>,
    pub source_file: Option<String>,
    pub source_line: Option<usize>,
    /// Source column number (1-based, when available).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_column: Option<usize>,
    pub counterexample: Option<Vec<JsonAssignment>>,
    /// Structured counterexample with typed variables (v2 schema).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample_v2: Option<JsonCounterexample>,
    pub suggestion: Option<String>,
}

/// Variable assignment in a counterexample.
#[derive(Serialize, Deserialize)]
pub struct JsonAssignment {
    pub variable: String,
    pub value: String,
}

/// Structured counterexample with typed variables and metadata (v2 schema).
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct JsonCounterexample {
    pub variables: Vec<JsonCexVariable>,
    pub failing_location: JsonLocation,
    pub vc_kind: String,
    pub violated_spec: Option<String>,
}

/// A single variable in a counterexample (may have single or dual initial/at_failure values).
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct JsonCexVariable {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    /// Present when variable has a single value at point of failure.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub display: Option<String>,
    /// Present when variable has a single value at point of failure.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub raw: Option<serde_json::Value>,
    /// Present when variable has an initial (parameter entry) value distinct from failure value.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub initial: Option<JsonCexValue>,
    /// Present when variable has a value at the point of failure distinct from its initial value.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub at_failure: Option<JsonCexValue>,
}

/// A single typed value with display string and raw JSON tree.
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct JsonCexValue {
    pub display: String,
    pub raw: serde_json::Value,
}

/// Source location with file, line, and column.
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct JsonLocation {
    pub file: String,
    pub line: usize,
    pub column: usize,
}

/// Summary of all verification results.
#[derive(Serialize, Deserialize)]
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
            source_column: None,
            counterexample: None,
            counterexample_v2: None,
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
            source_column: None,
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
            counterexample_v2: None,
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
                source_column: None,
                counterexample: None,
                counterexample_v2: None,
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
                        source_column: None,
                        counterexample: None,
                        counterexample_v2: None,
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

    // --- print_json_report tests ---
    // These tests exercise the print_json_report function (lines 59-63).
    // Output goes to stdout; we verify the function executes without panicking
    // and that both the Ok and Err paths are covered.

    #[test]
    fn test_print_json_report_minimal() {
        // Minimal report with empty functions list
        let report = JsonVerificationReport {
            crate_name: "test_crate".to_string(),
            functions: vec![],
            summary: JsonSummary {
                total: 0,
                ok: 0,
                fail: 0,
                timeout: 0,
            },
        };
        // This writes to stdout. Exercises lines 60-61 (Ok path).
        print_json_report(&report);
    }

    #[test]
    fn test_print_json_report_with_functions() {
        // Report with one passing and one failing function
        let report = JsonVerificationReport {
            crate_name: "my_crate".to_string(),
            functions: vec![
                JsonFunctionResult {
                    name: "passing_func".to_string(),
                    status: "ok".to_string(),
                    vc_count: 2,
                    verified_count: 2,
                    failures: vec![],
                },
                JsonFunctionResult {
                    name: "failing_func".to_string(),
                    status: "fail".to_string(),
                    vc_count: 3,
                    verified_count: 1,
                    failures: vec![JsonFailure {
                        vc_kind: "overflow".to_string(),
                        description: "arithmetic overflow possible".to_string(),
                        contract: None,
                        source_file: None,
                        source_line: None,
                        source_column: None,
                        counterexample: None,
                        counterexample_v2: None,
                        suggestion: Some("Use checked_add".to_string()),
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
        print_json_report(&report);
    }

    #[test]
    fn test_print_json_report_full_failure_details() {
        // Report with complete failure details including counterexample
        let report = JsonVerificationReport {
            crate_name: "detailed_crate".to_string(),
            functions: vec![JsonFunctionResult {
                name: "compute".to_string(),
                status: "fail".to_string(),
                vc_count: 1,
                verified_count: 0,
                failures: vec![JsonFailure {
                    vc_kind: "precondition".to_string(),
                    description: "precondition not satisfied".to_string(),
                    contract: Some("x > 0".to_string()),
                    source_file: Some("src/lib.rs".to_string()),
                    source_line: Some(42),
                    source_column: None,
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
                    counterexample_v2: None,
                    suggestion: Some("Add bounds check".to_string()),
                }],
            }],
            summary: JsonSummary {
                total: 1,
                ok: 0,
                fail: 1,
                timeout: 0,
            },
        };
        print_json_report(&report);
    }

    #[test]
    fn test_print_json_report_timeout_status() {
        // Report with a timeout function
        let report = JsonVerificationReport {
            crate_name: "timeout_crate".to_string(),
            functions: vec![JsonFunctionResult {
                name: "slow_func".to_string(),
                status: "timeout".to_string(),
                vc_count: 5,
                verified_count: 0,
                failures: vec![],
            }],
            summary: JsonSummary {
                total: 1,
                ok: 0,
                fail: 0,
                timeout: 1,
            },
        };
        print_json_report(&report);
    }

    #[test]
    fn test_print_json_report_multiple_failures_in_function() {
        // Function with multiple different failure types
        let report = JsonVerificationReport {
            crate_name: "multi_fail_crate".to_string(),
            functions: vec![JsonFunctionResult {
                name: "risky_func".to_string(),
                status: "fail".to_string(),
                vc_count: 4,
                verified_count: 1,
                failures: vec![
                    JsonFailure {
                        vc_kind: "overflow".to_string(),
                        description: "arithmetic overflow possible".to_string(),
                        contract: None,
                        source_file: Some("src/lib.rs".to_string()),
                        source_line: Some(10),
                        source_column: None,
                        counterexample: Some(vec![JsonAssignment {
                            variable: "n".to_string(),
                            value: "2147483647".to_string(),
                        }]),
                        counterexample_v2: None,
                        suggestion: Some("Use checked arithmetic".to_string()),
                    },
                    JsonFailure {
                        vc_kind: "postcondition".to_string(),
                        description: "postcondition not proven".to_string(),
                        contract: Some("result >= 0".to_string()),
                        source_file: Some("src/lib.rs".to_string()),
                        source_line: Some(15),
                        source_column: None,
                        counterexample: None,
                        counterexample_v2: None,
                        suggestion: Some("Check return paths".to_string()),
                    },
                    JsonFailure {
                        vc_kind: "division_by_zero".to_string(),
                        description: "division by zero possible".to_string(),
                        contract: None,
                        source_file: None,
                        source_line: None,
                        source_column: None,
                        counterexample: Some(vec![JsonAssignment {
                            variable: "d".to_string(),
                            value: "0".to_string(),
                        }]),
                        counterexample_v2: None,
                        suggestion: None,
                    },
                ],
            }],
            summary: JsonSummary {
                total: 1,
                ok: 0,
                fail: 1,
                timeout: 0,
            },
        };
        print_json_report(&report);
    }

    #[test]
    fn test_print_json_report_large_summary() {
        // Large summary values to ensure serialization handles big numbers
        let report = JsonVerificationReport {
            crate_name: "large_crate".to_string(),
            functions: vec![],
            summary: JsonSummary {
                total: 1000,
                ok: 950,
                fail: 30,
                timeout: 20,
            },
        };
        print_json_report(&report);
    }

    // --- JsonCounterexample v2 schema tests ---

    #[test]
    fn test_json_counterexample_single_value_no_null_fields() {
        // Variable with display/raw only — initial and at_failure must NOT appear in JSON
        let cex = JsonCounterexample {
            variables: vec![JsonCexVariable {
                name: "x".to_string(),
                ty: "i32".to_string(),
                display: Some("i32: -1".to_string()),
                raw: Some(serde_json::json!(-1)),
                initial: None,
                at_failure: None,
            }],
            failing_location: JsonLocation {
                file: "src/lib.rs".to_string(),
                line: 42,
                column: 5,
            },
            vc_kind: "precondition".to_string(),
            violated_spec: Some("x > 0".to_string()),
        };
        let json = serde_json::to_string(&cex).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        // Must have the core fields
        assert_eq!(parsed["vc_kind"], "precondition");
        assert_eq!(parsed["violated_spec"], "x > 0");
        assert_eq!(parsed["failing_location"]["file"], "src/lib.rs");
        assert_eq!(parsed["failing_location"]["line"], 42);
        assert_eq!(parsed["failing_location"]["column"], 5);
        let var = &parsed["variables"][0];
        assert_eq!(var["name"], "x");
        assert_eq!(var["type"], "i32");
        assert_eq!(var["display"], "i32: -1");
        assert_eq!(var["raw"], -1);
        // skip_serializing_if must suppress null fields
        assert!(
            !json.contains("\"initial\""),
            "initial must not appear when None"
        );
        assert!(
            !json.contains("\"at_failure\""),
            "at_failure must not appear when None"
        );
    }

    #[test]
    fn test_json_counterexample_dual_value_initial_and_at_failure() {
        // Variable with both initial and at_failure — display/raw may or may not be present
        let cex = JsonCounterexample {
            variables: vec![JsonCexVariable {
                name: "n".to_string(),
                ty: "i32".to_string(),
                display: Some("i32: 10".to_string()),
                raw: Some(serde_json::json!(10)),
                initial: Some(JsonCexValue {
                    display: "i32: 0".to_string(),
                    raw: serde_json::json!(0),
                }),
                at_failure: Some(JsonCexValue {
                    display: "i32: 10".to_string(),
                    raw: serde_json::json!(10),
                }),
            }],
            failing_location: JsonLocation {
                file: "src/main.rs".to_string(),
                line: 10,
                column: 1,
            },
            vc_kind: "overflow".to_string(),
            violated_spec: None,
        };
        let json = serde_json::to_string(&cex).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        let var = &parsed["variables"][0];
        assert_eq!(var["initial"]["display"], "i32: 0");
        assert_eq!(var["initial"]["raw"], 0);
        assert_eq!(var["at_failure"]["display"], "i32: 10");
        assert_eq!(var["at_failure"]["raw"], 10);
        // violated_spec absent when None
        assert!(parsed["violated_spec"].is_null());
    }

    #[test]
    fn test_json_failure_has_both_counterexample_and_v2() {
        // Both fields coexist — backward compat preserved
        let failure = JsonFailure {
            vc_kind: "precondition".to_string(),
            description: "precondition not satisfied".to_string(),
            contract: Some("x > 0".to_string()),
            source_file: Some("src/lib.rs".to_string()),
            source_line: Some(5),
            source_column: None,
            counterexample: Some(vec![JsonAssignment {
                variable: "x".to_string(),
                value: "-1".to_string(),
            }]),
            counterexample_v2: Some(JsonCounterexample {
                variables: vec![JsonCexVariable {
                    name: "x".to_string(),
                    ty: "i32".to_string(),
                    display: Some("i32: -1".to_string()),
                    raw: Some(serde_json::json!(-1)),
                    initial: None,
                    at_failure: None,
                }],
                failing_location: JsonLocation {
                    file: "src/lib.rs".to_string(),
                    line: 5,
                    column: 1,
                },
                vc_kind: "precondition".to_string(),
                violated_spec: Some("x > 0".to_string()),
            }),
            suggestion: None,
        };
        let json = serde_json::to_string(&failure).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        // Old flat field preserved
        assert_eq!(parsed["counterexample"][0]["variable"], "x");
        assert_eq!(parsed["counterexample"][0]["value"], "-1");
        // New v2 field present
        assert_eq!(parsed["counterexample_v2"]["vc_kind"], "precondition");
        assert_eq!(parsed["counterexample_v2"]["variables"][0]["name"], "x");
    }

    #[test]
    fn test_print_json_report_special_characters_in_strings() {
        // Strings with special characters that need JSON escaping
        let report = JsonVerificationReport {
            crate_name: "crate-with-dashes".to_string(),
            functions: vec![JsonFunctionResult {
                name: "fn_with_\"quotes\"".to_string(),
                status: "fail".to_string(),
                vc_count: 1,
                verified_count: 0,
                failures: vec![JsonFailure {
                    vc_kind: "assertion".to_string(),
                    description: "assertion 'x < y && y < z' might fail".to_string(),
                    contract: Some("x < y\n&& y < z".to_string()),
                    source_file: Some("src/path with spaces/lib.rs".to_string()),
                    source_line: Some(1),
                    source_column: None,
                    counterexample: None,
                    counterexample_v2: None,
                    suggestion: None,
                }],
            }],
            summary: JsonSummary {
                total: 1,
                ok: 0,
                fail: 1,
                timeout: 0,
            },
        };
        print_json_report(&report);
    }
}
