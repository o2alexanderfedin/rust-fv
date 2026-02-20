/// Rustc-compatible JSON diagnostic output for rust-analyzer integration.
///
/// Converts `JsonVerificationReport` into the JSON diagnostic format
/// that rust-analyzer's flycheck infrastructure expects (one JSON object
/// per stdout line with `reason`, `message`, `message.spans`, etc.).
use serde::Serialize;

use crate::json_output::JsonVerificationReport;

/// Top-level rustc diagnostic wrapper.
///
/// Each line of output is one of these serialized as single-line JSON.
#[derive(Serialize, Debug, Clone)]
pub struct RustcDiagnostic {
    /// Always `"compiler-message"` for diagnostics.
    pub reason: String,
    /// The diagnostic message payload.
    pub message: RustcMessage,
}

/// The `message` field inside a rustc diagnostic.
#[derive(Serialize, Debug, Clone)]
pub struct RustcMessage {
    /// Human-readable multiline rendered text (like rustc output).
    pub rendered: String,
    /// Always `"diagnostic"`.
    #[serde(rename = "$message_type")]
    pub message_type: String,
    /// Sub-diagnostics (empty for now).
    pub children: Vec<serde_json::Value>,
    /// Diagnostic code (e.g., `rust-fv::postcondition`).
    pub code: Option<RustcCode>,
    /// Severity: `"error"`, `"warning"`, or `"note"`.
    pub level: String,
    /// Short description.
    pub message: String,
    /// Source spans for location information.
    pub spans: Vec<RustcSpan>,
}

/// Diagnostic code identifying the source and kind.
#[derive(Serialize, Debug, Clone)]
pub struct RustcCode {
    /// Code identifier, e.g., `"rust-fv::postcondition"`.
    pub code: String,
    /// Optional explanation (always `null` for now).
    pub explanation: Option<String>,
}

/// Source location span for a diagnostic.
#[derive(Serialize, Debug, Clone)]
pub struct RustcSpan {
    pub byte_end: u32,
    pub byte_start: u32,
    pub column_end: u32,
    pub column_start: u32,
    pub expansion: Option<serde_json::Value>,
    pub file_name: String,
    pub is_primary: bool,
    pub label: Option<String>,
    pub line_end: u32,
    pub line_start: u32,
    pub suggested_replacement: Option<String>,
    pub suggestion_applicability: Option<String>,
    pub text: Vec<serde_json::Value>,
}

/// Convert a `JsonVerificationReport` into rustc-compatible diagnostics.
///
/// Only failures produce diagnostics. Passing functions are silent
/// (matching rustc behavior where successful compilation has no diagnostics).
/// A summary diagnostic is appended at the end.
pub fn convert_report_to_rustc_diagnostics(
    report: &JsonVerificationReport,
) -> Vec<RustcDiagnostic> {
    let mut diagnostics = Vec::new();

    for func in &report.functions {
        if func.status != "fail" {
            continue;
        }

        for failure in &func.failures {
            let file_name = failure
                .source_file
                .clone()
                .unwrap_or_else(|| "unknown".to_string());
            let line = failure.source_line.unwrap_or(1) as u32;

            // Build rendered text with counterexample details inline
            let mut rendered = format!(
                "error[rust-fv::{}]: {}\n --> {}:{}:1\n",
                failure.vc_kind, failure.description, file_name, line
            );

            if let Some(ref contract) = failure.contract {
                rendered.push_str(&format!(" = contract: {}\n", contract));
            }

            if let Some(ref cex) = failure.counterexample {
                let cex_str: Vec<String> = cex
                    .iter()
                    .map(|a| format!("{} = {}", a.variable, a.value))
                    .collect();
                rendered.push_str(&format!(" = counterexample: {}\n", cex_str.join(", ")));
            }

            if let Some(ref suggestion) = failure.suggestion {
                rendered.push_str(&format!(" = suggestion: {}\n", suggestion));
            }

            let span = RustcSpan {
                byte_end: 0,
                byte_start: 0,
                column_end: 1,
                column_start: 1,
                expansion: None,
                file_name,
                is_primary: true,
                label: None,
                line_end: line,
                line_start: line,
                suggested_replacement: None,
                suggestion_applicability: None,
                text: vec![],
            };

            let diagnostic = RustcDiagnostic {
                reason: "compiler-message".to_string(),
                message: RustcMessage {
                    rendered,
                    message_type: "diagnostic".to_string(),
                    children: vec![],
                    code: Some(RustcCode {
                        code: format!("rust-fv::{}", failure.vc_kind),
                        explanation: None,
                    }),
                    level: "error".to_string(),
                    message: failure.description.clone(),
                    spans: vec![span],
                },
            };

            diagnostics.push(diagnostic);
        }
    }

    // Add summary diagnostic
    let summary_msg = format!(
        "rust-fv: {} verified, {} failed",
        report.summary.ok, report.summary.fail
    );

    let summary_level = if report.summary.fail > 0 {
        "warning"
    } else {
        "note"
    };

    diagnostics.push(RustcDiagnostic {
        reason: "compiler-message".to_string(),
        message: RustcMessage {
            rendered: summary_msg.clone(),
            message_type: "diagnostic".to_string(),
            children: vec![],
            code: None,
            level: summary_level.to_string(),
            message: summary_msg,
            spans: vec![],
        },
    });

    diagnostics
}

/// Emit rustc-compatible diagnostics to stdout.
///
/// Each diagnostic is printed as a single line of JSON (not pretty-printed).
/// This is the format rust-analyzer's flycheck expects.
pub fn emit_rustc_diagnostics(report: &JsonVerificationReport) {
    let diagnostics = convert_report_to_rustc_diagnostics(report);
    for diag in &diagnostics {
        if let Ok(json) = serde_json::to_string(diag) {
            println!("{}", json);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::json_output::{
        JsonAssignment, JsonFailure, JsonFunctionResult, JsonSummary, JsonVerificationReport,
    };

    /// Helper: create a report with no failures.
    fn report_all_pass() -> JsonVerificationReport {
        JsonVerificationReport {
            crate_name: "my_crate".to_string(),
            functions: vec![JsonFunctionResult {
                name: "good_func".to_string(),
                status: "ok".to_string(),
                vc_count: 3,
                verified_count: 3,
                failures: vec![],
            }],
            summary: JsonSummary {
                total: 1,
                ok: 1,
                fail: 0,
                timeout: 0,
            },
        }
    }

    /// Helper: create a report with a single failure with full details.
    fn report_single_failure_full() -> JsonVerificationReport {
        JsonVerificationReport {
            crate_name: "my_crate".to_string(),
            functions: vec![JsonFunctionResult {
                name: "bad_func".to_string(),
                status: "fail".to_string(),
                vc_count: 2,
                verified_count: 1,
                failures: vec![JsonFailure {
                    vc_kind: "postcondition".to_string(),
                    description: "postcondition may not hold".to_string(),
                    contract: Some("result > 0".to_string()),
                    source_file: Some("src/lib.rs".to_string()),
                    source_line: Some(5),
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
        }
    }

    /// Helper: create a report with a failure with minimal details.
    fn report_single_failure_minimal() -> JsonVerificationReport {
        JsonVerificationReport {
            crate_name: "my_crate".to_string(),
            functions: vec![JsonFunctionResult {
                name: "bad_func".to_string(),
                status: "fail".to_string(),
                vc_count: 1,
                verified_count: 0,
                failures: vec![JsonFailure {
                    vc_kind: "overflow".to_string(),
                    description: "arithmetic overflow possible".to_string(),
                    contract: None,
                    source_file: None,
                    source_line: None,
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
        }
    }

    /// Helper: create a report with multiple failures across functions.
    fn report_multiple_failures() -> JsonVerificationReport {
        JsonVerificationReport {
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
                    failures: vec![
                        JsonFailure {
                            vc_kind: "postcondition".to_string(),
                            description: "postcondition may not hold".to_string(),
                            contract: Some("result >= 0".to_string()),
                            source_file: Some("src/lib.rs".to_string()),
                            source_line: Some(10),
                            source_column: None,
                            counterexample: None,
                            counterexample_v2: None,
                            suggestion: None,
                        },
                        JsonFailure {
                            vc_kind: "overflow".to_string(),
                            description: "overflow possible".to_string(),
                            contract: None,
                            source_file: Some("src/lib.rs".to_string()),
                            source_line: Some(12),
                            source_column: None,
                            counterexample: Some(vec![JsonAssignment {
                                variable: "n".to_string(),
                                value: "2147483647".to_string(),
                            }]),
                            counterexample_v2: None,
                            suggestion: Some("Use checked_add".to_string()),
                        },
                    ],
                },
                JsonFunctionResult {
                    name: "func_c".to_string(),
                    status: "fail".to_string(),
                    vc_count: 1,
                    verified_count: 0,
                    failures: vec![JsonFailure {
                        vc_kind: "precondition".to_string(),
                        description: "precondition not satisfied".to_string(),
                        contract: Some("x > 0".to_string()),
                        source_file: Some("src/utils.rs".to_string()),
                        source_line: Some(25),
                        source_column: None,
                        counterexample: Some(vec![JsonAssignment {
                            variable: "x".to_string(),
                            value: "0".to_string(),
                        }]),
                        counterexample_v2: None,
                        suggestion: None,
                    }],
                },
            ],
            summary: JsonSummary {
                total: 3,
                ok: 1,
                fail: 2,
                timeout: 0,
            },
        }
    }

    #[test]
    fn test_no_failures_produces_only_summary() {
        let report = report_all_pass();
        let diagnostics = convert_report_to_rustc_diagnostics(&report);

        // Only the summary diagnostic should be present
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].message.level, "note");
        assert!(diagnostics[0].message.message.contains("1 verified"));
        assert!(diagnostics[0].message.message.contains("0 failed"));
        assert!(diagnostics[0].message.spans.is_empty());
    }

    #[test]
    fn test_single_failure_full_details() {
        let report = report_single_failure_full();
        let diagnostics = convert_report_to_rustc_diagnostics(&report);

        // 1 failure diagnostic + 1 summary = 2
        assert_eq!(diagnostics.len(), 2);

        let diag = &diagnostics[0];
        assert_eq!(diag.reason, "compiler-message");
        assert_eq!(diag.message.level, "error");
        assert_eq!(diag.message.message, "postcondition may not hold");
        assert_eq!(diag.message.message_type, "diagnostic");
        assert!(diag.message.children.is_empty());

        // Check code
        let code = diag.message.code.as_ref().unwrap();
        assert_eq!(code.code, "rust-fv::postcondition");
        assert!(code.explanation.is_none());

        // Check span
        assert_eq!(diag.message.spans.len(), 1);
        let span = &diag.message.spans[0];
        assert_eq!(span.file_name, "src/lib.rs");
        assert_eq!(span.line_start, 5);
        assert_eq!(span.line_end, 5);
        assert_eq!(span.column_start, 1);
        assert!(span.is_primary);

        // Check rendered text includes contract, counterexample, suggestion
        assert!(diag.message.rendered.contains("contract: result > 0"));
        assert!(
            diag.message
                .rendered
                .contains("counterexample: x = -1, y = 0")
        );
        assert!(
            diag.message
                .rendered
                .contains("suggestion: Add bounds check")
        );
    }

    #[test]
    fn test_single_failure_minimal_details() {
        let report = report_single_failure_minimal();
        let diagnostics = convert_report_to_rustc_diagnostics(&report);

        assert_eq!(diagnostics.len(), 2);

        let diag = &diagnostics[0];
        assert_eq!(diag.message.message, "arithmetic overflow possible");

        // Check span uses defaults
        let span = &diag.message.spans[0];
        assert_eq!(span.file_name, "unknown");
        assert_eq!(span.line_start, 1);

        // Rendered should NOT contain contract/counterexample/suggestion lines
        assert!(!diag.message.rendered.contains("contract:"));
        assert!(!diag.message.rendered.contains("counterexample:"));
        assert!(!diag.message.rendered.contains("suggestion:"));

        // Code should still have rust-fv:: prefix
        let code = diag.message.code.as_ref().unwrap();
        assert_eq!(code.code, "rust-fv::overflow");
    }

    #[test]
    fn test_multiple_failures_across_functions() {
        let report = report_multiple_failures();
        let diagnostics = convert_report_to_rustc_diagnostics(&report);

        // func_a: 0 failures, func_b: 2 failures, func_c: 1 failure + 1 summary = 4
        assert_eq!(diagnostics.len(), 4);

        // First two are from func_b
        assert_eq!(
            diagnostics[0].message.code.as_ref().unwrap().code,
            "rust-fv::postcondition"
        );
        assert_eq!(
            diagnostics[1].message.code.as_ref().unwrap().code,
            "rust-fv::overflow"
        );

        // Third is from func_c
        assert_eq!(
            diagnostics[2].message.code.as_ref().unwrap().code,
            "rust-fv::precondition"
        );

        // Last is summary
        assert!(diagnostics[3].message.code.is_none());
        assert_eq!(diagnostics[3].message.level, "warning");
        assert!(diagnostics[3].message.message.contains("1 verified"));
        assert!(diagnostics[3].message.message.contains("2 failed"));
    }

    #[test]
    fn test_output_is_valid_single_line_json() {
        let report = report_single_failure_full();
        let diagnostics = convert_report_to_rustc_diagnostics(&report);

        for diag in &diagnostics {
            let json = serde_json::to_string(diag).unwrap();
            // Must be single line (no newlines in JSON itself)
            assert!(
                !json.contains('\n') || json.contains("\\n"),
                "JSON output must be single-line; got: {}",
                json
            );
            // Must be valid JSON
            let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
            assert_eq!(parsed["reason"], "compiler-message");
        }
    }

    #[test]
    fn test_summary_diagnostic_format() {
        let report = report_multiple_failures();
        let diagnostics = convert_report_to_rustc_diagnostics(&report);
        let summary = diagnostics.last().unwrap();

        assert_eq!(summary.reason, "compiler-message");
        assert_eq!(summary.message.level, "warning");
        assert!(summary.message.code.is_none());
        assert!(summary.message.spans.is_empty());
        assert_eq!(summary.message.message, "rust-fv: 1 verified, 2 failed");
        assert_eq!(summary.message.rendered, summary.message.message);
    }

    #[test]
    fn test_diagnostic_code_has_rust_fv_prefix() {
        let report = report_multiple_failures();
        let diagnostics = convert_report_to_rustc_diagnostics(&report);

        // All non-summary diagnostics should have rust-fv:: prefix
        for diag in diagnostics.iter().take(diagnostics.len() - 1) {
            let code = diag.message.code.as_ref().unwrap();
            assert!(
                code.code.starts_with("rust-fv::"),
                "Code should start with 'rust-fv::' but got: {}",
                code.code
            );
        }
    }

    #[test]
    fn test_emit_rustc_diagnostics_smoke() {
        // Smoke test: emit_rustc_diagnostics should not panic
        let report = report_single_failure_full();
        emit_rustc_diagnostics(&report);
    }

    #[test]
    fn test_empty_report_only_summary() {
        let report = JsonVerificationReport {
            crate_name: "empty".to_string(),
            functions: vec![],
            summary: JsonSummary {
                total: 0,
                ok: 0,
                fail: 0,
                timeout: 0,
            },
        };
        let diagnostics = convert_report_to_rustc_diagnostics(&report);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].message.level, "note");
        assert!(diagnostics[0].message.message.contains("0 verified"));
    }

    #[test]
    fn test_rendered_format_with_location() {
        let report = report_single_failure_full();
        let diagnostics = convert_report_to_rustc_diagnostics(&report);
        let rendered = &diagnostics[0].message.rendered;

        // Should follow rustc-like format
        assert!(rendered.starts_with("error[rust-fv::postcondition]:"));
        assert!(rendered.contains(" --> src/lib.rs:5:1"));
    }
}
