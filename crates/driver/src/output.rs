/// Colored verification output formatter.
///
/// Produces per-function verification results with color-coded status:
///   [OK]      function_name (green)
///   [FAIL]    function_name - error detail (red)
///   [TIMEOUT] function_name - reason (yellow)
use colored::Colorize;

/// Status of a function's verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerificationStatus {
    /// All VCs verified (UNSAT)
    Ok,
    /// At least one VC failed (SAT) or errored
    Fail,
    /// Verification timed out
    Timeout,
    /// Verification skipped (cached result used)
    Skipped,
}

/// Result of verifying a single function.
#[derive(Debug, Clone)]
pub struct FunctionResult {
    pub name: String,
    pub status: VerificationStatus,
    /// Detail message for FAIL/TIMEOUT
    pub message: Option<String>,
    /// Number of VCs checked
    pub vc_count: usize,
    /// Number of VCs that verified
    pub verified_count: usize,
    /// Human-readable invalidation reason (for re-verified functions)
    pub invalidation_reason: Option<String>,
    /// Verification duration in milliseconds (None if cached)
    pub duration_ms: Option<u64>,
}

/// Print verification results with colored output.
///
/// Output format:
/// ```text
///   [OK]      max(a: i32, b: i32) -> i32 (42ms) -- Re-verifying: body changed
///   [SKIP]    helper() -> i32 (cached)
///   [FAIL]    unsafe_div(a: i32, b: i32) -> i32 (division by zero at block 2)
///   [TIMEOUT] complex_loop() -> i32 (verification timed out)
///
/// Summary: 1 OK, 1 SKIP, 1 FAIL, 1 TIMEOUT (total: 156ms)
/// ```
///
/// # Arguments
/// * `results` - Verification results to display
/// * `verbose` - If true, show per-function timing
pub fn print_verification_results(results: &[FunctionResult], verbose: bool) {
    if results.is_empty() {
        eprintln!("{}", "No annotated functions found.".dimmed());
        return;
    }

    eprintln!();
    for result in results {
        match result.status {
            VerificationStatus::Ok => {
                let mut line = format!(
                    "  {}  {} ({} VCs)",
                    "[OK]".green().bold(),
                    result.name,
                    result.vc_count,
                );

                // Add timing in verbose mode
                if verbose && let Some(duration) = result.duration_ms {
                    line.push_str(&format!(", {}ms", duration));
                }

                // Add invalidation reason (always shown for re-verified functions)
                if let Some(reason) = &result.invalidation_reason {
                    line.push_str(&format!(" -- Re-verifying: {}", reason));
                }

                eprintln!("{}", line);
            }
            VerificationStatus::Skipped => {
                let line = format!("  {}  {} (cached)", "[SKIP]".cyan().bold(), result.name,);

                eprintln!("{}", line);
            }
            VerificationStatus::Fail => {
                let detail = result.message.as_deref().unwrap_or("verification failed");
                eprintln!("  {}  {} ({})", "[FAIL]".red().bold(), result.name, detail,);
            }
            VerificationStatus::Timeout => {
                let detail = result
                    .message
                    .as_deref()
                    .unwrap_or("verification timed out");
                eprintln!(
                    "  {}  {} ({})",
                    "[TIMEOUT]".yellow().bold(),
                    result.name,
                    detail,
                );
            }
        }
    }

    // Summary line with timing
    let ok_count = results
        .iter()
        .filter(|r| r.status == VerificationStatus::Ok)
        .count();
    let skip_count = results
        .iter()
        .filter(|r| r.status == VerificationStatus::Skipped)
        .count();
    let fail_count = results
        .iter()
        .filter(|r| r.status == VerificationStatus::Fail)
        .count();
    let timeout_count = results
        .iter()
        .filter(|r| r.status == VerificationStatus::Timeout)
        .count();

    // Calculate total timing
    let total_ms: u64 = results.iter().filter_map(|r| r.duration_ms).sum();

    eprintln!();
    eprint!("Summary: ");
    let mut parts = Vec::new();
    if ok_count > 0 {
        parts.push(format!("{} {}", ok_count, "OK".green()));
    }
    if skip_count > 0 {
        parts.push(format!("{} {}", skip_count, "SKIP".cyan()));
    }
    if fail_count > 0 {
        parts.push(format!("{} {}", fail_count, "FAIL".red()));
    }
    if timeout_count > 0 {
        parts.push(format!("{} {}", timeout_count, "TIMEOUT".yellow()));
    }

    let summary = parts.join(", ");
    if total_ms > 0 {
        eprintln!("{} (total: {}ms)", summary, total_ms);
    } else {
        eprintln!("{}", summary);
    }
    eprintln!();
}

/// Print a header for the verification run.
pub fn print_header(crate_name: &str, crate_path: &str) {
    eprintln!(
        "{}",
        format!("Verifying {crate_name} ({crate_path})").bold()
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- VerificationStatus tests ---

    #[test]
    fn test_verification_status_ok() {
        let status = VerificationStatus::Ok;
        assert_eq!(status, VerificationStatus::Ok);
    }

    #[test]
    fn test_verification_status_fail() {
        let status = VerificationStatus::Fail;
        assert_eq!(status, VerificationStatus::Fail);
    }

    #[test]
    fn test_verification_status_timeout() {
        let status = VerificationStatus::Timeout;
        assert_eq!(status, VerificationStatus::Timeout);
    }

    #[test]
    fn test_verification_status_ne() {
        assert_ne!(VerificationStatus::Ok, VerificationStatus::Fail);
        assert_ne!(VerificationStatus::Ok, VerificationStatus::Timeout);
        assert_ne!(VerificationStatus::Fail, VerificationStatus::Timeout);
    }

    #[test]
    fn test_verification_status_clone() {
        let status = VerificationStatus::Fail;
        let cloned = status.clone();
        assert_eq!(status, cloned);
    }

    #[test]
    fn test_verification_status_debug() {
        let debug_str = format!("{:?}", VerificationStatus::Ok);
        assert_eq!(debug_str, "Ok");
        let debug_str = format!("{:?}", VerificationStatus::Fail);
        assert_eq!(debug_str, "Fail");
        let debug_str = format!("{:?}", VerificationStatus::Timeout);
        assert_eq!(debug_str, "Timeout");
    }

    // --- FunctionResult tests ---

    #[test]
    fn test_function_result_ok() {
        let result = FunctionResult {
            name: "my_func".to_string(),
            status: VerificationStatus::Ok,
            message: None,
            vc_count: 3,
            verified_count: 3,
            invalidation_reason: None,
            duration_ms: None,
        };
        assert_eq!(result.name, "my_func");
        assert_eq!(result.status, VerificationStatus::Ok);
        assert!(result.message.is_none());
        assert_eq!(result.vc_count, 3);
        assert_eq!(result.verified_count, 3);
    }

    #[test]
    fn test_function_result_fail() {
        let result = FunctionResult {
            name: "bad_func".to_string(),
            status: VerificationStatus::Fail,
            message: Some("postcondition failed".to_string()),
            vc_count: 5,
            verified_count: 3,
            invalidation_reason: None,
            duration_ms: None,
        };
        assert_eq!(result.name, "bad_func");
        assert_eq!(result.status, VerificationStatus::Fail);
        assert_eq!(result.message.as_deref(), Some("postcondition failed"));
        assert_eq!(result.vc_count, 5);
        assert_eq!(result.verified_count, 3);
    }

    #[test]
    fn test_function_result_timeout() {
        let result = FunctionResult {
            name: "slow_func".to_string(),
            status: VerificationStatus::Timeout,
            message: Some("verification timed out after 30s".to_string()),
            vc_count: 10,
            verified_count: 0,
            invalidation_reason: None,
            duration_ms: None,
        };
        assert_eq!(result.name, "slow_func");
        assert_eq!(result.status, VerificationStatus::Timeout);
        assert!(result.message.unwrap().contains("timed out"));
        assert_eq!(result.vc_count, 10);
        assert_eq!(result.verified_count, 0);
    }

    #[test]
    fn test_function_result_clone() {
        let result = FunctionResult {
            name: "func".to_string(),
            status: VerificationStatus::Ok,
            message: Some("all good".to_string()),
            vc_count: 1,
            verified_count: 1,
            invalidation_reason: None,
            duration_ms: None,
        };
        let cloned = result.clone();
        assert_eq!(cloned.name, result.name);
        assert_eq!(cloned.status, result.status);
        assert_eq!(cloned.message, result.message);
        assert_eq!(cloned.vc_count, result.vc_count);
        assert_eq!(cloned.verified_count, result.verified_count);
    }

    #[test]
    fn test_function_result_debug() {
        let result = FunctionResult {
            name: "func".to_string(),
            status: VerificationStatus::Ok,
            message: None,
            vc_count: 2,
            verified_count: 2,
            invalidation_reason: None,
            duration_ms: None,
        };
        let debug = format!("{:?}", result);
        assert!(debug.contains("func"));
        assert!(debug.contains("Ok"));
    }

    #[test]
    fn test_function_result_zero_vcs() {
        let result = FunctionResult {
            name: "empty_func".to_string(),
            status: VerificationStatus::Ok,
            message: None,
            vc_count: 0,
            verified_count: 0,
            invalidation_reason: None,
            duration_ms: None,
        };
        assert_eq!(result.vc_count, 0);
        assert_eq!(result.verified_count, 0);
    }

    #[test]
    fn test_verification_status_skipped() {
        let status = VerificationStatus::Skipped;
        assert_eq!(status, VerificationStatus::Skipped);
        assert_ne!(status, VerificationStatus::Ok);
    }

    // --- print_verification_results tests (output to stderr) ---

    #[test]
    fn test_print_verification_results_empty() {
        // Should not panic with empty results
        let results: Vec<FunctionResult> = vec![];
        print_verification_results(&results, false);
    }

    #[test]
    fn test_print_verification_results_single_ok() {
        let results = vec![FunctionResult {
            name: "add".to_string(),
            status: VerificationStatus::Ok,
            message: None,
            vc_count: 2,
            verified_count: 2,
            invalidation_reason: None,
            duration_ms: None,
        }];
        // Should not panic
        print_verification_results(&results, false);
    }

    #[test]
    fn test_print_verification_results_mixed() {
        let results = vec![
            FunctionResult {
                name: "ok_func".to_string(),
                status: VerificationStatus::Ok,
                message: None,
                vc_count: 1,
                verified_count: 1,
                invalidation_reason: None,
                duration_ms: None,
            },
            FunctionResult {
                name: "fail_func".to_string(),
                status: VerificationStatus::Fail,
                message: Some("postcondition failed".to_string()),
                vc_count: 3,
                verified_count: 1,
                invalidation_reason: None,
                duration_ms: None,
            },
            FunctionResult {
                name: "timeout_func".to_string(),
                status: VerificationStatus::Timeout,
                message: Some("timed out".to_string()),
                vc_count: 5,
                verified_count: 0,
                invalidation_reason: None,
                duration_ms: None,
            },
        ];
        // Should not panic
        print_verification_results(&results, false);
    }

    #[test]
    fn test_print_verification_results_skipped() {
        let results = vec![FunctionResult {
            name: "cached_func".to_string(),
            status: VerificationStatus::Skipped,
            message: None,
            vc_count: 2,
            verified_count: 2,
            invalidation_reason: None,
            duration_ms: None,
        }];
        print_verification_results(&results, false);
    }

    #[test]
    fn test_print_verification_results_with_timing() {
        let results = vec![
            FunctionResult {
                name: "func1".to_string(),
                status: VerificationStatus::Ok,
                message: None,
                vc_count: 2,
                verified_count: 2,
                invalidation_reason: Some("body changed".to_string()),
                duration_ms: Some(42),
            },
            FunctionResult {
                name: "func2".to_string(),
                status: VerificationStatus::Skipped,
                message: None,
                vc_count: 1,
                verified_count: 1,
                invalidation_reason: None,
                duration_ms: None,
            },
        ];
        print_verification_results(&results, true);
    }

    #[test]
    fn test_print_verification_results_with_invalidation_reason() {
        let results = vec![FunctionResult {
            name: "test_func".to_string(),
            status: VerificationStatus::Ok,
            message: None,
            vc_count: 3,
            verified_count: 3,
            invalidation_reason: Some("contract of helper changed".to_string()),
            duration_ms: Some(150),
        }];
        print_verification_results(&results, false);
    }
}
