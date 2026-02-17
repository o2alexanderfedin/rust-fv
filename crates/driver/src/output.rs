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

/// Print the bv2int summary report table.
///
/// Output format:
/// ```text
/// bv2int Report:
///   Function          | Encoding  | BV Time | Int Time | Speedup
///   ---------------------------------------------------------------
///   add_integers      | Integer   |   120ms |     40ms | 3.0x faster
///   bitwise_and_mask  | Bitvector |       - |        - | ineligible: uses bitwise `&`
/// ```
///
/// Sorted by speedup factor descending (eligible functions first, then ineligible).
pub fn print_bv2int_report(records: &[crate::callbacks::Bv2intFunctionRecord]) {
    if records.is_empty() {
        return;
    }

    // Convert to Bv2intFunctionReport for structured access
    let reports: Vec<Bv2intFunctionReport> = records
        .iter()
        .map(Bv2intFunctionReport::from_record)
        .collect();

    eprintln!();
    eprintln!("{}", "bv2int Report:".bold());
    eprintln!(
        "  {:<30} | {:<9} | {:>7} | {:>8} | Speedup / Status",
        "Function", "Encoding", "BV Time", "Int Time"
    );
    eprintln!("  {}", "-".repeat(80));

    // Sort: eligible (by speedup desc) before ineligible
    let mut sorted: Vec<&Bv2intFunctionReport> = reports.iter().collect();
    sorted.sort_by(|a, b| {
        match (a.eligible, b.eligible) {
            (true, false) => std::cmp::Ordering::Less,
            (false, true) => std::cmp::Ordering::Greater,
            (true, true) => {
                // Both eligible: sort by speedup descending
                let sa = a.speedup_factor.unwrap_or(1.0);
                let sb = b.speedup_factor.unwrap_or(1.0);
                sb.partial_cmp(&sa).unwrap_or(std::cmp::Ordering::Equal)
            }
            (false, false) => a.func_name.cmp(&b.func_name),
        }
    });

    for report in sorted {
        let bv_time = report
            .bitvec_time_ms
            .map(|ms| format!("{ms}ms"))
            .unwrap_or_else(|| "-".to_string());
        let int_time = report
            .bv2int_time_ms
            .map(|ms| format!("{ms}ms"))
            .unwrap_or_else(|| "-".to_string());

        let status = if report.eligible {
            match report.speedup_factor {
                Some(s) if s >= 1.5 => format!("{:.1}x faster", s).green().to_string(),
                Some(s) if s < 0.5 => format!("{:.1}x slower", 1.0 / s).red().to_string(),
                Some(s) if s >= 1.0 => format!("{:.1}x faster", s).yellow().to_string(),
                Some(s) => format!("{:.1}x slower", 1.0 / s).yellow().to_string(),
                None => "pending".dimmed().to_string(),
            }
        } else {
            let reason = report.skip_reason.as_deref().unwrap_or("ineligible");
            format!("skip: {reason}").dimmed().to_string()
        };

        eprintln!(
            "  {:<30} | {:<9} | {:>7} | {:>8} | {}",
            // Truncate long names
            if report.func_name.len() > 30 {
                format!("...{}", &report.func_name[report.func_name.len() - 27..])
            } else {
                report.func_name.clone()
            },
            report.encoding_used,
            bv_time,
            int_time,
            status,
        );
    }
    eprintln!();
}

/// Per-function bv2int report entry for structured output.
///
/// A flattened view of `Bv2intFunctionRecord` suitable for report formatting.
/// Holds all fields needed to render one row in the bv2int summary table.
#[derive(Debug, Clone)]
pub struct Bv2intFunctionReport {
    /// Function qualified name.
    pub func_name: String,
    /// Encoding actually used for this function ("Integer" or "Bitvector").
    pub encoding_used: String,
    /// Bitvector solver time in milliseconds (None if not measured).
    pub bitvec_time_ms: Option<u64>,
    /// Integer solver time in milliseconds (None if not measured).
    pub bv2int_time_ms: Option<u64>,
    /// Speedup factor: bitvec_ms / bv2int_ms (None if not measured).
    pub speedup_factor: Option<f64>,
    /// Whether the function was statically eligible for bv2int.
    pub eligible: bool,
    /// Human-readable reason when ineligible (None if eligible).
    pub skip_reason: Option<String>,
}

impl Bv2intFunctionReport {
    /// Build a report from a `Bv2intFunctionRecord`.
    pub fn from_record(record: &crate::callbacks::Bv2intFunctionRecord) -> Self {
        Self {
            func_name: record.func_name.clone(),
            encoding_used: if record.bv2int_used {
                "Integer".to_string()
            } else {
                "Bitvector".to_string()
            },
            bitvec_time_ms: record.bitvec_time_ms,
            bv2int_time_ms: record.bv2int_time_ms,
            speedup_factor: record.speedup_factor,
            eligible: record.eligible,
            skip_reason: record.skip_reason.clone(),
        }
    }
}

/// Format a per-function bv2int timing comparison string.
///
/// # Examples
/// ```text
/// "bitvector: 120ms, bv2int: 40ms (3.0x faster)"
/// "bitvector: 40ms, bv2int: 120ms (3.0x slower)"
/// ```
pub fn format_bv2int_timing(func_name: &str, bv_ms: u64, int_ms: u64) -> String {
    let speedup = if int_ms == 0 {
        f64::INFINITY
    } else {
        bv_ms as f64 / int_ms as f64
    };
    let direction = if speedup >= 1.0 {
        format!("{speedup:.1}x faster")
    } else {
        format!("{:.1}x slower", 1.0 / speedup)
    };
    format!(
        "[rust-fv] bv2int `{func_name}`: bitvector: {bv_ms}ms, bv2int: {int_ms}ms ({direction})"
    )
}

/// Check whether a bv2int slowdown warning should be emitted.
///
/// Returns `Some(warning_message)` when `speedup < 1.0 / threshold`, which
/// means bv2int is more than `threshold` times slower than bitvector encoding.
///
/// # Arguments
/// * `func_name` - Function name (used in warning message)
/// * `speedup_factor` - Ratio: bitvec_time / bv2int_time (< 1.0 means slower)
/// * `threshold` - Slowdown threshold (default 2.0: warn when 2x+ slower)
pub fn check_slowdown_warning(
    func_name: &str,
    speedup_factor: f64,
    threshold: f64,
) -> Option<String> {
    if speedup_factor < 1.0 / threshold {
        Some(format!(
            "[rust-fv] warning: bv2int is {:.1}x slower than bitvector for `{}` \
             (threshold: {}x) -- consider #[fv::no_bv2int]",
            1.0 / speedup_factor,
            func_name,
            threshold
        ))
    } else {
        None
    }
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

    // --- format_bv2int_timing tests ---

    #[test]
    fn test_format_bv2int_timing_faster() {
        let s = format_bv2int_timing("add", 120, 40);
        assert!(s.contains("bitvector: 120ms"));
        assert!(s.contains("bv2int: 40ms"));
        assert!(s.contains("faster"));
        assert!(s.contains("add"));
    }

    #[test]
    fn test_format_bv2int_timing_slower() {
        let s = format_bv2int_timing("my_fn", 40, 120);
        assert!(s.contains("bitvector: 40ms"));
        assert!(s.contains("bv2int: 120ms"));
        assert!(s.contains("slower"));
    }

    #[test]
    fn test_format_bv2int_timing_equal_speed() {
        let s = format_bv2int_timing("equal_fn", 100, 100);
        assert!(s.contains("bitvector: 100ms"));
        assert!(s.contains("bv2int: 100ms"));
        // speedup = 1.0 → "1.0x faster"
        assert!(s.contains("faster"));
    }

    #[test]
    fn test_format_bv2int_timing_zero_int_time() {
        // Zero int time → infinity speedup → "faster"
        let s = format_bv2int_timing("fast_fn", 100, 0);
        assert!(s.contains("faster"));
    }

    // --- check_slowdown_warning tests ---

    #[test]
    fn test_check_slowdown_warning_none_when_fast() {
        // bv2int is 3x faster (speedup = 3.0), threshold = 2.0 → no warning
        let warning = check_slowdown_warning("fast_fn", 3.0, 2.0);
        assert!(warning.is_none());
    }

    #[test]
    fn test_check_slowdown_warning_none_when_equal() {
        // speedup = 1.0 (same speed), threshold = 2.0 → no warning
        let warning = check_slowdown_warning("even_fn", 1.0, 2.0);
        assert!(warning.is_none());
    }

    #[test]
    fn test_check_slowdown_warning_none_just_below_threshold() {
        // speedup = 0.6 (slightly slower but within 2x), threshold = 2.0
        // 0.6 >= 1.0/2.0 = 0.5 → no warning
        let warning = check_slowdown_warning("almost_fn", 0.6, 2.0);
        assert!(warning.is_none());
    }

    #[test]
    fn test_check_slowdown_warning_triggered_at_threshold() {
        // speedup = 0.4 (2.5x slower), threshold = 2.0
        // 0.4 < 1.0/2.0 = 0.5 → warning
        let warning = check_slowdown_warning("slow_fn", 0.4, 2.0);
        assert!(warning.is_some());
        let w = warning.unwrap();
        assert!(w.contains("slow_fn"));
        assert!(w.contains("threshold: 2"));
        assert!(w.contains("slower"));
    }

    #[test]
    fn test_check_slowdown_warning_message_contains_function_name() {
        let warning = check_slowdown_warning("my_function", 0.1, 2.0);
        assert!(warning.is_some());
        assert!(warning.unwrap().contains("my_function"));
    }

    #[test]
    fn test_check_slowdown_warning_custom_threshold() {
        // threshold = 5.0: only warn when 5x+ slower
        // speedup = 0.3 (3.3x slower) → no warning with threshold 5.0
        let warning = check_slowdown_warning("fn1", 0.3, 5.0);
        assert!(warning.is_none());
        // speedup = 0.1 (10x slower) → warning with threshold 5.0
        let warning = check_slowdown_warning("fn2", 0.1, 5.0);
        assert!(warning.is_some());
    }

    // --- Bv2intFunctionReport tests ---

    #[test]
    fn test_bv2int_function_report_from_record_integer_encoding() {
        let record = crate::callbacks::Bv2intFunctionRecord {
            func_name: "my_fn".to_string(),
            eligible: true,
            skip_reason: None,
            bv2int_used: true,
            bitvec_time_ms: Some(100),
            bv2int_time_ms: Some(30),
            speedup_factor: Some(3.33),
        };
        let report = Bv2intFunctionReport::from_record(&record);
        assert_eq!(report.func_name, "my_fn");
        assert_eq!(report.encoding_used, "Integer");
        assert_eq!(report.bitvec_time_ms, Some(100));
        assert_eq!(report.bv2int_time_ms, Some(30));
        assert!(report.eligible);
        assert!(report.skip_reason.is_none());
    }

    #[test]
    fn test_bv2int_function_report_from_record_bitvector_encoding() {
        let record = crate::callbacks::Bv2intFunctionRecord {
            func_name: "bw_fn".to_string(),
            eligible: false,
            skip_reason: Some("uses bitwise &".to_string()),
            bv2int_used: false,
            bitvec_time_ms: None,
            bv2int_time_ms: None,
            speedup_factor: None,
        };
        let report = Bv2intFunctionReport::from_record(&record);
        assert_eq!(report.encoding_used, "Bitvector");
        assert!(!report.eligible);
        assert_eq!(report.skip_reason.as_deref(), Some("uses bitwise &"));
    }

    // --- print_bv2int_report smoke test ---

    #[test]
    fn test_print_bv2int_report_empty() {
        let records: Vec<crate::callbacks::Bv2intFunctionRecord> = vec![];
        // Should not panic
        print_bv2int_report(&records);
    }

    #[test]
    fn test_print_bv2int_report_single_eligible() {
        let records = vec![crate::callbacks::Bv2intFunctionRecord {
            func_name: "add_integers".to_string(),
            eligible: true,
            skip_reason: None,
            bv2int_used: true,
            bitvec_time_ms: Some(120),
            bv2int_time_ms: Some(40),
            speedup_factor: Some(3.0),
        }];
        // Should not panic
        print_bv2int_report(&records);
    }

    #[test]
    fn test_print_bv2int_report_ineligible_with_reason() {
        let records = vec![crate::callbacks::Bv2intFunctionRecord {
            func_name: "bitwise_and_mask".to_string(),
            eligible: false,
            skip_reason: Some("uses bitwise `&` at line 12".to_string()),
            bv2int_used: false,
            bitvec_time_ms: None,
            bv2int_time_ms: None,
            speedup_factor: None,
        }];
        print_bv2int_report(&records);
    }

    #[test]
    fn test_print_bv2int_report_mixed() {
        let records = vec![
            crate::callbacks::Bv2intFunctionRecord {
                func_name: "fast_fn".to_string(),
                eligible: true,
                skip_reason: None,
                bv2int_used: true,
                bitvec_time_ms: Some(200),
                bv2int_time_ms: Some(50),
                speedup_factor: Some(4.0),
            },
            crate::callbacks::Bv2intFunctionRecord {
                func_name: "slow_fn".to_string(),
                eligible: true,
                skip_reason: None,
                bv2int_used: true,
                bitvec_time_ms: Some(50),
                bv2int_time_ms: Some(200),
                speedup_factor: Some(0.25),
            },
            crate::callbacks::Bv2intFunctionRecord {
                func_name: "ineligible_fn".to_string(),
                eligible: false,
                skip_reason: Some("uses bitwise |".to_string()),
                bv2int_used: false,
                bitvec_time_ms: None,
                bv2int_time_ms: None,
                speedup_factor: None,
            },
        ];
        print_bv2int_report(&records);
    }
}
