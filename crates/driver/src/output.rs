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
}

/// Print verification results with colored output.
///
/// Output format:
/// ```text
///   [OK]      max(a: i32, b: i32) -> i32
///   [FAIL]    unsafe_div(a: i32, b: i32) -> i32 (division by zero at block 2)
///   [TIMEOUT] complex_loop() -> i32 (verification timed out)
///
/// Summary: 1 OK, 1 FAIL, 1 TIMEOUT
/// ```
pub fn print_verification_results(results: &[FunctionResult]) {
    if results.is_empty() {
        eprintln!("{}", "No annotated functions found.".dimmed());
        return;
    }

    eprintln!();
    for result in results {
        match result.status {
            VerificationStatus::Ok => {
                eprintln!(
                    "  {}  {} ({}/{} VCs)",
                    "[OK]".green().bold(),
                    result.name,
                    result.verified_count,
                    result.vc_count,
                );
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

    // Summary line
    let ok_count = results
        .iter()
        .filter(|r| r.status == VerificationStatus::Ok)
        .count();
    let fail_count = results
        .iter()
        .filter(|r| r.status == VerificationStatus::Fail)
        .count();
    let timeout_count = results
        .iter()
        .filter(|r| r.status == VerificationStatus::Timeout)
        .count();

    eprintln!();
    eprint!("Summary: ");
    let mut parts = Vec::new();
    if ok_count > 0 {
        parts.push(format!("{} {}", ok_count, "OK".green()));
    }
    if fail_count > 0 {
        parts.push(format!("{} {}", fail_count, "FAIL".red()));
    }
    if timeout_count > 0 {
        parts.push(format!("{} {}", timeout_count, "TIMEOUT".yellow()));
    }
    eprintln!("{}", parts.join(", "));
    eprintln!();
}

/// Print a header for the verification run.
pub fn print_header(crate_name: &str, crate_path: &str) {
    eprintln!(
        "{}",
        format!("Verifying {crate_name} ({crate_path})").bold()
    );
}
