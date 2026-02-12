/// Rustc-style diagnostics for verification failures.
///
/// Formats verification errors with:
/// - Source file and line number (when available)
/// - Colored arrows pointing to failing spec
/// - Counterexample with concrete variable values
/// - Fix suggestions for common failure patterns
use ariadne::{Color, ColorGenerator, Label, Report, ReportKind, Source};
use colored::Colorize;
use rust_fv_analysis::vcgen::VcKind;

/// Complete information about a verification failure for diagnostics.
pub struct VerificationFailure {
    pub function_name: String,
    pub vc_kind: VcKind,
    pub contract_text: Option<String>,
    pub source_file: Option<String>,
    pub source_line: Option<usize>,
    pub counterexample: Option<Vec<(String, String)>>,
    pub message: String,
}

/// Report a verification failure using rustc-style diagnostics.
///
/// If source location is available, uses ariadne for rich error reporting.
/// Otherwise, falls back to enhanced colored text output.
pub fn report_verification_failure(failure: &VerificationFailure) {
    if let (Some(source_file), Some(source_line)) = (&failure.source_file, failure.source_line) {
        // Use ariadne for rich source-based error reporting
        report_with_ariadne(failure, source_file, source_line);
    } else {
        // Fall back to enhanced text output
        report_text_only(failure);
    }
}

/// Report failure using ariadne with source file context.
fn report_with_ariadne(failure: &VerificationFailure, source_file: &str, source_line: usize) {
    // For now, ariadne requires reading the actual source file.
    // In a real rustc driver integration, we'd have access to the source map.
    // For this phase, we'll implement ariadne support but acknowledge that
    // source_file/source_line aren't yet populated by the driver.

    // Calculate offset (0-based) from line number
    let offset = source_line.saturating_sub(1);

    let mut colors = ColorGenerator::new();
    let color = colors.next();

    let report = Report::build(ReportKind::Error, source_file, offset)
        .with_message(format!(
            "verification failed: {}",
            vc_kind_description(&failure.vc_kind)
        ))
        .with_label(
            Label::new((source_file, offset..offset + 1))
                .with_message(failure.message.clone())
                .with_color(color),
        );

    let report = if let Some(ref contract) = failure.contract_text {
        report.with_note(format!("contract: {}", contract))
    } else {
        report
    };

    let report = if let Some(ref cx) = failure.counterexample {
        report.with_help(format_counterexample(cx))
    } else {
        report
    };

    let report = if let Some(suggestion) = suggest_fix(&failure.vc_kind) {
        report.with_help(suggestion)
    } else {
        report
    };

    // For now, we can't actually read source files, so we skip eprint for ariadne.
    // When integrated with rustc driver, we'd use the real source map:
    // report.finish().eprint((source_file, Source::from(source_text))).unwrap();

    // Fall back to text for now
    report_text_only(failure);
}

/// Report failure using colored text output (no source file access).
fn report_text_only(failure: &VerificationFailure) {
    let error_code = "V001";
    let header = format!(
        "error[{}]: verification failed: {}",
        error_code,
        failure.function_name
    );

    eprintln!("{}", header.red().bold());
    eprintln!("  {}: {}", "kind".bold(), vc_kind_description(&failure.vc_kind));

    if let Some(ref contract) = failure.contract_text {
        eprintln!("  {}: {}", "contract".bold(), contract);
    }

    eprintln!("  {}: {}", "reason".bold(), failure.message);

    if let Some(ref cx) = failure.counterexample {
        eprintln!();
        eprintln!("{}", format_counterexample(cx));
    }

    if let Some(suggestion) = suggest_fix(&failure.vc_kind) {
        eprintln!();
        eprintln!("{}: {}", "help".cyan().bold(), suggestion);
    }

    eprintln!();
}

/// Get a human-readable description of a VC kind.
fn vc_kind_description(vc_kind: &VcKind) -> &'static str {
    match vc_kind {
        VcKind::Precondition => "precondition not satisfied",
        VcKind::Postcondition => "postcondition not proven",
        VcKind::LoopInvariantInit => "loop invariant does not hold on entry",
        VcKind::LoopInvariantPreserve => "loop invariant not preserved",
        VcKind::LoopInvariantExit => "loop invariant insufficient for postcondition",
        VcKind::Overflow => "arithmetic overflow possible",
        VcKind::DivisionByZero => "division by zero possible",
        VcKind::ShiftBounds => "shift amount out of bounds",
        VcKind::Assertion => "assertion might fail",
        VcKind::PanicFreedom => "panic possible",
    }
}

/// Suggest a fix for common verification failure patterns.
pub fn suggest_fix(vc_kind: &VcKind) -> Option<String> {
    match vc_kind {
        VcKind::Overflow => Some(
            "Consider adding a bounds check or using checked_add/wrapping_add".to_string(),
        ),
        VcKind::Precondition => Some(
            "The caller does not satisfy the callee's precondition. \
             Strengthen the caller's requires clause or weaken the callee's."
                .to_string(),
        ),
        VcKind::Postcondition => Some(
            "The function body does not satisfy the ensures clause. \
             Check return paths and edge cases."
                .to_string(),
        ),
        VcKind::LoopInvariantInit => Some(
            "The loop invariant does not hold before the loop. \
             Ensure initialization establishes the invariant."
                .to_string(),
        ),
        VcKind::LoopInvariantPreserve => Some(
            "The loop body does not preserve the invariant. \
             Check that the invariant holds after each iteration."
                .to_string(),
        ),
        VcKind::DivisionByZero => Some(
            "Add a check divisor != 0 or add #[requires(divisor != 0)]".to_string(),
        ),
        VcKind::Assertion => Some(
            "The assert condition may not hold on all paths. \
             Add preconditions to constrain inputs."
                .to_string(),
        ),
        _ => None,
    }
}

/// Format counterexample assignments for display.
pub fn format_counterexample(assignments: &[(String, String)]) -> String {
    // Filter out internal variables (those starting with _ that look like temporaries)
    let visible: Vec<_> = assignments
        .iter()
        .filter(|(name, _)| {
            // Show parameters (_1, _2, etc.) but hide complex temporaries
            if name.starts_with('_') {
                // Keep if it's a simple parameter-like name (_1, _2, _10, etc.)
                name.chars().skip(1).all(|c| c.is_ascii_digit())
            } else {
                true
            }
        })
        .collect();

    if visible.is_empty() {
        return "Counterexample: (no user-visible variables)".to_string();
    }

    let mut result = "Counterexample:".to_string();
    for (name, value) in visible {
        // Try to convert bitvector hex values to decimal for readability
        let readable_value = parse_bitvec_value(value).unwrap_or_else(|| value.clone());
        result.push_str(&format!("\n    {} = {}", name, readable_value));
    }

    result
}

/// Parse a Z3 bitvector value to a more readable format.
///
/// Z3 outputs bitvectors as `#xHEX` or `#bBINARY`. Convert to decimal when recognizable.
fn parse_bitvec_value(value: &str) -> Option<String> {
    if let Some(hex_str) = value.strip_prefix("#x") {
        // Hex bitvector: parse as i128
        if let Ok(int_val) = i128::from_str_radix(hex_str, 16) {
            return Some(int_val.to_string());
        }
    } else if let Some(bin_str) = value.strip_prefix("#b") {
        // Binary bitvector: parse as i128
        if let Ok(int_val) = i128::from_str_radix(bin_str, 2) {
            return Some(int_val.to_string());
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_bitvec_hex() {
        assert_eq!(parse_bitvec_value("#x0000002a"), Some("42".to_string()));
        assert_eq!(
            parse_bitvec_value("#xffffffff"),
            Some("-1".to_string()) // i128 interpretation
        );
    }

    #[test]
    fn test_parse_bitvec_binary() {
        assert_eq!(parse_bitvec_value("#b00101010"), Some("42".to_string()));
    }

    #[test]
    fn test_format_counterexample_filters_internals() {
        let assignments = vec![
            ("_1".to_string(), "42".to_string()),
            ("_temp_123".to_string(), "99".to_string()),
            ("_2".to_string(), "-1".to_string()),
        ];
        let formatted = format_counterexample(&assignments);
        assert!(formatted.contains("_1 = 42"));
        assert!(formatted.contains("_2 = -1"));
        assert!(!formatted.contains("_temp_123"));
    }

    #[test]
    fn test_suggest_fix_overflow() {
        let suggestion = suggest_fix(&VcKind::Overflow);
        assert!(suggestion.is_some());
        assert!(suggestion.unwrap().contains("checked_add"));
    }

    #[test]
    fn test_suggest_fix_division_by_zero() {
        let suggestion = suggest_fix(&VcKind::DivisionByZero);
        assert!(suggestion.is_some());
        assert!(suggestion.unwrap().contains("divisor != 0"));
    }
}
