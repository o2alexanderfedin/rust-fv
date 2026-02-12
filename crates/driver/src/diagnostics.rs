/// Rustc-style diagnostics for verification failures.
///
/// Formats verification errors with:
/// - Source file and line number (when available)
/// - Colored arrows pointing to failing spec
/// - Counterexample with concrete variable values
/// - Fix suggestions for common failure patterns
use ariadne::{ColorGenerator, Label, Report, ReportKind};
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

    let _report = if let Some(suggestion) = suggest_fix(&failure.vc_kind) {
        report.with_help(suggestion)
    } else {
        report
    };

    // For now, we can't actually read source files, so we skip eprint for ariadne.
    // When integrated with rustc driver, we'd use the real source map:
    // _report.finish().eprint((source_file, Source::from(source_text))).unwrap();

    // Fall back to text for now
    report_text_only(failure);
}

/// Report failure using colored text output (no source file access).
fn report_text_only(failure: &VerificationFailure) {
    let error_code = "V001";
    let header = format!(
        "error[{}]: verification failed: {}",
        error_code, failure.function_name
    );

    eprintln!("{}", header.red().bold());
    eprintln!(
        "  {}: {}",
        "kind".bold(),
        vc_kind_description(&failure.vc_kind)
    );

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
        VcKind::Overflow => {
            Some("Consider adding a bounds check or using checked_add/wrapping_add".to_string())
        }
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
        VcKind::DivisionByZero => {
            Some("Add a check divisor != 0 or add #[requires(divisor != 0)]".to_string())
        }
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

    // --- parse_bitvec_value tests ---

    #[test]
    fn test_parse_bitvec_hex() {
        assert_eq!(parse_bitvec_value("#x0000002a"), Some("42".to_string()));
        // Note: #xffffffff parses as 4294967295 (unsigned interpretation)
        // since we don't know the bit width. For proper signed interpretation,
        // we'd need to track the width, which would require more context.
        assert_eq!(
            parse_bitvec_value("#xffffffff"),
            Some("4294967295".to_string())
        );
    }

    #[test]
    fn test_parse_bitvec_binary() {
        assert_eq!(parse_bitvec_value("#b00101010"), Some("42".to_string()));
    }

    #[test]
    fn test_parse_bitvec_hex_zero() {
        assert_eq!(parse_bitvec_value("#x00000000"), Some("0".to_string()));
    }

    #[test]
    fn test_parse_bitvec_hex_one() {
        assert_eq!(parse_bitvec_value("#x00000001"), Some("1".to_string()));
    }

    #[test]
    fn test_parse_bitvec_binary_zero() {
        assert_eq!(parse_bitvec_value("#b0"), Some("0".to_string()));
    }

    #[test]
    fn test_parse_bitvec_binary_one() {
        assert_eq!(parse_bitvec_value("#b1"), Some("1".to_string()));
    }

    #[test]
    fn test_parse_bitvec_not_bitvec() {
        assert_eq!(parse_bitvec_value("42"), None);
        assert_eq!(parse_bitvec_value("true"), None);
        assert_eq!(parse_bitvec_value("hello"), None);
        assert_eq!(parse_bitvec_value(""), None);
    }

    #[test]
    fn test_parse_bitvec_hex_invalid_chars() {
        // #x followed by invalid hex should return None
        assert_eq!(parse_bitvec_value("#xZZZZ"), None);
    }

    #[test]
    fn test_parse_bitvec_binary_invalid_chars() {
        // #b followed by non-binary chars should return None
        assert_eq!(parse_bitvec_value("#b123"), None);
    }

    #[test]
    fn test_parse_bitvec_hex_large_value() {
        // 64-bit max value
        assert_eq!(
            parse_bitvec_value("#xffffffffffffffff"),
            Some("18446744073709551615".to_string())
        );
    }

    #[test]
    fn test_parse_bitvec_hex_prefix_only() {
        // Just "#x" with no digits - from_str_radix on empty string returns Err
        assert_eq!(parse_bitvec_value("#x"), None);
    }

    #[test]
    fn test_parse_bitvec_binary_prefix_only() {
        assert_eq!(parse_bitvec_value("#b"), None);
    }

    // --- format_counterexample tests ---

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
    fn test_format_counterexample_empty() {
        let assignments: Vec<(String, String)> = vec![];
        let formatted = format_counterexample(&assignments);
        assert_eq!(formatted, "Counterexample: (no user-visible variables)");
    }

    #[test]
    fn test_format_counterexample_all_filtered() {
        // All variables are complex temporaries that get filtered out
        let assignments = vec![
            ("_temp_abc".to_string(), "1".to_string()),
            ("_foo_bar".to_string(), "2".to_string()),
            ("_complex_temp".to_string(), "3".to_string()),
        ];
        let formatted = format_counterexample(&assignments);
        assert_eq!(formatted, "Counterexample: (no user-visible variables)");
    }

    #[test]
    fn test_format_counterexample_named_variables() {
        let assignments = vec![
            ("x".to_string(), "42".to_string()),
            ("y".to_string(), "-1".to_string()),
        ];
        let formatted = format_counterexample(&assignments);
        assert!(formatted.starts_with("Counterexample:"));
        assert!(formatted.contains("x = 42"));
        assert!(formatted.contains("y = -1"));
    }

    #[test]
    fn test_format_counterexample_with_bitvec_values() {
        let assignments = vec![("x".to_string(), "#x0000002a".to_string())];
        let formatted = format_counterexample(&assignments);
        // Should convert #x0000002a to 42
        assert!(formatted.contains("x = 42"));
    }

    #[test]
    fn test_format_counterexample_mixed_filtered_and_visible() {
        let assignments = vec![
            ("_1".to_string(), "10".to_string()),
            ("_temp_x".to_string(), "99".to_string()),
            ("result".to_string(), "20".to_string()),
            ("_abc_def".to_string(), "77".to_string()),
            ("_10".to_string(), "30".to_string()),
        ];
        let formatted = format_counterexample(&assignments);
        assert!(formatted.contains("_1 = 10"));
        assert!(formatted.contains("result = 20"));
        assert!(formatted.contains("_10 = 30"));
        assert!(!formatted.contains("_temp_x"));
        assert!(!formatted.contains("_abc_def"));
    }

    #[test]
    fn test_format_counterexample_parameter_like_names() {
        // _1, _2, _10 etc. should be kept (all digits after underscore)
        let assignments = vec![
            ("_1".to_string(), "a".to_string()),
            ("_2".to_string(), "b".to_string()),
            ("_10".to_string(), "c".to_string()),
            ("_100".to_string(), "d".to_string()),
        ];
        let formatted = format_counterexample(&assignments);
        assert!(formatted.contains("_1 = a"));
        assert!(formatted.contains("_2 = b"));
        assert!(formatted.contains("_10 = c"));
        assert!(formatted.contains("_100 = d"));
    }

    #[test]
    fn test_format_counterexample_underscore_only() {
        // Just "_" has no digits after it, so skip(1) is empty,
        // and all() on empty iterator returns true -- it should be kept
        let assignments = vec![("_".to_string(), "val".to_string())];
        let formatted = format_counterexample(&assignments);
        // "_" with no chars after `_` -> chars().skip(1).all(is_digit) = true (vacuously)
        assert!(formatted.contains("_ = val"));
    }

    // --- vc_kind_description tests ---

    #[test]
    fn test_vc_kind_description_precondition() {
        assert_eq!(
            vc_kind_description(&VcKind::Precondition),
            "precondition not satisfied"
        );
    }

    #[test]
    fn test_vc_kind_description_postcondition() {
        assert_eq!(
            vc_kind_description(&VcKind::Postcondition),
            "postcondition not proven"
        );
    }

    #[test]
    fn test_vc_kind_description_loop_invariant_init() {
        assert_eq!(
            vc_kind_description(&VcKind::LoopInvariantInit),
            "loop invariant does not hold on entry"
        );
    }

    #[test]
    fn test_vc_kind_description_loop_invariant_preserve() {
        assert_eq!(
            vc_kind_description(&VcKind::LoopInvariantPreserve),
            "loop invariant not preserved"
        );
    }

    #[test]
    fn test_vc_kind_description_loop_invariant_exit() {
        assert_eq!(
            vc_kind_description(&VcKind::LoopInvariantExit),
            "loop invariant insufficient for postcondition"
        );
    }

    #[test]
    fn test_vc_kind_description_overflow() {
        assert_eq!(
            vc_kind_description(&VcKind::Overflow),
            "arithmetic overflow possible"
        );
    }

    #[test]
    fn test_vc_kind_description_division_by_zero() {
        assert_eq!(
            vc_kind_description(&VcKind::DivisionByZero),
            "division by zero possible"
        );
    }

    #[test]
    fn test_vc_kind_description_shift_bounds() {
        assert_eq!(
            vc_kind_description(&VcKind::ShiftBounds),
            "shift amount out of bounds"
        );
    }

    #[test]
    fn test_vc_kind_description_assertion() {
        assert_eq!(
            vc_kind_description(&VcKind::Assertion),
            "assertion might fail"
        );
    }

    #[test]
    fn test_vc_kind_description_panic_freedom() {
        assert_eq!(vc_kind_description(&VcKind::PanicFreedom), "panic possible");
    }

    // --- suggest_fix tests ---

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

    #[test]
    fn test_suggest_fix_precondition() {
        let suggestion = suggest_fix(&VcKind::Precondition);
        assert!(suggestion.is_some());
        let text = suggestion.unwrap();
        assert!(text.contains("precondition"));
    }

    #[test]
    fn test_suggest_fix_postcondition() {
        let suggestion = suggest_fix(&VcKind::Postcondition);
        assert!(suggestion.is_some());
        let text = suggestion.unwrap();
        assert!(text.contains("ensures"));
    }

    #[test]
    fn test_suggest_fix_loop_invariant_init() {
        let suggestion = suggest_fix(&VcKind::LoopInvariantInit);
        assert!(suggestion.is_some());
        let text = suggestion.unwrap();
        assert!(text.contains("invariant"));
    }

    #[test]
    fn test_suggest_fix_loop_invariant_preserve() {
        let suggestion = suggest_fix(&VcKind::LoopInvariantPreserve);
        assert!(suggestion.is_some());
        let text = suggestion.unwrap();
        assert!(text.contains("invariant"));
    }

    #[test]
    fn test_suggest_fix_assertion() {
        let suggestion = suggest_fix(&VcKind::Assertion);
        assert!(suggestion.is_some());
        let text = suggestion.unwrap();
        assert!(text.contains("assert"));
    }

    #[test]
    fn test_suggest_fix_shift_bounds_returns_none() {
        // ShiftBounds falls into the _ => None arm
        let suggestion = suggest_fix(&VcKind::ShiftBounds);
        assert!(suggestion.is_none());
    }

    #[test]
    fn test_suggest_fix_loop_invariant_exit_returns_none() {
        // LoopInvariantExit falls into the _ => None arm
        let suggestion = suggest_fix(&VcKind::LoopInvariantExit);
        assert!(suggestion.is_none());
    }

    #[test]
    fn test_suggest_fix_panic_freedom_returns_none() {
        // PanicFreedom falls into the _ => None arm
        let suggestion = suggest_fix(&VcKind::PanicFreedom);
        assert!(suggestion.is_none());
    }

    // --- VerificationFailure construction helper ---

    /// Helper to create a VerificationFailure for testing.
    fn make_failure(
        vc_kind: VcKind,
        contract_text: Option<&str>,
        source_file: Option<&str>,
        source_line: Option<usize>,
        counterexample: Option<Vec<(String, String)>>,
    ) -> VerificationFailure {
        VerificationFailure {
            function_name: "test_func".to_string(),
            vc_kind,
            contract_text: contract_text.map(|s| s.to_string()),
            source_file: source_file.map(|s| s.to_string()),
            source_line,
            counterexample,
            message: "test failure message".to_string(),
        }
    }

    // --- report_verification_failure tests ---
    // These tests exercise the public entry point and both code paths.
    // Output goes to stderr, so we verify the functions execute without panicking.

    #[test]
    fn test_report_verification_failure_without_source_location() {
        // No source_file/source_line -> takes the text-only path (line 33)
        let failure = make_failure(VcKind::Overflow, None, None, None, None);
        report_verification_failure(&failure);
        // If we reach here without panic, the text-only path executed successfully.
    }

    #[test]
    fn test_report_verification_failure_with_source_location() {
        // Both source_file and source_line present -> takes ariadne path (line 30)
        let failure = make_failure(
            VcKind::Postcondition,
            Some("result > 0"),
            Some("src/lib.rs"),
            Some(42),
            Some(vec![("x".to_string(), "0".to_string())]),
        );
        report_verification_failure(&failure);
    }

    #[test]
    fn test_report_verification_failure_source_file_only() {
        // source_file present but source_line is None -> text-only path
        let failure = make_failure(VcKind::Assertion, None, Some("src/lib.rs"), None, None);
        report_verification_failure(&failure);
    }

    #[test]
    fn test_report_verification_failure_source_line_only() {
        // source_line present but source_file is None -> text-only path
        let failure = make_failure(VcKind::DivisionByZero, None, None, Some(10), None);
        report_verification_failure(&failure);
    }

    // --- report_with_ariadne tests ---
    // These test the ariadne-based reporting path which builds rich error reports.

    #[test]
    fn test_report_with_ariadne_minimal() {
        // Minimal failure: no contract, no counterexample
        let failure = make_failure(VcKind::Overflow, None, None, None, None);
        report_with_ariadne(&failure, "src/lib.rs", 10);
    }

    #[test]
    fn test_report_with_ariadne_with_contract() {
        // With contract text -> covers line 61-62
        let failure = make_failure(VcKind::Precondition, Some("x > 0"), None, None, None);
        report_with_ariadne(&failure, "src/lib.rs", 5);
    }

    #[test]
    fn test_report_with_ariadne_without_contract() {
        // Without contract text -> covers line 64 (else branch)
        let failure = make_failure(VcKind::Postcondition, None, None, None, None);
        report_with_ariadne(&failure, "src/lib.rs", 20);
    }

    #[test]
    fn test_report_with_ariadne_with_counterexample() {
        // With counterexample -> covers lines 67-68
        let cx = vec![
            ("x".to_string(), "42".to_string()),
            ("y".to_string(), "-1".to_string()),
        ];
        let failure = make_failure(VcKind::Overflow, None, None, None, Some(cx));
        report_with_ariadne(&failure, "src/lib.rs", 15);
    }

    #[test]
    fn test_report_with_ariadne_without_counterexample() {
        // No counterexample -> covers line 70 (else branch)
        let failure = make_failure(VcKind::ShiftBounds, None, None, None, None);
        report_with_ariadne(&failure, "src/lib.rs", 1);
    }

    #[test]
    fn test_report_with_ariadne_with_fix_suggestion() {
        // VcKind with a fix suggestion -> covers lines 73-74
        let failure = make_failure(VcKind::Overflow, None, None, None, None);
        report_with_ariadne(&failure, "src/lib.rs", 100);
    }

    #[test]
    fn test_report_with_ariadne_without_fix_suggestion() {
        // VcKind without fix suggestion (ShiftBounds) -> covers line 76
        let failure = make_failure(VcKind::ShiftBounds, None, None, None, None);
        report_with_ariadne(&failure, "src/lib.rs", 50);
    }

    #[test]
    fn test_report_with_ariadne_all_fields() {
        // Full failure with all optional fields populated
        let cx = vec![("_1".to_string(), "#x0000000a".to_string())];
        let failure = make_failure(
            VcKind::Precondition,
            Some("n > 0 && n < 100"),
            Some("src/main.rs"),
            Some(42),
            Some(cx),
        );
        report_with_ariadne(&failure, "src/main.rs", 42);
    }

    #[test]
    fn test_report_with_ariadne_source_line_zero() {
        // source_line = 0 -> saturating_sub(1) = 0 (line 45)
        let failure = make_failure(VcKind::Assertion, None, None, None, None);
        report_with_ariadne(&failure, "src/lib.rs", 0);
    }

    #[test]
    fn test_report_with_ariadne_source_line_one() {
        // source_line = 1 -> offset = 0 (line 45)
        let failure = make_failure(VcKind::PanicFreedom, None, None, None, None);
        report_with_ariadne(&failure, "src/lib.rs", 1);
    }

    #[test]
    fn test_report_with_ariadne_each_vc_kind() {
        // Exercise ariadne path with every VcKind to cover vc_kind_description calls
        let vc_kinds = [
            VcKind::Precondition,
            VcKind::Postcondition,
            VcKind::LoopInvariantInit,
            VcKind::LoopInvariantPreserve,
            VcKind::LoopInvariantExit,
            VcKind::Overflow,
            VcKind::DivisionByZero,
            VcKind::ShiftBounds,
            VcKind::Assertion,
            VcKind::PanicFreedom,
        ];
        for vc_kind in vc_kinds {
            let failure = make_failure(vc_kind, None, None, None, None);
            report_with_ariadne(&failure, "test.rs", 10);
        }
    }

    // --- report_text_only tests ---
    // These test the colored text output path directly.

    #[test]
    fn test_report_text_only_minimal() {
        // Minimal failure: no contract, no counterexample, no fix suggestion
        // ShiftBounds has no fix suggestion -> covers lines 88-96, 99, 106, 118
        let failure = make_failure(VcKind::ShiftBounds, None, None, None, None);
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_with_contract() {
        // With contract text -> covers lines 102-103
        let failure = make_failure(VcKind::Overflow, Some("x + y < 100"), None, None, None);
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_without_contract() {
        // Without contract -> skips lines 102-103
        let failure = make_failure(VcKind::Overflow, None, None, None, None);
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_with_counterexample() {
        // With counterexample -> covers lines 108-110
        let cx = vec![
            ("x".to_string(), "42".to_string()),
            ("y".to_string(), "-1".to_string()),
        ];
        let failure = make_failure(VcKind::Assertion, None, None, None, Some(cx));
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_without_counterexample() {
        // Without counterexample -> skips lines 108-110
        let failure = make_failure(VcKind::Assertion, None, None, None, None);
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_with_fix_suggestion() {
        // VcKind with suggestion (Overflow) -> covers lines 113-115
        let failure = make_failure(VcKind::Overflow, None, None, None, None);
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_without_fix_suggestion() {
        // VcKind without suggestion (PanicFreedom) -> skips lines 113-115
        let failure = make_failure(VcKind::PanicFreedom, None, None, None, None);
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_all_fields() {
        // Full failure with all optional fields populated
        let cx = vec![
            ("_1".to_string(), "#x0000002a".to_string()),
            ("result".to_string(), "0".to_string()),
        ];
        let failure = make_failure(
            VcKind::Postcondition,
            Some("result > 0"),
            Some("src/lib.rs"),
            Some(42),
            Some(cx),
        );
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_each_vc_kind() {
        // Exercise text-only path with every VcKind to maximize line coverage
        let vc_kinds = [
            VcKind::Precondition,
            VcKind::Postcondition,
            VcKind::LoopInvariantInit,
            VcKind::LoopInvariantPreserve,
            VcKind::LoopInvariantExit,
            VcKind::Overflow,
            VcKind::DivisionByZero,
            VcKind::ShiftBounds,
            VcKind::Assertion,
            VcKind::PanicFreedom,
        ];
        for vc_kind in vc_kinds {
            let failure = make_failure(vc_kind, None, None, None, None);
            report_text_only(&failure);
        }
    }

    #[test]
    fn test_report_text_only_with_empty_counterexample() {
        // Empty counterexample vec -> format_counterexample returns "no user-visible variables"
        let failure = make_failure(VcKind::Overflow, None, None, None, Some(vec![]));
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_precondition_with_all_optionals() {
        // Precondition with contract, counterexample, and suggestion
        let cx = vec![("n".to_string(), "-5".to_string())];
        let failure = make_failure(VcKind::Precondition, Some("n >= 0"), None, None, Some(cx));
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_division_by_zero_with_counterexample() {
        let cx = vec![("divisor".to_string(), "0".to_string())];
        let failure = make_failure(
            VcKind::DivisionByZero,
            Some("divisor != 0"),
            None,
            None,
            Some(cx),
        );
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_loop_invariant_init_with_contract() {
        let failure = make_failure(VcKind::LoopInvariantInit, Some("i < len"), None, None, None);
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_loop_invariant_preserve_with_counterexample() {
        let cx = vec![
            ("i".to_string(), "10".to_string()),
            ("len".to_string(), "10".to_string()),
        ];
        let failure = make_failure(
            VcKind::LoopInvariantPreserve,
            Some("i < len"),
            None,
            None,
            Some(cx),
        );
        report_text_only(&failure);
    }

    // --- report_verification_failure end-to-end tests ---

    #[test]
    fn test_report_verification_failure_overflow_no_source() {
        let failure = VerificationFailure {
            function_name: "add_numbers".to_string(),
            vc_kind: VcKind::Overflow,
            contract_text: None,
            source_file: None,
            source_line: None,
            counterexample: Some(vec![
                ("_1".to_string(), "#xffffffff".to_string()),
                ("_2".to_string(), "#x00000001".to_string()),
            ]),
            message: "i32 addition may overflow".to_string(),
        };
        report_verification_failure(&failure);
    }

    #[test]
    fn test_report_verification_failure_postcondition_with_source() {
        let failure = VerificationFailure {
            function_name: "compute".to_string(),
            vc_kind: VcKind::Postcondition,
            contract_text: Some("result >= 0".to_string()),
            source_file: Some("src/math.rs".to_string()),
            source_line: Some(15),
            counterexample: Some(vec![("_1".to_string(), "-1".to_string())]),
            message: "postcondition 'result >= 0' not proven".to_string(),
        };
        report_verification_failure(&failure);
    }

    #[test]
    fn test_report_verification_failure_assertion_no_extras() {
        let failure = VerificationFailure {
            function_name: "validate".to_string(),
            vc_kind: VcKind::Assertion,
            contract_text: None,
            source_file: None,
            source_line: None,
            counterexample: None,
            message: "assertion might fail".to_string(),
        };
        report_verification_failure(&failure);
    }
}
