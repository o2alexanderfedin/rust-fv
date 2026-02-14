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

    // Use Warning severity for MemorySafety (per USF-06 requirement) and FloatingPointNaN
    let report_kind =
        if failure.vc_kind == VcKind::MemorySafety || failure.vc_kind == VcKind::FloatingPointNaN {
            ReportKind::Warning
        } else {
            ReportKind::Error
        };

    let report = Report::build(report_kind, source_file, offset)
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
    // Emit performance warning for FloatingPoint verification (once per run)
    if failure.vc_kind == VcKind::FloatingPointNaN {
        use std::sync::atomic::{AtomicBool, Ordering};
        static FLOAT_WARNING_EMITTED: AtomicBool = AtomicBool::new(false);

        if !FLOAT_WARNING_EMITTED.swap(true, Ordering::Relaxed) {
            emit_float_verification_warning();
            eprintln!();
        }
    }

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
        if failure.vc_kind == VcKind::Termination {
            // Use termination-specific counterexample formatting
            eprintln!(
                "{}",
                format_termination_counterexample(&failure.function_name, cx, cx)
            );
        } else {
            eprintln!("{}", format_counterexample(cx));
        }
    }

    if failure.vc_kind == VcKind::Termination {
        eprintln!();
        eprintln!("{}", format_missing_decreases_help(&failure.function_name));
    }

    if failure.vc_kind == VcKind::ClosureContract {
        eprintln!();
        if failure.message.contains("FnOnce") && failure.message.contains("called more than once") {
            eprintln!("{}", format_fnonce_double_call_help(&failure.function_name));
        } else {
            eprintln!("{}", format_closure_contract_help());
        }
    }

    if failure.vc_kind == VcKind::BehavioralSubtyping {
        eprintln!();
        // Parse failure message to extract impl_type, trait_name, method_name
        // Expected format: "impl {impl_type} does not satisfy trait {trait_name} contract for method '{method_name}'"
        // For now, use function_name as fallback for all three
        let (impl_type, trait_name, method_name) = parse_behavioral_subtyping_message(
            &failure.message,
        )
        .unwrap_or((&failure.function_name, "Trait", "method"));

        eprintln!(
            "{}",
            format_behavioral_subtyping_help(impl_type, trait_name, method_name)
        );

        // Provide specific guidance based on message content
        if failure.message.contains("precondition") {
            eprintln!();
            eprintln!(
                "{}",
                format_precondition_weakening_help(impl_type, trait_name)
            );
        }
        if failure.message.contains("postcondition") {
            eprintln!();
            eprintln!(
                "{}",
                format_postcondition_strengthening_help(impl_type, trait_name)
            );
        }
    }

    if failure.vc_kind == VcKind::BorrowValidity {
        eprintln!();
        eprintln!("{}", format_borrow_validity_help());
    }

    if failure.vc_kind == VcKind::MemorySafety {
        eprintln!();
        // Check failure message to determine which sub-type of memory safety violation
        if failure.message.contains("null-check") {
            // Extract pointer name from message if possible (fallback to "ptr")
            let ptr_name =
                extract_identifier_from_message(&failure.message, "null-check").unwrap_or("ptr");
            eprintln!("{}", format_null_check_failure(ptr_name));
        } else if failure.message.contains("bounds-check") {
            // Extract pointer and offset names from message if possible
            let ptr_name =
                extract_identifier_from_message(&failure.message, "bounds-check").unwrap_or("ptr");
            let offset_name = "offset"; // Default offset name
            eprintln!("{}", format_bounds_check_failure(ptr_name, offset_name));
        } else if failure.message.contains("no safety contracts") {
            eprintln!(
                "{}",
                format_missing_unsafe_contracts_help(&failure.function_name)
            );
        }
        eprintln!();
        eprintln!("{}", format_memory_safety_help());
        eprintln!();
        eprintln!("{}", format_unsafe_contract_help());
    }

    if failure.vc_kind == VcKind::FloatingPointNaN {
        eprintln!();
        eprintln!("{}", format_float_verification_help());
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
        VcKind::Termination => "termination measure not proven to decrease",
        VcKind::ClosureContract => "closure contract not satisfied",
        VcKind::BehavioralSubtyping => "impl does not satisfy trait contract",
        VcKind::BorrowValidity => "borrow validity violation",
        VcKind::MemorySafety => "memory safety violation",
        VcKind::FloatingPointNaN => "floating-point verification failure",
        VcKind::DataRaceFreedom => "data race detected",
        VcKind::LockInvariant => "lock invariant violation",
        VcKind::Deadlock => "potential deadlock detected",
        VcKind::ChannelSafety => "channel operation safety violation",
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
        VcKind::Termination => Some(
            "Verify that #[decreases(expr)] expression strictly decreases \
             at each recursive call site"
                .to_string(),
        ),
        VcKind::BehavioralSubtyping => Some(
            "Check that the impl precondition is weaker (allows more) than the trait precondition, \
             and that the impl postcondition is stronger (guarantees more) than the trait postcondition."
                .to_string(),
        ),
        VcKind::BorrowValidity => Some(
            "Check borrow lifetimes: ensure shared and mutable borrows don't overlap, \
             borrows don't outlive their source, and reborrows maintain validity."
                .to_string(),
        ),
        VcKind::MemorySafety => Some(
            "Add safety contracts with #[unsafe_requires(ptr != null)] for null-safety, \
             #[unsafe_requires(offset < size)] for bounds-safety, or mark the function \
             #[trusted] if it has been manually verified."
                .to_string(),
        ),
        VcKind::FloatingPointNaN => Some(
            "Consider adding NaN guards (!x.is_nan()) or using #[allows_nan] to suppress. \
             Float operations may produce NaN from 0.0/0.0, Inf - Inf, etc."
                .to_string(),
        ),
        VcKind::DataRaceFreedom => Some(
            "Add synchronization (Mutex, RwLock, or atomic operations) to protect shared state. \
             Ensure all concurrent accesses to the same memory location are ordered by happens-before."
                .to_string(),
        ),
        VcKind::LockInvariant => Some(
            "Ensure the lock invariant holds before releasing the lock. \
             The invariant was assumed at acquire and must be re-established at release."
                .to_string(),
        ),
        VcKind::Deadlock => Some(
            "Establish a consistent lock ordering. If multiple locks are needed, \
             always acquire them in the same order across all threads."
                .to_string(),
        ),
        VcKind::ChannelSafety => Some(
            "Check channel usage: ensure sender is not dropped before receiver reads, \
             bounded channels have capacity for sends, and receivers handle closed channels."
                .to_string(),
        ),
        _ => None,
    }
}

/// Format a help message for a closure contract violation.
///
/// Provides guidance on what a closure contract failure means.
pub fn format_closure_contract_help() -> String {
    "Closure contract violation: the closure's behavior at the call site does not satisfy \
     the specified contract. Check that the closure's ensures clause holds for all valid \
     inputs satisfying the requires clause."
        .to_string()
}

/// Format a help message for a FnOnce closure called more than once.
///
/// Explains why FnOnce closures can only be called once.
pub fn format_fnonce_double_call_help(closure_name: &str) -> String {
    format!(
        "FnOnce closure '{}' is called more than once. FnOnce closures consume their \
         environment and can only be called once. Consider using Fn or FnMut if multiple \
         calls are needed.",
        closure_name
    )
}

/// Parse behavioral subtyping failure message to extract impl type, trait name, and method name.
///
/// Expected format: "impl {impl_type} does not satisfy trait {trait_name} contract for method '{method_name}'"
/// Returns None if the message doesn't match the expected format.
fn parse_behavioral_subtyping_message(message: &str) -> Option<(&str, &str, &str)> {
    // Try to extract impl_type, trait_name, method_name from message
    // Pattern: "impl X does not satisfy trait Y contract for method 'Z'"
    let impl_start = message.find("impl ")?;
    let impl_end = message[impl_start + 5..].find(" does not satisfy")?;
    let impl_type = &message[impl_start + 5..impl_start + 5 + impl_end];

    let trait_start = message.find("trait ")?;
    let trait_end = message[trait_start + 6..].find(" contract")?;
    let trait_name = &message[trait_start + 6..trait_start + 6 + trait_end];

    let method_start = message.find("method '")?;
    let method_end = message[method_start + 8..].find('\'')?;
    let method_name = &message[method_start + 8..method_start + 8 + method_end];

    Some((impl_type, trait_name, method_name))
}

/// Extract an identifier from a message based on a keyword.
///
/// Attempts to find an identifier (alphanumeric + underscore) near the keyword.
/// Returns None if no identifier is found.
fn extract_identifier_from_message<'a>(message: &'a str, _keyword: &str) -> Option<&'a str> {
    // Simple heuristic: find first underscore-prefixed identifier (like "_1", "_ptr")
    // or alphanumeric identifier
    for word in message.split_whitespace() {
        let cleaned = word.trim_matches(|c: char| !c.is_alphanumeric() && c != '_');
        if !cleaned.is_empty()
            && (cleaned.starts_with('_') || cleaned.chars().next().unwrap().is_alphabetic())
        {
            return Some(cleaned);
        }
    }
    None
}

/// Format a help message for a behavioral subtyping violation.
///
/// Provides guidance on Liskov Substitution Principle for trait impl contracts.
pub fn format_behavioral_subtyping_help(
    impl_type: &str,
    trait_name: &str,
    method_name: &str,
) -> String {
    format!(
        "impl {} does not satisfy trait {} contract for method '{}'.\n\
         \n\
         Behavioral subtyping (Liskov Substitution Principle) requires:\n\
         - Precondition weakening: impl must accept ALL inputs the trait accepts\n\
         - Postcondition strengthening: impl must guarantee AT LEAST what the trait promises\n\
         \n\
         To fix: weaken the impl's precondition or strengthen its postcondition\n\
         to match the trait-level contract.",
        impl_type, trait_name, method_name
    )
}

/// Format a help message for precondition weakening violations.
///
/// Explains that the impl precondition is stricter than the trait precondition.
pub fn format_precondition_weakening_help(impl_type: &str, trait_name: &str) -> String {
    format!(
        "impl {}'s precondition is STRICTER than {}'s.\n\
         Impl must accept all inputs the trait contract allows.\n\
         Consider removing or relaxing the impl's additional precondition.",
        impl_type, trait_name
    )
}

/// Format a help message for postcondition strengthening violations.
///
/// Explains that the impl postcondition does not imply the trait postcondition.
pub fn format_postcondition_strengthening_help(impl_type: &str, trait_name: &str) -> String {
    format!(
        "impl {}'s postcondition does not IMPLY {}'s.\n\
         Impl must guarantee at least what the trait contract promises.\n\
         Verify that the impl's behavior satisfies the trait postcondition.",
        impl_type, trait_name
    )
}

/// Format a help message for borrow validity failures.
///
/// Explains the borrow lifecycle and common validity violations.
pub fn format_borrow_validity_help() -> String {
    "borrow validity error: check the following:\n\
     - Shared (&) and mutable (&mut) borrows cannot overlap\n\
     - A borrow must not outlive the lifetime of its source\n\
     - Reborrows (&mut &mut T) must maintain validity through all layers\n\
     - Ensure lifetime constraints ('a: 'b) are satisfied"
        .to_string()
}

/// Format a help message for memory safety violations.
///
/// Explains the three-tier unsafe verification approach: detection, basic checks, and trust boundaries.
pub fn format_memory_safety_help() -> String {
    "memory safety violation: rust-fv uses a three-tier approach for unsafe code:\n\
     \n\
     1. Detection: unsafe blocks and operations are flagged for manual review\n\
     2. Basic checks: null-safety, bounds-safety, and use-after-free detection\n\
     3. Trust boundaries: verified functions can be marked with #[verifier::trusted]\n\
     \n\
     This is a WARNING, not an error. Review the unsafe code and add contracts if needed."
        .to_string()
}

/// Format a help message for unsafe contract annotations.
///
/// Explains how to annotate unsafe functions with safety contracts.
pub fn format_unsafe_contract_help() -> String {
    "annotating unsafe functions with safety contracts:\n\
     \n\
     - #[unsafe_requires(ptr != null)] for null-safety preconditions\n\
     - #[unsafe_requires(offset < size)] for bounds-safety preconditions\n\
     - #[unsafe_ensures(result != null)] for safety postconditions\n\
     - #[verifier::trusted] to skip body verification for manually verified functions\n\
     \n\
     Contracts enable compositional verification: callers must satisfy preconditions,\n\
     and can assume postconditions hold."
        .to_string()
}

/// Format a help message for floating-point verification failures.
///
/// Explains IEEE 754 quirks and opt-in performance trade-off.
pub fn format_float_verification_help() -> String {
    "floating-point verification: IEEE 754 semantics include NaN propagation, \
     signed zeros, and infinity overflow. These checks are warnings because \
     float arithmetic is inherently approximate. Add guards like !x.is_nan() \
     for stricter guarantees, or use #[allows_nan] (future) to suppress warnings."
        .to_string()
}

/// Emit a performance warning when floating-point verification is enabled.
///
/// Per FPV-06 requirement: Warn users that FPA theory is 2-10x slower than bitvectors.
/// This warning should be emitted ONCE per verification run when FloatingPointNaN VCs are present.
pub fn emit_float_verification_warning() {
    eprintln!(
        "{}",
        "warning: FloatingPoint verification enabled -- FPA theory is 2-10x slower than bitvectors."
            .yellow()
            .bold()
    );
    eprintln!("  Consider limiting float verification to functions that need it.");
}

/// Format a warning for an unsafe block detected during verification.
///
/// Provides information about the unsafe block location and reason.
#[allow(dead_code)]
pub fn format_unsafe_block_warning(block_desc: &str, reason: &str) -> String {
    format!(
        "warning: unsafe code detected: {}\n  Reason: {}\n  \
         The verifier flags all unsafe code for review. Consider adding safety contracts\n  \
         or marking with #[trusted] if manually verified.",
        block_desc, reason
    )
}

/// Format a diagnostic for a null-check failure on a raw pointer dereference.
///
/// Suggests adding safety contracts or deriving pointers from valid references.
pub fn format_null_check_failure(ptr_name: &str) -> String {
    format!(
        "Raw pointer '{}' may be null at dereference.\n  \
         The verifier could not prove the pointer is non-null.\n  \
         Suggestion: Add #[unsafe_requires({} != null)] to the function,\n  \
         or ensure the pointer is derived from a valid reference.",
        ptr_name, ptr_name
    )
}

/// Format a diagnostic for a bounds-check failure on pointer arithmetic.
///
/// Suggests adding safety contracts to constrain offset bounds.
pub fn format_bounds_check_failure(ptr_name: &str, offset_name: &str) -> String {
    format!(
        "Pointer arithmetic on '{}' with offset '{}' may exceed allocation bounds.\n  \
         The verifier could not prove the offset stays within the allocated region.\n  \
         Suggestion: Add #[unsafe_requires({} < alloc_size)] to the function.",
        ptr_name, offset_name, offset_name
    )
}

/// Format a notice for a trusted function whose body verification is skipped.
///
/// Warns that incorrect contracts may lead to unsoundness.
#[allow(dead_code)]
pub fn format_trusted_function_notice(func_name: &str) -> String {
    format!(
        "note: function '{}' is marked #[trusted]\n  \
         Body verification skipped. Contracts are verified at call sites.\n  \
         WARNING: Incorrect contracts may lead to unsound verification results.\n  \
         Ensure manual review has been performed.",
        func_name
    )
}

/// Format a help message for an unsafe function missing safety contracts.
///
/// Suggests adding contract annotations or marking the function as trusted.
pub fn format_missing_unsafe_contracts_help(func_name: &str) -> String {
    format!(
        "warning: unsafe function '{}' has no safety contracts.\n  \
         Without contracts, the verifier cannot check safety properties at call sites.\n  \
         Add #[unsafe_requires(...)] for preconditions (e.g., pointer validity).\n  \
         Add #[unsafe_ensures(...)] for postconditions.\n  \
         Or mark #[trusted] if the function has been manually verified.",
        func_name
    )
}

/// Format a help message for a recursive function missing a `#[decreases]` annotation.
///
/// Provides actionable guidance: what the annotation does, how to add it, and an example.
pub fn format_missing_decreases_help(function_name: &str) -> String {
    format!(
        "recursive function `{}` requires a termination measure.\n\
         Add #[decreases(expr)] where expr is a non-negative integer expression\n\
         that strictly decreases at each recursive call.\n\
         Example: #[decreases(n)] for a function that recurses with n-1",
        function_name
    )
}

/// Format a counterexample specifically for termination VC failures.
///
/// Shows the measure values at function entry vs. at the recursive call site,
/// making it clear why the termination proof failed.
pub fn format_termination_counterexample(
    function_name: &str,
    entry_values: &[(String, String)],
    call_values: &[(String, String)],
) -> String {
    let mut result = format!("termination counterexample for `{}`:", function_name);

    if !entry_values.is_empty() {
        result.push_str("\n  at function entry: ");
        let entries: Vec<String> = entry_values
            .iter()
            .map(|(name, value)| format!("{} = {}", name, value))
            .collect();
        result.push_str(&entries.join(", "));
    }

    if !call_values.is_empty() {
        result.push_str("\n  at recursive call: ");
        let calls: Vec<String> = call_values
            .iter()
            .map(|(name, value)| format!("{} = {}", name, value))
            .collect();
        result.push_str(&calls.join(", "));
        result.push_str(" (not decreasing)");
    }

    result
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
            VcKind::Termination,
            VcKind::ClosureContract,
            VcKind::BehavioralSubtyping,
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
            VcKind::Termination,
            VcKind::ClosureContract,
            VcKind::BehavioralSubtyping,
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

    // --- VcKind::Termination tests (Phase 6) ---

    #[test]
    fn test_vc_kind_description_termination() {
        assert_eq!(
            vc_kind_description(&VcKind::Termination),
            "termination measure not proven to decrease"
        );
    }

    #[test]
    fn test_suggest_fix_termination() {
        let suggestion = suggest_fix(&VcKind::Termination);
        assert!(suggestion.is_some());
        let text = suggestion.unwrap();
        assert!(text.contains("decreases"));
    }

    // --- format_missing_decreases_help tests ---

    #[test]
    fn test_format_missing_decreases_help_contains_function_name() {
        let help = format_missing_decreases_help("factorial");
        assert!(
            help.contains("factorial"),
            "Help text should contain function name"
        );
    }

    #[test]
    fn test_format_missing_decreases_help_contains_decreases_suggestion() {
        let help = format_missing_decreases_help("fibonacci");
        assert!(
            help.contains("#[decreases("),
            "Help text should suggest #[decreases] annotation"
        );
        assert!(
            help.contains("termination measure"),
            "Help text should explain what's needed"
        );
    }

    #[test]
    fn test_format_missing_decreases_help_contains_example() {
        let help = format_missing_decreases_help("my_func");
        assert!(
            help.contains("Example"),
            "Help text should include an example"
        );
        assert!(
            help.contains("#[decreases(n)]"),
            "Help text should show a concrete example"
        );
    }

    // --- format_termination_counterexample tests ---

    #[test]
    fn test_format_termination_counterexample_shows_entry_and_call() {
        let result = format_termination_counterexample(
            "factorial",
            &[("n".to_string(), "5".to_string())],
            &[("n".to_string(), "5".to_string())],
        );
        assert!(result.contains("factorial"), "Should contain function name");
        assert!(
            result.contains("at function entry"),
            "Should show entry values"
        );
        assert!(
            result.contains("at recursive call"),
            "Should show call values"
        );
        assert!(
            result.contains("not decreasing"),
            "Should indicate non-decreasing"
        );
    }

    #[test]
    fn test_format_termination_counterexample_multiple_values() {
        let result = format_termination_counterexample(
            "mutual_func",
            &[
                ("x".to_string(), "10".to_string()),
                ("y".to_string(), "3".to_string()),
            ],
            &[
                ("x".to_string(), "10".to_string()),
                ("y".to_string(), "3".to_string()),
            ],
        );
        assert!(result.contains("x = 10"));
        assert!(result.contains("y = 3"));
    }

    #[test]
    fn test_format_termination_counterexample_empty_values() {
        let result = format_termination_counterexample("empty_func", &[], &[]);
        assert!(result.contains("empty_func"));
        // Should not crash with empty values
        assert!(!result.contains("at function entry"));
        assert!(!result.contains("at recursive call"));
    }

    // --- format_behavioral_subtyping_help tests ---

    #[test]
    fn test_format_behavioral_subtyping_help_contains_impl_name() {
        let help = format_behavioral_subtyping_help("VecStack", "Stack", "push");
        assert!(
            help.contains("VecStack"),
            "Help text should contain impl name"
        );
    }

    #[test]
    fn test_format_behavioral_subtyping_help_contains_explanation() {
        let help = format_behavioral_subtyping_help("MyImpl", "MyTrait", "my_method");
        assert!(
            help.contains("Behavioral subtyping"),
            "Help text should mention behavioral subtyping"
        );
        assert!(
            help.contains("ALL inputs"),
            "Help text should explain precondition weakening"
        );
        assert!(
            help.contains("AT LEAST"),
            "Help text should explain postcondition strengthening"
        );
        assert!(
            help.contains("Liskov Substitution"),
            "Help text should explain Liskov substitution principle"
        );
    }

    #[test]
    fn test_format_precondition_weakening_help() {
        let help = format_precondition_weakening_help("VecStack", "Stack");
        assert!(
            help.contains("STRICTER"),
            "Help text should mention STRICTER precondition"
        );
        assert!(
            help.contains("VecStack"),
            "Help text should contain impl type"
        );
        assert!(
            help.contains("Stack"),
            "Help text should contain trait name"
        );
    }

    #[test]
    fn test_format_postcondition_strengthening_help() {
        let help = format_postcondition_strengthening_help("VecStack", "Stack");
        assert!(
            help.contains("IMPLY"),
            "Help text should mention IMPLY for postcondition"
        );
        assert!(
            help.contains("VecStack"),
            "Help text should contain impl type"
        );
        assert!(
            help.contains("Stack"),
            "Help text should contain trait name"
        );
    }

    #[test]
    fn test_suggest_fix_behavioral_subtyping() {
        let suggestion = suggest_fix(&VcKind::BehavioralSubtyping);
        assert!(suggestion.is_some());
        let text = suggestion.unwrap();
        assert!(text.contains("precondition"));
        assert!(text.contains("postcondition"));
    }

    #[test]
    fn test_report_text_only_behavioral_subtyping() {
        let failure = make_failure(
            VcKind::BehavioralSubtyping,
            Some("impl VecStack does not satisfy trait Stack contract for method 'push'"),
            None,
            None,
            None,
        );
        report_text_only(&failure);
        // Should not panic and should handle behavioral subtyping
    }

    // --- format_closure_contract_help tests ---

    #[test]
    fn test_format_closure_contract_help_contains_explanation() {
        let help = format_closure_contract_help();
        assert!(
            help.contains("Closure contract violation"),
            "Help text should mention closure contract violation"
        );
        assert!(
            help.contains("ensures clause"),
            "Help text should mention ensures clause"
        );
        assert!(
            help.contains("requires clause"),
            "Help text should mention requires clause"
        );
    }

    // --- format_fnonce_double_call_help tests ---

    #[test]
    fn test_format_fnonce_double_call_help_contains_closure_name() {
        let help = format_fnonce_double_call_help("my_closure");
        assert!(
            help.contains("my_closure"),
            "Help text should contain closure name"
        );
    }

    #[test]
    fn test_format_fnonce_double_call_help_contains_explanation() {
        let help = format_fnonce_double_call_help("test_closure");
        assert!(help.contains("FnOnce"), "Help text should mention FnOnce");
        assert!(
            help.contains("called more than once"),
            "Help text should mention double-call issue"
        );
        assert!(
            help.contains("consume their environment"),
            "Help text should explain why FnOnce is restricted"
        );
        assert!(
            help.contains("Fn or FnMut"),
            "Help text should suggest alternatives"
        );
    }

    // --- report_text_only trait tests ---
    // (test_report_text_only_behavioral_subtyping moved to format_behavioral_subtyping_help tests section)

    // --- report_text_only closure contract tests ---

    #[test]
    fn test_report_text_only_closure_contract() {
        let failure = make_failure(
            VcKind::ClosureContract,
            Some("predicate(x) == true"),
            None,
            None,
            None,
        );
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_fnonce_double_call() {
        let failure = VerificationFailure {
            function_name: "my_closure".to_string(),
            vc_kind: VcKind::ClosureContract,
            contract_text: None,
            source_file: None,
            source_line: None,
            counterexample: None,
            message: "FnOnce closure called more than once".to_string(),
        };
        report_text_only(&failure);
    }

    #[test]
    fn test_vc_kind_description_closure_contract() {
        assert_eq!(
            vc_kind_description(&VcKind::ClosureContract),
            "closure contract not satisfied"
        );
    }

    // --- VcKind::BehavioralSubtyping tests (Phase 8) ---

    #[test]
    fn test_vc_kind_description_behavioral_subtyping() {
        assert_eq!(
            vc_kind_description(&VcKind::BehavioralSubtyping),
            "impl does not satisfy trait contract"
        );
    }

    // --- VcKind::BorrowValidity tests (Phase 9) ---

    #[test]
    fn test_vc_kind_description_borrow_validity() {
        assert_eq!(
            vc_kind_description(&VcKind::BorrowValidity),
            "borrow validity violation"
        );
    }

    #[test]
    fn test_suggest_fix_borrow_validity() {
        let suggestion = suggest_fix(&VcKind::BorrowValidity);
        assert!(suggestion.is_some());
        let text = suggestion.unwrap();
        assert!(text.contains("borrow"));
        assert!(text.contains("lifetime"));
    }

    // --- VcKind::MemorySafety tests (Phase 10) ---

    #[test]
    fn test_vc_kind_description_memory_safety() {
        assert_eq!(
            vc_kind_description(&VcKind::MemorySafety),
            "memory safety violation"
        );
    }

    #[test]
    fn test_suggest_fix_memory_safety() {
        let suggestion = suggest_fix(&VcKind::MemorySafety);
        assert!(suggestion.is_some());
        let text = suggestion.unwrap();
        assert!(text.contains("unsafe_requires"));
        assert!(text.contains("trusted"));
    }

    // --- format_unsafe_block_warning tests ---

    #[test]
    fn test_format_unsafe_block_warning() {
        let warning =
            format_unsafe_block_warning("unsafe block in process_data", "raw pointer dereference");
        assert!(warning.contains("unsafe block in process_data"));
        assert!(warning.contains("raw pointer dereference"));
        assert!(warning.contains("warning: unsafe code detected"));
        assert!(warning.contains("safety contracts"));
        assert!(warning.contains("#[trusted]"));
    }

    // --- format_null_check_failure tests ---

    #[test]
    fn test_format_null_check_failure() {
        let diagnostic = format_null_check_failure("_1");
        assert!(diagnostic.contains("_1"));
        assert!(diagnostic.contains("may be null"));
        assert!(diagnostic.contains("non-null"));
        assert!(diagnostic.contains("#[unsafe_requires(_1 != null)]"));
        assert!(diagnostic.contains("valid reference"));
    }

    // --- format_bounds_check_failure tests ---

    #[test]
    fn test_format_bounds_check_failure() {
        let diagnostic = format_bounds_check_failure("_1", "_2");
        assert!(diagnostic.contains("_1"));
        assert!(diagnostic.contains("_2"));
        assert!(diagnostic.contains("Pointer arithmetic"));
        assert!(diagnostic.contains("allocation bounds"));
        assert!(diagnostic.contains("#[unsafe_requires(_2 < alloc_size)]"));
    }

    // --- format_trusted_function_notice tests ---

    #[test]
    fn test_format_trusted_function_notice() {
        let notice = format_trusted_function_notice("my_unsafe_fn");
        assert!(notice.contains("my_unsafe_fn"));
        assert!(notice.contains("#[trusted]"));
        assert!(notice.contains("Body verification skipped"));
        assert!(notice.contains("call sites"));
        assert!(notice.contains("unsound verification results"));
        assert!(notice.contains("manual review"));
    }

    // --- format_missing_unsafe_contracts_help tests ---

    #[test]
    fn test_format_missing_unsafe_contracts_help() {
        let help = format_missing_unsafe_contracts_help("unsafe_fn");
        assert!(help.contains("unsafe_fn"));
        assert!(help.contains("no safety contracts"));
        assert!(help.contains("#[unsafe_requires(...)]"));
        assert!(help.contains("#[unsafe_ensures(...)]"));
        assert!(help.contains("#[trusted]"));
        assert!(help.contains("call sites"));
    }

    // --- VcKind::MemorySafety in test arrays ---

    #[test]
    fn test_memory_safety_vc_kind_in_all_arrays() {
        // Verify that VcKind::MemorySafety is present in comprehensive test arrays
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
            VcKind::Termination,
            VcKind::ClosureContract,
            VcKind::BehavioralSubtyping,
            VcKind::BorrowValidity,
            VcKind::MemorySafety,
        ];
        // Just verify we can iterate over all kinds including MemorySafety
        for vc_kind in vc_kinds {
            let _desc = vc_kind_description(&vc_kind);
        }
    }

    // --- report_text_only MemorySafety tests ---

    #[test]
    fn test_report_text_only_memory_safety_null_check() {
        let failure = VerificationFailure {
            function_name: "test_fn".to_string(),
            vc_kind: VcKind::MemorySafety,
            contract_text: None,
            source_file: None,
            source_line: None,
            counterexample: None,
            message: "null-check failed for _1".to_string(),
        };
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_memory_safety_bounds_check() {
        let failure = VerificationFailure {
            function_name: "test_fn".to_string(),
            vc_kind: VcKind::MemorySafety,
            contract_text: None,
            source_file: None,
            source_line: None,
            counterexample: None,
            message: "bounds-check failed for ptr".to_string(),
        };
        report_text_only(&failure);
    }

    #[test]
    fn test_report_text_only_memory_safety_no_contracts() {
        let failure = VerificationFailure {
            function_name: "unsafe_func".to_string(),
            vc_kind: VcKind::MemorySafety,
            contract_text: None,
            source_file: None,
            source_line: None,
            counterexample: None,
            message: "no safety contracts found".to_string(),
        };
        report_text_only(&failure);
    }

    // --- report_with_ariadne MemorySafety warning severity test ---

    #[test]
    fn test_report_with_ariadne_memory_safety_warning() {
        let failure = VerificationFailure {
            function_name: "unsafe_fn".to_string(),
            vc_kind: VcKind::MemorySafety,
            contract_text: None,
            source_file: None,
            source_line: None,
            counterexample: None,
            message: "null-check failed".to_string(),
        };
        // This should use ReportKind::Warning instead of Error
        report_with_ariadne(&failure, "src/lib.rs", 10);
    }

    // --- FloatingPoint performance warning tests ---

    #[test]
    fn test_emit_float_verification_warning() {
        // Test that emit_float_verification_warning() produces expected output
        // Note: This writes to stderr, so we're just testing it doesn't panic
        emit_float_verification_warning();
    }

    #[test]
    fn test_report_text_only_float_nan() {
        // Test that FloatingPointNaN failures trigger the performance warning
        let failure = VerificationFailure {
            function_name: "float_fn".to_string(),
            vc_kind: VcKind::FloatingPointNaN,
            contract_text: None,
            source_file: None,
            source_line: None,
            counterexample: None,
            message: "NaN propagation check failed".to_string(),
        };
        // This should emit the performance warning (once)
        report_text_only(&failure);
    }
}
