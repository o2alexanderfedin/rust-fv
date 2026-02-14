/// cargo verify subcommand implementation.
///
/// When invoked as `cargo-verify verify [args]`, this module:
/// 1. Determines the crate name from Cargo.toml
/// 2. Sets RUSTC to point to the current binary (the driver)
/// 3. Sets RUST_FV_VERIFY=1 to enable verification mode
/// 4. Runs `cargo check` as a subprocess
/// 5. Collects results and displays colored output
///
/// The driver prints results to stderr, which cargo verify reads.
use std::path::Path;
use std::process::{Command, Stdio};

use colored::Colorize;

use crate::output;

/// Run the cargo verify subcommand.
///
/// # Arguments
/// * `args` - Arguments after "verify" (e.g., `--timeout 30`)
pub fn run_cargo_verify(args: &[String]) -> i32 {
    // Check for --help
    if args.iter().any(|a| a == "--help" || a == "-h") {
        print_usage();
        return 0;
    }

    // Determine the crate name and path
    let crate_path = std::env::current_dir()
        .map(|p| p.display().to_string())
        .unwrap_or_else(|_| ".".to_string());

    let crate_name = read_crate_name().unwrap_or_else(|| "unknown".to_string());

    output::print_header(&crate_name, &crate_path);

    // Find the path to the current binary (the driver)
    let driver_path = match std::env::current_exe() {
        Ok(p) => p,
        Err(e) => {
            eprintln!(
                "{} Could not find driver binary: {e}",
                "error:".red().bold()
            );
            return 2;
        }
    };

    // Parse timeout from args (default: 30 seconds per function)
    let timeout = parse_timeout(args);

    // Parse output format from args (default: text)
    let output_format = parse_output_format(args);

    // Parse fresh flag from args (default: false)
    let fresh = parse_fresh(args);

    // Parse jobs flag from args (default: num_cpus/2)
    let jobs = parse_jobs(args);

    // Parse no-stdlib-contracts flag from args (default: false)
    let no_stdlib_contracts = parse_no_stdlib_contracts(args);

    // Build the cargo check command with our driver as RUSTC
    let mut cmd = Command::new("cargo");
    cmd.arg("check")
        .env("RUSTC", &driver_path)
        .env("RUST_FV_VERIFY", "1")
        .stderr(Stdio::inherit())
        .stdout(Stdio::inherit());

    if timeout > 0 {
        cmd.env("RUST_FV_TIMEOUT", timeout.to_string());
    }

    if output_format == "json" {
        cmd.env("RUST_FV_OUTPUT_FORMAT", "json");
    }

    if fresh {
        cmd.env("RUST_FV_FRESH", "1");
    }

    if let Some(j) = jobs {
        cmd.env("RUST_FV_JOBS", j.to_string());
    }

    if no_stdlib_contracts {
        cmd.env("RUST_FV_NO_STDLIB_CONTRACTS", "1");
    }

    // Forward any extra args (e.g., --package, --lib, etc.)
    for arg in args {
        if !arg.starts_with("--timeout")
            && !arg.starts_with("--output-format")
            && !arg.starts_with("--fresh")
            && !arg.starts_with("--jobs")
            && !arg.starts_with("--no-stdlib-contracts")
        {
            cmd.arg(arg);
        }
    }

    if output_format != "json" {
        eprintln!("{}", "Running verification...".dimmed());
    }

    match cmd.status() {
        Ok(status) => {
            if status.success() {
                0
            } else {
                // cargo check failed -- could be compilation error or verification failure
                1
            }
        }
        Err(e) => {
            eprintln!("{} Failed to run cargo check: {e}", "error:".red().bold());
            2
        }
    }
}

/// Read the crate name from Cargo.toml in the current directory.
fn read_crate_name() -> Option<String> {
    let cargo_toml = Path::new("Cargo.toml");
    if !cargo_toml.exists() {
        return None;
    }

    let content = std::fs::read_to_string(cargo_toml).ok()?;

    // Simple TOML parsing: find `name = "..."` in [package] section
    let mut in_package = false;
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed == "[package]" {
            in_package = true;
            continue;
        }
        if trimmed.starts_with('[') {
            in_package = false;
            continue;
        }
        if in_package && let Some(rest) = trimmed.strip_prefix("name") {
            let rest = rest.trim();
            if let Some(rest) = rest.strip_prefix('=') {
                let rest = rest.trim();
                // Remove quotes
                let name = rest.trim_matches('"').trim_matches('\'');
                return Some(name.to_string());
            }
        }
    }
    None
}

/// Parse --timeout N from arguments (seconds).
fn parse_timeout(args: &[String]) -> u64 {
    for (i, arg) in args.iter().enumerate() {
        if arg == "--timeout"
            && let Some(val) = args.get(i + 1)
        {
            return val.parse().unwrap_or(30);
        }
        if let Some(val) = arg.strip_prefix("--timeout=") {
            return val.parse().unwrap_or(30);
        }
    }
    30 // default: 30 seconds
}

/// Parse --output-format FORMAT from arguments.
fn parse_output_format(args: &[String]) -> String {
    for (i, arg) in args.iter().enumerate() {
        if arg == "--output-format"
            && let Some(val) = args.get(i + 1)
        {
            return val.clone();
        }
        if let Some(val) = arg.strip_prefix("--output-format=") {
            return val.to_string();
        }
    }
    "text".to_string() // default: text
}

/// Parse --fresh flag from arguments.
fn parse_fresh(args: &[String]) -> bool {
    args.iter().any(|a| a == "--fresh")
}

/// Parse --jobs N from arguments.
fn parse_jobs(args: &[String]) -> Option<usize> {
    for (i, arg) in args.iter().enumerate() {
        if arg == "--jobs"
            && let Some(val) = args.get(i + 1)
        {
            return val.parse().ok();
        }
        if let Some(val) = arg.strip_prefix("--jobs=") {
            return val.parse().ok();
        }
    }
    None
}

/// Parse --no-stdlib-contracts flag from arguments.
fn parse_no_stdlib_contracts(args: &[String]) -> bool {
    args.iter().any(|a| a == "--no-stdlib-contracts")
}

/// Print usage information.
fn print_usage() {
    eprintln!("rust-fv: Formal verification for Rust");
    eprintln!();
    eprintln!("USAGE:");
    eprintln!("    cargo verify [OPTIONS]");
    eprintln!();
    eprintln!("OPTIONS:");
    eprintln!("    --timeout <SECONDS>         Verification timeout per function (default: 30)");
    eprintln!("    --output-format <FORMAT>    Output format: text or json (default: text)");
    eprintln!("    --fresh                     Force re-verification, bypassing cache");
    eprintln!(
        "    --jobs <N>                  Number of parallel verification threads (default: num_cpus/2)"
    );
    eprintln!("    --no-stdlib-contracts       Disable standard library contracts");
    eprintln!("    --help, -h                  Print this help message");
    eprintln!();
    eprintln!("DESCRIPTION:");
    eprintln!("    Runs formal verification on all annotated functions in the current crate.");
    eprintln!("    Functions are annotated with #[requires(...)], #[ensures(...)], #[pure],");
    eprintln!("    and #[invariant(...)] attributes from the rust-fv-macros crate.");
    eprintln!();
    eprintln!("    Results are displayed with colored status (text mode):");
    eprintln!("      [OK]      - All verification conditions verified");
    eprintln!("      [FAIL]    - At least one verification condition failed");
    eprintln!("      [TIMEOUT] - Verification timed out");
    eprintln!();
    eprintln!("    JSON mode outputs structured results to stdout for IDE integration.");
    eprintln!();
    eprintln!("    Caching: Verification results are cached in target/rust-fv-cache/ and reused");
    eprintln!("    when source code hasn't changed. Use --fresh to force re-verification.");
    eprintln!();
    eprintln!("EXIT CODES:");
    eprintln!("    0  All functions verified successfully");
    eprintln!("    1  At least one function failed verification");
    eprintln!("    2  Build/compilation error");
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- parse_timeout tests ---

    #[test]
    fn test_parse_timeout_default() {
        let args: Vec<String> = vec![];
        assert_eq!(parse_timeout(&args), 30);
    }

    #[test]
    fn test_parse_timeout_separate_arg() {
        let args: Vec<String> = vec!["--timeout".into(), "60".into()];
        assert_eq!(parse_timeout(&args), 60);
    }

    #[test]
    fn test_parse_timeout_equals_form() {
        let args: Vec<String> = vec!["--timeout=120".into()];
        assert_eq!(parse_timeout(&args), 120);
    }

    #[test]
    fn test_parse_timeout_invalid_value_returns_default() {
        let args: Vec<String> = vec!["--timeout".into(), "not_a_number".into()];
        assert_eq!(parse_timeout(&args), 30);
    }

    #[test]
    fn test_parse_timeout_equals_invalid_returns_default() {
        let args: Vec<String> = vec!["--timeout=abc".into()];
        assert_eq!(parse_timeout(&args), 30);
    }

    #[test]
    fn test_parse_timeout_zero() {
        let args: Vec<String> = vec!["--timeout".into(), "0".into()];
        assert_eq!(parse_timeout(&args), 0);
    }

    #[test]
    fn test_parse_timeout_among_other_args() {
        let args: Vec<String> = vec![
            "--package".into(),
            "mylib".into(),
            "--timeout".into(),
            "45".into(),
            "--lib".into(),
        ];
        assert_eq!(parse_timeout(&args), 45);
    }

    #[test]
    fn test_parse_timeout_missing_value() {
        // --timeout is last arg, no value follows
        let args: Vec<String> = vec!["--timeout".into()];
        assert_eq!(parse_timeout(&args), 30);
    }

    // --- parse_output_format tests ---

    #[test]
    fn test_parse_output_format_default() {
        let args: Vec<String> = vec![];
        assert_eq!(parse_output_format(&args), "text");
    }

    #[test]
    fn test_parse_output_format_json_separate() {
        let args: Vec<String> = vec!["--output-format".into(), "json".into()];
        assert_eq!(parse_output_format(&args), "json");
    }

    #[test]
    fn test_parse_output_format_json_equals() {
        let args: Vec<String> = vec!["--output-format=json".into()];
        assert_eq!(parse_output_format(&args), "json");
    }

    #[test]
    fn test_parse_output_format_text_explicit() {
        let args: Vec<String> = vec!["--output-format".into(), "text".into()];
        assert_eq!(parse_output_format(&args), "text");
    }

    #[test]
    fn test_parse_output_format_custom_value() {
        let args: Vec<String> = vec!["--output-format=sarif".into()];
        assert_eq!(parse_output_format(&args), "sarif");
    }

    #[test]
    fn test_parse_output_format_missing_value() {
        // --output-format is last arg, no value follows
        let args: Vec<String> = vec!["--output-format".into()];
        assert_eq!(parse_output_format(&args), "text");
    }

    #[test]
    fn test_parse_output_format_among_other_args() {
        let args: Vec<String> = vec![
            "--fresh".into(),
            "--output-format".into(),
            "json".into(),
            "--timeout".into(),
            "10".into(),
        ];
        assert_eq!(parse_output_format(&args), "json");
    }

    // --- parse_fresh tests ---

    #[test]
    fn test_parse_fresh_default() {
        let args: Vec<String> = vec![];
        assert!(!parse_fresh(&args));
    }

    #[test]
    fn test_parse_fresh_present() {
        let args: Vec<String> = vec!["--fresh".into()];
        assert!(parse_fresh(&args));
    }

    #[test]
    fn test_parse_fresh_among_other_args() {
        let args: Vec<String> = vec![
            "--timeout".into(),
            "30".into(),
            "--fresh".into(),
            "--lib".into(),
        ];
        assert!(parse_fresh(&args));
    }

    #[test]
    fn test_parse_fresh_not_present() {
        let args: Vec<String> = vec!["--timeout".into(), "30".into(), "--lib".into()];
        assert!(!parse_fresh(&args));
    }

    // --- parse_jobs tests ---

    #[test]
    fn test_parse_jobs_default() {
        let args: Vec<String> = vec![];
        assert_eq!(parse_jobs(&args), None);
    }

    #[test]
    fn test_parse_jobs_separate_arg() {
        let args: Vec<String> = vec!["--jobs".into(), "4".into()];
        assert_eq!(parse_jobs(&args), Some(4));
    }

    #[test]
    fn test_parse_jobs_equals_form() {
        let args: Vec<String> = vec!["--jobs=8".into()];
        assert_eq!(parse_jobs(&args), Some(8));
    }

    #[test]
    fn test_parse_jobs_invalid_value() {
        let args: Vec<String> = vec!["--jobs".into(), "abc".into()];
        assert_eq!(parse_jobs(&args), None);
    }

    #[test]
    fn test_parse_jobs_equals_invalid() {
        let args: Vec<String> = vec!["--jobs=xyz".into()];
        assert_eq!(parse_jobs(&args), None);
    }

    #[test]
    fn test_parse_jobs_one() {
        let args: Vec<String> = vec!["--jobs".into(), "1".into()];
        assert_eq!(parse_jobs(&args), Some(1));
    }

    #[test]
    fn test_parse_jobs_missing_value() {
        let args: Vec<String> = vec!["--jobs".into()];
        assert_eq!(parse_jobs(&args), None);
    }

    #[test]
    fn test_parse_jobs_among_other_args() {
        let args: Vec<String> = vec![
            "--timeout".into(),
            "10".into(),
            "--jobs".into(),
            "16".into(),
            "--fresh".into(),
        ];
        assert_eq!(parse_jobs(&args), Some(16));
    }

    #[test]
    fn test_parse_jobs_zero() {
        let args: Vec<String> = vec!["--jobs".into(), "0".into()];
        assert_eq!(parse_jobs(&args), Some(0));
    }

    // --- Combined argument parsing tests ---

    #[test]
    fn test_all_args_combined() {
        let args: Vec<String> = vec![
            "--timeout".into(),
            "90".into(),
            "--output-format=json".into(),
            "--fresh".into(),
            "--jobs".into(),
            "2".into(),
        ];
        assert_eq!(parse_timeout(&args), 90);
        assert_eq!(parse_output_format(&args), "json");
        assert!(parse_fresh(&args));
        assert_eq!(parse_jobs(&args), Some(2));
    }

    // --- print_usage tests ---

    #[test]
    fn test_print_usage_does_not_panic() {
        // Smoke test: ensure print_usage() executes without panicking
        // Output goes to stderr, which is acceptable in tests
        print_usage();
    }

    // --- read_crate_name tests ---
    // These tests use set_current_dir to a temporary directory. Since changing
    // the current directory is a process-global operation, a mutex serializes
    // all tests that rely on it.

    use std::sync::Mutex;

    static CWD_MUTEX: Mutex<()> = Mutex::new(());

    /// Helper: run a closure inside a temporary directory, restoring the
    /// original working directory afterwards. The CWD_MUTEX is held for
    /// the duration to avoid interference from concurrent tests.
    fn with_temp_dir<F: FnOnce(&std::path::Path)>(f: F) {
        let _lock = CWD_MUTEX.lock().unwrap();
        let original_dir = std::env::current_dir().unwrap();

        // Create a unique temp directory
        let mut tmp = std::env::temp_dir();
        tmp.push(format!(
            "rust_fv_test_{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&tmp).unwrap();

        std::env::set_current_dir(&tmp).unwrap();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(&tmp)));

        // Always restore the original directory and clean up
        std::env::set_current_dir(&original_dir).unwrap();
        let _ = std::fs::remove_dir_all(&tmp);

        if let Err(panic) = result {
            std::panic::resume_unwind(panic);
        }
    }

    #[test]
    fn test_read_crate_name_valid_package() {
        with_temp_dir(|tmp| {
            let cargo_toml = tmp.join("Cargo.toml");
            std::fs::write(
                &cargo_toml,
                r#"[package]
name = "my-awesome-crate"
version = "0.1.0"
edition = "2021"
"#,
            )
            .unwrap();
            assert_eq!(read_crate_name(), Some("my-awesome-crate".to_string()));
        });
    }

    #[test]
    fn test_read_crate_name_no_cargo_toml() {
        with_temp_dir(|_tmp| {
            // No Cargo.toml exists in temp dir
            assert_eq!(read_crate_name(), None);
        });
    }

    #[test]
    fn test_read_crate_name_no_package_section() {
        with_temp_dir(|tmp| {
            let cargo_toml = tmp.join("Cargo.toml");
            std::fs::write(
                &cargo_toml,
                r#"[workspace]
members = ["crates/*"]
"#,
            )
            .unwrap();
            assert_eq!(read_crate_name(), None);
        });
    }

    #[test]
    fn test_read_crate_name_empty_file() {
        with_temp_dir(|tmp| {
            let cargo_toml = tmp.join("Cargo.toml");
            std::fs::write(&cargo_toml, "").unwrap();
            assert_eq!(read_crate_name(), None);
        });
    }

    #[test]
    fn test_read_crate_name_name_in_wrong_section() {
        with_temp_dir(|tmp| {
            let cargo_toml = tmp.join("Cargo.toml");
            std::fs::write(
                &cargo_toml,
                r#"[dependencies]
name = "not-a-crate"

[package]
version = "0.1.0"
"#,
            )
            .unwrap();
            // Name is in [dependencies], not [package], so no name found
            assert_eq!(read_crate_name(), None);
        });
    }

    #[test]
    fn test_read_crate_name_with_single_quotes() {
        with_temp_dir(|tmp| {
            let cargo_toml = tmp.join("Cargo.toml");
            std::fs::write(
                &cargo_toml,
                "[package]\nname = 'single-quoted'\nversion = \"0.1.0\"\n",
            )
            .unwrap();
            assert_eq!(read_crate_name(), Some("single-quoted".to_string()));
        });
    }

    #[test]
    fn test_read_crate_name_with_spaces_around_equals() {
        with_temp_dir(|tmp| {
            let cargo_toml = tmp.join("Cargo.toml");
            std::fs::write(
                &cargo_toml,
                "[package]\nname   =   \"spaced-name\"\nversion = \"0.1.0\"\n",
            )
            .unwrap();
            assert_eq!(read_crate_name(), Some("spaced-name".to_string()));
        });
    }

    #[test]
    fn test_read_crate_name_with_leading_whitespace_on_lines() {
        with_temp_dir(|tmp| {
            let cargo_toml = tmp.join("Cargo.toml");
            std::fs::write(
                &cargo_toml,
                "[package]\n  name = \"indented-crate\"\n  version = \"0.1.0\"\n",
            )
            .unwrap();
            assert_eq!(read_crate_name(), Some("indented-crate".to_string()));
        });
    }

    #[test]
    fn test_read_crate_name_package_not_first_section() {
        with_temp_dir(|tmp| {
            let cargo_toml = tmp.join("Cargo.toml");
            std::fs::write(
                &cargo_toml,
                r#"[workspace]
members = ["crates/*"]

[package]
name = "after-workspace"
version = "0.1.0"
"#,
            )
            .unwrap();
            assert_eq!(read_crate_name(), Some("after-workspace".to_string()));
        });
    }

    #[test]
    fn test_read_crate_name_name_after_other_fields() {
        with_temp_dir(|tmp| {
            let cargo_toml = tmp.join("Cargo.toml");
            std::fs::write(
                &cargo_toml,
                r#"[package]
version = "0.1.0"
edition = "2021"
name = "name-last"
"#,
            )
            .unwrap();
            assert_eq!(read_crate_name(), Some("name-last".to_string()));
        });
    }

    #[test]
    fn test_read_crate_name_multiple_sections_after_package() {
        with_temp_dir(|tmp| {
            let cargo_toml = tmp.join("Cargo.toml");
            std::fs::write(
                &cargo_toml,
                r#"[package]
name = "multi-section"
version = "0.1.0"

[dependencies]
serde = "1.0"

[dev-dependencies]
name = "should-not-match"
"#,
            )
            .unwrap();
            assert_eq!(read_crate_name(), Some("multi-section".to_string()));
        });
    }

    #[test]
    fn test_read_crate_name_no_name_field_in_package() {
        with_temp_dir(|tmp| {
            let cargo_toml = tmp.join("Cargo.toml");
            std::fs::write(
                &cargo_toml,
                r#"[package]
version = "0.1.0"
edition = "2021"

[dependencies]
"#,
            )
            .unwrap();
            assert_eq!(read_crate_name(), None);
        });
    }

    #[test]
    fn test_read_crate_name_package_section_at_end_without_name() {
        with_temp_dir(|tmp| {
            let cargo_toml = tmp.join("Cargo.toml");
            std::fs::write(
                &cargo_toml,
                r#"[dependencies]
serde = "1.0"

[package]
version = "0.1.0"
"#,
            )
            .unwrap();
            assert_eq!(read_crate_name(), None);
        });
    }

    // --- Additional edge case tests ---

    #[test]
    fn test_parse_timeout_multiple_occurrences_uses_first() {
        let args: Vec<String> = vec![
            "--timeout".into(),
            "10".into(),
            "--timeout".into(),
            "20".into(),
        ];
        // Should use the first occurrence
        assert_eq!(parse_timeout(&args), 10);
    }

    #[test]
    fn test_parse_output_format_multiple_occurrences_uses_first() {
        let args: Vec<String> = vec![
            "--output-format".into(),
            "json".into(),
            "--output-format".into(),
            "text".into(),
        ];
        // Should use the first occurrence
        assert_eq!(parse_output_format(&args), "json");
    }

    #[test]
    fn test_parse_jobs_multiple_occurrences_uses_first() {
        let args: Vec<String> = vec!["--jobs".into(), "4".into(), "--jobs".into(), "8".into()];
        // Should use the first occurrence
        assert_eq!(parse_jobs(&args), Some(4));
    }

    #[test]
    fn test_parse_timeout_very_large_value() {
        let args: Vec<String> = vec!["--timeout".into(), "999999999".into()];
        assert_eq!(parse_timeout(&args), 999999999);
    }

    #[test]
    fn test_parse_timeout_negative_value_returns_default() {
        let args: Vec<String> = vec!["--timeout".into(), "-10".into()];
        // Negative numbers fail to parse as u64, so default is returned
        assert_eq!(parse_timeout(&args), 30);
    }

    #[test]
    fn test_parse_jobs_very_large_value() {
        let args: Vec<String> = vec!["--jobs".into(), "1000".into()];
        assert_eq!(parse_jobs(&args), Some(1000));
    }

    #[test]
    fn test_parse_jobs_negative_value_returns_none() {
        let args: Vec<String> = vec!["--jobs".into(), "-5".into()];
        // Negative numbers fail to parse as usize
        assert_eq!(parse_jobs(&args), None);
    }

    #[test]
    fn test_parse_output_format_empty_value() {
        let args: Vec<String> = vec!["--output-format=".into()];
        // Empty string after equals is still a valid string
        assert_eq!(parse_output_format(&args), "");
    }

    #[test]
    fn test_parse_timeout_equals_empty_returns_default() {
        let args: Vec<String> = vec!["--timeout=".into()];
        // Empty string fails to parse, so default is returned
        assert_eq!(parse_timeout(&args), 30);
    }

    #[test]
    fn test_parse_jobs_equals_empty_returns_none() {
        let args: Vec<String> = vec!["--jobs=".into()];
        // Empty string fails to parse
        assert_eq!(parse_jobs(&args), None);
    }

    #[test]
    fn test_parse_fresh_multiple_occurrences() {
        let args: Vec<String> = vec!["--fresh".into(), "--fresh".into()];
        // Multiple --fresh flags should still return true
        assert!(parse_fresh(&args));
    }

    #[test]
    fn test_parse_timeout_whitespace_value_returns_default() {
        let args: Vec<String> = vec!["--timeout".into(), "  ".into()];
        // Whitespace fails to parse as u64
        assert_eq!(parse_timeout(&args), 30);
    }

    #[test]
    fn test_parse_jobs_whitespace_value_returns_none() {
        let args: Vec<String> = vec!["--jobs".into(), "  ".into()];
        // Whitespace fails to parse as usize
        assert_eq!(parse_jobs(&args), None);
    }

    #[test]
    fn test_parse_timeout_mixed_with_similar_flags() {
        let args: Vec<String> = vec![
            "--timeout-extra".into(), // Similar but different flag
            "100".into(),
            "--timeout".into(),
            "50".into(),
        ];
        // Should only match exact --timeout flag
        assert_eq!(parse_timeout(&args), 50);
    }

    #[test]
    fn test_parse_output_format_mixed_with_similar_flags() {
        let args: Vec<String> = vec![
            "--output-format-extra".into(), // Similar but different flag
            "wrong".into(),
            "--output-format".into(),
            "json".into(),
        ];
        // Should only match exact --output-format flag
        assert_eq!(parse_output_format(&args), "json");
    }

    #[test]
    fn test_parse_timeout_equals_with_equals_in_value() {
        let args: Vec<String> = vec!["--timeout=30=40".into()];
        // The value after first = is "30=40", which fails to parse
        assert_eq!(parse_timeout(&args), 30);
    }

    #[test]
    fn test_all_args_with_equals_forms() {
        let args: Vec<String> = vec![
            "--timeout=15".into(),
            "--output-format=json".into(),
            "--jobs=3".into(),
            "--fresh".into(),
        ];
        assert_eq!(parse_timeout(&args), 15);
        assert_eq!(parse_output_format(&args), "json");
        assert_eq!(parse_jobs(&args), Some(3));
        assert!(parse_fresh(&args));
    }

    #[test]
    fn test_empty_args_all_defaults() {
        let args: Vec<String> = vec![];
        assert_eq!(parse_timeout(&args), 30);
        assert_eq!(parse_output_format(&args), "text");
        assert_eq!(parse_jobs(&args), None);
        assert!(!parse_fresh(&args));
        assert!(!parse_no_stdlib_contracts(&args));
    }

    // --- parse_no_stdlib_contracts tests ---

    #[test]
    fn test_parse_no_stdlib_contracts_default() {
        let args: Vec<String> = vec![];
        assert!(!parse_no_stdlib_contracts(&args));
    }

    #[test]
    fn test_parse_no_stdlib_contracts_present() {
        let args: Vec<String> = vec!["--no-stdlib-contracts".into()];
        assert!(parse_no_stdlib_contracts(&args));
    }

    #[test]
    fn test_parse_no_stdlib_contracts_among_other_args() {
        let args: Vec<String> = vec![
            "--timeout".into(),
            "30".into(),
            "--no-stdlib-contracts".into(),
            "--lib".into(),
        ];
        assert!(parse_no_stdlib_contracts(&args));
    }

    #[test]
    fn test_parse_no_stdlib_contracts_not_present() {
        let args: Vec<String> = vec!["--timeout".into(), "30".into(), "--lib".into()];
        assert!(!parse_no_stdlib_contracts(&args));
    }
}
