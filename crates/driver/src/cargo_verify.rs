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

use crate::json_output::JsonVerificationReport;
use crate::output;
use crate::rustc_json;

/// Run the cargo verify subcommand.
///
/// # Arguments
/// * `args` - Arguments after "verify" (e.g., `--timeout 30`)
pub fn run_cargo_verify(args: &[String]) -> i32 {
    // Check for clean subcommand
    if args.first().map(|s| s.as_str()) == Some("clean") {
        return run_cargo_verify_clean();
    }

    // Check for --help
    if args.iter().any(|a| a == "--help" || a == "-h") {
        print_usage();
        return 0;
    }

    // Check for --version
    if args.iter().any(|a| a == "--version" || a == "-V") {
        eprintln!(
            "rust-fv {}",
            option_env!("CARGO_PKG_VERSION").unwrap_or("0.1.0")
        );
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

    // Parse verbose flag from args (default: false)
    let verbose = parse_verbose(args);

    // Parse message-format from args (default: None -- rustc-compatible JSON for IDE integration)
    let message_format = parse_message_format(args);

    // When message-format=json, force JSON output internally so we can convert
    let effective_output_format = if message_format.as_deref() == Some("json") {
        "json".to_string()
    } else {
        output_format.clone()
    };

    // Build the cargo check command with our driver as RUSTC
    let mut cmd = Command::new("cargo");
    cmd.arg("check")
        .env("RUSTC", &driver_path)
        .env("RUST_FV_VERIFY", "1")
        .stderr(Stdio::inherit());

    // When message-format=json, capture stdout to convert to rustc format
    if message_format.as_deref() == Some("json") {
        cmd.stdout(Stdio::piped());
    } else {
        cmd.stdout(Stdio::inherit());
    }

    if timeout > 0 {
        cmd.env("RUST_FV_TIMEOUT", timeout.to_string());
    }

    if effective_output_format == "json" {
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

    if verbose {
        cmd.env("RUST_FV_VERBOSE", "1");
    }

    // Forward any extra args (e.g., --package, --lib, etc.)
    // Skip rust-fv-specific flags that cargo check doesn't understand
    let mut skip_next = false;
    for arg in args {
        if skip_next {
            skip_next = false;
            continue;
        }
        if arg == "--message-format"
            || arg == "--output-format"
            || arg == "--timeout"
            || arg == "--jobs"
        {
            skip_next = true;
            continue;
        }
        if arg.starts_with("--timeout")
            || arg.starts_with("--output-format")
            || arg.starts_with("--fresh")
            || arg.starts_with("--jobs")
            || arg.starts_with("--no-stdlib-contracts")
            || arg.starts_with("--verbose")
            || arg.starts_with("--message-format")
            || arg == "-v"
            || arg == "--version"
            || arg == "-V"
        {
            continue;
        }
        cmd.arg(arg);
    }

    if effective_output_format != "json" {
        eprintln!("{}", "Running verification...".dimmed());
    }

    if message_format.as_deref() == Some("json") {
        // Capture stdout and convert to rustc-compatible JSON diagnostics
        match cmd.output() {
            Ok(output) => {
                let stdout = String::from_utf8_lossy(&output.stdout);
                // Try to parse the JSON verification report from stdout
                if let Some(report) = parse_json_report_from_output(&stdout) {
                    rustc_json::emit_rustc_diagnostics(&report);
                }
                if output.status.success() { 0 } else { 1 }
            }
            Err(e) => {
                eprintln!("{} Failed to run cargo check: {e}", "error:".red().bold());
                2
            }
        }
    } else {
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

/// Parse --verbose flag from arguments.
fn parse_verbose(args: &[String]) -> bool {
    args.iter().any(|a| a == "--verbose" || a == "-v")
}

/// Parse --message-format FORMAT from arguments.
///
/// This is separate from `--output-format` which controls the existing
/// `JsonVerificationReport` format. `--message-format json` produces
/// rustc-compatible diagnostics for rust-analyzer integration.
fn parse_message_format(args: &[String]) -> Option<String> {
    for (i, arg) in args.iter().enumerate() {
        if arg == "--message-format" {
            return args.get(i + 1).cloned();
        }
        if let Some(val) = arg.strip_prefix("--message-format=") {
            if val.is_empty() {
                return None;
            }
            return Some(val.to_string());
        }
    }
    None
}

/// Parse JSON verification report from captured subprocess output.
///
/// The driver (rustc replacement) writes the JSON report to stdout
/// when `RUST_FV_OUTPUT_FORMAT=json`. This function extracts it.
fn parse_json_report_from_output(stdout: &str) -> Option<JsonVerificationReport> {
    // The output may contain cargo's own output mixed in.
    // Try to find and parse the JSON report -- it's the pretty-printed
    // JSON object that starts with { and contains "crate_name".
    // Try parsing the whole output first (simple case).
    if let Ok(report) = serde_json::from_str::<JsonVerificationReport>(stdout) {
        return Some(report);
    }

    // Try to find a JSON object in the output by looking for balanced braces
    let trimmed = stdout.trim();
    if let Some(start) = trimmed.find('{') {
        // Find the matching closing brace
        let bytes = trimmed.as_bytes();
        let mut depth = 0;
        let mut end = start;
        for (i, &b) in bytes[start..].iter().enumerate() {
            match b {
                b'{' => depth += 1,
                b'}' => {
                    depth -= 1;
                    if depth == 0 {
                        end = start + i;
                        break;
                    }
                }
                _ => {}
            }
        }
        if depth == 0 {
            let json_str = &trimmed[start..=end];
            if let Ok(report) = serde_json::from_str::<JsonVerificationReport>(json_str) {
                return Some(report);
            }
        }
    }

    None
}

/// Run the `cargo verify clean` subcommand.
///
/// Deletes the verification cache directory (target/verify-cache/).
fn run_cargo_verify_clean() -> i32 {
    let cache_dir = std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".to_string());
    let cache_path = std::path::PathBuf::from(cache_dir).join("verify-cache");

    if !cache_path.exists() {
        eprintln!("Cache directory does not exist: {}", cache_path.display());
        return 0;
    }

    match std::fs::remove_dir_all(&cache_path) {
        Ok(()) => {
            eprintln!(
                "{}",
                format!("Removed cache directory: {}", cache_path.display())
                    .green()
                    .bold()
            );
            0
        }
        Err(e) => {
            eprintln!(
                "{} Failed to remove cache directory: {e}",
                "error:".red().bold()
            );
            1
        }
    }
}

/// Print usage information.
fn print_usage() {
    eprintln!("rust-fv: Formal verification for Rust");
    eprintln!();
    eprintln!("USAGE:");
    eprintln!("    cargo verify [OPTIONS]");
    eprintln!("    cargo verify clean");
    eprintln!();
    eprintln!("SUBCOMMANDS:");
    eprintln!("    clean    Delete verification cache (target/verify-cache/)");
    eprintln!();
    eprintln!("OPTIONS:");
    eprintln!("    --timeout <SECONDS>         Verification timeout per function (default: 30)");
    eprintln!("    --output-format <FORMAT>    Output format: text or json (default: text)");
    eprintln!(
        "    --fresh                     Force re-verification, bypassing cache (keeps cache files)"
    );
    eprintln!(
        "    --jobs <N>                  Number of parallel verification threads (default: num_cpus/2)"
    );
    eprintln!("    --verbose, -v               Show per-function timing information");
    eprintln!("    --no-stdlib-contracts       Disable standard library contracts");
    eprintln!(
        "    --message-format <FORMAT>   Output format for IDE integration: json (default: none)"
    );
    eprintln!(
        "                                Use 'json' for rust-analyzer compatible diagnostics"
    );
    eprintln!("    --version, -V               Print version information");
    eprintln!("    --help, -h                  Print this help message");
    eprintln!();
    eprintln!("DESCRIPTION:");
    eprintln!("    Runs formal verification on all annotated functions in the current crate.");
    eprintln!("    Functions are annotated with #[requires(...)], #[ensures(...)], #[pure],");
    eprintln!("    and #[invariant(...)] attributes from the rust-fv-macros crate.");
    eprintln!();
    eprintln!("    Results are displayed with colored status (text mode):");
    eprintln!("      [OK]      - All verification conditions verified");
    eprintln!("      [SKIP]    - Verification skipped (cached result)");
    eprintln!("      [FAIL]    - At least one verification condition failed");
    eprintln!("      [TIMEOUT] - Verification timed out");
    eprintln!();
    eprintln!("    JSON mode outputs structured results to stdout for IDE integration.");
    eprintln!();
    eprintln!("    Caching: Verification results are cached in target/verify-cache/ and reused");
    eprintln!("    when source code hasn't changed. Use --fresh to bypass cache or");
    eprintln!("    'cargo verify clean' to permanently delete the cache.");
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

    // --- parse_verbose tests ---

    #[test]
    fn test_parse_verbose_default() {
        let args: Vec<String> = vec![];
        assert!(!parse_verbose(&args));
    }

    #[test]
    fn test_parse_verbose_long_form() {
        let args: Vec<String> = vec!["--verbose".into()];
        assert!(parse_verbose(&args));
    }

    #[test]
    fn test_parse_verbose_short_form() {
        let args: Vec<String> = vec!["-v".into()];
        assert!(parse_verbose(&args));
    }

    #[test]
    fn test_parse_verbose_among_other_args() {
        let args: Vec<String> = vec![
            "--timeout".into(),
            "30".into(),
            "--verbose".into(),
            "--lib".into(),
        ];
        assert!(parse_verbose(&args));
    }

    #[test]
    fn test_parse_verbose_not_present() {
        let args: Vec<String> = vec!["--timeout".into(), "30".into(), "--lib".into()];
        assert!(!parse_verbose(&args));
    }

    #[test]
    fn test_parse_verbose_multiple_forms() {
        let args: Vec<String> = vec!["-v".into(), "--verbose".into()];
        assert!(parse_verbose(&args));
    }

    // --- cargo verify clean tests ---

    #[test]
    fn test_clean_command_detection() {
        // Test that "clean" as first arg is recognized
        let args: Vec<String> = vec!["clean".into()];
        assert_eq!(args.first().map(|s| s.as_str()), Some("clean"));
    }

    #[test]
    fn test_clean_command_with_extra_args() {
        // Test that "clean" is recognized even with extra args
        let args: Vec<String> = vec!["clean".into(), "--extra".into()];
        assert_eq!(args.first().map(|s| s.as_str()), Some("clean"));
    }

    #[test]
    fn test_run_cargo_verify_clean_nonexistent_dir() {
        // Test cleaning when cache directory doesn't exist
        // Uses environment variable to point to a non-existent location
        unsafe {
            std::env::set_var("CARGO_TARGET_DIR", "/tmp/nonexistent-rust-fv-test-dir");
        }
        let exit_code = run_cargo_verify_clean();
        unsafe {
            std::env::remove_var("CARGO_TARGET_DIR");
        }
        assert_eq!(exit_code, 0); // Should succeed even if dir doesn't exist
    }

    // --- parse_message_format tests ---

    #[test]
    fn test_parse_message_format_default() {
        let args: Vec<String> = vec![];
        assert_eq!(parse_message_format(&args), None);
    }

    #[test]
    fn test_parse_message_format_json_separate() {
        let args: Vec<String> = vec!["--message-format".into(), "json".into()];
        assert_eq!(parse_message_format(&args), Some("json".to_string()));
    }

    #[test]
    fn test_parse_message_format_json_equals() {
        let args: Vec<String> = vec!["--message-format=json".into()];
        assert_eq!(parse_message_format(&args), Some("json".to_string()));
    }

    #[test]
    fn test_parse_message_format_among_other_args() {
        let args: Vec<String> = vec![
            "--timeout".into(),
            "30".into(),
            "--message-format".into(),
            "json".into(),
            "--lib".into(),
        ];
        assert_eq!(parse_message_format(&args), Some("json".to_string()));
    }

    #[test]
    fn test_parse_message_format_missing_value() {
        // --message-format is last arg, no value follows
        let args: Vec<String> = vec!["--message-format".into()];
        assert_eq!(parse_message_format(&args), None);
    }

    #[test]
    fn test_parse_message_format_empty_value() {
        let args: Vec<String> = vec!["--message-format=".into()];
        assert_eq!(parse_message_format(&args), None);
    }

    // --- parse_json_report_from_output tests ---

    #[test]
    fn test_parse_json_report_valid() {
        use crate::json_output::{JsonSummary, JsonVerificationReport};
        let report = JsonVerificationReport {
            crate_name: "test".to_string(),
            functions: vec![],
            summary: JsonSummary {
                total: 0,
                ok: 0,
                fail: 0,
                timeout: 0,
            },
        };
        let json = serde_json::to_string_pretty(&report).unwrap();
        let parsed = parse_json_report_from_output(&json);
        assert!(parsed.is_some());
        assert_eq!(parsed.unwrap().crate_name, "test");
    }

    #[test]
    fn test_parse_json_report_with_prefix() {
        use crate::json_output::{JsonSummary, JsonVerificationReport};
        let report = JsonVerificationReport {
            crate_name: "embedded".to_string(),
            functions: vec![],
            summary: JsonSummary {
                total: 1,
                ok: 1,
                fail: 0,
                timeout: 0,
            },
        };
        let json = serde_json::to_string_pretty(&report).unwrap();
        let output = format!("Some cargo output\n{}\n", json);
        let parsed = parse_json_report_from_output(&output);
        assert!(parsed.is_some());
        assert_eq!(parsed.unwrap().crate_name, "embedded");
    }

    #[test]
    fn test_parse_json_report_empty_output() {
        let parsed = parse_json_report_from_output("");
        assert!(parsed.is_none());
    }

    #[test]
    fn test_parse_json_report_invalid_json() {
        let parsed = parse_json_report_from_output("not json at all");
        assert!(parsed.is_none());
    }
}
