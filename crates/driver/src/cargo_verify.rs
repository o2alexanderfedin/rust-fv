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

    // Forward any extra args (e.g., --package, --lib, etc.)
    for arg in args {
        if !arg.starts_with("--timeout")
            && !arg.starts_with("--output-format")
            && !arg.starts_with("--fresh")
            && !arg.starts_with("--jobs")
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
