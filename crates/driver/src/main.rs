#![feature(rustc_private)]
#![feature(box_patterns)]

//! rust-fv-driver: A rustc wrapper that performs formal verification.
//!
//! This binary replaces `rustc` via the `RUSTC` environment variable.
//! It hooks into compilation via `rustc_driver::Callbacks` and performs
//! verification at the `after_analysis` phase, where MIR and type
//! information are fully available.
//!
//! Usage:
//!   RUSTC=/path/to/rust-fv-driver cargo check
//!
//! Or via the cargo subcommand (future):
//!   cargo fv check

extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod cache;
mod callbacks;
mod cargo_verify;
mod diagnostics;
mod invalidation;
mod json_output;
mod mir_converter;
mod output;
mod parallel;
mod rustc_json;

#[cfg(test)]
mod bench_incremental;

use std::process::ExitCode;

fn main() -> ExitCode {
    // Check if invoked as `cargo verify` subcommand.
    // When cargo runs a subcommand, args are: [binary, "verify", ...]
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 && args[1] == "verify" {
        let exit_code = cargo_verify::run_cargo_verify(&args[2..]);
        return match exit_code {
            0 => ExitCode::SUCCESS,
            _ => ExitCode::FAILURE,
        };
    }

    // Initialize tracing subscriber before any verification work
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::from_default_env()
                .add_directive("rust_fv=info".parse().unwrap()),
        )
        .with_target(true)
        .init();

    let early_dcx =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&early_dcx);

    let verify =
        std::env::var("RUST_FV_VERIFY").is_ok() || args.iter().any(|a| a == "--rust-fv-verify");

    let output_format = match std::env::var("RUST_FV_OUTPUT_FORMAT").as_deref() {
        Ok("json") => callbacks::OutputFormat::Json,
        _ => callbacks::OutputFormat::Text,
    };

    // Read RUST_FV_FRESH flag (default: false)
    let fresh = std::env::var("RUST_FV_FRESH").is_ok();

    // Read RUST_FV_JOBS flag (default: num_cpus/2, min 1)
    let jobs = std::env::var("RUST_FV_JOBS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or_else(|| {
            let cpus = std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(2);
            (cpus / 2).max(1)
        });

    let rustc_args: Vec<String> = args
        .into_iter()
        .filter(|a| a != "--rust-fv-verify")
        .collect();

    let mut callbacks = if verify {
        callbacks::VerificationCallbacks::new(output_format, jobs, fresh)
    } else {
        callbacks::VerificationCallbacks::passthrough()
    };

    let result = rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(&rustc_args, &mut callbacks);
    });

    if verify {
        callbacks.print_results();
    }

    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}
