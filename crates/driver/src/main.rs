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

mod callbacks;
mod mir_converter;

use std::process::ExitCode;

fn main() -> ExitCode {
    let early_dcx =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&early_dcx);

    let args: Vec<String> = std::env::args().collect();

    let verify =
        std::env::var("RUST_FV_VERIFY").is_ok() || args.iter().any(|a| a == "--rust-fv-verify");

    let rustc_args: Vec<String> = args
        .into_iter()
        .filter(|a| a != "--rust-fv-verify")
        .collect();

    let mut callbacks = if verify {
        callbacks::VerificationCallbacks::new()
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
