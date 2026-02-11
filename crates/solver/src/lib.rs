//! # rust-fv-solver
//!
//! SMT solver interface for Rust formal verification.
//!
//! This crate provides a clean interface to the Z3 SMT solver by spawning it
//! as an external process and communicating via SMT-LIB2 text.
//!
//! ## Usage
//!
//! ```no_run
//! use rust_fv_solver::{Z3Solver, SolverResult};
//!
//! let solver = Z3Solver::with_default_config().unwrap();
//! let result = solver.check_sat_raw("
//!     (declare-const x Int)
//!     (assert (> x 0))
//!     (assert (< x 10))
//!     (check-sat)
//!     (get-model)
//! ").unwrap();
//!
//! match result {
//!     SolverResult::Sat(model) => println!("SAT: {model:?}"),
//!     SolverResult::Unsat => println!("UNSAT (proved)"),
//!     SolverResult::Unknown(reason) => println!("Unknown: {reason}"),
//! }
//! ```

pub mod config;
pub mod error;
pub mod model;
mod parser;
pub mod result;
pub mod solver;

// Re-export primary types for ergonomic use
pub use config::SolverConfig;
pub use error::SolverError;
pub use model::Model;
pub use result::SolverResult;
pub use solver::Z3Solver;
