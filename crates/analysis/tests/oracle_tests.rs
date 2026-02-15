//! Property-based oracle tests for stdlib contract soundness.
//!
//! These tests run real stdlib operations with random inputs (via proptest)
//! and verify that all contract postconditions hold. Any oracle failure
//! indicates an unsound contract.
//!
//! NOTE: Many clippy lints are suppressed because oracle tests intentionally
//! exercise operations in ways that mirror contract specifications rather
//! than idiomatic Rust (e.g., testing Some(x).map(f) on known Some values).

#![allow(
    clippy::len_zero,
    clippy::unnecessary_map_on_constructor,
    clippy::unnecessary_literal_unwrap,
    clippy::unnecessary_lazy_evaluations,
    clippy::nonminimal_bool,
    clippy::bool_assert_comparison,
    clippy::iter_count,
    clippy::suspicious_map,
    clippy::needless_collect,
    clippy::unnecessary_get_then_check
)]

mod oracle;
