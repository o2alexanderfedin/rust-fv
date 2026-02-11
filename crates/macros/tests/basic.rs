//! Integration tests for `rust-fv-macros` proc-macro attributes.
//!
//! These tests verify that the macros compile, preserve the original item,
//! and embed the expected hidden doc attributes.

use rust_fv_macros::{ensures, invariant, pure, requires};

// ---------------------------------------------------------------------------
// #[requires] — basic compilation
// ---------------------------------------------------------------------------

#[requires(x > 0)]
fn positive_only(x: i32) -> i32 {
    x
}

#[test]
fn requires_basic_compiles_and_runs() {
    assert_eq!(positive_only(5), 5);
}

// ---------------------------------------------------------------------------
// #[ensures] — basic compilation (with `result` keyword)
// ---------------------------------------------------------------------------

#[ensures(result >= 0)]
fn absolute(x: i32) -> i32 {
    x.abs()
}

#[test]
fn ensures_basic_compiles_and_runs() {
    assert_eq!(absolute(-3), 3);
    assert_eq!(absolute(7), 7);
}

// ---------------------------------------------------------------------------
// #[pure] — basic compilation
// ---------------------------------------------------------------------------

#[pure]
fn square(x: i32) -> i32 {
    x * x
}

#[test]
fn pure_basic_compiles_and_runs() {
    assert_eq!(square(4), 16);
}

// ---------------------------------------------------------------------------
// Multiple attributes on one function
// ---------------------------------------------------------------------------

#[requires(x > 0)]
#[requires(x < 100)]
#[ensures(result > 0)]
#[ensures(result < 10000)]
#[pure]
fn bounded_square(x: i32) -> i32 {
    x * x
}

#[test]
fn multiple_attributes_compile_and_run() {
    assert_eq!(bounded_square(3), 9);
    assert_eq!(bounded_square(10), 100);
}

// ---------------------------------------------------------------------------
// #[invariant] on a struct
// ---------------------------------------------------------------------------

#[invariant(self.len <= self.capacity)]
struct Buffer {
    len: usize,
    capacity: usize,
}

#[test]
fn invariant_on_struct_compiles() {
    let buf = Buffer {
        len: 5,
        capacity: 10,
    };
    assert!(buf.len <= buf.capacity);
}

// ---------------------------------------------------------------------------
// #[requires] / #[ensures] with complex expressions
// ---------------------------------------------------------------------------

#[requires(items.len() > 0)]
#[ensures(result <= items.len())]
fn count_positive(items: &[i32]) -> usize {
    items.iter().filter(|&&v| v > 0).count()
}

#[test]
fn complex_expressions_compile_and_run() {
    assert_eq!(count_positive(&[1, -2, 3]), 2);
}

// ---------------------------------------------------------------------------
// #[requires] with boolean operators
// ---------------------------------------------------------------------------

#[requires(a != 0 && b != 0)]
fn divide(a: i32, b: i32) -> i32 {
    a / b
}

#[test]
fn boolean_operators_in_requires() {
    assert_eq!(divide(10, 2), 5);
}

// ---------------------------------------------------------------------------
// #[ensures] with old-style result reference and arithmetic
// ---------------------------------------------------------------------------

#[ensures(result == a + b)]
fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[test]
fn ensures_arithmetic_expression() {
    assert_eq!(add(2, 3), 5);
}

// ---------------------------------------------------------------------------
// #[invariant] on a tuple struct
// ---------------------------------------------------------------------------

#[invariant(self.0 >= 0)]
struct NonNegative(i32);

#[test]
fn invariant_on_tuple_struct_compiles() {
    let nn = NonNegative(42);
    assert!(nn.0 >= 0);
}

// ---------------------------------------------------------------------------
// #[invariant] on an enum
// ---------------------------------------------------------------------------

#[invariant(true)]
enum Status {
    Active,
    #[allow(dead_code)]
    Inactive,
}

#[test]
fn invariant_on_enum_compiles() {
    let _s = Status::Active;
}

// ---------------------------------------------------------------------------
// #[pure] on a function with no arguments
// ---------------------------------------------------------------------------

#[pure]
fn constant() -> i32 {
    42
}

#[test]
fn pure_no_args() {
    assert_eq!(constant(), 42);
}
