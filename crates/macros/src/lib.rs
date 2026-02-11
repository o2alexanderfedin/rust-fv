//! Procedural macros for Rust formal verification annotations.
//!
//! These macros attach formal specifications to Rust items as hidden doc
//! attributes, enabling the compiler driver to extract them from HIR
//! without any runtime overhead.
//!
//! # Macros
//!
//! - `#[requires(condition)]` — Function precondition
//! - `#[ensures(condition)]` — Function postcondition (`result` refers to the return value)
//! - `#[pure]` — Pure function marker (usable in specifications)
//! - `#[invariant(condition)]` — Type or loop invariant

extern crate proc_macro;

use proc_macro::TokenStream;
use quote::ToTokens;
use syn::parse_macro_input;

/// Attach a precondition to a function.
///
/// The condition must be a valid Rust expression. It is stored as a hidden
/// doc attribute so the verification driver can retrieve it later.
///
/// # Example
///
/// ```ignore
/// #[requires(x > 0)]
/// fn positive_only(x: i32) -> i32 { x }
/// ```
#[proc_macro_attribute]
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    spec_attribute("requires", attr, item)
}

/// Attach a postcondition to a function.
///
/// The keyword `result` inside the condition refers to the function's
/// return value. The condition must be a valid Rust expression.
///
/// # Example
///
/// ```ignore
/// #[ensures(result >= 0)]
/// fn absolute(x: i32) -> i32 { x.abs() }
/// ```
#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    spec_attribute("ensures", attr, item)
}

/// Mark a function as pure (side-effect-free).
///
/// Pure functions may be referenced inside `requires` and `ensures`
/// specifications.
///
/// # Example
///
/// ```ignore
/// #[pure]
/// fn square(x: i32) -> i32 { x * x }
/// ```
#[proc_macro_attribute]
pub fn pure(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new_spanned(
            proc_macro2::TokenStream::from(attr),
            "`#[pure]` does not accept arguments",
        )
        .to_compile_error()
        .into();
    }

    let item = proc_macro2::TokenStream::from(item);
    let doc_value = "rust_fv::pure";

    quote::quote! {
        #[doc(hidden)]
        #[doc = #doc_value]
        #item
    }
    .into()
}

/// Attach an invariant to a type or loop.
///
/// The condition must be a valid Rust expression.
///
/// # Example
///
/// ```ignore
/// #[invariant(self.len <= self.capacity)]
/// struct Buffer { len: usize, capacity: usize }
/// ```
#[proc_macro_attribute]
pub fn invariant(attr: TokenStream, item: TokenStream) -> TokenStream {
    spec_attribute("invariant", attr, item)
}

/// Mark a variable or code block as specification-only (ghost code).
///
/// Ghost variables and functions are used in specifications but erased
/// from the compiled executable. They exist only for verification purposes.
///
/// # Example
///
/// ```ignore
/// #[ghost]
/// fn spec_helper(x: i32) -> i32 { x * 2 }
/// ```
#[proc_macro_attribute]
pub fn ghost(attr: TokenStream, item: TokenStream) -> TokenStream {
    if !attr.is_empty() {
        return syn::Error::new_spanned(
            proc_macro2::TokenStream::from(attr),
            "`#[ghost]` does not accept arguments",
        )
        .to_compile_error()
        .into();
    }

    let item = proc_macro2::TokenStream::from(item);
    let doc_value = "rust_fv::ghost";

    quote::quote! {
        #[doc(hidden)]
        #[doc = #doc_value]
        #item
    }
    .into()
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Shared implementation for `requires`, `ensures`, and `invariant`.
///
/// 1. Parses `attr` as a Rust expression (compile error on failure).
/// 2. Converts the expression back to a canonical string.
/// 3. Prepends a hidden doc attribute encoding the spec.
/// 4. Emits the original item unchanged.
fn spec_attribute(kind: &str, attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse the attribute content as a Rust expression to validate it.
    let expr = parse_macro_input!(attr as syn::Expr);

    // Canonical string representation of the specification expression.
    let spec_string = expr.to_token_stream().to_string();

    let doc_value = format!("rust_fv::{kind}::{spec_string}");
    let item = proc_macro2::TokenStream::from(item);

    quote::quote! {
        #[doc(hidden)]
        #[doc = #doc_value]
        #item
    }
    .into()
}
