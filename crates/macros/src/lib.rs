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
//! - `#[decreases(expr)]` — Termination measure for recursive functions

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
    pure_impl(attr.into(), item.into()).into()
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

/// Attach a termination measure (decreases clause) to a recursive function.
///
/// The expression must be a valid Rust expression that decreases at each
/// recursive call site. It is stored as a hidden doc attribute so the
/// verification driver can retrieve it later.
///
/// # Example
///
/// ```ignore
/// #[decreases(n)]
/// fn factorial(n: u64) -> u64 {
///     if n == 0 { 1 } else { n * factorial(n - 1) }
/// }
/// ```
#[proc_macro_attribute]
pub fn decreases(attr: TokenStream, item: TokenStream) -> TokenStream {
    spec_attribute("decreases", attr, item)
}

/// Attach a borrow ensures specification to a function with mutable reference parameters.
///
/// `#[borrow_ensures(param, expr)]` specifies the final value constraint for a mutable
/// borrow parameter. The first argument is the parameter name, the second is the
/// expression describing its final value.
///
/// # Example
///
/// ```ignore
/// #[borrow_ensures(x, *x == old(*x) + 1)]
/// fn increment(x: &mut i32) {
///     *x += 1;
/// }
/// ```
#[proc_macro_attribute]
pub fn borrow_ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    borrow_ensures_impl(attr.into(), item.into()).into()
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
    ghost_impl(attr.into(), item.into()).into()
}

/// Attach a safety precondition to an unsafe function.
///
/// `#[unsafe_requires(expr)]` specifies a safety precondition that must hold
/// for unsafe code to be correct. Unlike `#[requires]`, this is about memory
/// safety rather than logical correctness.
///
/// # Example
///
/// ```ignore
/// #[unsafe_requires(ptr != null)]
/// unsafe fn deref_ptr(ptr: *const i32) -> i32 { *ptr }
/// ```
#[proc_macro_attribute]
pub fn unsafe_requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    spec_attribute("unsafe_requires", attr, item)
}

/// Attach a safety postcondition to an unsafe function.
///
/// `#[unsafe_ensures(expr)]` specifies a safety postcondition that the unsafe
/// function guarantees on return.
///
/// # Example
///
/// ```ignore
/// #[unsafe_ensures(result != null)]
/// unsafe fn allocate() -> *mut u8 { /* ... */ }
/// ```
#[proc_macro_attribute]
pub fn unsafe_ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    spec_attribute("unsafe_ensures", attr, item)
}

/// Mark a function as manually verified (trusted).
///
/// Functions annotated with `#[trusted]` have their body verification skipped,
/// but call-site contracts are still checked. This establishes a trust boundary
/// for code that has been manually verified or is axiomatically correct.
///
/// Note: The actual annotation path in user code is `#[verifier::trusted]`, but
/// Rust proc macros cannot use `::` in attribute names, so the implementation
/// is named `#[trusted]` and documented as `verifier::trusted`.
///
/// # Example
///
/// ```ignore
/// #[trusted]
/// unsafe fn manually_verified_operation() -> i32 { /* ... */ }
/// ```
#[proc_macro_attribute]
pub fn trusted(attr: TokenStream, item: TokenStream) -> TokenStream {
    trusted_impl(attr.into(), item.into()).into()
}

/// Attach a lock invariant to a mutex or rwlock field.
///
/// `#[lock_invariant(expr)]` specifies a predicate that must hold whenever the
/// lock is acquired or released. The invariant is assumed on lock acquisition
/// and must be re-established before lock release.
///
/// # Example
///
/// ```ignore
/// struct Counter {
///     #[lock_invariant(value >= 0)]
///     data: Mutex<i32>,
/// }
/// ```
#[proc_macro_attribute]
pub fn lock_invariant(attr: TokenStream, item: TokenStream) -> TokenStream {
    spec_attribute("lock_invariant", attr, item)
}

/// Enable concurrency verification for a function with optional configuration.
///
/// `#[verify(concurrent)]` enables bounded model checking of concurrent code.
/// Optional parameters:
/// - `threads = N`: Maximum number of threads to verify (default: 3)
/// - `switches = M`: Maximum context switches to explore (default: 5)
///
/// # Examples
///
/// ```ignore
/// #[verify(concurrent)]
/// fn simple_concurrent() { /* ... */ }
///
/// #[verify(concurrent, threads = 4, switches = 10)]
/// fn heavy_concurrent() { /* ... */ }
/// ```
#[proc_macro_attribute]
pub fn verify(attr: TokenStream, item: TokenStream) -> TokenStream {
    verify_impl(attr.into(), item.into()).into()
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

/// `proc_macro2`-based implementation of `spec_attribute` for unit testing.
///
/// Parses the attribute as a Rust expression, converts it to a canonical
/// string, and prepends a hidden doc attribute encoding the spec.
#[cfg(test)]
fn spec_attribute_impl(
    kind: &str,
    attr: proc_macro2::TokenStream,
    item: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    let expr: syn::Expr = match syn::parse2(attr) {
        Ok(e) => e,
        Err(err) => return err.to_compile_error(),
    };

    let spec_string = expr.to_token_stream().to_string();
    let doc_value = format!("rust_fv::{kind}::{spec_string}");

    quote::quote! {
        #[doc(hidden)]
        #[doc = #doc_value]
        #item
    }
}

/// `proc_macro2`-based implementation of `pure` for unit testing.
fn pure_impl(
    attr: proc_macro2::TokenStream,
    item: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    if !attr.is_empty() {
        return syn::Error::new_spanned(attr, "`#[pure]` does not accept arguments")
            .to_compile_error();
    }

    let doc_value = "rust_fv::pure";

    quote::quote! {
        #[doc(hidden)]
        #[doc = #doc_value]
        #item
    }
}

/// Parser for borrow_ensures attribute syntax: (param, expr).
struct BorrowEnsuresArgs {
    param: syn::Expr,
    _comma: syn::Token![,],
    expr: syn::Expr,
}

impl syn::parse::Parse for BorrowEnsuresArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(BorrowEnsuresArgs {
            param: input.parse()?,
            _comma: input.parse()?,
            expr: input.parse()?,
        })
    }
}

/// `proc_macro2`-based implementation of `borrow_ensures` for unit testing.
///
/// Parses the attribute as (param_name, expression) and encodes as:
/// `rust_fv::borrow_ensures::PARAM::EXPR`
fn borrow_ensures_impl(
    attr: proc_macro2::TokenStream,
    item: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    // Parse attribute as (param, expr)
    let args: BorrowEnsuresArgs = match syn::parse2(attr) {
        Ok(a) => a,
        Err(err) => return err.to_compile_error(),
    };

    // Convert to strings
    let param_str = args.param.to_token_stream().to_string();
    let expr_str = args.expr.to_token_stream().to_string();

    let doc_value = format!("rust_fv::borrow_ensures::{}::{}", param_str, expr_str);

    quote::quote! {
        #[doc(hidden)]
        #[doc = #doc_value]
        #item
    }
}

/// `proc_macro2`-based implementation of `ghost` for unit testing.
fn ghost_impl(
    attr: proc_macro2::TokenStream,
    item: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    if !attr.is_empty() {
        return syn::Error::new_spanned(attr, "`#[ghost]` does not accept arguments")
            .to_compile_error();
    }

    let doc_value = "rust_fv::ghost";

    quote::quote! {
        #[doc(hidden)]
        #[doc = #doc_value]
        #item
    }
}

/// `proc_macro2`-based implementation of `trusted` for unit testing.
///
/// Marks a function as manually verified. Takes no arguments and embeds
/// the marker `rust_fv::trusted` as a doc attribute.
fn trusted_impl(
    attr: proc_macro2::TokenStream,
    item: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    if !attr.is_empty() {
        return syn::Error::new_spanned(attr, "`#[trusted]` does not accept arguments")
            .to_compile_error();
    }

    let doc_value = "rust_fv::trusted";

    quote::quote! {
        #[doc(hidden)]
        #[doc = #doc_value]
        #item
    }
}

/// Parse and encode `#[verify(concurrent, threads = N, switches = M)]` attributes.
fn verify_impl(
    attr: proc_macro2::TokenStream,
    item: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    use syn::{Expr, Meta, Token, parse::Parser, punctuated::Punctuated};

    // Parse as comma-separated meta items
    let parser = Punctuated::<Meta, Token![,]>::parse_terminated;
    let metas = match parser.parse2(attr) {
        Ok(m) => m,
        Err(err) => return err.to_compile_error(),
    };

    let mut doc_attrs = Vec::new();

    for meta in metas {
        match meta {
            Meta::Path(path) => {
                // #[verify(concurrent)]
                if path.is_ident("concurrent") {
                    doc_attrs.push("rust_fv::verify::concurrent".to_string());
                } else {
                    return syn::Error::new_spanned(path, "Unknown verify option")
                        .to_compile_error();
                }
            }
            Meta::NameValue(nv) => {
                // #[verify(threads = N)] or #[verify(switches = M)]
                if nv.path.is_ident("threads") {
                    if let Expr::Lit(lit) = &nv.value {
                        doc_attrs.push(format!(
                            "rust_fv::verify::threads::{}",
                            lit.lit.to_token_stream()
                        ));
                    } else {
                        return syn::Error::new_spanned(nv.value, "Expected integer literal")
                            .to_compile_error();
                    }
                } else if nv.path.is_ident("switches") {
                    if let Expr::Lit(lit) = &nv.value {
                        doc_attrs.push(format!(
                            "rust_fv::verify::switches::{}",
                            lit.lit.to_token_stream()
                        ));
                    } else {
                        return syn::Error::new_spanned(nv.value, "Expected integer literal")
                            .to_compile_error();
                    }
                } else {
                    return syn::Error::new_spanned(nv.path, "Unknown verify parameter")
                        .to_compile_error();
                }
            }
            _ => {
                return syn::Error::new_spanned(meta, "Unsupported syntax in verify attribute")
                    .to_compile_error();
            }
        }
    }

    // Generate doc attributes for each parsed option
    let doc_values = doc_attrs;
    quote::quote! {
        #(
            #[doc(hidden)]
            #[doc = #doc_values]
        )*
        #item
    }
}

// ---------------------------------------------------------------------------
// Unit tests — exercise the `proc_macro2`-based helpers directly
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;

    /// Helper: convert a `proc_macro2::TokenStream` to a normalised string
    /// for assertion comparisons.
    ///
    /// Note: `proc_macro2` serialises tokens with spaces between them,
    /// e.g. `#[doc(hidden)]` → `# [doc (hidden)]` and `self.len` →
    /// `self . len`.  Assertions must account for this.
    fn normalise(ts: proc_macro2::TokenStream) -> String {
        ts.to_string()
    }

    // --- spec_attribute_impl tests ---

    #[test]
    fn test_spec_attribute_requires_simple() {
        let attr: proc_macro2::TokenStream = quote! { x > 0 };
        let item: proc_macro2::TokenStream = quote! {
            fn positive_only(x: i32) -> i32 { x }
        };

        let result = spec_attribute_impl("requires", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("# [doc (hidden)]"));
        assert!(result_str.contains("rust_fv::requires::x > 0"));
        assert!(result_str.contains("fn positive_only"));
    }

    #[test]
    fn test_spec_attribute_ensures_with_result() {
        let attr: proc_macro2::TokenStream = quote! { result >= 0 };
        let item: proc_macro2::TokenStream = quote! {
            fn absolute(x: i32) -> i32 { x.abs() }
        };

        let result = spec_attribute_impl("ensures", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::ensures::result >= 0"));
        assert!(result_str.contains("fn absolute"));
    }

    #[test]
    fn test_spec_attribute_invariant_on_struct() {
        let attr: proc_macro2::TokenStream = quote! { self.len <= self.capacity };
        let item: proc_macro2::TokenStream = quote! {
            struct Buffer { len: usize, capacity: usize }
        };

        let result = spec_attribute_impl("invariant", attr, item);
        let result_str = normalise(result);

        // proc_macro2 serialises `self.len` as `self . len`
        assert!(result_str.contains("rust_fv::invariant::self . len <= self . capacity"));
        assert!(result_str.contains("struct Buffer"));
    }

    #[test]
    fn test_spec_attribute_complex_boolean_expression() {
        let attr: proc_macro2::TokenStream = quote! { a != 0 && b != 0 };
        let item: proc_macro2::TokenStream = quote! {
            fn divide(a: i32, b: i32) -> i32 { a / b }
        };

        let result = spec_attribute_impl("requires", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::requires::a != 0 && b != 0"));
    }

    #[test]
    fn test_spec_attribute_arithmetic_expression() {
        let attr: proc_macro2::TokenStream = quote! { result == a + b };
        let item: proc_macro2::TokenStream = quote! {
            fn add(a: i32, b: i32) -> i32 { a + b }
        };

        let result = spec_attribute_impl("ensures", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::ensures::result == a + b"));
    }

    #[test]
    fn test_spec_attribute_method_call_expression() {
        let attr: proc_macro2::TokenStream = quote! { items.len() > 0 };
        let item: proc_macro2::TokenStream = quote! {
            fn count_positive(items: &[i32]) -> usize { 0 }
        };

        let result = spec_attribute_impl("requires", attr, item);
        let result_str = normalise(result);

        // proc_macro2 serialises `items.len()` as `items . len ()`
        assert!(result_str.contains("rust_fv::requires::items . len () > 0"));
    }

    #[test]
    fn test_spec_attribute_invalid_expression_returns_compile_error() {
        // An empty attribute is not a valid Rust expression
        let attr: proc_macro2::TokenStream = proc_macro2::TokenStream::new();
        let item: proc_macro2::TokenStream = quote! {
            fn foo() {}
        };

        let result = spec_attribute_impl("requires", attr, item);
        let result_str = normalise(result);

        // syn::parse2 on empty input produces a compile_error
        assert!(result_str.contains("compile_error"));
    }

    #[test]
    fn test_spec_attribute_preserves_item_body() {
        let attr: proc_macro2::TokenStream = quote! { true };
        let item: proc_macro2::TokenStream = quote! {
            fn complex_body(x: i32) -> i32 {
                let y = x * 2;
                y + 1
            }
        };

        let result = spec_attribute_impl("requires", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("let y = x * 2"));
        assert!(result_str.contains("y + 1"));
    }

    #[test]
    fn test_spec_attribute_on_enum() {
        let attr: proc_macro2::TokenStream = quote! { true };
        let item: proc_macro2::TokenStream = quote! {
            enum Status { Active, Inactive }
        };

        let result = spec_attribute_impl("invariant", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::invariant::true"));
        assert!(result_str.contains("enum Status"));
    }

    // --- pure_impl tests ---

    #[test]
    fn test_pure_impl_empty_attr() {
        let attr = proc_macro2::TokenStream::new();
        let item: proc_macro2::TokenStream = quote! {
            fn square(x: i32) -> i32 { x * x }
        };

        let result = pure_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("# [doc (hidden)]"));
        assert!(result_str.contains("rust_fv::pure"));
        assert!(result_str.contains("fn square"));
    }

    #[test]
    fn test_pure_impl_with_args_returns_error() {
        let attr: proc_macro2::TokenStream = quote! { something };
        let item: proc_macro2::TokenStream = quote! {
            fn foo() -> i32 { 42 }
        };

        let result = pure_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("compile_error"));
        assert!(result_str.contains("does not accept arguments"));
    }

    #[test]
    fn test_pure_impl_preserves_function() {
        let attr = proc_macro2::TokenStream::new();
        let item: proc_macro2::TokenStream = quote! {
            fn constant() -> i32 { 42 }
        };

        let result = pure_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("fn constant"));
        assert!(result_str.contains("42"));
    }

    // --- ghost_impl tests ---

    #[test]
    fn test_ghost_impl_empty_attr() {
        let attr = proc_macro2::TokenStream::new();
        let item: proc_macro2::TokenStream = quote! {
            fn spec_helper(x: i32) -> i32 { x * 2 }
        };

        let result = ghost_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("# [doc (hidden)]"));
        assert!(result_str.contains("rust_fv::ghost"));
        assert!(result_str.contains("fn spec_helper"));
    }

    #[test]
    fn test_ghost_impl_with_args_returns_error() {
        let attr: proc_macro2::TokenStream = quote! { something };
        let item: proc_macro2::TokenStream = quote! {
            fn foo() -> i32 { 42 }
        };

        let result = ghost_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("compile_error"));
        assert!(result_str.contains("does not accept arguments"));
    }

    #[test]
    fn test_ghost_impl_preserves_function() {
        let attr = proc_macro2::TokenStream::new();
        let item: proc_macro2::TokenStream = quote! {
            fn ghost_fn(a: i32, b: i32) -> i32 { a + b }
        };

        let result = ghost_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("fn ghost_fn"));
        assert!(result_str.contains("a + b"));
    }

    // --- doc attribute format tests ---

    #[test]
    fn test_requires_doc_format() {
        let attr: proc_macro2::TokenStream = quote! { x > 0 };
        let item: proc_macro2::TokenStream = quote! { fn f(x: i32) {} };

        let result = spec_attribute_impl("requires", attr, item);
        let result_str = normalise(result);

        // The doc attribute should follow the format: rust_fv::kind::expression
        assert!(result_str.contains("rust_fv::requires::"));
    }

    #[test]
    fn test_ensures_doc_format() {
        let attr: proc_macro2::TokenStream = quote! { result > 0 };
        let item: proc_macro2::TokenStream = quote! { fn f() -> i32 { 1 } };

        let result = spec_attribute_impl("ensures", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::ensures::"));
    }

    #[test]
    fn test_invariant_doc_format() {
        let attr: proc_macro2::TokenStream = quote! { self.x > 0 };
        let item: proc_macro2::TokenStream = quote! { struct S { x: i32 } };

        let result = spec_attribute_impl("invariant", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::invariant::"));
    }

    #[test]
    fn test_pure_doc_value_exact() {
        let attr = proc_macro2::TokenStream::new();
        let item: proc_macro2::TokenStream = quote! { fn f() {} };

        let result = pure_impl(attr, item);
        let result_str = normalise(result);

        // Should contain the exact doc value string
        assert!(result_str.contains("rust_fv::pure"));
        // Should NOT contain spec separator (::) after "pure"
        // since pure has no expression
    }

    #[test]
    fn test_ghost_doc_value_exact() {
        let attr = proc_macro2::TokenStream::new();
        let item: proc_macro2::TokenStream = quote! { fn f() {} };

        let result = ghost_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::ghost"));
    }

    // --- Edge cases ---

    #[test]
    fn test_spec_attribute_with_closure_expression() {
        let attr: proc_macro2::TokenStream = quote! { items.iter().all(|x| *x > 0) };
        let item: proc_macro2::TokenStream = quote! {
            fn all_positive(items: &[i32]) -> bool { true }
        };

        let result = spec_attribute_impl("requires", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::requires::"));
        assert!(result_str.contains("fn all_positive"));
    }

    #[test]
    fn test_spec_attribute_with_nested_method_calls() {
        let attr: proc_macro2::TokenStream = quote! { s.chars().count() < 256 };
        let item: proc_macro2::TokenStream = quote! {
            fn short_string(s: &str) -> bool { true }
        };

        let result = spec_attribute_impl("requires", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::requires::"));
    }

    #[test]
    fn test_pure_impl_on_method_like_function() {
        let attr = proc_macro2::TokenStream::new();
        let item: proc_macro2::TokenStream = quote! {
            fn len(&self) -> usize { self.data.len() }
        };

        let result = pure_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::pure"));
        assert!(result_str.contains("fn len"));
    }

    #[test]
    fn test_ghost_impl_on_struct() {
        let attr = proc_macro2::TokenStream::new();
        let item: proc_macro2::TokenStream = quote! {
            struct GhostState { counter: usize }
        };

        let result = ghost_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::ghost"));
        assert!(result_str.contains("struct GhostState"));
    }

    // --- decreases tests (Phase 6) ---

    #[test]
    fn test_decreases_simple() {
        let attr: proc_macro2::TokenStream = quote! { n };
        let item: proc_macro2::TokenStream = quote! {
            fn factorial(n: u64) -> u64 { if n == 0 { 1 } else { n * factorial(n - 1) } }
        };

        let result = spec_attribute_impl("decreases", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::decreases::n"));
        assert!(result_str.contains("fn factorial"));
    }

    #[test]
    fn test_decreases_complex_expr() {
        let attr: proc_macro2::TokenStream = quote! { n - 1 };
        let item: proc_macro2::TokenStream = quote! {
            fn countdown(n: u64) -> u64 { n }
        };

        let result = spec_attribute_impl("decreases", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::decreases::n - 1"));
        assert!(result_str.contains("fn countdown"));
    }

    #[test]
    fn test_decreases_method_call_expr() {
        let attr: proc_macro2::TokenStream = quote! { tree.size() };
        let item: proc_macro2::TokenStream = quote! {
            fn traverse(tree: &Tree) -> usize { 0 }
        };

        let result = spec_attribute_impl("decreases", attr, item);
        let result_str = normalise(result);

        // proc_macro2 serialises `tree.size()` as `tree . size ()`
        assert!(result_str.contains("rust_fv::decreases::tree . size ()"));
        assert!(result_str.contains("fn traverse"));
    }

    #[test]
    fn test_decreases_preserves_function_body() {
        let attr: proc_macro2::TokenStream = quote! { n };
        let item: proc_macro2::TokenStream = quote! {
            fn factorial(n: u64) -> u64 {
                if n == 0 {
                    1
                } else {
                    n * factorial(n - 1)
                }
            }
        };

        let result = spec_attribute_impl("decreases", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("if n == 0"));
        assert!(result_str.contains("n * factorial (n - 1)"));
    }

    // --- borrow_ensures tests (Phase 9-02) ---

    #[test]
    fn test_borrow_ensures_macro() {
        let attr: proc_macro2::TokenStream = quote! { x, *x == old(*x) + 1 };
        let item: proc_macro2::TokenStream = quote! {
            fn increment(x: &mut i32) {
                *x += 1;
            }
        };

        let result = borrow_ensures_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("# [doc (hidden)]"));
        assert!(result_str.contains("rust_fv::borrow_ensures::"));
        assert!(result_str.contains("fn increment"));
    }

    #[test]
    fn test_borrow_ensures_doc_format() {
        let attr: proc_macro2::TokenStream = quote! { x, *x == old(*x) + 1 };
        let item: proc_macro2::TokenStream = quote! {
            fn f(x: &mut i32) {}
        };

        let result = borrow_ensures_impl(attr, item);
        let result_str = normalise(result);

        // Should encode as rust_fv::borrow_ensures::PARAM::EXPR
        assert!(result_str.contains("rust_fv::borrow_ensures::x::"));
        assert!(result_str.contains("* x == old (* x) + 1"));
    }

    // --- unsafe contract tests (Phase 10-01) ---

    #[test]
    fn test_unsafe_requires_embeds_annotation() {
        let attr: proc_macro2::TokenStream = quote! { x > 0 };
        let item: proc_macro2::TokenStream = quote! {
            unsafe fn positive_only(x: i32) -> i32 { x }
        };

        let result = spec_attribute_impl("unsafe_requires", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("# [doc (hidden)]"));
        assert!(result_str.contains("rust_fv::unsafe_requires::x > 0"));
        assert!(result_str.contains("unsafe fn positive_only"));
    }

    #[test]
    fn test_unsafe_ensures_embeds_annotation() {
        let attr: proc_macro2::TokenStream = quote! { result > 0 };
        let item: proc_macro2::TokenStream = quote! {
            unsafe fn allocate() -> *mut u8 { /* ... */ }
        };

        let result = spec_attribute_impl("unsafe_ensures", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("# [doc (hidden)]"));
        assert!(result_str.contains("rust_fv::unsafe_ensures::result > 0"));
        assert!(result_str.contains("unsafe fn allocate"));
    }

    #[test]
    fn test_trusted_embeds_annotation() {
        let attr: proc_macro2::TokenStream = quote! {};
        let item: proc_macro2::TokenStream = quote! {
            unsafe fn manually_verified() -> i32 { 42 }
        };

        let result = trusted_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("# [doc (hidden)]"));
        assert!(result_str.contains("rust_fv::trusted"));
        assert!(result_str.contains("unsafe fn manually_verified"));
    }

    #[test]
    fn test_unsafe_requires_complex_expr() {
        let attr: proc_macro2::TokenStream = quote! { ptr != null && len > 0 };
        let item: proc_macro2::TokenStream = quote! {
            unsafe fn deref_slice(ptr: *const u8, len: usize) {}
        };

        let result = spec_attribute_impl("unsafe_requires", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("ptr != null && len > 0"));
    }

    #[test]
    fn test_trusted_no_args() {
        let attr: proc_macro2::TokenStream = quote! {};
        let item: proc_macro2::TokenStream = quote! {
            fn f() {}
        };

        let result = trusted_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::trusted"));
        assert!(result_str.contains("fn f"));
    }

    #[test]
    fn test_unsafe_requires_on_unsafe_fn() {
        let attr: proc_macro2::TokenStream = quote! { x > 0 };
        let item: proc_macro2::TokenStream = quote! {
            unsafe fn test(x: i32) -> i32 {
                x * 2
            }
        };

        let result = spec_attribute_impl("unsafe_requires", attr, item);
        let result_str = normalise(result);

        // Verify both annotation and original function preserved
        assert!(result_str.contains("rust_fv::unsafe_requires::x > 0"));
        assert!(result_str.contains("unsafe fn test"));
        assert!(result_str.contains("x * 2"));
    }

    // --- concurrency annotation tests (Phase 12-01) ---

    #[test]
    fn test_lock_invariant_embeds_annotation() {
        let attr: proc_macro2::TokenStream = quote! { value >= 0 };
        let item: proc_macro2::TokenStream = quote! {
            data: Mutex<i32>
        };

        let result = spec_attribute_impl("lock_invariant", attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("# [doc (hidden)]"));
        assert!(result_str.contains("rust_fv::lock_invariant::value >= 0"));
        assert!(result_str.contains("data : Mutex < i32 >"));
    }

    #[test]
    fn test_verify_concurrent_embeds_annotation() {
        let attr: proc_macro2::TokenStream = quote! { concurrent };
        let item: proc_macro2::TokenStream = quote! {
            fn concurrent_fn() {}
        };

        let result = verify_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("# [doc (hidden)]"));
        assert!(result_str.contains("rust_fv::verify::concurrent"));
        assert!(result_str.contains("fn concurrent_fn"));
    }

    #[test]
    fn test_verify_threads_switches_embeds_annotations() {
        let attr: proc_macro2::TokenStream = quote! { concurrent, threads = 4, switches = 8 };
        let item: proc_macro2::TokenStream = quote! {
            fn heavy_concurrent() {}
        };

        let result = verify_impl(attr, item);
        let result_str = normalise(result);

        assert!(result_str.contains("rust_fv::verify::concurrent"));
        assert!(result_str.contains("rust_fv::verify::threads::4"));
        assert!(result_str.contains("rust_fv::verify::switches::8"));
        assert!(result_str.contains("fn heavy_concurrent"));
    }
}
