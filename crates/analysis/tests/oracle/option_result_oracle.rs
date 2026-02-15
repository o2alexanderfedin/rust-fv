//! Proptest oracle tests for Option<T> and Result<T, E> stdlib contracts.
//!
//! Validates that all Option/Result contract postconditions from
//! `crates/analysis/src/stdlib_contracts/option.rs` and `result.rs`
//! hold for real stdlib operations.
//!
//! NOTE: Many clippy lints are suppressed because these oracle tests
//! intentionally exercise operations on known Some/None/Ok/Err values
//! to validate contract postconditions.

use proptest::prelude::*;

// ---------------------------------------------------------------------------
// Option oracle tests
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Oracle for Option::map postconditions:
    /// - Some(x).map(f) => result.is_some()
    /// - None.map(f) => result.is_none()
    #[test]
    fn option_map_oracle(x in any::<i32>()) {
        let f = |v: i32| v.wrapping_mul(2).wrapping_add(1);

        // Some case
        let some_result = Some(x).map(f);
        prop_assert!(some_result.is_some());
        prop_assert_eq!(some_result.unwrap(), f(x));

        // None case
        let none_result: Option<i32> = None.map(f);
        prop_assert!(none_result.is_none());
    }

    /// Oracle for Option::and_then postconditions:
    /// - Some(x).and_then(f) == f(x)
    /// - None.and_then(f) == None
    #[test]
    fn option_and_then_oracle(x in any::<i32>()) {
        let f = |v: i32| if v > 0 { Some(v.wrapping_mul(2)) } else { None };

        // Some case
        let some_result = Some(x).and_then(f);
        prop_assert_eq!(some_result, f(x));

        // None case: and_then on None always returns None
        let none_result: Option<i32> = None.and_then(f);
        prop_assert!(none_result.is_none());
    }

    /// Oracle for Option::unwrap_or postconditions:
    /// - Some(x).unwrap_or(d) == x
    /// - None.unwrap_or(d) == d
    #[test]
    fn option_unwrap_or_oracle(x in any::<i32>(), default in any::<i32>()) {
        // Some case
        let some_result = Some(x).unwrap_or(default);
        prop_assert_eq!(some_result, x);

        // None case
        let none_result: i32 = None.unwrap_or(default);
        prop_assert_eq!(none_result, default);
    }

    /// Oracle for Option::ok_or postconditions:
    /// - Some(x).ok_or(e) == Ok(x)
    /// - None.ok_or(e) == Err(e)
    #[test]
    fn option_ok_or_oracle(x in any::<i32>(), err in any::<String>()) {
        // Some case
        let some_result: Result<i32, String> = Some(x).ok_or(err.clone());
        prop_assert!(some_result.is_ok());
        prop_assert_eq!(some_result.unwrap(), x);

        // None case
        let none_result: Result<i32, String> = None.ok_or(err.clone());
        prop_assert!(none_result.is_err());
        prop_assert_eq!(none_result.unwrap_err(), err);
    }

    /// Oracle for Option::is_some / is_none postconditions:
    /// - is_some == !is_none
    #[test]
    fn option_is_some_is_none_oracle(x in any::<i32>()) {
        let some: Option<i32> = Some(x);
        let none: Option<i32> = None;

        prop_assert_eq!(some.is_some(), !some.is_none());
        prop_assert_eq!(none.is_some(), !none.is_none());
        prop_assert!(some.is_some());
        prop_assert!(none.is_none());
    }

    /// Oracle for Option::unwrap_or_else postcondition:
    /// - Some(x).unwrap_or_else(f) == x
    #[test]
    fn option_unwrap_or_else_oracle(x in any::<i32>(), default in any::<i32>()) {
        let some_result = Some(x).unwrap_or_else(|| default);
        prop_assert_eq!(some_result, x);

        let none_result: i32 = None.unwrap_or_else(|| default);
        prop_assert_eq!(none_result, default);
    }
}

// ---------------------------------------------------------------------------
// Result oracle tests
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Oracle for Result::map postconditions:
    /// - Ok(x).map(f) => result.is_ok()
    /// - Err(e).map(f) => result.is_err()
    #[test]
    fn result_map_oracle(x in any::<i32>(), err in any::<String>()) {
        let f = |v: i32| v.wrapping_mul(2).wrapping_add(1);

        // Ok case
        let ok_result: Result<i32, String> = Ok(x).map(f);
        prop_assert!(ok_result.is_ok());
        prop_assert_eq!(ok_result.unwrap(), f(x));

        // Err case
        let err_result: Result<i32, String> = Err(err.clone()).map(f);
        prop_assert!(err_result.is_err());
        prop_assert_eq!(err_result.unwrap_err(), err);
    }

    /// Oracle for Result::and_then postconditions:
    /// - Ok(x).and_then(f) == f(x)
    /// - Err(e).and_then(f) => result.is_err()
    #[test]
    fn result_and_then_oracle(x in any::<i32>(), err in any::<String>()) {
        let f = |v: i32| -> Result<i32, String> {
            if v > 0 { Ok(v.wrapping_mul(2)) } else { Err("negative".to_string()) }
        };

        // Ok case
        let ok_result: Result<i32, String> = Ok(x).and_then(f);
        prop_assert_eq!(ok_result, f(x));

        // Err case: and_then on Err always returns Err
        let err_result: Result<i32, String> = Err(err.clone()).and_then(f);
        prop_assert!(err_result.is_err());
        prop_assert_eq!(err_result.unwrap_err(), err);
    }

    /// Oracle for Result::ok postconditions:
    /// - Ok(x).ok() == Some(x)
    /// - Err(e).ok() == None
    #[test]
    fn result_ok_oracle(x in any::<i32>(), err in any::<String>()) {
        let ok_result: Option<i32> = Ok::<i32, String>(x).ok();
        prop_assert_eq!(ok_result, Some(x));

        let err_result: Option<i32> = Err::<i32, String>(err).ok();
        prop_assert_eq!(err_result, None);
    }

    /// Oracle for Result::is_ok / is_err postconditions:
    /// - is_ok == !is_err
    #[test]
    fn result_is_ok_is_err_oracle(x in any::<i32>(), err in any::<String>()) {
        let ok: Result<i32, String> = Ok(x);
        let err_val: Result<i32, String> = Err(err);

        prop_assert_eq!(ok.is_ok(), !ok.is_err());
        prop_assert_eq!(err_val.is_ok(), !err_val.is_err());
        prop_assert!(ok.is_ok());
        prop_assert!(err_val.is_err());
    }

    /// Oracle for Result::map_err postconditions:
    /// - Ok(x).map_err(f) => result.is_ok()
    /// - Err(e).map_err(f) => result.is_err()
    #[test]
    fn result_map_err_oracle(x in any::<i32>(), err in any::<String>()) {
        let ok_result: Result<i32, String> = Ok::<i32, String>(x).map_err(|e: String| format!("mapped: {}", e));
        prop_assert!(ok_result.is_ok());

        let err_result: Result<i32, String> = Err::<i32, String>(err.clone()).map_err(|e: String| format!("mapped: {}", e));
        prop_assert!(err_result.is_err());
        prop_assert_eq!(err_result.unwrap_err(), format!("mapped: {}", err));
    }

    /// Oracle for Result::err postconditions:
    /// - Ok(x).err() == None
    /// - Err(e).err() == Some(e)
    #[test]
    fn result_err_oracle(x in any::<i32>(), err in any::<String>()) {
        let ok_result: Option<String> = Ok::<i32, String>(x).err();
        prop_assert_eq!(ok_result, None);

        let err_result: Option<String> = Err::<i32, String>(err.clone()).err();
        prop_assert_eq!(err_result, Some(err));
    }
}
