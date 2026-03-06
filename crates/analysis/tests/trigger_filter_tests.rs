//! Tests for datatype symbol filtering in trigger inference (COMPL-08).
//!
//! Ensures that SMT datatype selectors, constructors, and testers are not
//! proposed as trigger candidates, which would cause unsound quantifier
//! instantiation loops.

use rust_fv_analysis::encode_quantifier::{infer_triggers, is_datatype_symbol};
use rust_fv_smtlib::term::Term;

// --- is_datatype_symbol unit tests ---

#[test]
fn test_selector_pattern_filtered() {
    // Test 1: Term::App("Struct-field0", [x]) is filtered out (selector pattern)
    assert!(
        is_datatype_symbol("Struct-field0"),
        "Selector 'Struct-field0' must be recognized as a datatype symbol"
    );
    assert!(
        is_datatype_symbol("Point-x"),
        "Selector 'Point-x' must be recognized as a datatype symbol"
    );
    assert!(
        is_datatype_symbol("Option-val"),
        "Selector 'Option-val' must be recognized as a datatype symbol"
    );
}

#[test]
fn test_constructor_pattern_filtered() {
    // Test 2: Term::App("mk-Point", [x, y]) is filtered out (constructor pattern)
    assert!(
        is_datatype_symbol("mk-Point"),
        "Constructor 'mk-Point' must be recognized as a datatype symbol"
    );
    assert!(
        is_datatype_symbol("mk-Some"),
        "Constructor 'mk-Some' must be recognized as a datatype symbol"
    );
}

#[test]
fn test_tester_pattern_filtered() {
    // Test 3: Term::App("is-Some", [x]) is filtered out (tester pattern)
    assert!(
        is_datatype_symbol("is-Some"),
        "Tester 'is-Some' must be recognized as a datatype symbol"
    );
    assert!(
        is_datatype_symbol("is-None"),
        "Tester 'is-None' must be recognized as a datatype symbol"
    );
}

#[test]
fn test_user_function_not_filtered() {
    // Test 4: Term::App("user_fn", [x]) is NOT filtered out
    assert!(
        !is_datatype_symbol("user_fn"),
        "User function 'user_fn' must NOT be recognized as a datatype symbol"
    );
}

#[test]
fn test_spec_function_not_filtered() {
    // Test 5: Term::App("spec_len", [x]) is NOT filtered out
    assert!(
        !is_datatype_symbol("spec_len"),
        "Spec function 'spec_len' must NOT be recognized as a datatype symbol"
    );
    assert!(
        !is_datatype_symbol("seq_len"),
        "Spec function 'seq_len' must NOT be recognized as a datatype symbol"
    );
}

#[test]
fn test_all_candidates_filtered_generates_synthetic_wrapper() {
    // Test 6: When all candidates are datatype symbols, a synthetic wrapper
    // trigger "__trigger_wrap" is generated instead of returning empty.
    //
    // Build a forall body that only contains datatype symbol applications:
    //   Struct-field0(x) = y
    let body = Term::Eq(
        Box::new(Term::App(
            "Struct-field0".to_string(),
            vec![Term::Const("x".to_string())],
        )),
        Box::new(Term::Const("y".to_string())),
    );
    let bound_vars = vec!["x".to_string(), "y".to_string()];

    let triggers = infer_triggers(&body, &bound_vars);

    // Should not be empty — should have a synthetic trigger
    assert!(
        !triggers.is_empty(),
        "Triggers must not be empty when all candidates are datatype symbols"
    );

    // The synthetic trigger should use __trigger_wrap
    let first_group = &triggers[0];
    assert_eq!(
        first_group.len(),
        1,
        "Synthetic trigger group must have exactly one term"
    );
    match &first_group[0] {
        Term::App(name, _) => {
            assert_eq!(
                name, "__trigger_wrap",
                "Synthetic trigger must use __trigger_wrap"
            );
        }
        other => panic!("Synthetic trigger must be a Term::App, got: {:?}", other),
    }
}

#[test]
fn test_infer_triggers_with_only_datatype_selectors_returns_synthetic() {
    // Test 7: infer_triggers on a forall with only datatype selectors returns
    // a synthetic trigger group, not empty.
    //
    // Body: is-Some(x) && mk-Point(x, y) = z
    let body = Term::And(vec![
        Term::App("is-Some".to_string(), vec![Term::Const("x".to_string())]),
        Term::Eq(
            Box::new(Term::App(
                "mk-Point".to_string(),
                vec![Term::Const("x".to_string()), Term::Const("y".to_string())],
            )),
            Box::new(Term::Const("z".to_string())),
        ),
    ]);
    let bound_vars = vec!["x".to_string(), "y".to_string(), "z".to_string()];

    let triggers = infer_triggers(&body, &bound_vars);

    // Must not be empty
    assert!(
        !triggers.is_empty(),
        "Triggers must not be empty for body with only datatype symbols"
    );

    // Check that it's a synthetic wrapper
    let first_group = &triggers[0];
    match &first_group[0] {
        Term::App(name, _) => {
            assert_eq!(
                name, "__trigger_wrap",
                "Must generate __trigger_wrap when all candidates are datatype symbols"
            );
        }
        other => panic!("Expected Term::App, got: {:?}", other),
    }
}
