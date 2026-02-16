//! Integration tests for the complete trigger customization pipeline.
//!
//! Tests the full flow: annotation → parse → validate → SMT-LIB or error
//! Proves all 5 phase success criteria are met.

use rust_fv_analysis::encode_quantifier::annotate_quantifier;
use rust_fv_analysis::trigger_validation::{
    TriggerValidationError, TriggerValidator, format_trigger_sets,
};
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

// ==============================================================================
// Success Criterion 1: Developer can annotate with #[trigger(expr)]
// ==============================================================================

#[test]
fn test_manual_trigger_single_annotation() {
    // Quantifier: forall x. #[trigger(f(x))] f(x) > 0
    // Manual trigger should override auto-inference
    let body = Term::Annotated(
        Box::new(Term::BvSGt(
            Box::new(Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )),
            Box::new(Term::IntLit(0)),
        )),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )],
        )],
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(forall_term).expect("Should succeed");

    // Verify result is still a Forall
    if let Term::Forall(_vars, annotated_body) = result {
        // Verify body has :pattern annotation (not rust_fv_trigger_hint)
        if let Term::Annotated(_, annotations) = &*annotated_body {
            assert_eq!(annotations.len(), 1);
            assert_eq!(annotations[0].0, "pattern");
            assert_eq!(annotations[0].1.len(), 1);
            // Verify the pattern is f(x)
            if let Term::App(name, _) = &annotations[0].1[0] {
                assert_eq!(name, "f");
            } else {
                panic!("Expected App trigger");
            }
        } else {
            panic!("Expected Annotated body");
        }
    } else {
        panic!("Expected Forall term");
    }
}

#[test]
fn test_manual_trigger_multi_trigger_set() {
    // Quantifier: forall x y. #[trigger(f(x), g(y))] ...
    // Multi-pattern trigger set
    let body = Term::Annotated(
        Box::new(Term::BoolLit(true)),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![
                Term::App("f".to_string(), vec![Term::Const("x".to_string())]),
                Term::App("g".to_string(), vec![Term::Const("y".to_string())]),
            ],
        )],
    );

    let forall_term = Term::Forall(
        vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        Box::new(body),
    );

    let result = annotate_quantifier(forall_term).expect("Should succeed");

    if let Term::Forall(_vars, annotated_body) = result {
        if let Term::Annotated(_, annotations) = &*annotated_body {
            assert_eq!(annotations.len(), 1);
            assert_eq!(annotations[0].0, "pattern");
            assert_eq!(annotations[0].1.len(), 2); // Two triggers in the set
        } else {
            panic!("Expected Annotated body");
        }
    } else {
        panic!("Expected Forall term");
    }
}

#[test]
fn test_manual_trigger_multiple_sets() {
    // Quantifier with two separate trigger sets
    let body = Term::Annotated(
        Box::new(Term::BoolLit(true)),
        vec![
            (
                "rust_fv_trigger_hint".to_string(),
                vec![Term::App(
                    "f".to_string(),
                    vec![Term::Const("x".to_string())],
                )],
            ),
            (
                "rust_fv_trigger_hint".to_string(),
                vec![Term::App(
                    "g".to_string(),
                    vec![Term::Const("x".to_string())],
                )],
            ),
        ],
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(forall_term).expect("Should succeed");

    if let Term::Forall(_vars, annotated_body) = result {
        if let Term::Annotated(_, annotations) = &*annotated_body {
            // Should have all triggers flattened into a single :pattern annotation
            assert_eq!(annotations.len(), 1);
            assert_eq!(annotations[0].0, "pattern");
            assert_eq!(annotations[0].1.len(), 2); // Two trigger sets flattened
        } else {
            panic!("Expected Annotated body");
        }
    } else {
        panic!("Expected Forall term");
    }
}

// ==============================================================================
// Success Criterion 2: Tool warns/errors on bad triggers
// ==============================================================================

#[test]
fn test_error_interpreted_symbol_arithmetic() {
    // forall x. #[trigger(x + 1)] ...
    // Arithmetic operations are interpreted symbols
    let body = Term::Annotated(
        Box::new(Term::BoolLit(true)),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![Term::BvAdd(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::IntLit(1)),
            )],
        )],
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(forall_term);

    assert!(result.is_err());
    if let Err(TriggerValidationError::InterpretedSymbol { symbol, .. }) = result {
        assert_eq!(symbol, "+");
    } else {
        panic!("Expected InterpretedSymbol error");
    }
}

#[test]
fn test_error_interpreted_symbol_equality() {
    // forall x. #[trigger(x == 0)] ...
    // Equality is an interpreted symbol
    let body = Term::Annotated(
        Box::new(Term::BoolLit(true)),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![Term::Eq(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::IntLit(0)),
            )],
        )],
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(forall_term);

    assert!(result.is_err());
    if let Err(TriggerValidationError::InterpretedSymbol { symbol, .. }) = result {
        assert_eq!(symbol, "==");
    } else {
        panic!("Expected InterpretedSymbol error");
    }
}

#[test]
fn test_error_no_trigger_inferred_warning() {
    // Quantifier where auto-inference finds nothing
    // Body: x > 0 (no function application)
    let body = Term::BvSGt(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::IntLit(0)),
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    // This should succeed but log a warning (tracing::warn)
    // We can't test warnings directly, but we can verify it doesn't error
    let result = annotate_quantifier(forall_term);
    assert!(result.is_ok());
}

// ==============================================================================
// Success Criterion 3: Self-instantiation detection
// ==============================================================================

#[test]
fn test_error_self_instantiation_detected() {
    // Trigger: f(f(x)) - self-instantiates
    let body = Term::Annotated(
        Box::new(Term::BoolLit(true)),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![Term::App(
                "f".to_string(),
                vec![Term::App(
                    "f".to_string(),
                    vec![Term::Const("x".to_string())],
                )],
            )],
        )],
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(forall_term);

    assert!(result.is_err());
    if let Err(TriggerValidationError::SelfInstantiation { loop_example, .. }) = result {
        assert!(loop_example.contains("->"));
        assert!(loop_example.contains("..."));
    } else {
        panic!("Expected SelfInstantiation error");
    }
}

#[test]
fn test_safe_trigger_not_flagged() {
    // Trigger: f(g(x)) - nested but doesn't loop
    let body = Term::Annotated(
        Box::new(Term::BoolLit(true)),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![Term::App(
                "f".to_string(),
                vec![Term::App(
                    "g".to_string(),
                    vec![Term::Const("x".to_string())],
                )],
            )],
        )],
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(forall_term);
    assert!(result.is_ok());
}

// ==============================================================================
// Success Criterion 4: Manual triggers override auto-inference
// ==============================================================================

#[test]
fn test_manual_overrides_auto() {
    // Body has both f(x) and g(x), auto-inference would pick f(x)
    // But we manually specify g(x) as the trigger
    let body = Term::Annotated(
        Box::new(Term::And(vec![
            Term::App("f".to_string(), vec![Term::Const("x".to_string())]),
            Term::App("g".to_string(), vec![Term::Const("x".to_string())]),
        ])),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![Term::App(
                "g".to_string(),
                vec![Term::Const("x".to_string())],
            )],
        )],
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(forall_term).expect("Should succeed");

    if let Term::Forall(_vars, annotated_body) = result {
        if let Term::Annotated(_, annotations) = &*annotated_body {
            assert_eq!(annotations[0].0, "pattern");
            // Verify it's g(x), not f(x)
            if let Term::App(name, _) = &annotations[0].1[0] {
                assert_eq!(name, "g");
            } else {
                panic!("Expected App trigger");
            }
        } else {
            panic!("Expected Annotated body");
        }
    } else {
        panic!("Expected Forall term");
    }
}

#[test]
fn test_no_annotation_uses_auto() {
    // Standard quantifier without #[trigger] annotation
    // Should use auto-inference (backward compat)
    let body = Term::BvSGt(
        Box::new(Term::App(
            "f".to_string(),
            vec![Term::Const("x".to_string())],
        )),
        Box::new(Term::IntLit(0)),
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(forall_term).expect("Should succeed");

    if let Term::Forall(_vars, annotated_body) = result {
        if let Term::Annotated(_, annotations) = &*annotated_body {
            assert_eq!(annotations[0].0, "pattern");
            // Should have auto-inferred f(x)
            if let Term::App(name, _) = &annotations[0].1[0] {
                assert_eq!(name, "f");
            } else {
                panic!("Expected App trigger");
            }
        } else {
            panic!("Expected Annotated body");
        }
    } else {
        panic!("Expected Forall term");
    }
}

#[test]
fn test_validation_failure_blocks_verification() {
    // Bad trigger annotation (interpreted symbol)
    let body = Term::Annotated(
        Box::new(Term::BoolLit(true)),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![Term::Eq(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::IntLit(0)),
            )],
        )],
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(forall_term);

    // Should return error, not success
    assert!(result.is_err());
}

// ==============================================================================
// Success Criterion 5: Error messages provide good trigger examples
// ==============================================================================

#[test]
fn test_error_suggests_auto_inferred() {
    // Use interpreted symbol trigger on quantifier where auto-inference works
    // Body: f(x) > 0, trigger: x + 1 (bad)
    let body_term = Term::BvSGt(
        Box::new(Term::App(
            "f".to_string(),
            vec![Term::Const("x".to_string())],
        )),
        Box::new(Term::IntLit(0)),
    );

    let body = Term::Annotated(
        Box::new(body_term),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![Term::BvAdd(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::IntLit(1)),
            )],
        )],
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(forall_term);

    if let Err(TriggerValidationError::InterpretedSymbol { auto_inferred, .. }) = result {
        // Should suggest f(x) as an auto-inferred trigger
        assert!(!auto_inferred.is_empty());
        if let Term::App(name, _) = &auto_inferred[0][0] {
            assert_eq!(name, "f");
        }
    } else {
        panic!("Expected InterpretedSymbol error with suggestion");
    }
}

#[test]
fn test_error_incomplete_coverage_suggests_multi() {
    // Trigger with missing variables
    // Bound vars: x, y; trigger: f(x) only
    let body = Term::Annotated(
        Box::new(Term::BoolLit(true)),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )],
        )],
    );

    let forall_term = Term::Forall(
        vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        Box::new(body),
    );

    let result = annotate_quantifier(forall_term);

    if let Err(TriggerValidationError::IncompleteCoverage { missing_vars, .. }) = result {
        assert!(missing_vars.contains(&"y".to_string()));
    } else {
        panic!("Expected IncompleteCoverage error");
    }
}

#[test]
fn test_error_too_many_triggers_suggests_simplification() {
    // 11 trigger sets (exceeds limit of 10)
    let mut trigger_sets = Vec::new();
    for i in 0..11 {
        trigger_sets.push((
            "rust_fv_trigger_hint".to_string(),
            vec![Term::App(
                format!("f{}", i),
                vec![Term::Const("x".to_string())],
            )],
        ));
    }

    let body = Term::Annotated(Box::new(Term::BoolLit(true)), trigger_sets);

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(forall_term);

    if let Err(TriggerValidationError::TooManyTriggers { count, limit }) = result {
        assert_eq!(count, 11);
        assert_eq!(limit, 10);
    } else {
        panic!("Expected TooManyTriggers error");
    }
}

// ==============================================================================
// Additional integration tests
// ==============================================================================

#[test]
fn test_trigger_validation_direct() {
    // Test TriggerValidator directly
    let validator = TriggerValidator::default();

    // Valid trigger
    let trigger_sets = vec![vec![Term::App(
        "f".to_string(),
        vec![Term::Const("x".to_string())],
    )]];
    let bound_vars = vec![("x".to_string(), Sort::Int)];
    let body = Term::BoolLit(true);

    let result = validator.validate(&trigger_sets, &bound_vars, &body);
    assert!(result.is_ok());
}

#[test]
fn test_format_trigger_sets_output() {
    // Test formatting function
    let sets = vec![
        vec![Term::App(
            "f".to_string(),
            vec![Term::Const("x".to_string())],
        )],
        vec![Term::App(
            "g".to_string(),
            vec![Term::Const("y".to_string())],
        )],
    ];

    let formatted = format_trigger_sets(&sets);
    assert!(formatted.contains("f"));
    assert!(formatted.contains("g"));
    assert!(formatted.contains(";"));
}

#[test]
fn test_exists_quantifier_with_manual_trigger() {
    // Test that exists quantifiers also support manual triggers
    let body = Term::Annotated(
        Box::new(Term::BoolLit(true)),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )],
        )],
    );

    let exists_term = Term::Exists(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(exists_term).expect("Should succeed");

    if let Term::Exists(_vars, annotated_body) = result {
        if let Term::Annotated(_, annotations) = &*annotated_body {
            assert_eq!(annotations.len(), 1);
            assert_eq!(annotations[0].0, "pattern");
        } else {
            panic!("Expected Annotated body");
        }
    } else {
        panic!("Expected Exists term");
    }
}
