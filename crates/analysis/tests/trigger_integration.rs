//! Integration tests for the complete trigger customization pipeline.
//!
//! Tests the full flow: annotation → parse → validate → SMT-LIB or error
//! Proves all 5 phase success criteria are met.

use rust_fv_analysis::encode_quantifier::annotate_quantifier;
use rust_fv_analysis::ir::{Contracts, Function, IntTy, Local, Ty};
use rust_fv_analysis::spec_parser::parse_spec_expr;
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

// ==============================================================================
// Phase 33 Edge Case Tests (9 new) — Trigger/Quantifier Schema Edge Cases
// ==============================================================================

/// Build a minimal Function for spec_parser E2E tests.
fn make_i64_func_for_trigger_test() -> Function {
    Function {
        name: "test_trigger_e2e".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Bool,
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I64),
            is_ghost: false,
        }],
        locals: vec![],
        basic_blocks: vec![],
        contracts: Contracts::default(),
        loops: vec![],
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        unsafe_blocks: vec![],
        unsafe_operations: vec![],
        unsafe_contracts: None,
        is_unsafe_fn: false,
        thread_spawns: vec![],
        atomic_ops: vec![],
        sync_ops: vec![],
        lock_invariants: vec![],
        concurrency_config: None,
        source_names: std::collections::HashMap::new(),
        coroutine_info: None,
    }
}

#[test]
fn test_nested_quantifier_triggers() {
    // forall x, forall y, trigger(f(x, y)) — cross-scope trigger binding both x and y.
    // The inner Forall binds y; trigger f(x, y) contains y (inner bound var).
    // x is free in the inner quantifier (outer scope). Coverage check on inner sees y covered.
    // Expected: Ok — f(x, y) covers the inner bound var y.
    let inner_body = Term::Annotated(
        Box::new(Term::BoolLit(true)),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string()), Term::Const("y".to_string())],
            )],
        )],
    );

    // Inner: forall y. #[trigger(f(x, y))] true
    let inner_forall = Term::Forall(vec![("y".to_string(), Sort::Int)], Box::new(inner_body));

    // Outer: forall x. (inner_forall) — outer has no manual trigger, uses auto-inference
    let outer_forall = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(inner_forall));

    let result = annotate_quantifier(outer_forall);
    assert!(
        result.is_ok(),
        "Nested quantifier should succeed: {:?}",
        result
    );
}

#[test]
fn test_trigger_with_struct_selector() {
    // Trigger is a struct field selector: Term::App("Point-x", [x])
    // Selector is modeled as an uninterpreted function application.
    // Expected: validates successfully — uninterpreted outermost symbol is valid.
    let body = Term::Annotated(
        Box::new(Term::BoolLit(true)),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![Term::App(
                "Point-x".to_string(),
                vec![Term::Const("x".to_string())],
            )],
        )],
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(forall_term);
    assert!(
        result.is_ok(),
        "Struct selector trigger should succeed: {:?}",
        result
    );
}

#[test]
fn test_trigger_in_exists_with_shadowed_var() {
    // Exists quantifier where bound var "x" would shadow an outer scope "x".
    // The inner exists only knows its own bound "x"; scopes are independent.
    // Expected: Ok — trigger f(x) covers the inner bound var x.
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

    let result = annotate_quantifier(exists_term);
    assert!(
        result.is_ok(),
        "Shadowed var in exists trigger should succeed: {:?}",
        result
    );

    if let Ok(Term::Exists(_vars, annotated_body)) = result {
        if let Term::Annotated(_, annotations) = &*annotated_body {
            assert_eq!(annotations[0].0, "pattern");
            if let Term::App(name, _) = &annotations[0].1[0] {
                assert_eq!(name, "f", "Expected f trigger");
            } else {
                panic!("Expected App trigger");
            }
        } else {
            panic!("Expected Annotated body");
        }
    }
}

#[test]
fn test_overlapping_multiple_triggers() {
    // Two trigger sets where both contain x: [f(x)] and [g(x)].
    // Non-conflicting: each set independently covers x.
    // Expected: Ok — multiple trigger sets with same variable are valid.
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

    let result = annotate_quantifier(forall_term);
    assert!(
        result.is_ok(),
        "Overlapping multiple triggers should succeed: {:?}",
        result
    );
}

#[test]
fn test_trigger_on_arithmetic_result_as_arg() {
    // Trigger: h(x + 0) — h is uninterpreted outermost, but argument contains arithmetic.
    // The validator performs recursive checking inside trigger arguments.
    // BvAdd is an interpreted symbol, even when nested inside an uninterpreted function's arg.
    // Expected: Err(InterpretedSymbol) — the validator rejects arithmetic inside trigger args.
    let trigger = Term::App(
        "h".to_string(),
        vec![Term::BvAdd(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::IntLit(0)),
        )],
    );

    let body = Term::Annotated(
        Box::new(Term::BoolLit(true)),
        vec![("rust_fv_trigger_hint".to_string(), vec![trigger])],
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(body));

    let result = annotate_quantifier(forall_term);
    // The validator finds "+" inside the trigger arg and rejects it
    assert!(
        matches!(
            result,
            Err(TriggerValidationError::InterpretedSymbol { .. })
        ),
        "Trigger h(x+0) should fail due to interpreted '+' in arg: {:?}",
        result
    );
}

#[test]
fn test_trigger_outer_scope_variable() {
    // Inner forall binds only y, but trigger f(x) references only outer-scope variable x.
    // The validator sees bound_vars=[y] and checks coverage: trigger f(x) doesn't cover y.
    // Expected: Err(IncompleteCoverage) — y is missing from the trigger.
    let inner_body = Term::Annotated(
        Box::new(Term::BoolLit(true)),
        vec![(
            "rust_fv_trigger_hint".to_string(),
            vec![Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )],
        )],
    );

    // Inner forall binds y, trigger only covers x (outer scope)
    let inner_forall = Term::Forall(vec![("y".to_string(), Sort::Int)], Box::new(inner_body));

    let result = annotate_quantifier(inner_forall);
    assert!(
        matches!(
            result,
            Err(TriggerValidationError::IncompleteCoverage { .. })
        ),
        "Trigger missing inner bound var y should give IncompleteCoverage, got: {:?}",
        result
    );

    if let Err(TriggerValidationError::IncompleteCoverage { missing_vars, .. }) = result {
        assert!(
            missing_vars.contains(&"y".to_string()),
            "Should report y as missing, got: {:?}",
            missing_vars
        );
    }
}

#[test]
fn test_trigger_on_recursive_function_application() {
    // Trigger: f(g(x)) — f is outermost, g is a nested application.
    // f does NOT appear in its own arguments → no self-instantiation.
    // Expected: Ok — two-level application f(g(x)) is a valid trigger.
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
    assert!(
        result.is_ok(),
        "f(g(x)) two-level trigger should succeed: {:?}",
        result
    );
}

#[test]
fn test_missing_variable_in_multi_trigger_set() {
    // Quantifier binds both x and y. Trigger set [f(x)] only covers x, not y.
    // Expected: Err(IncompleteCoverage) with missing_vars containing y.
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
    assert!(
        matches!(
            result,
            Err(TriggerValidationError::IncompleteCoverage { .. })
        ),
        "Single trigger missing y should give IncompleteCoverage, got: {:?}",
        result
    );

    if let Err(TriggerValidationError::IncompleteCoverage { missing_vars, .. }) = result {
        assert!(
            missing_vars.contains(&"y".to_string()),
            "y should be reported as missing var, got: {:?}",
            missing_vars
        );
    }
}

#[test]
fn test_e2e_trigger_through_spec_parser() {
    // E2E test: Parse a spec string with trigger annotation through the full parse pipeline.
    // Closes the "No E2E test with actual Rust code" gap from Phase 15 VERIFICATION.md.
    //
    // Spec: forall(|x: i64| { #[trigger(is_prime(x))] x > 0 })
    // The trigger is the uninterpreted function is_prime(x); the body is a simple comparison.
    // Expected: parses to Term::Forall with body Term::Annotated containing
    // a rust_fv_trigger_hint annotation with is_prime(x) — triggers survive the parser.
    let func = make_i64_func_for_trigger_test();

    let spec = "forall(|x: i64| { #[trigger(is_prime(x))] x > 0 })";
    let result = parse_spec_expr(spec, &func);

    assert!(
        result.is_some(),
        "E2E spec with trigger annotation should parse successfully"
    );

    let term = result.unwrap();
    match &term {
        Term::Forall(vars, body) => {
            assert_eq!(vars.len(), 1, "Should have one bound variable");
            assert_eq!(vars[0].0, "x", "Bound var should be x");
            assert_eq!(
                vars[0].1,
                Sort::BitVec(64),
                "x should have BitVec(64) sort for i64"
            );

            // Body should carry the trigger hint annotation from the parser
            match body.as_ref() {
                Term::Annotated(_, annotations) => {
                    assert!(
                        !annotations.is_empty(),
                        "Body should carry trigger hint annotations"
                    );
                    let trigger_annot = annotations
                        .iter()
                        .find(|(key, _)| key == "rust_fv_trigger_hint");
                    assert!(
                        trigger_annot.is_some(),
                        "Should have rust_fv_trigger_hint annotation, got: {:?}",
                        annotations
                    );
                    let (_, trigger_terms) = trigger_annot.unwrap();
                    assert_eq!(trigger_terms.len(), 1, "Should have one trigger term");
                    if let Term::App(name, args) = &trigger_terms[0] {
                        assert_eq!(name, "is_prime", "Trigger should be is_prime");
                        assert_eq!(args.len(), 1, "is_prime takes one arg");
                        assert!(
                            matches!(&args[0], Term::Const(v) if v == "x"),
                            "Trigger arg should be x, got: {:?}",
                            args[0]
                        );
                    } else {
                        panic!(
                            "Expected App trigger for is_prime(x), got: {:?}",
                            trigger_terms[0]
                        );
                    }
                }
                other => panic!("Expected Annotated body, got: {:?}", other),
            }
        }
        other => panic!("Expected Forall, got: {:?}", other),
    }
}
