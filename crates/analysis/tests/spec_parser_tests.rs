/// Integration tests for the full specification parser.
///
/// Tests that the syn-based parser handles the full range of specification
/// syntax and maintains backward compatibility with parse_simple_spec.
use rust_fv_analysis::ir::*;
use rust_fv_analysis::spec_parser::parse_spec_expr;
use rust_fv_analysis::vcgen::parse_simple_spec;
use rust_fv_smtlib::term::Term;

// === Test helper functions ===

fn make_i32_function() -> Function {
    Function {
        name: "test_fn".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
        ],
        locals: vec![],
        basic_blocks: vec![],
        contracts: Contracts::default(),
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
        loops: vec![],
    }
}

fn make_u32_function() -> Function {
    Function {
        name: "test_u32".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Uint(UintTy::U32),
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Uint(UintTy::U32),
            is_ghost: false,
        }],
        locals: vec![],
        basic_blocks: vec![],
        contracts: Contracts::default(),
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
        loops: vec![],
    }
}

fn make_struct_return_function() -> Function {
    Function {
        name: "make_point".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Struct(
                "Point".to_string(),
                vec![
                    ("x".to_string(), Ty::Int(IntTy::I32)),
                    ("y".to_string(), Ty::Int(IntTy::I32)),
                ],
            ),
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        locals: vec![],
        basic_blocks: vec![],
        contracts: Contracts::default(),
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
        loops: vec![],
    }
}

fn make_tuple_return_function() -> Function {
    Function {
        name: "make_pair".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Uint(UintTy::U32)]),
            is_ghost: false,
        },
        params: vec![],
        locals: vec![],
        basic_blocks: vec![],
        contracts: Contracts::default(),
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
        loops: vec![],
    }
}

fn make_bool_return_function() -> Function {
    Function {
        name: "check".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Bool,
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        locals: vec![],
        basic_blocks: vec![],
        contracts: Contracts::default(),
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
        loops: vec![],
    }
}

// === Simple comparison tests ===

#[test]
fn test_result_greater_than_zero() {
    let func = make_i32_function();
    let term = parse_spec_expr("result > 0", &func).unwrap();
    assert!(
        matches!(term, Term::BvSGt(_, _)),
        "Expected BvSGt, got {term:?}"
    );
}

#[test]
fn test_result_ge_param() {
    let func = make_i32_function();
    let term = parse_spec_expr("result >= _1", &func).unwrap();
    assert!(
        matches!(term, Term::BvSGe(_, _)),
        "Expected BvSGe, got {term:?}"
    );
}

#[test]
fn test_result_lt_param() {
    let func = make_i32_function();
    let term = parse_spec_expr("result < _1", &func).unwrap();
    assert!(
        matches!(term, Term::BvSLt(_, _)),
        "Expected BvSLt, got {term:?}"
    );
}

#[test]
fn test_result_le_param() {
    let func = make_i32_function();
    let term = parse_spec_expr("result <= _1", &func).unwrap();
    assert!(
        matches!(term, Term::BvSLe(_, _)),
        "Expected BvSLe, got {term:?}"
    );
}

#[test]
fn test_unsigned_comparison() {
    let func = make_u32_function();
    let term = parse_spec_expr("result > 0", &func).unwrap();
    assert!(
        matches!(term, Term::BvUGt(_, _)),
        "Expected BvUGt, got {term:?}"
    );
}

// === Arithmetic tests ===

#[test]
fn test_addition() {
    let func = make_i32_function();
    let term = parse_spec_expr("result == _1 + _2", &func).unwrap();
    if let Term::Eq(_, rhs) = &term {
        assert!(matches!(&**rhs, Term::BvAdd(_, _)));
    } else {
        panic!("Expected Eq, got {term:?}");
    }
}

#[test]
fn test_subtraction() {
    let func = make_i32_function();
    let term = parse_spec_expr("result == _1 - _2", &func).unwrap();
    if let Term::Eq(_, rhs) = &term {
        assert!(matches!(&**rhs, Term::BvSub(_, _)));
    } else {
        panic!("Expected Eq, got {term:?}");
    }
}

#[test]
fn test_multiplication() {
    let func = make_i32_function();
    let term = parse_spec_expr("result == _1 * 2 - _2", &func).unwrap();
    // _1 * 2 - _2 parses as (_1 * 2) - _2 per Rust precedence
    if let Term::Eq(_, rhs) = &term {
        assert!(matches!(&**rhs, Term::BvSub(_, _)));
    } else {
        panic!("Expected Eq with BvSub, got {term:?}");
    }
}

#[test]
fn test_division() {
    let func = make_i32_function();
    let term = parse_spec_expr("result == _1 / _2", &func).unwrap();
    if let Term::Eq(_, rhs) = &term {
        assert!(
            matches!(&**rhs, Term::BvSDiv(_, _)),
            "Expected BvSDiv, got {rhs:?}"
        );
    } else {
        panic!("Expected Eq, got {term:?}");
    }
}

#[test]
fn test_remainder() {
    let func = make_i32_function();
    let term = parse_spec_expr("result == _1 % _2", &func).unwrap();
    if let Term::Eq(_, rhs) = &term {
        assert!(
            matches!(&**rhs, Term::BvSRem(_, _)),
            "Expected BvSRem, got {rhs:?}"
        );
    } else {
        panic!("Expected Eq, got {term:?}");
    }
}

// === Logical operator tests ===

#[test]
fn test_logical_and() {
    let func = make_i32_function();
    let term = parse_spec_expr("result >= _1 && result >= _2", &func).unwrap();
    if let Term::And(parts) = &term {
        assert_eq!(parts.len(), 2);
    } else {
        panic!("Expected And, got {term:?}");
    }
}

#[test]
fn test_logical_or() {
    let func = make_i32_function();
    let term = parse_spec_expr("result > 0 || result == 0", &func).unwrap();
    if let Term::Or(parts) = &term {
        assert_eq!(parts.len(), 2);
    } else {
        panic!("Expected Or, got {term:?}");
    }
}

#[test]
fn test_not_equal() {
    let func = make_i32_function();
    let term = parse_spec_expr("result != 0", &func).unwrap();
    assert!(
        matches!(term, Term::Not(_)),
        "Expected Not(Eq), got {term:?}"
    );
}

// === Field access tests ===

#[test]
fn test_struct_field_x() {
    let func = make_struct_return_function();
    let term = parse_spec_expr("result.x > 0", &func).unwrap();
    if let Term::BvSGt(lhs, _) = &term {
        if let Term::App(name, args) = &**lhs {
            assert_eq!(name, "Point-x");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], Term::Const("_0".to_string()));
        } else {
            panic!("Expected App selector, got {lhs:?}");
        }
    } else {
        panic!("Expected BvSGt, got {term:?}");
    }
}

#[test]
fn test_struct_field_y_eq() {
    let func = make_struct_return_function();
    let term = parse_spec_expr("result.y == _1", &func).unwrap();
    if let Term::Eq(lhs, _) = &term {
        assert!(matches!(&**lhs, Term::App(name, _) if name == "Point-y"));
    } else {
        panic!("Expected Eq, got {term:?}");
    }
}

#[test]
fn test_tuple_field_0() {
    let func = make_tuple_return_function();
    let term = parse_spec_expr("result.0 > 0", &func).unwrap();
    if let Term::BvSGt(lhs, _) = &term {
        assert!(matches!(&**lhs, Term::App(name, _) if name == "Tuple2-_0"));
    } else {
        panic!("Expected BvSGt with Tuple2-_0, got {term:?}");
    }
}

#[test]
fn test_tuple_field_1() {
    let func = make_tuple_return_function();
    let term = parse_spec_expr("result.1 > 0", &func).unwrap();
    if let Term::BvUGt(lhs, _) = &term {
        // Field 1 is U32, so unsigned comparison
        assert!(matches!(&**lhs, Term::App(name, _) if name == "Tuple2-_1"));
    } else {
        panic!("Expected BvUGt with Tuple2-_1, got {term:?}");
    }
}

// === old() operator tests ===

#[test]
fn test_old_simple_variable() {
    let func = make_i32_function();
    let term = parse_spec_expr("result == old(_1) + 1", &func).unwrap();
    if let Term::Eq(_, rhs) = &term {
        if let Term::BvAdd(lhs_inner, _) = &**rhs {
            assert_eq!(**lhs_inner, Term::Const("_1_pre".to_string()));
        } else {
            panic!("Expected BvAdd, got {rhs:?}");
        }
    } else {
        panic!("Expected Eq, got {term:?}");
    }
}

#[test]
fn test_old_complex_expression() {
    let func = make_i32_function();
    let term = parse_spec_expr("old(_1 + _2)", &func).unwrap();
    if let Term::BvAdd(lhs, rhs) = &term {
        assert_eq!(**lhs, Term::Const("_1_pre".to_string()));
        assert_eq!(**rhs, Term::Const("_2_pre".to_string()));
    } else {
        panic!("Expected BvAdd with _pre vars, got {term:?}");
    }
}

#[test]
fn test_old_result_reference() {
    let func = make_i32_function();
    // old(result) should reference _0_pre
    let term = parse_spec_expr("result > old(result)", &func).unwrap();
    if let Term::BvSGt(lhs, rhs) = &term {
        assert_eq!(**lhs, Term::Const("_0".to_string()));
        assert_eq!(**rhs, Term::Const("_0_pre".to_string()));
    } else {
        panic!("Expected BvSGt, got {term:?}");
    }
}

// === Nested and complex expressions ===

#[test]
fn test_nested_logic_with_fields() {
    let func = make_struct_return_function();
    let term = parse_spec_expr("(result.x > 0) && (result.y > 0)", &func).unwrap();
    if let Term::And(parts) = &term {
        assert_eq!(parts.len(), 2);
    } else {
        panic!("Expected And, got {term:?}");
    }
}

#[test]
fn test_parenthesized_expressions() {
    let func = make_i32_function();
    let term = parse_spec_expr("(result > 0) && (result < 100)", &func).unwrap();
    assert!(matches!(term, Term::And(_)));
}

// === Literal tests ===

#[test]
fn test_integer_literal_eq() {
    let func = make_i32_function();
    let term = parse_spec_expr("result == 42", &func).unwrap();
    if let Term::Eq(_, rhs) = &term {
        assert_eq!(**rhs, Term::BitVecLit(42, 32));
    } else {
        panic!("Expected Eq, got {term:?}");
    }
}

#[test]
fn test_bool_literal_true() {
    let func = make_bool_return_function();
    let term = parse_spec_expr("true", &func).unwrap();
    assert_eq!(term, Term::BoolLit(true));
}

#[test]
fn test_bool_literal_false() {
    let func = make_bool_return_function();
    let term = parse_spec_expr("false", &func).unwrap();
    assert_eq!(term, Term::BoolLit(false));
}

// === Unary operator tests ===

#[test]
fn test_negation() {
    let func = make_i32_function();
    let term = parse_spec_expr("-_1", &func).unwrap();
    assert!(
        matches!(term, Term::BvNeg(_)),
        "Expected BvNeg, got {term:?}"
    );
}

#[test]
fn test_logical_not() {
    let func = make_i32_function();
    let term = parse_spec_expr("!(result > 0)", &func).unwrap();
    assert!(matches!(term, Term::Not(_)), "Expected Not, got {term:?}");
}

// === Error case tests ===

#[test]
fn test_invalid_syntax_returns_none() {
    let func = make_i32_function();
    assert!(parse_spec_expr("result >>><<< 0", &func).is_none());
}

#[test]
fn test_empty_string_returns_none() {
    let func = make_i32_function();
    assert!(parse_spec_expr("", &func).is_none());
}

#[test]
fn test_unknown_variable_returns_none() {
    let func = make_i32_function();
    assert!(parse_spec_expr("unknown_var > 0", &func).is_none());
}

// === Backward compatibility tests ===

#[test]
fn backward_compat_result_ge_0() {
    let func = make_i32_function();
    let old = parse_simple_spec("result >= 0", &func);
    let new = parse_spec_expr("result >= 0", &func);
    assert!(old.is_some(), "Old parser should handle this");
    assert!(new.is_some(), "New parser should handle this");
    // Both produce signed GE
    assert!(matches!(old.unwrap(), Term::BvSGe(_, _)));
    assert!(matches!(new.unwrap(), Term::BvSGe(_, _)));
}

#[test]
fn backward_compat_and_expression() {
    let func = make_i32_function();
    let old = parse_simple_spec("result >= _1 && result >= _2", &func);
    let new = parse_spec_expr("result >= _1 && result >= _2", &func);
    assert!(old.is_some());
    assert!(new.is_some());
    assert!(matches!(old.unwrap(), Term::And(_)));
    assert!(matches!(new.unwrap(), Term::And(_)));
}

#[test]
fn backward_compat_equality() {
    let func = make_i32_function();
    let old = parse_simple_spec("result == _1", &func);
    let new = parse_spec_expr("result == _1", &func);
    assert!(old.is_some());
    assert!(new.is_some());
    assert!(matches!(old.unwrap(), Term::Eq(_, _)));
    assert!(matches!(new.unwrap(), Term::Eq(_, _)));
}

#[test]
fn backward_compat_arithmetic_addition() {
    let func = make_i32_function();
    let old = parse_simple_spec("result == _1 + _2", &func);
    let new = parse_spec_expr("result == _1 + _2", &func);
    assert!(old.is_some());
    assert!(new.is_some());
}

#[test]
fn backward_compat_less_than() {
    let func = make_i32_function();
    let old = parse_simple_spec("_1 < 100", &func);
    let new = parse_spec_expr("_1 < 100", &func);
    assert!(old.is_some());
    assert!(new.is_some());
}

#[test]
fn backward_compat_result_field_access() {
    let func = make_struct_return_function();
    let old = parse_simple_spec("result.x > 0", &func);
    let new = parse_spec_expr("result.x > 0", &func);
    assert!(old.is_some(), "Old parser should handle result.x");
    assert!(new.is_some(), "New parser should handle result.x");
}
