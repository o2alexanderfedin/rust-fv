//! Tests for spec validation error propagation through VCGen.
//!
//! Verifies that syntactically invalid `#[requires(...)]` or `#[ensures(...)]`
//! expressions produce `SpecValidationError`s instead of being silently dropped,
//! and that valid contracts and code-level VCs continue to be generated.

use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::generate_vcs;

/// Build a simple `fn add(a: i32, b: i32) -> i32 { a + b }` with custom contracts.
fn make_add_with_contracts(requires: Vec<&str>, ensures: Vec<&str>) -> Function {
    Function {
        name: "add".to_string(),
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
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_2")),
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: requires
                .into_iter()
                .map(|s| SpecExpr { raw: s.to_string() })
                .collect(),
            ensures: ensures
                .into_iter()
                .map(|s| SpecExpr { raw: s.to_string() })
                .collect(),
            ..Contracts::default()
        },
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
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
        union_ghost_states: vec![],
        pin_ghost_states: vec![],
        drop_locals: vec![],
        hrtb_bounds: vec![],
        loops: vec![],
    }
}

#[test]
fn spec_validation_invalid_requires_produces_error() {
    // An invalid spec expression should produce a SpecValidationError
    let func = make_add_with_contracts(vec!["result >>><<< 0"], vec![]);
    let result = generate_vcs(&func, None);

    // The spec_errors field should contain the invalid spec
    assert!(
        !result.spec_errors.is_empty(),
        "Invalid spec should produce SpecValidationError, got empty spec_errors"
    );
    assert!(
        result.spec_errors[0].spec_text.contains(">>><<<"),
        "Error should contain the invalid expression text"
    );
}

#[test]
fn spec_validation_invalid_requires_still_generates_code_vcs() {
    // Even with an invalid requires, code-level VCs (overflow) should still be generated
    let func = make_add_with_contracts(vec!["result >>><<< 0"], vec![]);
    let result = generate_vcs(&func, None);

    assert!(
        !result.conditions.is_empty(),
        "Code-level VCs should still be generated despite invalid spec"
    );
}

#[test]
fn spec_validation_mixed_valid_and_invalid_requires() {
    // One valid and one invalid requires: valid one should be used, invalid reported
    let func = make_add_with_contracts(vec!["_1 >= 0", "result >>><<< 0"], vec!["result >= 0"]);
    let result = generate_vcs(&func, None);

    // Should have spec errors only for the invalid requires (may appear multiple times
    // because different VC generators iterate over contracts independently)
    assert!(
        !result.spec_errors.is_empty(),
        "Should have spec errors for the invalid requires"
    );
    assert!(
        result
            .spec_errors
            .iter()
            .all(|e| e.spec_text.contains(">>><<<")),
        "All spec errors should be for the invalid spec, got: {:?}",
        result.spec_errors
    );

    // Should still generate VCs (both code-level and postcondition from valid contracts)
    assert!(
        !result.conditions.is_empty(),
        "Should still generate VCs from valid contracts and code"
    );
}

#[test]
fn spec_validation_valid_spec_returns_ok() {
    // Valid specs should produce no errors (regression test)
    let func = make_add_with_contracts(vec!["_1 >= 0"], vec!["result >= 0"]);
    let result = generate_vcs(&func, None);

    assert!(
        result.spec_errors.is_empty(),
        "Valid specs should produce no SpecValidationErrors, got: {:?}",
        result.spec_errors
    );
}

#[test]
fn spec_validation_error_contains_function_name() {
    let func = make_add_with_contracts(vec!["completely invalid gibberish @#$%"], vec![]);
    let result = generate_vcs(&func, None);

    assert!(!result.spec_errors.is_empty());
    assert_eq!(
        result.spec_errors[0].function_name, "add",
        "Error should reference the function name"
    );
}
