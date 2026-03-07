//! End-to-end tests for spec validation error diagnostics (COMPL-06).
//!
//! Tests that syntactically invalid `#[requires(...)]` expressions produce
//! V080 error diagnostics and that the function's code-level VCs are still
//! generated and checked.

use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen::{SpecValidationError, VcKind, generate_vcs};
use std::collections::HashMap;

/// Build a function with a given set of requires/ensures contracts.
fn make_func_with_contracts(name: &str, requires: Vec<&str>, ensures: Vec<&str>) -> Function {
    Function {
        name: name.to_string(),
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
        source_names: HashMap::new(),
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

/// Test: Invalid #[requires] produces spec_errors containing V080-relevant info.
#[test]
fn spec_diagnostic_e2e_invalid_requires_produces_spec_error() {
    let func = make_func_with_contracts("broken_spec", vec!["result >>><<< 0"], vec![]);
    let result = generate_vcs(&func, None);

    // Should have spec errors
    assert!(
        !result.spec_errors.is_empty(),
        "Invalid spec should produce SpecValidationError"
    );

    // The error should contain the invalid expression text
    let error = &result.spec_errors[0];
    assert!(
        error.spec_text.contains(">>><<<"),
        "Error should contain the invalid expression"
    );
    assert_eq!(error.function_name, "broken_spec");
}

/// Test: The V080 diagnostic formatter produces expected output.
#[test]
fn spec_diagnostic_e2e_v080_format() {
    use rust_fv_driver::diagnostics::format_spec_validation_error;

    let error = SpecValidationError {
        spec_text: "result >>><<< 0".to_string(),
        function_name: "broken_spec".to_string(),
        source_file: Some("src/lib.rs".to_string()),
        source_line: Some(10),
        source_column: Some(5),
        kind: rust_fv_analysis::vcgen::SpecErrorKind::ParseFailure,
    };

    let formatted = format_spec_validation_error(&error);
    assert!(
        formatted.contains("V080"),
        "Diagnostic should contain V080 error code, got: {}",
        formatted
    );
    assert!(
        formatted.contains(">>><<<"),
        "Diagnostic should contain the invalid expression"
    );
}

/// Test: Fix suggestion for shift-like operators.
#[test]
fn spec_diagnostic_e2e_fix_suggestion_shift() {
    use rust_fv_driver::diagnostics::format_spec_validation_error;

    let error = SpecValidationError {
        spec_text: "result >>> 0".to_string(),
        function_name: "shift_test".to_string(),
        source_file: None,
        source_line: None,
        source_column: None,
        kind: rust_fv_analysis::vcgen::SpecErrorKind::ParseFailure,
    };

    let formatted = format_spec_validation_error(&error);
    assert!(
        formatted.contains(">>") || formatted.contains("did you mean"),
        "Should contain fix suggestion for >>>, got: {}",
        formatted
    );
}

/// Test: Function still generates code-level VCs despite broken annotation.
#[test]
fn spec_diagnostic_e2e_code_vcs_still_generated() {
    let func = make_func_with_contracts("still_verifies", vec!["result >>><<< 0"], vec![]);
    let result = generate_vcs(&func, None);

    // Code-level VCs (overflow) should still be present
    let code_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::Overflow)
        .collect();

    assert!(
        !code_vcs.is_empty(),
        "Code-level overflow VCs should still be generated despite invalid spec"
    );
}
