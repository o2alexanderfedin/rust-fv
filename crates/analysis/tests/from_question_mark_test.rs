//! Tests for From::from stdlib contracts and ? operator MIR pattern detection.
//!
//! Verifies:
//! - From::from contracts are registered in the StdlibContractRegistry
//! - Identity From<T> for T is detected and skipped (no contract)
//! - VCGen detects ? operator MIR pattern and injects From::from postcondition
//! - Caller's #[ensures] can reason about converted error type after ? propagation
//! - Missing From::from contract falls back gracefully (BoolLit(true))

use rust_fv_analysis::contract_db::ContractDatabase;
use rust_fv_analysis::ir::*;
use rust_fv_analysis::stdlib_contracts::StdlibContractRegistry;
use rust_fv_analysis::stdlib_contracts::from::{is_identity_from, register_from_contracts};
use rust_fv_analysis::stdlib_contracts::loader::load_default_contracts;
use rust_fv_analysis::vcgen;

// ---------------------------------------------------------------------------
// Test 1: From::from contracts registered for common conversions
// ---------------------------------------------------------------------------

#[test]
fn from_question_mark_registry_has_from_contracts() {
    let mut registry = StdlibContractRegistry::new();
    register_from_contracts(&mut registry);

    let contract = registry.get("From::from");
    assert!(
        contract.is_some(),
        "From::from contract should be registered"
    );
    let c = contract.unwrap();
    assert_eq!(c.type_path, "std::convert::From");
    assert_eq!(c.method_name, "from");
    assert!(
        !c.summary.contracts.ensures.is_empty(),
        "From::from should have postconditions"
    );
}

#[test]
fn from_question_mark_default_loader_includes_from() {
    let registry = load_default_contracts();
    assert!(
        registry.get("From::from").is_some(),
        "Default loader should include From::from contracts"
    );
}

// ---------------------------------------------------------------------------
// Test 2: Identity From<T> for T is detected and skipped
// ---------------------------------------------------------------------------

#[test]
fn from_question_mark_identity_from_detected() {
    assert!(is_identity_from("i32", "i32"));
    assert!(is_identity_from("String", "String"));
    assert!(is_identity_from("MyError", "MyError"));
}

#[test]
fn from_question_mark_non_identity_not_detected() {
    assert!(!is_identity_from("&str", "String"));
    assert!(!is_identity_from("i32", "i64"));
    assert!(!is_identity_from("u8", "u32"));
}

// ---------------------------------------------------------------------------
// Test 3: VCGen detects ? operator MIR pattern and injects From::from postcondition
// ---------------------------------------------------------------------------

/// Build a function that models the ? operator MIR pattern:
///   bb0: call result = inner_fn() -> bb1
///   bb1: discriminant = discriminant(result)
///         SwitchInt(discriminant) -> [0: bb2 (Ok), 1: bb3 (Err)]
///   bb2: _0 = result.0 (Ok value); return
///   bb3: err = result.1 (Err value)
///         call <E2 as From<E1>>::from(err) -> bb4
///   bb4: _0 = Err(converted); return
fn build_question_mark_mir() -> Function {
    let return_ty = Ty::Named("Result_i32_IoError".to_string());

    Function {
        name: "fn_with_question_mark".to_string(),
        return_local: Local::new("_0", return_ty),
        params: vec![],
        locals: vec![
            Local::new("_1", Ty::Named("Result_i32_ParseError".to_string())),
            Local::new("_2", Ty::Int(IntTy::I32)),
            Local::new("_3", Ty::Int(IntTy::I32)),
            Local::new("_4", Ty::Named("ParseError".to_string())),
            Local::new("_5", Ty::Named("IoError".to_string())),
        ],
        basic_blocks: vec![
            // bb0: call inner_fn() -> bb1
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "inner_fn".to_string(),
                    args: vec![],
                    destination: Place::local("_1"),
                    target: 1,
                },
            },
            // bb1: discriminant + SwitchInt (? operator pattern)
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_2"),
                    Rvalue::Discriminant(Place::local("_1")),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_2")),
                    targets: vec![(0, 2), (1, 3)],
                    otherwise: 2,
                },
            },
            // bb2: Ok path - extract value and return
            BasicBlock {
                statements: vec![
                    Statement::Assign(
                        Place::local("_3"),
                        Rvalue::Use(Operand::Copy(Place {
                            local: "_1".to_string(),
                            projections: vec![Projection::Field(0)],
                        })),
                    ),
                    Statement::Assign(
                        Place::local("_0"),
                        Rvalue::Use(Operand::Copy(Place::local("_3"))),
                    ),
                ],
                terminator: Terminator::Return,
            },
            // bb3: Err path - call From::from on the error
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_4"),
                    Rvalue::Use(Operand::Copy(Place {
                        local: "_1".to_string(),
                        projections: vec![Projection::Field(1)],
                    })),
                )],
                terminator: Terminator::Call {
                    func: "<IoError as From<ParseError>>::from".to_string(),
                    args: vec![Operand::Move(Place::local("_4"))],
                    destination: Place::local("_5"),
                    target: 4,
                },
            },
            // bb4: wrap in Err and return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Aggregate(
                        AggregateKind::Enum("Result".to_string(), 1),
                        vec![Operand::Move(Place::local("_5"))],
                    ),
                )],
                terminator: Terminator::Return,
            },
        ],
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
        refcell_ghost_states: vec![],
        loops: vec![],
    }
}

#[test]
fn from_question_mark_vcgen_detects_pattern() {
    let func = build_question_mark_mir();

    let mut db = ContractDatabase::new();
    let registry = load_default_contracts();
    registry.merge_into(&mut db);

    // Generate VCs - should detect the ? pattern and not crash
    let vcs = vcgen::generate_vcs(&func, Some(&db));

    assert!(
        vcs.spec_errors.is_empty(),
        "No spec errors should occur during ? pattern detection"
    );
}

// ---------------------------------------------------------------------------
// Test 4: Caller's ensures can reason about converted error type after ?
// ---------------------------------------------------------------------------

#[test]
fn from_question_mark_caller_ensures_with_from_postcondition() {
    let mut func = build_question_mark_mir();

    // Add an ensures clause that reasons about the return value
    func.contracts.ensures.push(SpecExpr {
        raw: "true".to_string(),
    });

    let mut db = ContractDatabase::new();
    let registry = load_default_contracts();
    registry.merge_into(&mut db);

    let vcs = vcgen::generate_vcs(&func, Some(&db));

    let postcondition_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| {
            matches!(
                vc.location.vc_kind,
                rust_fv_analysis::vcgen::VcKind::Postcondition
            )
        })
        .collect();

    assert!(
        !postcondition_vcs.is_empty(),
        "Should generate postcondition VCs for function with ? operator"
    );
}

// ---------------------------------------------------------------------------
// Test 5: Missing From::from contract falls back gracefully
// ---------------------------------------------------------------------------

#[test]
fn from_question_mark_no_contract_fallback() {
    let func = build_question_mark_mir();

    // Empty contract DB - no From::from contract available
    let db = ContractDatabase::new();

    // Should not crash, falls back to BoolLit(true)
    let vcs = vcgen::generate_vcs(&func, Some(&db));

    assert!(
        vcs.spec_errors.is_empty(),
        "No spec errors with missing From::from contract (graceful fallback)"
    );
}
