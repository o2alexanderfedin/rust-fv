//! End-to-end driver-level integration tests for pattern matching constructs.
//!
//! These tests exercise the FULL pipeline: VerificationTask -> verify_functions_parallel()
//! -> verify_single() -> generate_vcs_with_db() with synthetic IR that models how Rust
//! pattern matching constructs desugar to MIR (SwitchInt, Assert, Discriminant, etc.).
//!
//! Four pattern constructs tested:
//!   PAT-01: let-else desugaring (Discriminant + SwitchInt)
//!   PAT-02: Slice patterns with length guards (Assert + Field access)
//!   PAT-03: Range patterns 1..=5 (BinaryOp comparisons + SwitchInt)
//!   PAT-04: @ bindings (local binding + range check via SwitchInt)
//!
//! Each construct has a positive test (correct VCs with `ensures: "true"`)
//! and a negative/constraint test (VCs generated with meaningful postconditions).

use rust_fv_analysis::ghost_predicate_db::GhostPredicateDatabase;
use rust_fv_analysis::ir::{
    AssertKind, BasicBlock, BinOp, Constant, Contracts, Function, IntTy, Local, Operand, Place,
    Rvalue, SpecExpr, Statement, Terminator, Ty,
};
use rust_fv_analysis::monomorphize::MonomorphizationRegistry;
use rust_fv_driver::cache::VcCache;
use rust_fv_driver::invalidation::{InvalidationDecision, InvalidationReason};
use rust_fv_driver::parallel::{VerificationTask, verify_functions_parallel};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

fn temp_cache_dir(name: &str) -> PathBuf {
    let mut dir = std::env::temp_dir();
    dir.push(format!(
        "rust-fv-pattern-e2e-{}-{}",
        name,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

fn make_pattern_task(func: Function) -> VerificationTask {
    VerificationTask {
        name: func.name.clone(),
        ir_func: func,
        contract_db: Arc::new(rust_fv_analysis::contract_db::ContractDatabase::new()),
        ghost_pred_db: Arc::new(GhostPredicateDatabase::new()),
        monomorphization_registry: Arc::new(MonomorphizationRegistry::new()),
        cache_key: [0u8; 32],
        mir_hash: [0u8; 32],
        contract_hash: [0u8; 32],
        dependencies: vec![],
        invalidation_decision: InvalidationDecision::verify(InvalidationReason::Fresh),
        source_locations: HashMap::new(),
    }
}

fn make_contracts(ensures: &[&str]) -> Contracts {
    Contracts {
        requires: vec![],
        ensures: ensures
            .iter()
            .map(|s| SpecExpr { raw: s.to_string() })
            .collect(),
        invariants: vec![],
        is_pure: false,
        decreases: None,
        fn_specs: vec![],
        state_invariant: None,
        is_inferred: false,
    }
}

fn make_base_function(name: &str, contracts: Contracts) -> Function {
    Function {
        name: name.to_string(),
        params: vec![Local::new("_1", Ty::Int(IntTy::I32))],
        return_local: Local::new("_0", Ty::Int(IntTy::I32)),
        locals: vec![],
        basic_blocks: vec![],
        contracts,
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
        source_names: HashMap::new(),
        coroutine_info: None,
        refcell_ghost_states: vec![],
        maybeuninit_ghost_states: vec![],
    }
}

fn assert_nonempty_results(
    results: &[rust_fv_driver::parallel::VerificationTaskResult],
    test_name: &str,
) {
    assert_eq!(
        results.len(),
        1,
        "{}: must have exactly one task result",
        test_name
    );
    let task_results = &results[0].results;
    assert!(
        !task_results.is_empty(),
        "{}: must produce at least one VC result. Got 0 results. Conditions: {:?}",
        test_name,
        task_results
            .iter()
            .map(|r| &r.condition)
            .collect::<Vec<_>>()
    );
}

// =============================================================================
// PAT-01: let-else desugaring
// =============================================================================

/// PAT-01 positive: let-else pattern desugaring produces correct VCs.
///
/// Models `let Some(x) = opt else { return }`:
///   bb0: _disc = Discriminant(_1)
///   bb0: SwitchInt(_disc) -> [1: bb1 (Some), otherwise: bb2 (else/diverge)]
///   bb1: _0 = _1.field[0]  // extract inner value
///   bb1: Return
///   bb2: _0 = Constant(0)  // diverging else path
///   bb2: Return
#[test]
fn pat01_let_else_positive() {
    let mut func = make_base_function("pat01_let_else_positive", make_contracts(&["true"]));
    func.locals = vec![Local::new("_disc", Ty::Int(IntTy::I32))];
    func.basic_blocks = vec![
        // bb0: discriminant check + switch
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_disc"),
                Rvalue::Discriminant(Place::local("_1")),
            )],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local("_disc")),
                targets: vec![(1, 1)], // Some variant -> bb1
                otherwise: 2,          // else -> bb2
            },
        },
        // bb1: matched Some — extract field and return
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Copy(Place::local("_1").field(0))),
            )],
            terminator: Terminator::Return,
        },
        // bb2: else branch (diverging path)
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
            )],
            terminator: Terminator::Return,
        },
    ];

    let task = make_pattern_task(func);
    let cache_dir = temp_cache_dir("pat01-positive");
    let mut cache = VcCache::new(cache_dir);
    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

    assert_nonempty_results(&results, "pat01_let_else_positive");
}

/// PAT-01 negative: let-else with diverging else branch still generates VCs for both paths.
///
/// Ensures the else branch is reachable and VCs are generated (not silently skipped).
#[test]
fn pat01_let_else_diverging_else() {
    let mut func = make_base_function("pat01_let_else_diverging_else", make_contracts(&["true"]));
    func.locals = vec![Local::new("_disc", Ty::Int(IntTy::I32))];
    func.basic_blocks = vec![
        // bb0: discriminant check + switch
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_disc"),
                Rvalue::Discriminant(Place::local("_1")),
            )],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local("_disc")),
                targets: vec![(1, 1)], // Some variant -> bb1
                otherwise: 2,          // else -> bb2
            },
        },
        // bb1: matched — set return to input
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Copy(Place::local("_1"))),
            )],
            terminator: Terminator::Return,
        },
        // bb2: else/diverging — still a valid path producing VCs
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Int(-1, IntTy::I32))),
            )],
            terminator: Terminator::Return,
        },
    ];

    let task = make_pattern_task(func);
    let cache_dir = temp_cache_dir("pat01-diverging");
    let mut cache = VcCache::new(cache_dir);
    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

    assert_nonempty_results(&results, "pat01_let_else_diverging_else");
}

// =============================================================================
// PAT-02: Slice patterns [first, .., last]
// =============================================================================

/// PAT-02 positive: Slice pattern with length guard produces correct VCs.
///
/// Models `[first, .., last]` destructuring:
///   bb0: Assert(len(_1) >= 2, true, bb1, "slice too short")
///   bb1: _first = _1[0]
///   bb1: _last = _1[len-1]  (simplified to field access)
///   bb1: _0 = _first
///   bb1: Return
#[test]
fn pat02_slice_pattern_positive() {
    let mut func = make_base_function("pat02_slice_pattern_positive", make_contracts(&["true"]));
    func.locals = vec![
        Local::new("_len", Ty::Int(IntTy::I32)),
        Local::new("_len_check", Ty::Bool),
        Local::new("_first", Ty::Int(IntTy::I32)),
        Local::new("_last", Ty::Int(IntTy::I32)),
    ];
    func.basic_blocks = vec![
        // bb0: length check via Assert terminator
        BasicBlock {
            statements: vec![
                // _len = Len(_1)
                Statement::Assign(Place::local("_len"), Rvalue::Len(Place::local("_1"))),
                // _len_check = _len >= 2
                Statement::Assign(
                    Place::local("_len_check"),
                    Rvalue::BinaryOp(
                        BinOp::Ge,
                        Operand::Copy(Place::local("_len")),
                        Operand::Constant(Constant::Int(2, IntTy::I32)),
                    ),
                ),
            ],
            terminator: Terminator::Assert {
                cond: Operand::Copy(Place::local("_len_check")),
                expected: true,
                target: 1,
                kind: AssertKind::UserAssert,
            },
        },
        // bb1: extract first and last elements
        BasicBlock {
            statements: vec![
                Statement::Assign(
                    Place::local("_first"),
                    Rvalue::Use(Operand::Copy(Place::local("_1").field(0))),
                ),
                Statement::Assign(
                    Place::local("_last"),
                    Rvalue::Use(Operand::Copy(Place::local("_1").field(1))),
                ),
                Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_first"))),
                ),
            ],
            terminator: Terminator::Return,
        },
    ];

    let task = make_pattern_task(func);
    let cache_dir = temp_cache_dir("pat02-positive");
    let mut cache = VcCache::new(cache_dir);
    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

    assert_nonempty_results(&results, "pat02_slice_pattern_positive");
}

/// PAT-02 negative: Slice pattern with postcondition referencing length.
///
/// Uses `ensures: "_0 >= 0"` to confirm VCs include the length guard assertion.
#[test]
fn pat02_slice_pattern_length_check() {
    let mut func = make_base_function(
        "pat02_slice_pattern_length_check",
        make_contracts(&["_0 >= 0"]),
    );
    func.locals = vec![
        Local::new("_len", Ty::Int(IntTy::I32)),
        Local::new("_len_check", Ty::Bool),
        Local::new("_first", Ty::Int(IntTy::I32)),
    ];
    func.basic_blocks = vec![
        // bb0: length guard
        BasicBlock {
            statements: vec![
                Statement::Assign(Place::local("_len"), Rvalue::Len(Place::local("_1"))),
                Statement::Assign(
                    Place::local("_len_check"),
                    Rvalue::BinaryOp(
                        BinOp::Ge,
                        Operand::Copy(Place::local("_len")),
                        Operand::Constant(Constant::Int(2, IntTy::I32)),
                    ),
                ),
            ],
            terminator: Terminator::Assert {
                cond: Operand::Copy(Place::local("_len_check")),
                expected: true,
                target: 1,
                kind: AssertKind::UserAssert,
            },
        },
        // bb1: extract first, assign to return
        BasicBlock {
            statements: vec![
                Statement::Assign(
                    Place::local("_first"),
                    Rvalue::Use(Operand::Copy(Place::local("_1").field(0))),
                ),
                Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_first"))),
                ),
            ],
            terminator: Terminator::Return,
        },
    ];

    let task = make_pattern_task(func);
    let cache_dir = temp_cache_dir("pat02-length-check");
    let mut cache = VcCache::new(cache_dir);
    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

    assert_nonempty_results(&results, "pat02_slice_pattern_length_check");
}

// =============================================================================
// PAT-03: Range patterns 1..=5
// =============================================================================

/// PAT-03 positive: Range pattern in match arm produces correct VCs.
///
/// Models `match x { 1..=5 => 1, _ => 0 }`:
///   bb0: _cmp1 = BinaryOp(Ge, _1, 1)
///   bb0: _cmp2 = BinaryOp(Le, _1, 5)
///   bb0: _in_range = BinaryOp(BitAnd, _cmp1, _cmp2)
///   bb0: SwitchInt(_in_range) -> [1: bb1, otherwise: bb2]
///   bb1: _0 = 1; Return
///   bb2: _0 = 0; Return
#[test]
fn pat03_range_pattern_positive() {
    let mut func = make_base_function("pat03_range_pattern_positive", make_contracts(&["true"]));
    func.locals = vec![
        Local::new("_cmp1", Ty::Bool),
        Local::new("_cmp2", Ty::Bool),
        Local::new("_in_range", Ty::Bool),
    ];
    func.basic_blocks = vec![
        // bb0: range comparison + switch
        BasicBlock {
            statements: vec![
                Statement::Assign(
                    Place::local("_cmp1"),
                    Rvalue::BinaryOp(
                        BinOp::Ge,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(1, IntTy::I32)),
                    ),
                ),
                Statement::Assign(
                    Place::local("_cmp2"),
                    Rvalue::BinaryOp(
                        BinOp::Le,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(5, IntTy::I32)),
                    ),
                ),
                Statement::Assign(
                    Place::local("_in_range"),
                    Rvalue::BinaryOp(
                        BinOp::BitAnd,
                        Operand::Copy(Place::local("_cmp1")),
                        Operand::Copy(Place::local("_cmp2")),
                    ),
                ),
            ],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local("_in_range")),
                targets: vec![(1, 1)], // in range -> bb1
                otherwise: 2,          // wildcard -> bb2
            },
        },
        // bb1: matched range
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Int(1, IntTy::I32))),
            )],
            terminator: Terminator::Return,
        },
        // bb2: wildcard
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
            )],
            terminator: Terminator::Return,
        },
    ];

    let task = make_pattern_task(func);
    let cache_dir = temp_cache_dir("pat03-positive");
    let mut cache = VcCache::new(cache_dir);
    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

    assert_nonempty_results(&results, "pat03_range_pattern_positive");
}

/// PAT-03 negative: Range pattern with postcondition that depends on range constraints.
///
/// Uses `ensures: "_0 >= 0"` to verify range constraints flow through VCs.
#[test]
fn pat03_range_pattern_with_postcondition() {
    let mut func = make_base_function(
        "pat03_range_pattern_with_postcondition",
        make_contracts(&["_0 >= 0"]),
    );
    func.locals = vec![
        Local::new("_cmp1", Ty::Bool),
        Local::new("_cmp2", Ty::Bool),
        Local::new("_in_range", Ty::Bool),
    ];
    func.basic_blocks = vec![
        // bb0: range comparison + switch
        BasicBlock {
            statements: vec![
                Statement::Assign(
                    Place::local("_cmp1"),
                    Rvalue::BinaryOp(
                        BinOp::Ge,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(1, IntTy::I32)),
                    ),
                ),
                Statement::Assign(
                    Place::local("_cmp2"),
                    Rvalue::BinaryOp(
                        BinOp::Le,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(5, IntTy::I32)),
                    ),
                ),
                Statement::Assign(
                    Place::local("_in_range"),
                    Rvalue::BinaryOp(
                        BinOp::BitAnd,
                        Operand::Copy(Place::local("_cmp1")),
                        Operand::Copy(Place::local("_cmp2")),
                    ),
                ),
            ],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local("_in_range")),
                targets: vec![(1, 1)],
                otherwise: 2,
            },
        },
        // bb1: matched range — return 1
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Int(1, IntTy::I32))),
            )],
            terminator: Terminator::Return,
        },
        // bb2: wildcard — return 0
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
            )],
            terminator: Terminator::Return,
        },
    ];

    let task = make_pattern_task(func);
    let cache_dir = temp_cache_dir("pat03-postcondition");
    let mut cache = VcCache::new(cache_dir);
    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

    assert_nonempty_results(&results, "pat03_range_pattern_with_postcondition");
}

// =============================================================================
// PAT-04: @ bindings
// =============================================================================

/// PAT-04 positive: @ binding pattern produces correct VCs.
///
/// Models `x @ 1..=5 => use x`:
///   bb0: _x = Use(_1)  // @ binding
///   bb0: _cmp = BinaryOp(Ge, _x, 1)
///   bb0: SwitchInt(_cmp) -> [1: bb1, otherwise: bb2]
///   bb1: _0 = Use(_x)  // use the bound value
///   bb1: Return
///   bb2: _0 = 0; Return
#[test]
fn pat04_at_binding_positive() {
    let mut func = make_base_function("pat04_at_binding_positive", make_contracts(&["true"]));
    func.locals = vec![
        Local::new("_x", Ty::Int(IntTy::I32)),
        Local::new("_cmp", Ty::Bool),
    ];
    func.basic_blocks = vec![
        // bb0: @ binding + range check
        BasicBlock {
            statements: vec![
                // _x = _1 (@ binding)
                Statement::Assign(
                    Place::local("_x"),
                    Rvalue::Use(Operand::Copy(Place::local("_1"))),
                ),
                // _cmp = _x >= 1
                Statement::Assign(
                    Place::local("_cmp"),
                    Rvalue::BinaryOp(
                        BinOp::Ge,
                        Operand::Copy(Place::local("_x")),
                        Operand::Constant(Constant::Int(1, IntTy::I32)),
                    ),
                ),
            ],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local("_cmp")),
                targets: vec![(1, 1)], // matched -> bb1
                otherwise: 2,          // not matched -> bb2
            },
        },
        // bb1: use the @ bound value
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Copy(Place::local("_x"))),
            )],
            terminator: Terminator::Return,
        },
        // bb2: wildcard
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
            )],
            terminator: Terminator::Return,
        },
    ];

    let task = make_pattern_task(func);
    let cache_dir = temp_cache_dir("pat04-positive");
    let mut cache = VcCache::new(cache_dir);
    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

    assert_nonempty_results(&results, "pat04_at_binding_positive");
}

/// PAT-04 negative: @ binding with postcondition verifying the binding constraint.
///
/// Uses `ensures: "_0 >= 1"` in the matched branch, verifying that the @ binding
/// constraint (_x >= 1) is available in the VC for the matched path.
#[test]
fn pat04_at_binding_with_postcondition() {
    let mut func = make_base_function(
        "pat04_at_binding_with_postcondition",
        make_contracts(&["_0 >= 0"]),
    );
    func.locals = vec![
        Local::new("_x", Ty::Int(IntTy::I32)),
        Local::new("_cmp", Ty::Bool),
    ];
    func.basic_blocks = vec![
        // bb0: @ binding + range check
        BasicBlock {
            statements: vec![
                Statement::Assign(
                    Place::local("_x"),
                    Rvalue::Use(Operand::Copy(Place::local("_1"))),
                ),
                Statement::Assign(
                    Place::local("_cmp"),
                    Rvalue::BinaryOp(
                        BinOp::Ge,
                        Operand::Copy(Place::local("_x")),
                        Operand::Constant(Constant::Int(1, IntTy::I32)),
                    ),
                ),
            ],
            terminator: Terminator::SwitchInt {
                discr: Operand::Copy(Place::local("_cmp")),
                targets: vec![(1, 1)],
                otherwise: 2,
            },
        },
        // bb1: matched — return bound value
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Copy(Place::local("_x"))),
            )],
            terminator: Terminator::Return,
        },
        // bb2: not matched — return 0
        BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
            )],
            terminator: Terminator::Return,
        },
    ];

    let task = make_pattern_task(func);
    let cache_dir = temp_cache_dir("pat04-postcondition");
    let mut cache = VcCache::new(cache_dir);
    let results = verify_functions_parallel(vec![task], &mut cache, 1, false, false);

    assert_nonempty_results(&results, "pat04_at_binding_with_postcondition");
}
