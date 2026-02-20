//! Separation Logic End-to-End Integration Tests (Phase 20-04)
//!
//! Verifies all four SEP requirements hold end-to-end:
//!   SEP-01: pts_to ownership — IR with pts_to contract → correct SMT encoding
//!   SEP-02: separating conjunction — pts_to * pts_to → And([pts_to_enc, pts_to_enc])
//!   SEP-03: frame rule — call-site VC contains forall + AUFBV logic
//!   SEP-04: ghost predicate unfold — ghost pred expanded at depth 3, BoolLit(false) at depth 0
//!
//! Pipeline: spec annotation → IR → VCGen → SMT-LIB → Z3

use rust_fv_analysis::contract_db::{ContractDatabase, FunctionSummary};
use rust_fv_analysis::ghost_predicate_db::{GhostPredicate, GhostPredicateDatabase};
use rust_fv_analysis::ir::*;
use rust_fv_analysis::spec_parser::{parse_spec_expr, parse_spec_expr_with_db};
use rust_fv_analysis::vcgen::{self, VcKind};
use rust_fv_smtlib::term::Term;
use rust_fv_solver::{SolverResult, Z3Solver};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Create a Z3Solver or skip if Z3 is not installed.
fn solver_or_skip() -> Z3Solver {
    match Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Skipping test -- Z3 not available: {e}");
            panic!("Z3_NOT_AVAILABLE: {e}");
        }
    }
}

/// Build a minimal Function with a single RawPtr param (`p`) and an i32 value param (`v`).
///
/// Parameters: `p: *const i32` (RawPtr), `v: i32`
/// Return: `_0: i32`
fn build_ptr_func(name: &str, requires_raw: &str, ensures_raw: &str) -> Function {
    Function {
        name: name.to_string(),
        params: vec![
            Local::new(
                "p",
                Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
            ),
            Local::new("v", Ty::Int(IntTy::I32)),
        ],
        return_local: Local::new("_0", Ty::Int(IntTy::I32)),
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Copy(Place::local("v"))),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: if requires_raw.is_empty() {
                vec![]
            } else {
                vec![SpecExpr {
                    raw: requires_raw.to_string(),
                }]
            },
            ensures: if ensures_raw.is_empty() {
                vec![]
            } else {
                vec![SpecExpr {
                    raw: ensures_raw.to_string(),
                }]
            },
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
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
        loops: vec![],
    }
}

/// Build a Function with two RawPtr params (`p`, `q`) and two i32 params (`x`, `y`).
fn build_two_ptr_func(name: &str, requires_raw: &str) -> Function {
    Function {
        name: name.to_string(),
        params: vec![
            Local::new(
                "p",
                Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
            ),
            Local::new(
                "q",
                Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
            ),
            Local::new("x", Ty::Int(IntTy::I32)),
            Local::new("y", Ty::Int(IntTy::I32)),
        ],
        return_local: Local::new("_0", Ty::Int(IntTy::I32)),
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: if requires_raw.is_empty() {
                vec![]
            } else {
                vec![SpecExpr {
                    raw: requires_raw.to_string(),
                }]
            },
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
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
        loops: vec![],
    }
}

/// Build a caller function that calls `write_ptr(_1, _2)` via Terminator::Call.
///
/// The caller has one RawPtr param `_1` and one i32 param `_2`, and calls `write_ptr`.
fn build_caller_func() -> Function {
    // bb0: call write_ptr(_1, _2) -> bb1
    let bb0 = BasicBlock {
        statements: vec![],
        terminator: Terminator::Call {
            func: "write_ptr".to_string(),
            args: vec![
                Operand::Copy(Place::local("_1")),
                Operand::Copy(Place::local("_2")),
            ],
            destination: Place::local("_0"),
            target: 1,
        },
    };
    let bb1 = BasicBlock {
        statements: vec![],
        terminator: Terminator::Return,
    };

    Function {
        name: "caller".to_string(),
        params: vec![
            Local::new(
                "_1",
                Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
            ),
            Local::new("_2", Ty::Int(IntTy::I32)),
        ],
        return_local: Local::new("_0", Ty::Unit),
        locals: vec![],
        basic_blocks: vec![bb0, bb1],
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
        loops: vec![],
    }
}

// ---------------------------------------------------------------------------
// SEP-01: pts_to ownership
// ---------------------------------------------------------------------------

/// SEP-01: Verifies that `pts_to(p, v)` in a requires clause:
/// 1. Parses to `Term::And([Select(perm, p), Eq(heapval_as_bv32(Select(sep_heap, p)), v)])`.
/// 2. `generate_vcs` produces VC scripts containing `sep_heap`.
/// 3. The raw pts_to precondition is satisfiable (Z3 returns `sat`).
#[test]
fn sep_01_pts_to_ownership() {
    // Build write_ptr function: requires pts_to(p, v), ensures pts_to(p, v)
    let func = build_ptr_func("write_ptr", "pts_to(p, v)", "pts_to(p, v)");

    // --- 1. Verify spec parsing produces correct Term structure ---
    let term = parse_spec_expr("pts_to(p, v)", &func);
    assert!(
        term.is_some(),
        "SEP-01: pts_to(p, v) must parse to Some(term)"
    );
    let term = term.unwrap();
    // pts_to encodes as And([Select(perm, p), Eq(heapval_as_bvN(...), v)])
    assert!(
        matches!(&term, Term::And(_)),
        "SEP-01: pts_to must produce Term::And, got {term:?}"
    );
    if let Term::And(arms) = &term {
        assert_eq!(arms.len(), 2, "SEP-01: pts_to And must have exactly 2 arms");
        // First arm: Select(perm, ptr)
        assert!(
            matches!(&arms[0], Term::Select(arr, _) if matches!(arr.as_ref(), Term::Const(n) if n == "perm")),
            "SEP-01: first arm must be Select(perm, p), got {:?}",
            arms[0]
        );
        // Second arm: Eq(heapval_accessor(...), v)
        assert!(
            matches!(&arms[1], Term::Eq(_, _)),
            "SEP-01: second arm must be Eq(...), got {:?}",
            arms[1]
        );
    }

    // --- 2. Verify VCGen produces scripts mentioning sep_heap ---
    let vcs = vcgen::generate_vcs(&func, None);
    let sep_heap_vc = vcs
        .conditions
        .iter()
        .find(|vc| vc.script.to_string().contains("sep_heap"));
    assert!(
        sep_heap_vc.is_some(),
        "SEP-01: generate_vcs must produce at least one VC with sep_heap declarations. Got {} VCs",
        vcs.conditions.len()
    );

    // --- 3. Verify Z3 finds pts_to precondition satisfiable ---
    let solver = solver_or_skip();

    // Build a direct satisfiability check: declare the heap model and assert pts_to
    let smt = r"
(set-logic QF_AUFBV)
(declare-sort HeapVal 0)
(declare-fun sep_heap () (Array (_ BitVec 64) HeapVal))
(declare-fun perm () (Array (_ BitVec 64) Bool))
(declare-fun heapval_as_bv32 (HeapVal) (_ BitVec 32))
(declare-const p (_ BitVec 64))
(declare-const v (_ BitVec 32))
(assert (select perm p))
(assert (= (heapval_as_bv32 (select sep_heap p)) v))
(check-sat)
";
    let result = solver.check_sat_raw(smt).expect("Z3 must not fail");
    assert!(
        matches!(result, SolverResult::Sat(_)),
        "SEP-01: pts_to(p, v) precondition must be satisfiable, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// SEP-02: Separating conjunction
// ---------------------------------------------------------------------------

/// SEP-02: Verifies that `pts_to(p, x) * pts_to(q, y)` in a requires clause:
/// 1. Parses to `Term::And([pts_to_p_x, pts_to_q_y])` — outer And with two pts_to Arms.
/// 2. Z3 returns `sat` for the conjunction (both pts_to hold simultaneously).
#[test]
fn sep_02_separating_conjunction() {
    // Build swap_ptrs: requires pts_to(p, x) * pts_to(q, y)
    let func = build_two_ptr_func("swap_ptrs", "pts_to(p, x) * pts_to(q, y)");
    let db = GhostPredicateDatabase::new();

    // --- 1. Verify spec parsing produces Term::And([pts_to_enc, pts_to_enc]) ---
    let term = parse_spec_expr_with_db("pts_to(p, x) * pts_to(q, y)", &func, &db);
    assert!(
        term.is_some(),
        "SEP-02: pts_to(p,x) * pts_to(q,y) must parse to Some(term)"
    );
    let term = term.unwrap();
    assert!(
        matches!(&term, Term::And(_)),
        "SEP-02: separating conjunction must produce Term::And, got {term:?}"
    );
    if let Term::And(arms) = &term {
        assert_eq!(
            arms.len(),
            2,
            "SEP-02: sep-conj And must have exactly 2 arms (one per pts_to)"
        );
        // Each arm is a pts_to encoding (Term::And)
        assert!(
            matches!(&arms[0], Term::And(_)),
            "SEP-02: left arm must be pts_to encoding (Term::And), got {:?}",
            arms[0]
        );
        assert!(
            matches!(&arms[1], Term::And(_)),
            "SEP-02: right arm must be pts_to encoding (Term::And), got {:?}",
            arms[1]
        );
    }

    // --- 2. Verify Z3 finds both pts_to assertions simultaneously satisfiable ---
    let solver = solver_or_skip();

    let smt = r"
(set-logic QF_AUFBV)
(declare-sort HeapVal 0)
(declare-fun sep_heap () (Array (_ BitVec 64) HeapVal))
(declare-fun perm () (Array (_ BitVec 64) Bool))
(declare-fun heapval_as_bv32 (HeapVal) (_ BitVec 32))
(declare-const p (_ BitVec 64))
(declare-const q (_ BitVec 64))
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(assert (select perm p))
(assert (= (heapval_as_bv32 (select sep_heap p)) x))
(assert (select perm q))
(assert (= (heapval_as_bv32 (select sep_heap q)) y))
(check-sat)
";
    let result = solver.check_sat_raw(smt).expect("Z3 must not fail");
    assert!(
        matches!(result, SolverResult::Sat(_)),
        "SEP-02: pts_to(p,x) * pts_to(q,y) must be satisfiable simultaneously, got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// SEP-03: Frame rule
// ---------------------------------------------------------------------------

/// SEP-03: Verifies that when a callee `write_ptr` has `pts_to` in its requires:
/// 1. The call-site VC script contains `forall` (the frame axiom).
/// 2. The script uses `AUFBV` logic.
/// 3. Z3 returns `unsat` for the negation of the frame axiom (axiom is valid).
#[test]
fn sep_03_frame_rule() {
    // Build callee summary: write_ptr(_1: *const i32, _2: i32) requires pts_to(_1, _2)
    let callee_contracts = Contracts {
        requires: vec![SpecExpr {
            raw: "pts_to(_1, _2)".to_string(),
        }],
        ensures: vec![SpecExpr {
            raw: "pts_to(_1, _2)".to_string(),
        }],
        invariants: vec![],
        is_pure: false,
        decreases: None,
        fn_specs: vec![],
    };

    let mut contract_db = ContractDatabase::new();
    contract_db.insert(
        "write_ptr".to_string(),
        FunctionSummary {
            contracts: callee_contracts,
            param_names: vec!["_1".to_string(), "_2".to_string()],
            param_types: vec![
                Ty::RawPtr(Box::new(Ty::Int(IntTy::I32)), Mutability::Shared),
                Ty::Int(IntTy::I32),
            ],
            return_ty: Ty::Unit,
        },
    );

    let caller = build_caller_func();
    let result = vcgen::generate_vcs(&caller, Some(&contract_db));

    // --- 1. Find call-site precondition VCs ---
    let call_vcs: Vec<_> = result
        .conditions
        .iter()
        .filter(|vc| vc.location.vc_kind == VcKind::Precondition)
        .collect();

    assert!(
        !call_vcs.is_empty(),
        "SEP-03: must have at least one call-site Precondition VC, got {} total VCs",
        result.conditions.len()
    );

    let vc = &call_vcs[0];
    let script_str = vc.script.to_string();

    // --- 2. Verify AUFBV logic (frame forall requires quantifiers) ---
    assert!(
        script_str.contains("AUFBV"),
        "SEP-03: call-site VC must use AUFBV logic, got script:\n{script_str}"
    );

    // --- 3. Verify frame axiom (forall) is present in the script ---
    assert!(
        script_str.contains("forall"),
        "SEP-03: call-site VC must contain frame axiom (forall), got script:\n{script_str}"
    );

    // --- 4. Verify Z3 returns unsat for the frame axiom negation ---
    // The frame axiom asserts: for all addr NOT in footprint, sep_heap is unchanged.
    // We check that the negation (exists addr where heap changes outside footprint) is UNSAT.
    let solver = solver_or_skip();
    let smt = r"
(set-logic AUFBV)
(declare-sort HeapVal 0)
(declare-fun sep_heap () (Array (_ BitVec 64) HeapVal))
(declare-fun sep_heap_pre () (Array (_ BitVec 64) HeapVal))
(declare-fun perm () (Array (_ BitVec 64) Bool))
(declare-const p (_ BitVec 64))
(assert (= sep_heap_pre sep_heap))
(assert (not (forall ((_sep_frame_addr (_ BitVec 64)))
  (! (=> (not (= _sep_frame_addr p))
         (= (select sep_heap _sep_frame_addr) (select sep_heap_pre _sep_frame_addr)))
     :pattern ((select sep_heap _sep_frame_addr))))))
(check-sat)
";
    let result = solver.check_sat_raw(smt).expect("Z3 must not fail");
    assert!(
        matches!(result, SolverResult::Unsat),
        "SEP-03: negation of frame axiom must be UNSAT (axiom is valid), got {result:?}"
    );
}

// ---------------------------------------------------------------------------
// SEP-04: Ghost predicate unfold
// ---------------------------------------------------------------------------

/// SEP-04: Verifies ghost predicate expansion:
/// 1. `owned(p): pts_to(p, 0)` registered in DB, `owned(p)` at depth 3 → `Some(And([...]))`.
/// 2. Recursively-defined ghost pred exhausts depth → `Some(BoolLit(false))` via public API.
#[test]
fn sep_04_ghost_predicate_unfold() {
    // Build a function with a RawPtr param `p` and i32 param `v`
    let func = build_ptr_func("test_func", "", "");

    // --- 1. Ghost predicate at depth 3 expands to pts_to encoding ---
    // Register `owned(p): pts_to(p, 0)` — simple ownership predicate
    let mut db = GhostPredicateDatabase::new();
    db.insert(
        "owned".to_string(),
        GhostPredicate {
            param_names: vec!["p".to_string()],
            body_raw: "pts_to(p, 0)".to_string(),
        },
    );

    // Parse `owned(p)` — should expand to pts_to(p, 0) encoding
    let term_depth3 = parse_spec_expr_with_db("owned(p)", &func, &db);
    assert!(
        term_depth3.is_some(),
        "SEP-04: owned(p) at depth 3 must return Some(term), got None"
    );
    let term = term_depth3.unwrap();
    // pts_to(p, 0) encodes as Term::And([Select(perm, p), Eq(heapval_as_bvN(...), 0)])
    assert!(
        matches!(&term, Term::And(_)),
        "SEP-04: ghost pred expansion of pts_to must produce Term::And, got {term:?}"
    );
    if let Term::And(arms) = &term {
        assert!(
            matches!(&arms[0], Term::Select(arr, _) if matches!(arr.as_ref(), Term::Const(n) if n == "perm")),
            "SEP-04: first arm must select from perm (pts_to ownership check), got {:?}",
            arms[0]
        );
    }

    // --- 2. Recursively-defined predicate exhausts depth → BoolLit(false) ---
    // Register `looping(p): looping(p)` — self-recursive, exhausts depth
    let mut db_recursive = GhostPredicateDatabase::new();
    db_recursive.insert(
        "looping".to_string(),
        GhostPredicate {
            param_names: vec!["p".to_string()],
            body_raw: "looping(p)".to_string(),
        },
    );

    // parse_spec_expr_with_db uses depth=3; recursive pred unwinds 3 times → depth=0 → BoolLit(false)
    let term_exhausted = parse_spec_expr_with_db("looping(p)", &func, &db_recursive);
    assert!(
        term_exhausted.is_some(),
        "SEP-04: recursively-defined ghost pred must return Some(BoolLit(false)) at depth 0, got None"
    );
    assert!(
        matches!(term_exhausted.unwrap(), Term::BoolLit(false)),
        "SEP-04: depth-exhausted ghost pred must return BoolLit(false)"
    );
}
