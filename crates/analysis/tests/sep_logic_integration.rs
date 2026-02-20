//! Separation Logic End-to-End Integration Tests (Phase 20-04)
//!
//! Verifies all four SEP requirements hold end-to-end:
//!   SEP-01: pts_to ownership — IR with pts_to contract → correct SMT encoding
//!   SEP-02: separating conjunction — pts_to * pts_to → And([pts_to_enc, pts_to_enc])
//!   SEP-03: frame rule — call-site VC contains forall + AUFBV logic
//!   SEP-04: ghost predicate unfold — ghost pred expanded at depth 3, BoolLit(false) at depth 0
//!
//! Pipeline: spec annotation → IR → VCGen → SMT-LIB → Z3

#![allow(dead_code, unused_imports)]

use rust_fv_analysis::ghost_predicate_db::{GhostPredicate, GhostPredicateDatabase};
use rust_fv_analysis::ir::*;
use rust_fv_analysis::spec_parser::{parse_spec_expr, parse_spec_expr_with_db};
use rust_fv_analysis::vcgen;
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

/// Build a minimal Function with a single RawPtr param and an i32 value param.
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

/// Build a Function with two RawPtr params (p, q) and two i32 params (x, y).
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

// ---------------------------------------------------------------------------
// SEP-01: pts_to ownership
// ---------------------------------------------------------------------------

/// SEP-01: Verifies that `pts_to(p, v)` in a requires clause:
/// 1. Parses into a `Term::And([Select(perm, p), Eq(heapval_accessor(Select(sep_heap, p)), v)])`.
/// 2. `generate_vcs` produces at least one VC script containing `sep_heap`.
/// 3. The pts_to precondition is satisfiable (Z3 returns `sat` for the raw encoding).
#[test]
fn sep_01_pts_to_ownership() {
    panic!("not yet implemented");
}

// ---------------------------------------------------------------------------
// SEP-02: Separating conjunction
// ---------------------------------------------------------------------------

/// SEP-02: Verifies that `pts_to(p, x) * pts_to(q, y)` in a requires clause:
/// 1. Parses to `Term::And([pts_to_p, pts_to_q])` (two nested And terms).
/// 2. The sep_heap model allows both pts_to assertions simultaneously (satisfiable).
#[test]
fn sep_02_separating_conjunction() {
    panic!("not yet implemented");
}

// ---------------------------------------------------------------------------
// SEP-03: Frame rule
// ---------------------------------------------------------------------------

/// SEP-03: Verifies that when a callee has `pts_to` in its requires:
/// 1. The call-site VC script contains a `forall` quantifier (frame axiom).
/// 2. The script uses `AUFBV` logic (quantified arrays + bitvectors).
/// 3. Z3 returns `unsat` for the frame axiom negation (i.e., axiom is valid).
#[test]
fn sep_03_frame_rule() {
    panic!("not yet implemented");
}

// ---------------------------------------------------------------------------
// SEP-04: Ghost predicate unfold
// ---------------------------------------------------------------------------

/// SEP-04: Verifies ghost predicate expansion:
/// 1. A ghost predicate `is_null_list(p, n): if n == 0 { true } else { pts_to(p, 0i64) }`
///    registered in the DB at depth 3 returns `Some(term)` containing a pts_to encoding.
/// 2. At depth 0, the parse returns `Some(BoolLit(false))` (depth exhausted).
#[test]
fn sep_04_ghost_predicate_unfold() {
    panic!("not yet implemented");
}
