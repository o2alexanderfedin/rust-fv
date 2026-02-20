//! TDD test suite for HOF-01 and HOF-02 requirements.
//!
//! Validates that `generate_fn_spec_vcs()` produces AUFLIA SMT scripts that:
//! - Return UNSAT when given an axiom constraining the closure (entailment holds)
//! - Return SAT when no axiom is given (uninterpreted closure can violate the spec)
//!
//! ## Test matrix
//!
//! | Test | Closure trait | Axiom? | Expected |
//! |------|---------------|--------|----------|
//! | fn_spec_fn_verified | Fn | yes | UNSAT |
//! | fn_spec_fn_falsified | Fn | no | SAT |
//! | fn_spec_fn_trivially_true | Fn | no | UNSAT (vacuous) |
//! | fn_spec_fnmut_verified | FnMut | yes | UNSAT |
//! | fn_spec_fnmut_falsified | FnMut | no | SAT |
//! | fn_spec_fnonce_single_call | FnOnce | yes | UNSAT |
//!
//! ## Axiom injection technique
//!
//! `generate_fn_spec_vcs()` produces a Script ending with `(check-sat)`.
//! For verified cases, we clone the script commands (excluding the final
//! `check-sat`), insert the axiom Assert, then append `check-sat` again.
//! This is equivalent to Z3 receiving:
//!   (assert <axiom that says f IS correct>)
//!   (assert (not (forall x. pre => post)))  ; negated entailment
//!   (check-sat)
//! If the axiom says f IS correct, the negation is contradictory → UNSAT.

use rust_fv_analysis::hof_vcgen::generate_fn_spec_vcs;
use rust_fv_analysis::ir::{
    BasicBlock, ClosureInfo, ClosureTrait, Contracts, FnSpec, Function, IntTy, Local, Terminator,
    Ty,
};
use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::script::Script;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;
use rust_fv_solver::{SolverResult, Z3Solver};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Returns a Z3Solver or panics with a clear skip message.
fn solver_or_skip() -> Z3Solver {
    match Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Skipping HOF test — Z3 not available: {e}");
            panic!("Z3_NOT_AVAILABLE");
        }
    }
}

/// Build a test `Function` with a single Fn/FnOnce closure parameter.
///
/// The closure has one captured-nothing env, takes `x: i32`, returns `i32`.
fn make_fn_func(param_name: &str, trait_kind: ClosureTrait) -> Function {
    let closure_info = ClosureInfo {
        name: format!("closure_{param_name}"),
        env_fields: vec![],
        params: vec![("x".to_string(), Ty::Int(IntTy::I32))],
        return_ty: Ty::Int(IntTy::I32),
        trait_kind,
    };
    Function {
        name: "hof_test_fn".to_string(),
        params: vec![Local::new(param_name, Ty::Closure(Box::new(closure_info)))],
        return_local: Local::new("_0", Ty::Int(IntTy::I32)),
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            fn_specs: vec![],
            ..Default::default()
        },
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
    }
}

/// Build a test `Function` with a FnMut closure that captures `count: i32`.
fn make_fnmut_func(param_name: &str) -> Function {
    let closure_info = ClosureInfo {
        name: format!("closure_{param_name}"),
        env_fields: vec![("count".to_string(), Ty::Int(IntTy::I32))],
        params: vec![("x".to_string(), Ty::Int(IntTy::I32))],
        return_ty: Ty::Int(IntTy::I32),
        trait_kind: ClosureTrait::FnMut,
    };
    Function {
        name: "hof_test_fnmut".to_string(),
        params: vec![Local::new(param_name, Ty::Closure(Box::new(closure_info)))],
        return_local: Local::new("_0", Ty::Int(IntTy::I32)),
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            fn_specs: vec![],
            ..Default::default()
        },
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
    }
}

/// Clone all commands from a Script except the trailing `(check-sat)`.
fn commands_without_check_sat(script: &Script) -> Vec<Command> {
    let cmds = script.commands();
    let last_check = cmds
        .iter()
        .rposition(|c| matches!(c, Command::CheckSat))
        .unwrap_or(cmds.len());
    cmds[..last_check].to_vec()
}

/// Format a Script to SMT-LIB2 text (for error messages).
fn script_to_smtlib(script: &Script) -> String {
    script
        .commands()
        .iter()
        .map(|cmd| format!("{cmd}"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Build a Script from a list of commands.
fn build_script(cmds: Vec<Command>) -> Script {
    let mut s = Script::new();
    for c in cmds {
        s.push(c);
    }
    s
}

// ---------------------------------------------------------------------------
// Case 1: fn_spec_fn_verified
//
// fn_spec(f, |x: i32| x > 0 => result > 0)
// Axiom: (forall ((x Int)) (=> (> x 0) (> (f_impl env_f x) 0)))
// Check: NOT (forall x. x > 0 => f_impl(env_f, x) > 0) → UNSAT
// ---------------------------------------------------------------------------

#[test]
fn fn_spec_fn_verified() {
    let solver = solver_or_skip();

    let func = make_fn_func("f", ClosureTrait::Fn);
    let spec = FnSpec {
        closure_param: "f".to_string(),
        pre: "x > 0".to_string(),
        post: "result > 0".to_string(),
        bound_vars: vec!["x".to_string()],
    };

    let vcs = generate_fn_spec_vcs(&func, &[spec]);
    assert_eq!(vcs.len(), 1, "Expected exactly 1 VC for one fn_spec clause");

    let vc = &vcs[0];

    // Confirm the VC uses AUFLIA and has ClosureContract kind
    let script_str = vc
        .script
        .commands()
        .iter()
        .map(|c| c.to_string())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        script_str.contains("AUFLIA"),
        "VC must use AUFLIA logic, got:\n{script_str}"
    );

    // Build augmented script: original commands (without trailing check-sat) +
    // axiom constraining f_impl + check-sat
    let mut cmds = commands_without_check_sat(&vc.script);

    // Axiom: (forall ((x Int)) (=> (> x 0) (> (f_impl env_f x) 0)))
    // This says "f IS the correct function" — makes the negated entailment contradictory
    let axiom = Term::Forall(
        vec![("x".to_string(), Sort::Int)],
        Box::new(Term::Implies(
            Box::new(Term::IntGt(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::IntLit(0)),
            )),
            Box::new(Term::IntGt(
                Box::new(Term::App(
                    "f_impl".to_string(),
                    vec![
                        Term::Const("env_f".to_string()),
                        Term::Const("x".to_string()),
                    ],
                )),
                Box::new(Term::IntLit(0)),
            )),
        )),
    );
    cmds.push(Command::Assert(axiom));
    cmds.push(Command::CheckSat);

    let augmented_script = build_script(cmds);

    let result = solver.check_sat(&augmented_script).unwrap_or_else(|e| {
        panic!(
            "Z3 failed: {e}\nSMT:\n{}",
            script_to_smtlib(&augmented_script)
        )
    });

    assert!(
        matches!(result, SolverResult::Unsat),
        "fn_spec_fn_verified: with axiom constraining f, entailment must hold (UNSAT). Got: {result:?}\nSMT:\n{}",
        script_to_smtlib(&augmented_script)
    );
}

// ---------------------------------------------------------------------------
// Case 2: fn_spec_fn_falsified
//
// fn_spec(f, |x: i32| x > 0 => result > 0)
// No axiom — uninterpreted f can violate the spec
// Expected: SAT (Z3 finds f that violates)
// ---------------------------------------------------------------------------

#[test]
fn fn_spec_fn_falsified() {
    let solver = solver_or_skip();

    let func = make_fn_func("f", ClosureTrait::Fn);
    let spec = FnSpec {
        closure_param: "f".to_string(),
        pre: "x > 0".to_string(),
        post: "result > 0".to_string(),
        bound_vars: vec!["x".to_string()],
    };

    let vcs = generate_fn_spec_vcs(&func, &[spec]);
    assert_eq!(vcs.len(), 1);

    let vc = &vcs[0];
    // Run the VC as-is — no axiom about f, so the uninterpreted function is free
    let result = solver
        .check_sat(&vc.script)
        .unwrap_or_else(|e| panic!("Z3 failed: {e}\nSMT:\n{}", script_to_smtlib(&vc.script)));

    assert!(
        matches!(result, SolverResult::Sat(_)),
        "fn_spec_fn_falsified: without axiom, uninterpreted f can violate spec (SAT). Got: {result:?}\nSMT:\n{}",
        script_to_smtlib(&vc.script)
    );
}

// ---------------------------------------------------------------------------
// Case 3: fn_spec_fn_trivially_true
//
// fn_spec(f, |x: i32| false => result > 0)
// Precondition is `false` — vacuously true for any f
// Expected: UNSAT (NOT(forall x. false => ...) = NOT(true) = false → UNSAT)
// ---------------------------------------------------------------------------

#[test]
fn fn_spec_fn_trivially_true() {
    let solver = solver_or_skip();

    let func = make_fn_func("f", ClosureTrait::Fn);
    let spec = FnSpec {
        closure_param: "f".to_string(),
        pre: "false".to_string(),
        post: "result > 0".to_string(),
        bound_vars: vec!["x".to_string()],
    };

    let vcs = generate_fn_spec_vcs(&func, &[spec]);
    assert_eq!(vcs.len(), 1);

    let vc = &vcs[0];
    let result = solver
        .check_sat(&vc.script)
        .unwrap_or_else(|e| panic!("Z3 failed: {e}\nSMT:\n{}", script_to_smtlib(&vc.script)));

    assert!(
        matches!(result, SolverResult::Unsat),
        "fn_spec_fn_trivially_true: unsatisfiable precondition => vacuously true (UNSAT). Got: {result:?}\nSMT:\n{}",
        script_to_smtlib(&vc.script)
    );
}

// ---------------------------------------------------------------------------
// Case 4: fn_spec_fnmut_verified
//
// Closure captures `count: i32`.
// fn_spec(inc, |x: i32| x > 0 => result == env_before_count + x)
// Axiom: inc_impl IS the correct increment: result = env_before_count + x
// Expected: UNSAT
// ---------------------------------------------------------------------------

#[test]
fn fn_spec_fnmut_verified() {
    let solver = solver_or_skip();

    let func = make_fnmut_func("inc");
    let spec = FnSpec {
        closure_param: "inc".to_string(),
        pre: "x > 0".to_string(),
        // post uses env_before_count (the captured variable before mutation)
        post: "result == env_before_count + x".to_string(),
        bound_vars: vec!["x".to_string()],
    };

    let vcs = generate_fn_spec_vcs(&func, &[spec]);
    assert_eq!(vcs.len(), 1);

    let vc = &vcs[0];

    // Confirm env_before_count is present
    let script_str = vc
        .script
        .commands()
        .iter()
        .map(|c| c.to_string())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        script_str.contains("env_before_count"),
        "FnMut VC must declare env_before_count\nSMT:\n{script_str}"
    );

    // Build augmented script with axiom that inc_impl is correct:
    // (forall ((x Int)) (=> (> x 0) (= (inc_impl env_inc x) (+ env_before_count x))))
    let mut cmds = commands_without_check_sat(&vc.script);

    let axiom = Term::Forall(
        vec![("x".to_string(), Sort::Int)],
        Box::new(Term::Implies(
            Box::new(Term::IntGt(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::IntLit(0)),
            )),
            Box::new(Term::Eq(
                Box::new(Term::App(
                    "inc_impl".to_string(),
                    vec![
                        Term::Const("env_inc".to_string()),
                        Term::Const("x".to_string()),
                    ],
                )),
                Box::new(Term::IntAdd(
                    Box::new(Term::Const("env_before_count".to_string())),
                    Box::new(Term::Const("x".to_string())),
                )),
            )),
        )),
    );
    cmds.push(Command::Assert(axiom));
    cmds.push(Command::CheckSat);

    let augmented_script = build_script(cmds);

    let result = solver.check_sat(&augmented_script).unwrap_or_else(|e| {
        panic!(
            "Z3 failed: {e}\nSMT:\n{}",
            script_to_smtlib(&augmented_script)
        )
    });

    assert!(
        matches!(result, SolverResult::Unsat),
        "fn_spec_fnmut_verified: with axiom that inc IS correct, entailment holds (UNSAT). Got: {result:?}\nSMT:\n{}",
        script_to_smtlib(&augmented_script)
    );
}

// ---------------------------------------------------------------------------
// Case 5: fn_spec_fnmut_falsified
//
// Same FnMut setup but wrong postcondition: result == env_before_count + x + 1
// No axiom about inc_impl — uninterpreted function is free
// Expected: SAT (counterexample: inc that returns anything)
// ---------------------------------------------------------------------------

#[test]
fn fn_spec_fnmut_falsified() {
    let solver = solver_or_skip();

    let func = make_fnmut_func("inc");
    let spec = FnSpec {
        closure_param: "inc".to_string(),
        pre: "x > 0".to_string(),
        // Wrong postcondition (off by 1)
        post: "result == env_before_count + x + 1".to_string(),
        bound_vars: vec!["x".to_string()],
    };

    let vcs = generate_fn_spec_vcs(&func, &[spec]);
    assert_eq!(vcs.len(), 1);

    let vc = &vcs[0];
    // Run as-is — no axiom, uninterpreted inc_impl is free, so SAT is expected
    let result = solver
        .check_sat(&vc.script)
        .unwrap_or_else(|e| panic!("Z3 failed: {e}\nSMT:\n{}", script_to_smtlib(&vc.script)));

    assert!(
        matches!(result, SolverResult::Sat(_)),
        "fn_spec_fnmut_falsified: without axiom, uninterpreted inc can violate spec (SAT). Got: {result:?}\nSMT:\n{}",
        script_to_smtlib(&vc.script)
    );
}

// ---------------------------------------------------------------------------
// Case 6: fn_spec_fnonce_single_call
//
// FnOnce closure: fn_spec(consume, |x: i32| x > 0 => result > 0)
// Verify: FnOnce uses same code path as Fn (no env_before/after)
// With axiom: UNSAT
// ---------------------------------------------------------------------------

#[test]
fn fn_spec_fnonce_single_call() {
    let solver = solver_or_skip();

    let func = make_fn_func("consume", ClosureTrait::FnOnce);
    let spec = FnSpec {
        closure_param: "consume".to_string(),
        pre: "x > 0".to_string(),
        post: "result > 0".to_string(),
        bound_vars: vec!["x".to_string()],
    };

    let vcs = generate_fn_spec_vcs(&func, &[spec]);
    assert_eq!(vcs.len(), 1);

    let vc = &vcs[0];

    // Confirm no env_before/after constants (FnOnce uses same path as Fn)
    let script_str = vc
        .script
        .commands()
        .iter()
        .map(|c| c.to_string())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        !script_str.contains("env_before_"),
        "FnOnce VC must NOT contain env_before constants\nSMT:\n{script_str}"
    );
    assert!(
        !script_str.contains("env_after_"),
        "FnOnce VC must NOT contain env_after constants\nSMT:\n{script_str}"
    );
    assert!(
        script_str.contains("AUFLIA"),
        "FnOnce VC must use AUFLIA logic\nSMT:\n{script_str}"
    );

    // Build augmented script with axiom constraining consume_impl
    let mut cmds = commands_without_check_sat(&vc.script);

    let axiom = Term::Forall(
        vec![("x".to_string(), Sort::Int)],
        Box::new(Term::Implies(
            Box::new(Term::IntGt(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::IntLit(0)),
            )),
            Box::new(Term::IntGt(
                Box::new(Term::App(
                    "consume_impl".to_string(),
                    vec![
                        Term::Const("env_consume".to_string()),
                        Term::Const("x".to_string()),
                    ],
                )),
                Box::new(Term::IntLit(0)),
            )),
        )),
    );
    cmds.push(Command::Assert(axiom));
    cmds.push(Command::CheckSat);

    let augmented_script = build_script(cmds);

    let result = solver.check_sat(&augmented_script).unwrap_or_else(|e| {
        panic!(
            "Z3 failed: {e}\nSMT:\n{}",
            script_to_smtlib(&augmented_script)
        )
    });

    assert!(
        matches!(result, SolverResult::Unsat),
        "fn_spec_fnonce_single_call: with axiom, FnOnce entailment holds (UNSAT). Got: {result:?}\nSMT:\n{}",
        script_to_smtlib(&augmented_script)
    );
}
