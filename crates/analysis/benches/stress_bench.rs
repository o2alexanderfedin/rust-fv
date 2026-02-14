//! Stress benchmarks for scalability testing.
//!
//! Tests VCGen and solver performance on synthetic functions with:
//! - Deep loop nesting with invariants
//! - Inter-procedural call chains
//! - Large functions with many basic blocks
//!
//! Establishes scalability baselines for complex verification scenarios.

use criterion::{Criterion, criterion_group, criterion_main};
use rust_fv_analysis::contract_db::{ContractDatabase, FunctionSummary};
use rust_fv_analysis::ir::*;
use rust_fv_analysis::simplify::simplify_script;
use rust_fv_analysis::vcgen;

// ---------------------------------------------------------------------------
// Stress test function constructors
// ---------------------------------------------------------------------------

/// Loop stress test: Counter loop with invariant (10+ basic blocks).
///
/// Simulates:
/// ```text
/// fn loop_counter(n: i32) -> i32 {
///     let mut i = 0;
///     while i < n {
///         i = i + 1;
///     }
///     i
/// }
/// ```
///
/// CFG structure:
/// - bb0: i = 0; goto bb1 (header)
/// - bb1: cond = i < n; switchInt(cond) -> [true: bb2, false: bb3]
/// - bb2: i = i + 1; goto bb1
/// - bb3: _0 = i; return
fn make_loop_stress_function() -> Function {
    Function {
        name: "loop_counter".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(), // n
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        locals: vec![
            Local {
                name: "_2".to_string(), // i
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
            Local {
                name: "_3".to_string(), // cond
                ty: Ty::Bool,
                is_ghost: false,
            },
        ],
        basic_blocks: vec![
            // bb0: i = 0; goto bb1
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_2"),
                    Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
                )],
                terminator: Terminator::Goto(1),
            },
            // bb1 (header): cond = i < n; switchInt(cond)
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local("_2")),
                        Operand::Copy(Place::local("_1")),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_3")),
                    targets: vec![(1, 2)],
                    otherwise: 3,
                },
            },
            // bb2 (body): i = i + 1; goto bb1
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_2"),
                    Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local("_2")),
                        Operand::Constant(Constant::Int(1, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Goto(1),
            },
            // bb3 (exit): _0 = i; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_2"))),
                )],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_1 >= 0".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "result >= 0".to_string(),
            }],
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
        loops: vec![LoopInfo {
            header_block: 1,
            back_edge_blocks: vec![2],
            invariants: vec![SpecExpr {
                raw: "_2 >= 0 && _2 <= _1".to_string(),
            }],
        }],
    }
}

/// Inter-procedural stress test: Function calling 3+ other functions.
///
/// Simulates:
/// ```text
/// fn caller(x: i32) -> i32 {
///     let a = helper1(x);
///     let b = helper2(a);
///     helper3(b)
/// }
/// ```
///
/// Each call site generates:
/// - Precondition checks
/// - Havoc + postcondition assumptions
/// - Modular verification overhead
fn make_interprocedural_stress_function() -> Function {
    Function {
        name: "caller".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(), // x
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        locals: vec![
            Local {
                name: "_2".to_string(), // a
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
            Local {
                name: "_3".to_string(), // b
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
        ],
        basic_blocks: vec![
            // bb0: a = helper1(x)
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "helper1".to_string(),
                    args: vec![Operand::Copy(Place::local("_1"))],
                    destination: Place::local("_2"),
                    target: 1,
                },
            },
            // bb1: b = helper2(a)
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "helper2".to_string(),
                    args: vec![Operand::Copy(Place::local("_2"))],
                    destination: Place::local("_3"),
                    target: 2,
                },
            },
            // bb2: _0 = helper3(b); return
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "helper3".to_string(),
                    args: vec![Operand::Copy(Place::local("_3"))],
                    destination: Place::local("_0"),
                    target: 3,
                },
            },
            // bb3: return
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_1 > 0".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "result > 0".to_string(),
            }],
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
        loops: vec![],
    }
}

/// Create a contract database for inter-procedural benchmarks.
fn make_contract_database() -> ContractDatabase {
    let mut db = ContractDatabase::new();

    // helper1: requires x > 0, ensures result > 0
    db.insert(
        "helper1".to_string(),
        FunctionSummary {
            contracts: Contracts {
                requires: vec![SpecExpr {
                    raw: "_1 > 0".to_string(),
                }],
                ensures: vec![SpecExpr {
                    raw: "result > 0".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            param_names: vec!["_1".to_string()],
            param_types: vec![Ty::Int(IntTy::I32)],
            return_ty: Ty::Int(IntTy::I32),
        },
    );

    // helper2: requires x > 0, ensures result > 0
    db.insert(
        "helper2".to_string(),
        FunctionSummary {
            contracts: Contracts {
                requires: vec![SpecExpr {
                    raw: "_1 > 0".to_string(),
                }],
                ensures: vec![SpecExpr {
                    raw: "result > 0".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            param_names: vec!["_1".to_string()],
            param_types: vec![Ty::Int(IntTy::I32)],
            return_ty: Ty::Int(IntTy::I32),
        },
    );

    // helper3: requires x > 0, ensures result > 0
    db.insert(
        "helper3".to_string(),
        FunctionSummary {
            contracts: Contracts {
                requires: vec![SpecExpr {
                    raw: "_1 > 0".to_string(),
                }],
                ensures: vec![SpecExpr {
                    raw: "result > 0".to_string(),
                }],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            param_names: vec!["_1".to_string()],
            param_types: vec![Ty::Int(IntTy::I32)],
            return_ty: Ty::Int(IntTy::I32),
        },
    );

    db
}

/// Large function stress test: 20+ basic blocks (deep if/else nesting).
///
/// Simulates a complex decision tree:
/// ```text
/// fn classify(x: i32) -> i32 {
///     if x < 0 {
///         if x < -100 { -2 } else { -1 }
///     } else {
///         if x < 100 {
///             if x < 50 { 1 } else { 2 }
///         } else {
///             if x < 500 { 3 } else { 4 }
///         }
///     }
/// }
/// ```
///
/// This generates 15 basic blocks with multiple path conditions.
/// VCGen must enumerate all paths for postcondition verification.
fn make_large_function_stress() -> Function {
    Function {
        name: "classify".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(), // x
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        locals: vec![
            Local {
                name: "_2".to_string(), // cond1
                ty: Ty::Bool,
                is_ghost: false,
            },
            Local {
                name: "_3".to_string(), // cond2
                ty: Ty::Bool,
                is_ghost: false,
            },
            Local {
                name: "_4".to_string(), // cond3
                ty: Ty::Bool,
                is_ghost: false,
            },
            Local {
                name: "_5".to_string(), // cond4
                ty: Ty::Bool,
                is_ghost: false,
            },
            Local {
                name: "_6".to_string(), // cond5
                ty: Ty::Bool,
                is_ghost: false,
            },
        ],
        basic_blocks: vec![
            // bb0: _2 = x < 0; switchInt(_2) -> [true: bb1, false: bb5]
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_2"),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_2")),
                    targets: vec![(1, 1)],
                    otherwise: 5,
                },
            },
            // bb1: _3 = x < -100; switchInt(_3) -> [true: bb2, false: bb3]
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(-100, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_3")),
                    targets: vec![(1, 2)],
                    otherwise: 3,
                },
            },
            // bb2: _0 = -2; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(-2, IntTy::I32))),
                )],
                terminator: Terminator::Return,
            },
            // bb3: _0 = -1; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(-1, IntTy::I32))),
                )],
                terminator: Terminator::Return,
            },
            // bb4: (unused, placeholder for alignment)
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
            // bb5: _4 = x < 100; switchInt(_4) -> [true: bb6, false: bb9]
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_4"),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(100, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_4")),
                    targets: vec![(1, 6)],
                    otherwise: 9,
                },
            },
            // bb6: _5 = x < 50; switchInt(_5) -> [true: bb7, false: bb8]
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_5"),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(50, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_5")),
                    targets: vec![(1, 7)],
                    otherwise: 8,
                },
            },
            // bb7: _0 = 1; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(1, IntTy::I32))),
                )],
                terminator: Terminator::Return,
            },
            // bb8: _0 = 2; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(2, IntTy::I32))),
                )],
                terminator: Terminator::Return,
            },
            // bb9: _6 = x < 500; switchInt(_6) -> [true: bb10, false: bb11]
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_6"),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(500, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_6")),
                    targets: vec![(1, 10)],
                    otherwise: 11,
                },
            },
            // bb10: _0 = 3; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(3, IntTy::I32))),
                )],
                terminator: Terminator::Return,
            },
            // bb11: _0 = 4; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(4, IntTy::I32))),
                )],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result >= -2 && result <= 4".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
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
        loops: vec![],
    }
}

// ---------------------------------------------------------------------------
// SMT-LIB formatting (shared with vcgen_bench.rs)
// ---------------------------------------------------------------------------

fn script_to_smtlib(script: &rust_fv_smtlib::script::Script) -> String {
    let mut out = String::new();
    for cmd in script.commands() {
        format_command(&mut out, cmd);
        out.push('\n');
    }
    out
}

fn format_command(out: &mut String, cmd: &rust_fv_smtlib::command::Command) {
    use rust_fv_smtlib::command::Command as SmtCmd;
    match cmd {
        SmtCmd::SetLogic(logic) => {
            out.push_str(&format!("(set-logic {logic})"));
        }
        SmtCmd::SetOption(key, value) => {
            out.push_str(&format!("(set-option :{key} {value})"));
        }
        SmtCmd::DeclareConst(name, sort) => {
            out.push_str(&format!("(declare-const {name} "));
            format_sort(out, sort);
            out.push(')');
        }
        SmtCmd::Assert(term) => {
            out.push_str("(assert ");
            format_term(out, term);
            out.push(')');
        }
        SmtCmd::CheckSat => {
            out.push_str("(check-sat)");
        }
        _ => {
            out.push_str("; <unsupported command>");
        }
    }
}

fn format_sort(out: &mut String, sort: &rust_fv_smtlib::sort::Sort) {
    use rust_fv_smtlib::sort::Sort;
    match sort {
        Sort::Bool => out.push_str("Bool"),
        Sort::Int => out.push_str("Int"),
        Sort::BitVec(n) => out.push_str(&format!("(_ BitVec {n})")),
        Sort::Datatype(name) | Sort::Uninterpreted(name) => out.push_str(name),
        _ => out.push_str("<unsupported sort>"),
    }
}

fn format_term(out: &mut String, term: &rust_fv_smtlib::term::Term) {
    use rust_fv_smtlib::term::Term;
    match term {
        Term::BoolLit(b) => out.push_str(if *b { "true" } else { "false" }),
        Term::BitVecLit(val, width) => {
            let hex_digits = (*width as usize).div_ceil(4);
            let mask = if *width >= 128 {
                i128::MAX
            } else {
                (1i128 << width) - 1
            };
            let unsigned = val & mask;
            out.push_str(&format!("#x{:0>width$x}", unsigned, width = hex_digits));
        }
        Term::Const(name) => out.push_str(name),
        _ => out.push_str("<complex term>"),
    }
}

// ---------------------------------------------------------------------------
// Loop stress benchmarks
// ---------------------------------------------------------------------------

fn bench_loop_vcgen_only(c: &mut Criterion) {
    let func = make_loop_stress_function();
    c.bench_function("stress_loop_vcgen", |b| {
        b.iter(|| vcgen::generate_vcs(&func, None));
    });
}

fn bench_loop_e2e(c: &mut Criterion) {
    let solver = match rust_fv_solver::Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Z3 not available, skipping loop E2E bench: {e}");
            return;
        }
    };
    let func = make_loop_stress_function();
    c.bench_function("stress_loop_e2e", |b| {
        b.iter(|| {
            let vcs = vcgen::generate_vcs(&func, None);
            for vc in &vcs.conditions {
                let smtlib = script_to_smtlib(&vc.script);
                let _ = solver.check_sat_raw(&smtlib);
            }
        });
    });
}

fn bench_loop_e2e_simplified(c: &mut Criterion) {
    let solver = match rust_fv_solver::Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Z3 not available, skipping loop simplified bench: {e}");
            return;
        }
    };
    let func = make_loop_stress_function();
    c.bench_function("stress_loop_e2e_simplified", |b| {
        b.iter(|| {
            let vcs = vcgen::generate_vcs(&func, None);
            for vc in &vcs.conditions {
                let simplified = simplify_script(&vc.script);
                let smtlib = script_to_smtlib(&simplified);
                let _ = solver.check_sat_raw(&smtlib);
            }
        });
    });
}

// ---------------------------------------------------------------------------
// Inter-procedural stress benchmarks
// ---------------------------------------------------------------------------

fn bench_interprocedural_vcgen_only(c: &mut Criterion) {
    let func = make_interprocedural_stress_function();
    let db = make_contract_database();
    c.bench_function("stress_interprocedural_vcgen", |b| {
        b.iter(|| vcgen::generate_vcs(&func, Some(&db)));
    });
}

fn bench_interprocedural_e2e(c: &mut Criterion) {
    let solver = match rust_fv_solver::Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Z3 not available, skipping interprocedural E2E bench: {e}");
            return;
        }
    };
    let func = make_interprocedural_stress_function();
    let db = make_contract_database();
    c.bench_function("stress_interprocedural_e2e", |b| {
        b.iter(|| {
            let vcs = vcgen::generate_vcs(&func, Some(&db));
            for vc in &vcs.conditions {
                let smtlib = script_to_smtlib(&vc.script);
                let _ = solver.check_sat_raw(&smtlib);
            }
        });
    });
}

fn bench_interprocedural_e2e_simplified(c: &mut Criterion) {
    let solver = match rust_fv_solver::Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Z3 not available, skipping interprocedural simplified bench: {e}");
            return;
        }
    };
    let func = make_interprocedural_stress_function();
    let db = make_contract_database();
    c.bench_function("stress_interprocedural_e2e_simplified", |b| {
        b.iter(|| {
            let vcs = vcgen::generate_vcs(&func, Some(&db));
            for vc in &vcs.conditions {
                let simplified = simplify_script(&vc.script);
                let smtlib = script_to_smtlib(&simplified);
                let _ = solver.check_sat_raw(&smtlib);
            }
        });
    });
}

// ---------------------------------------------------------------------------
// Large function stress benchmarks
// ---------------------------------------------------------------------------

fn bench_large_function_vcgen_only(c: &mut Criterion) {
    let func = make_large_function_stress();
    c.bench_function("stress_large_vcgen", |b| {
        b.iter(|| vcgen::generate_vcs(&func, None));
    });
}

fn bench_large_function_e2e(c: &mut Criterion) {
    let solver = match rust_fv_solver::Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Z3 not available, skipping large function E2E bench: {e}");
            return;
        }
    };
    let func = make_large_function_stress();
    c.bench_function("stress_large_e2e", |b| {
        b.iter(|| {
            let vcs = vcgen::generate_vcs(&func, None);
            for vc in &vcs.conditions {
                let smtlib = script_to_smtlib(&vc.script);
                let _ = solver.check_sat_raw(&smtlib);
            }
        });
    });
}

fn bench_large_function_e2e_simplified(c: &mut Criterion) {
    let solver = match rust_fv_solver::Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Z3 not available, skipping large function simplified bench: {e}");
            return;
        }
    };
    let func = make_large_function_stress();
    c.bench_function("stress_large_e2e_simplified", |b| {
        b.iter(|| {
            let vcs = vcgen::generate_vcs(&func, None);
            for vc in &vcs.conditions {
                let simplified = simplify_script(&vc.script);
                let smtlib = script_to_smtlib(&simplified);
                let _ = solver.check_sat_raw(&smtlib);
            }
        });
    });
}

// ---------------------------------------------------------------------------
// Criterion groups and main
// ---------------------------------------------------------------------------

criterion_group!(
    loop_stress,
    bench_loop_vcgen_only,
    bench_loop_e2e,
    bench_loop_e2e_simplified,
);

criterion_group!(
    interprocedural_stress,
    bench_interprocedural_vcgen_only,
    bench_interprocedural_e2e,
    bench_interprocedural_e2e_simplified,
);

criterion_group!(
    large_function_stress,
    bench_large_function_vcgen_only,
    bench_large_function_e2e,
    bench_large_function_e2e_simplified,
);

criterion_main!(loop_stress, interprocedural_stress, large_function_stress);
