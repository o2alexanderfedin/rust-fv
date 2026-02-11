//! Performance benchmarks for VCGen and end-to-end verification.
//!
//! Establishes the PERF-01 baseline: single-function contract verification
//! must complete in under 1 second.
//!
//! Benchmark groups:
//! - `vcgen_*`: Pure VCGen (IR -> SMT-LIB scripts), no solver involved
//! - `e2e_*`: Full pipeline (IR -> VCGen -> Z3 solving)

use criterion::{Criterion, criterion_group, criterion_main};
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen;

// ---------------------------------------------------------------------------
// Test function constructors
// ---------------------------------------------------------------------------

/// Simple: `fn add(a: i32, b: i32) -> i32 { a + b }` with overflow check.
fn make_add_function() -> Function {
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
        contracts: Contracts::default(),
        generic_params: vec![],
        prophecies: vec![],
        loops: vec![],
    }
}

/// Branching: `fn max(a: i32, b: i32) -> i32 { if a > b { a } else { b } }`
/// 3 basic blocks with SwitchInt terminator.
fn make_max_function() -> Function {
    Function {
        name: "max".to_string(),
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
        locals: vec![Local {
            name: "_3".to_string(),
            ty: Ty::Bool,
            is_ghost: false,
        }],
        basic_blocks: vec![
            // bb0: _3 = _1 > _2; switchInt(_3)
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_2")),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_3")),
                    targets: vec![(1, 1)],
                    otherwise: 2,
                },
            },
            // bb1: _0 = _1; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_1"))),
                )],
                terminator: Terminator::Return,
            },
            // bb2: _0 = _2; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_2"))),
                )],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result >= _1 && result >= _2".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
        },
        generic_params: vec![],
        prophecies: vec![],
        loops: vec![],
    }
}

/// Complex: simulates a realistic small function with 5+ basic blocks,
/// multiple branches, and arithmetic operations.
///
/// Modeled after:
/// ```text
/// fn clamp(val: i32, lo: i32, hi: i32) -> i32 {
///     if val < lo { lo }
///     else if val > hi { hi }
///     else { val }
/// }
/// ```
///
/// This produces 5 basic blocks:
///   bb0: _5 = _1 < _2; switchInt(_5) -> [true: bb1, false: bb2]
///   bb1: _0 = _2; return
///   bb2: _6 = _1 > _3; switchInt(_6) -> [true: bb3, false: bb4]
///   bb3: _0 = _3; return
///   bb4: _0 = _1; return
fn make_complex_function() -> Function {
    Function {
        name: "clamp".to_string(),
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
            Local {
                name: "_3".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
        ],
        locals: vec![
            Local {
                name: "_4".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
            Local {
                name: "_5".to_string(),
                ty: Ty::Bool,
                is_ghost: false,
            },
            Local {
                name: "_6".to_string(),
                ty: Ty::Bool,
                is_ghost: false,
            },
        ],
        basic_blocks: vec![
            // bb0: _5 = _1 < _2; switchInt(_5)
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_5"),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_2")),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_5")),
                    targets: vec![(1, 1)],
                    otherwise: 2,
                },
            },
            // bb1: _0 = _2; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_2"))),
                )],
                terminator: Terminator::Return,
            },
            // bb2: _6 = _1 > _3; switchInt(_6)
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_6"),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_3")),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_6")),
                    targets: vec![(1, 3)],
                    otherwise: 4,
                },
            },
            // bb3: _0 = _3; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_3"))),
                )],
                terminator: Terminator::Return,
            },
            // bb4: _0 = _1; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_1"))),
                )],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_2 <= _3".to_string(),
            }],
            ensures: vec![
                SpecExpr {
                    raw: "result >= _2".to_string(),
                },
                SpecExpr {
                    raw: "result <= _3".to_string(),
                },
            ],
            invariants: vec![],
            is_pure: true,
        },
        generic_params: vec![],
        prophecies: vec![],
        loops: vec![],
    }
}

// ---------------------------------------------------------------------------
// SMT-LIB formatting (mirrors e2e_verification.rs helpers)
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
        SmtCmd::GetModel => {
            out.push_str("(get-model)");
        }
        SmtCmd::Comment(text) => {
            out.push_str(&format!(";; {text}"));
        }
        SmtCmd::Exit => {
            out.push_str("(exit)");
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
        Sort::Real => out.push_str("Real"),
        Sort::BitVec(n) => out.push_str(&format!("(_ BitVec {n})")),
        Sort::Array(idx, elem) => {
            out.push_str("(Array ");
            format_sort(out, idx);
            out.push(' ');
            format_sort(out, elem);
            out.push(')');
        }
        Sort::Datatype(name) | Sort::Uninterpreted(name) => out.push_str(name),
        Sort::Float(e, s) => out.push_str(&format!("(_ FloatingPoint {e} {s})")),
    }
}

fn format_term(out: &mut String, term: &rust_fv_smtlib::term::Term) {
    use rust_fv_smtlib::term::Term;
    match term {
        Term::BoolLit(true) => out.push_str("true"),
        Term::BoolLit(false) => out.push_str("false"),
        Term::IntLit(n) => {
            if *n < 0 {
                out.push_str(&format!("(- {})", -n));
            } else {
                out.push_str(&format!("{n}"));
            }
        }
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
        Term::Not(t) => {
            out.push_str("(not ");
            format_term(out, t);
            out.push(')');
        }
        Term::And(terms) => format_nary(out, "and", terms),
        Term::Or(terms) => format_nary(out, "or", terms),
        Term::Implies(a, b) => format_binary(out, "=>", a, b),
        Term::Iff(a, b) | Term::Eq(a, b) => format_binary(out, "=", a, b),
        Term::Distinct(terms) => format_nary(out, "distinct", terms),
        Term::Ite(c, t, e) => {
            out.push_str("(ite ");
            format_term(out, c);
            out.push(' ');
            format_term(out, t);
            out.push(' ');
            format_term(out, e);
            out.push(')');
        }
        Term::BvAdd(a, b) => format_binary(out, "bvadd", a, b),
        Term::BvSub(a, b) => format_binary(out, "bvsub", a, b),
        Term::BvMul(a, b) => format_binary(out, "bvmul", a, b),
        Term::BvSDiv(a, b) => format_binary(out, "bvsdiv", a, b),
        Term::BvUDiv(a, b) => format_binary(out, "bvudiv", a, b),
        Term::BvSRem(a, b) => format_binary(out, "bvsrem", a, b),
        Term::BvURem(a, b) => format_binary(out, "bvurem", a, b),
        Term::BvNeg(a) => {
            out.push_str("(bvneg ");
            format_term(out, a);
            out.push(')');
        }
        Term::BvSLt(a, b) => format_binary(out, "bvslt", a, b),
        Term::BvSLe(a, b) => format_binary(out, "bvsle", a, b),
        Term::BvSGt(a, b) => format_binary(out, "bvsgt", a, b),
        Term::BvSGe(a, b) => format_binary(out, "bvsge", a, b),
        Term::BvULt(a, b) => format_binary(out, "bvult", a, b),
        Term::BvULe(a, b) => format_binary(out, "bvule", a, b),
        Term::BvUGt(a, b) => format_binary(out, "bvugt", a, b),
        Term::BvUGe(a, b) => format_binary(out, "bvuge", a, b),
        Term::BvAnd(a, b) => format_binary(out, "bvand", a, b),
        Term::BvOr(a, b) => format_binary(out, "bvor", a, b),
        Term::BvXor(a, b) => format_binary(out, "bvxor", a, b),
        Term::BvNot(a) => {
            out.push_str("(bvnot ");
            format_term(out, a);
            out.push(')');
        }
        Term::BvShl(a, b) => format_binary(out, "bvshl", a, b),
        Term::BvLShr(a, b) => format_binary(out, "bvlshr", a, b),
        Term::BvAShr(a, b) => format_binary(out, "bvashr", a, b),
        Term::ZeroExtend(n, a) => {
            out.push_str(&format!("((_ zero_extend {n}) "));
            format_term(out, a);
            out.push(')');
        }
        Term::SignExtend(n, a) => {
            out.push_str(&format!("((_ sign_extend {n}) "));
            format_term(out, a);
            out.push(')');
        }
        Term::Extract(hi, lo, a) => {
            out.push_str(&format!("((_ extract {hi} {lo}) "));
            format_term(out, a);
            out.push(')');
        }
        Term::Concat(a, b) => format_binary(out, "concat", a, b),
        Term::Bv2Int(a) => {
            out.push_str("(bv2int ");
            format_term(out, a);
            out.push(')');
        }
        Term::Int2Bv(n, a) => {
            out.push_str(&format!("((_ int2bv {n}) "));
            format_term(out, a);
            out.push(')');
        }
        Term::IntAdd(a, b) => format_binary(out, "+", a, b),
        Term::IntSub(a, b) => format_binary(out, "-", a, b),
        Term::IntMul(a, b) => format_binary(out, "*", a, b),
        Term::IntDiv(a, b) => format_binary(out, "div", a, b),
        Term::IntMod(a, b) => format_binary(out, "mod", a, b),
        Term::IntNeg(a) => {
            out.push_str("(- ");
            format_term(out, a);
            out.push(')');
        }
        Term::IntLt(a, b) => format_binary(out, "<", a, b),
        Term::IntLe(a, b) => format_binary(out, "<=", a, b),
        Term::IntGt(a, b) => format_binary(out, ">", a, b),
        Term::IntGe(a, b) => format_binary(out, ">=", a, b),
        Term::Select(a, i) => format_binary(out, "select", a, i),
        Term::Store(a, i, v) => {
            out.push_str("(store ");
            format_term(out, a);
            out.push(' ');
            format_term(out, i);
            out.push(' ');
            format_term(out, v);
            out.push(')');
        }
        Term::Forall(bindings, body) => {
            out.push_str("(forall (");
            for (i, (name, sort)) in bindings.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                out.push_str(&format!("({name} "));
                format_sort(out, sort);
                out.push(')');
            }
            out.push_str(") ");
            format_term(out, body);
            out.push(')');
        }
        Term::Exists(bindings, body) => {
            out.push_str("(exists (");
            for (i, (name, sort)) in bindings.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                out.push_str(&format!("({name} "));
                format_sort(out, sort);
                out.push(')');
            }
            out.push_str(") ");
            format_term(out, body);
            out.push(')');
        }
        Term::Let(bindings, body) => {
            out.push_str("(let (");
            for (i, (name, val)) in bindings.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                out.push_str(&format!("({name} "));
                format_term(out, val);
                out.push(')');
            }
            out.push_str(") ");
            format_term(out, body);
            out.push(')');
        }
        Term::App(func, args) => {
            out.push_str(&format!("({func}"));
            for arg in args {
                out.push(' ');
                format_term(out, arg);
            }
            out.push(')');
        }
        Term::Annotated(body, annotations) => {
            if annotations.is_empty() {
                format_term(out, body);
            } else {
                out.push_str("(! ");
                format_term(out, body);
                for (key, values) in annotations {
                    out.push_str(&format!(" :{key} ("));
                    for (i, val) in values.iter().enumerate() {
                        if i > 0 {
                            out.push(' ');
                        }
                        format_term(out, val);
                    }
                    out.push(')');
                }
                out.push(')');
            }
        }
    }
}

fn format_binary(
    out: &mut String,
    op: &str,
    a: &rust_fv_smtlib::term::Term,
    b: &rust_fv_smtlib::term::Term,
) {
    out.push_str(&format!("({op} "));
    format_term(out, a);
    out.push(' ');
    format_term(out, b);
    out.push(')');
}

fn format_nary(out: &mut String, op: &str, terms: &[rust_fv_smtlib::term::Term]) {
    out.push_str(&format!("({op}"));
    for t in terms {
        out.push(' ');
        format_term(out, t);
    }
    out.push(')');
}

// ---------------------------------------------------------------------------
// VCGen-only benchmarks (pure, no solver)
// ---------------------------------------------------------------------------

fn bench_vcgen_simple_add(c: &mut Criterion) {
    let func = make_add_function();
    c.bench_function("vcgen_simple_add", |b| {
        b.iter(|| vcgen::generate_vcs(&func, None));
    });
}

fn bench_vcgen_max_function(c: &mut Criterion) {
    let func = make_max_function();
    c.bench_function("vcgen_max_function", |b| {
        b.iter(|| vcgen::generate_vcs(&func, None));
    });
}

fn bench_vcgen_complex_function(c: &mut Criterion) {
    let func = make_complex_function();
    c.bench_function("vcgen_complex_function", |b| {
        b.iter(|| vcgen::generate_vcs(&func, None));
    });
}

// ---------------------------------------------------------------------------
// End-to-end benchmarks (VCGen + Z3)
// ---------------------------------------------------------------------------

fn bench_e2e_simple_add(c: &mut Criterion) {
    let solver = match rust_fv_solver::Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Z3 not available, skipping E2E bench: {e}");
            return;
        }
    };
    let func = make_add_function();
    c.bench_function("e2e_simple_add", |b| {
        b.iter(|| {
            let vcs = vcgen::generate_vcs(&func, None);
            for vc in &vcs.conditions {
                let smtlib = script_to_smtlib(&vc.script);
                let _ = solver.check_sat_raw(&smtlib);
            }
        });
    });
}

fn bench_e2e_max_function(c: &mut Criterion) {
    let solver = match rust_fv_solver::Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Z3 not available, skipping E2E bench: {e}");
            return;
        }
    };
    let func = make_max_function();
    c.bench_function("e2e_max_function", |b| {
        b.iter(|| {
            let vcs = vcgen::generate_vcs(&func, None);
            for vc in &vcs.conditions {
                let smtlib = script_to_smtlib(&vc.script);
                let _ = solver.check_sat_raw(&smtlib);
            }
        });
    });
}

fn bench_e2e_complex_function(c: &mut Criterion) {
    let solver = match rust_fv_solver::Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Z3 not available, skipping E2E bench: {e}");
            return;
        }
    };
    let func = make_complex_function();
    c.bench_function("e2e_complex_function", |b| {
        b.iter(|| {
            let vcs = vcgen::generate_vcs(&func, None);
            for vc in &vcs.conditions {
                let smtlib = script_to_smtlib(&vc.script);
                let _ = solver.check_sat_raw(&smtlib);
            }
        });
    });
}

// ---------------------------------------------------------------------------
// Criterion groups and main
// ---------------------------------------------------------------------------

criterion_group!(
    vcgen_benches,
    bench_vcgen_simple_add,
    bench_vcgen_max_function,
    bench_vcgen_complex_function,
);

criterion_group!(
    e2e_benches,
    bench_e2e_simple_add,
    bench_e2e_max_function,
    bench_e2e_complex_function,
);

criterion_main!(vcgen_benches, e2e_benches);
