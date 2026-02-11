//! Soundness test suite: programs with known bugs that MUST be rejected.
//!
//! Each test constructs an `ir::Function` with a known bug (overflow, wrong
//! postcondition, control-flow issue), runs `vcgen::generate_vcs()`, and
//! asserts that Z3 finds a counterexample (SAT).
//!
//! If Z3 is not installed, tests are skipped gracefully.

use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen;
use rust_fv_solver::Z3Solver;

// ---------------------------------------------------------------------------
// Helpers (duplicated from e2e_verification.rs for self-containment)
// ---------------------------------------------------------------------------

fn solver_or_skip() -> Z3Solver {
    match Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Skipping test -- Z3 not available: {e}");
            panic!("Z3_NOT_AVAILABLE: {e}");
        }
    }
}

fn script_to_smtlib(script: &rust_fv_smtlib::script::Script) -> String {
    let mut out = String::new();
    for cmd in script.commands() {
        format_command(&mut out, cmd);
        out.push('\n');
    }
    out
}

fn format_command(out: &mut String, cmd: &rust_fv_smtlib::command::Command) {
    use rust_fv_smtlib::command::Command as C;
    match cmd {
        C::SetLogic(l) => out.push_str(&format!("(set-logic {l})")),
        C::SetOption(k, v) => out.push_str(&format!("(set-option :{k} {v})")),
        C::DeclareConst(n, s) => {
            out.push_str(&format!("(declare-const {n} "));
            format_sort(out, s);
            out.push(')');
        }
        C::Assert(t) => {
            out.push_str("(assert ");
            format_term(out, t);
            out.push(')');
        }
        C::CheckSat => out.push_str("(check-sat)"),
        C::GetModel => out.push_str("(get-model)"),
        C::Comment(t) => out.push_str(&format!(";; {t}")),
        C::Exit => out.push_str("(exit)"),
        C::DeclareDatatype { name, variants } => {
            out.push_str(&format!("(declare-datatype {name} ("));
            for (i, variant) in variants.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                if variant.fields.is_empty() {
                    out.push_str(&format!("({})", variant.constructor));
                } else {
                    out.push_str(&format!("({}", variant.constructor));
                    for (field_name, field_sort) in &variant.fields {
                        out.push_str(&format!(" ({field_name} "));
                        format_sort(out, field_sort);
                        out.push(')');
                    }
                    out.push(')');
                }
            }
            out.push_str("))");
        }
        _ => out.push_str("; <unsupported>"),
    }
}

fn format_sort(out: &mut String, sort: &rust_fv_smtlib::sort::Sort) {
    use rust_fv_smtlib::sort::Sort;
    match sort {
        Sort::Bool => out.push_str("Bool"),
        Sort::Int => out.push_str("Int"),
        Sort::Real => out.push_str("Real"),
        Sort::BitVec(n) => out.push_str(&format!("(_ BitVec {n})")),
        Sort::Array(i, e) => {
            out.push_str("(Array ");
            format_sort(out, i);
            out.push(' ');
            format_sort(out, e);
            out.push(')');
        }
        Sort::Datatype(n) | Sort::Uninterpreted(n) => out.push_str(n),
        Sort::Float(e, s) => out.push_str(&format!("(_ FloatingPoint {e} {s})")),
    }
}

fn format_term(out: &mut String, term: &rust_fv_smtlib::term::Term) {
    use rust_fv_smtlib::term::Term as T;
    match term {
        T::BoolLit(true) => out.push_str("true"),
        T::BoolLit(false) => out.push_str("false"),
        T::IntLit(n) => {
            if *n < 0 {
                out.push_str(&format!("(- {})", -n));
            } else {
                out.push_str(&format!("{n}"));
            }
        }
        T::BitVecLit(val, width) => {
            let hex_digits = (*width as usize).div_ceil(4);
            let mask = if *width >= 128 {
                i128::MAX
            } else {
                (1i128 << width) - 1
            };
            let unsigned = val & mask;
            out.push_str(&format!("#x{:0>width$x}", unsigned, width = hex_digits));
        }
        T::Const(n) => out.push_str(n),
        T::Not(t) => {
            out.push_str("(not ");
            format_term(out, t);
            out.push(')');
        }
        T::And(ts) => fmt_nary(out, "and", ts),
        T::Or(ts) => fmt_nary(out, "or", ts),
        T::Implies(a, b) => fmt_bin(out, "=>", a, b),
        T::Iff(a, b) | T::Eq(a, b) => fmt_bin(out, "=", a, b),
        T::Distinct(ts) => fmt_nary(out, "distinct", ts),
        T::Ite(c, t, e) => {
            out.push_str("(ite ");
            format_term(out, c);
            out.push(' ');
            format_term(out, t);
            out.push(' ');
            format_term(out, e);
            out.push(')');
        }
        T::BvAdd(a, b) => fmt_bin(out, "bvadd", a, b),
        T::BvSub(a, b) => fmt_bin(out, "bvsub", a, b),
        T::BvMul(a, b) => fmt_bin(out, "bvmul", a, b),
        T::BvSDiv(a, b) => fmt_bin(out, "bvsdiv", a, b),
        T::BvUDiv(a, b) => fmt_bin(out, "bvudiv", a, b),
        T::BvSRem(a, b) => fmt_bin(out, "bvsrem", a, b),
        T::BvURem(a, b) => fmt_bin(out, "bvurem", a, b),
        T::BvNeg(a) => {
            out.push_str("(bvneg ");
            format_term(out, a);
            out.push(')');
        }
        T::BvSLt(a, b) => fmt_bin(out, "bvslt", a, b),
        T::BvSLe(a, b) => fmt_bin(out, "bvsle", a, b),
        T::BvSGt(a, b) => fmt_bin(out, "bvsgt", a, b),
        T::BvSGe(a, b) => fmt_bin(out, "bvsge", a, b),
        T::BvULt(a, b) => fmt_bin(out, "bvult", a, b),
        T::BvULe(a, b) => fmt_bin(out, "bvule", a, b),
        T::BvUGt(a, b) => fmt_bin(out, "bvugt", a, b),
        T::BvUGe(a, b) => fmt_bin(out, "bvuge", a, b),
        T::BvAnd(a, b) => fmt_bin(out, "bvand", a, b),
        T::BvOr(a, b) => fmt_bin(out, "bvor", a, b),
        T::BvXor(a, b) => fmt_bin(out, "bvxor", a, b),
        T::BvNot(a) => {
            out.push_str("(bvnot ");
            format_term(out, a);
            out.push(')');
        }
        T::BvShl(a, b) => fmt_bin(out, "bvshl", a, b),
        T::BvLShr(a, b) => fmt_bin(out, "bvlshr", a, b),
        T::BvAShr(a, b) => fmt_bin(out, "bvashr", a, b),
        T::ZeroExtend(n, a) => {
            out.push_str(&format!("((_ zero_extend {n}) "));
            format_term(out, a);
            out.push(')');
        }
        T::SignExtend(n, a) => {
            out.push_str(&format!("((_ sign_extend {n}) "));
            format_term(out, a);
            out.push(')');
        }
        T::Extract(hi, lo, a) => {
            out.push_str(&format!("((_ extract {hi} {lo}) "));
            format_term(out, a);
            out.push(')');
        }
        T::Concat(a, b) => fmt_bin(out, "concat", a, b),
        T::Bv2Int(a) => {
            out.push_str("(bv2int ");
            format_term(out, a);
            out.push(')');
        }
        T::Int2Bv(n, a) => {
            out.push_str(&format!("((_ int2bv {n}) "));
            format_term(out, a);
            out.push(')');
        }
        T::IntAdd(a, b) => fmt_bin(out, "+", a, b),
        T::IntSub(a, b) => fmt_bin(out, "-", a, b),
        T::IntMul(a, b) => fmt_bin(out, "*", a, b),
        T::IntDiv(a, b) => fmt_bin(out, "div", a, b),
        T::IntMod(a, b) => fmt_bin(out, "mod", a, b),
        T::IntNeg(a) => {
            out.push_str("(- ");
            format_term(out, a);
            out.push(')');
        }
        T::IntLt(a, b) => fmt_bin(out, "<", a, b),
        T::IntLe(a, b) => fmt_bin(out, "<=", a, b),
        T::IntGt(a, b) => fmt_bin(out, ">", a, b),
        T::IntGe(a, b) => fmt_bin(out, ">=", a, b),
        T::Select(a, i) => fmt_bin(out, "select", a, i),
        T::Store(a, i, v) => {
            out.push_str("(store ");
            format_term(out, a);
            out.push(' ');
            format_term(out, i);
            out.push(' ');
            format_term(out, v);
            out.push(')');
        }
        T::Forall(bs, body) => {
            out.push_str("(forall (");
            for (i, (n, s)) in bs.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                out.push_str(&format!("({n} "));
                format_sort(out, s);
                out.push(')');
            }
            out.push_str(") ");
            format_term(out, body);
            out.push(')');
        }
        T::Exists(bs, body) => {
            out.push_str("(exists (");
            for (i, (n, s)) in bs.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                out.push_str(&format!("({n} "));
                format_sort(out, s);
                out.push(')');
            }
            out.push_str(") ");
            format_term(out, body);
            out.push(')');
        }
        T::Let(bs, body) => {
            out.push_str("(let (");
            for (i, (n, v)) in bs.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                out.push_str(&format!("({n} "));
                format_term(out, v);
                out.push(')');
            }
            out.push_str(") ");
            format_term(out, body);
            out.push(')');
        }
        T::App(f, args) => {
            out.push_str(&format!("({f}"));
            for a in args {
                out.push(' ');
                format_term(out, a);
            }
            out.push(')');
        }
        T::Annotated(body, annotations) => {
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

fn fmt_bin(
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

fn fmt_nary(out: &mut String, op: &str, ts: &[rust_fv_smtlib::term::Term]) {
    out.push_str(&format!("({op}"));
    for t in ts {
        out.push(' ');
        format_term(out, t);
    }
    out.push(')');
}

/// Assert that overflow VCs exist and are all SAT.
fn assert_overflow_sat(vcs: &vcgen::FunctionVCs, solver: &Z3Solver, test_name: &str) {
    let overflow_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("overflow"))
        .collect();
    assert!(
        !overflow_vcs.is_empty(),
        "{test_name}: expected overflow VCs"
    );
    for vc in &overflow_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .unwrap_or_else(|e| panic!("{test_name}: Z3 error: {e}\nScript:\n{smtlib}"));
        assert!(
            result.is_sat(),
            "{test_name}: expected SAT for overflow VC, got {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

/// Assert that postcondition VCs exist and are all SAT.
fn assert_postcondition_sat(vcs: &vcgen::FunctionVCs, solver: &Z3Solver, test_name: &str) {
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(
        !post_vcs.is_empty(),
        "{test_name}: expected postcondition VCs"
    );
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .unwrap_or_else(|e| panic!("{test_name}: Z3 error: {e}\nScript:\n{smtlib}"));
        assert!(
            result.is_sat(),
            "{test_name}: expected SAT (wrong postcondition), got {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ===========================================================================
// Arithmetic overflow tests (8 tests)
// ===========================================================================

/// 1. i32::MAX + 1 overflows without precondition
#[test]
fn snd_signed_add_overflow() {
    let func = Function {
        name: "signed_add".to_string(),
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_overflow_sat(&vcs, &solver, "snd_signed_add_overflow");
}

/// 2. u32::MAX + 1 wraps without precondition
#[test]
fn snd_unsigned_add_overflow() {
    let func = Function {
        name: "unsigned_add".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Uint(UintTy::U32),
            is_ghost: false,
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Uint(UintTy::U32),
                is_ghost: false,
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Uint(UintTy::U32),
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_overflow_sat(&vcs, &solver, "snd_unsigned_add_overflow");
}

/// 3. i32::MIN - 1 overflows without precondition
#[test]
fn snd_signed_sub_overflow() {
    let func = Function {
        name: "signed_sub".to_string(),
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
                    BinOp::Sub,
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_2")),
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_overflow_sat(&vcs, &solver, "snd_signed_sub_overflow");
}

/// 4. Unconstrained a - b for u32 can underflow
#[test]
fn snd_unsigned_sub_underflow() {
    let func = Function {
        name: "unsigned_sub".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Uint(UintTy::U32),
            is_ghost: false,
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Uint(UintTy::U32),
                is_ghost: false,
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Uint(UintTy::U32),
                is_ghost: false,
            },
        ],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::BinaryOp(
                    BinOp::Sub,
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_2")),
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_overflow_sat(&vcs, &solver, "snd_unsigned_sub_underflow");
}

/// 5. Unconstrained a * b for i32 can overflow
#[test]
fn snd_signed_mul_overflow() {
    let func = Function {
        name: "signed_mul".to_string(),
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
                    BinOp::Mul,
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_2")),
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_overflow_sat(&vcs, &solver, "snd_signed_mul_overflow");
}

/// 6. Unconstrained a * b for u32 can overflow
#[test]
fn snd_unsigned_mul_overflow() {
    let func = Function {
        name: "unsigned_mul".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Uint(UintTy::U32),
            is_ghost: false,
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Uint(UintTy::U32),
                is_ghost: false,
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Uint(UintTy::U32),
                is_ghost: false,
            },
        ],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::BinaryOp(
                    BinOp::Mul,
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_2")),
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_overflow_sat(&vcs, &solver, "snd_unsigned_mul_overflow");
}

/// 7. a / b without b != 0 precondition => division by zero possible
#[test]
fn snd_division_by_zero() {
    let func = Function {
        name: "div_by_zero".to_string(),
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
                    BinOp::Div,
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_2")),
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_overflow_sat(&vcs, &solver, "snd_division_by_zero");
}

/// 8. a << b without b < 32 precondition => shift overflow possible
#[test]
fn snd_shift_overflow() {
    let func = Function {
        name: "shift_overflow".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Uint(UintTy::U32),
            is_ghost: false,
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Uint(UintTy::U32),
                is_ghost: false,
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Uint(UintTy::U32),
                is_ghost: false,
            },
        ],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::BinaryOp(
                    BinOp::Shl,
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_2")),
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_overflow_sat(&vcs, &solver, "snd_shift_overflow");
}

// ===========================================================================
// Wrong postcondition tests (6 tests)
// ===========================================================================

/// 9. ensures(result == _1) on fn add(a, b) = a + b -- wrong when b != 0
#[test]
fn snd_wrong_postcondition_add() {
    let func = Function {
        name: "add_wrong_post".to_string(),
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
            requires: vec![
                SpecExpr {
                    raw: "_1 >= 0 && _1 <= 100".to_string(),
                },
                SpecExpr {
                    raw: "_2 >= 1 && _2 <= 100".to_string(),
                },
            ],
            ensures: vec![SpecExpr {
                raw: "result == _1".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
        },
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_postcondition_sat(&vcs, &solver, "snd_wrong_postcondition_add");
}

/// 10. ensures(result == _1) on max(a, b) -- wrong when b > a
#[test]
fn snd_wrong_postcondition_max() {
    let func = Function {
        name: "max_wrong_post".to_string(),
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
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_1"))),
                )],
                terminator: Terminator::Return,
            },
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
                raw: "result == _1".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
        },
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_postcondition_sat(&vcs, &solver, "snd_wrong_postcondition_max");
}

/// 11. ensures(result > _1) on identity fn -- wrong always
#[test]
fn snd_wrong_postcondition_identity() {
    let func = Function {
        name: "identity_wrong_post".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Copy(Place::local("_1"))),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_1 >= 0 && _1 <= 100".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "result > _1".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
        },
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_postcondition_sat(&vcs, &solver, "snd_wrong_postcondition_identity");
}

/// 12. ensures(result == 0) on fn returning 42 -- wrong always
#[test]
fn snd_wrong_postcondition_constant() {
    let func = Function {
        name: "const_wrong_post".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        },
        params: vec![],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Constant(Constant::Int(42, IntTy::I32))),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result == 0".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
        },
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_postcondition_sat(&vcs, &solver, "snd_wrong_postcondition_constant");
}

/// 13. Wrong postcondition on branching function
///     fn choose(x: i32) -> i32 { if x > 0 { 1 } else { -1 } }
///     ensures: result == 0  -- never true
#[test]
fn snd_wrong_postcondition_branch() {
    let func = Function {
        name: "choose_wrong_post".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        locals: vec![Local {
            name: "_2".to_string(),
            ty: Ty::Bool,
            is_ghost: false,
        }],
        basic_blocks: vec![
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_2"),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_2")),
                    targets: vec![(1, 1)],
                    otherwise: 2,
                },
            },
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(1, IntTy::I32))),
                )],
                terminator: Terminator::Goto(3),
            },
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(-1, IntTy::I32))),
                )],
                terminator: Terminator::Goto(3),
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result == 0".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
        },
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_postcondition_sat(&vcs, &solver, "snd_wrong_postcondition_branch");
}

/// 14. Off-by-one: ensures(result >= _1 + 1) on fn returning _1
#[test]
fn snd_postcondition_off_by_one() {
    let func = Function {
        name: "off_by_one".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Use(Operand::Copy(Place::local("_1"))),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_1 >= 0 && _1 <= 100".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "result >= _1 + 1".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
        },
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_postcondition_sat(&vcs, &solver, "snd_postcondition_off_by_one");
}

// ===========================================================================
// Control flow bug tests (6 tests)
// ===========================================================================

/// 15. Function where linear block walking would miss a bug.
///     fn buggy_branch(x: i32) -> i32 { if x > 0 { x } else { -x } }
///     ensures: result > 0  -- wrong when x == 0 (else branch returns 0)
#[test]
fn snd_branch_unsound_if_linear() {
    let func = Function {
        name: "buggy_branch".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        locals: vec![
            Local {
                name: "_2".to_string(),
                ty: Ty::Bool,
                is_ghost: false,
            },
            Local {
                name: "_3".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
        ],
        basic_blocks: vec![
            // bb0: _2 = _1 > 0; switchInt
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_2"),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_2")),
                    targets: vec![(1, 1)],
                    otherwise: 2,
                },
            },
            // bb1: _0 = _1; goto bb3
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_1"))),
                )],
                terminator: Terminator::Goto(3),
            },
            // bb2: _3 = neg(_1); _0 = _3; goto bb3
            BasicBlock {
                statements: vec![
                    Statement::Assign(
                        Place::local("_3"),
                        Rvalue::UnaryOp(UnOp::Neg, Operand::Copy(Place::local("_1"))),
                    ),
                    Statement::Assign(
                        Place::local("_0"),
                        Rvalue::Use(Operand::Copy(Place::local("_3"))),
                    ),
                ],
                terminator: Terminator::Goto(3),
            },
            // bb3: return
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_1 >= -100 && _1 <= 100".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "result > 0".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
        },
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_postcondition_sat(&vcs, &solver, "snd_branch_unsound_if_linear");
}

/// 16. i32::MIN / -1 overflow
#[test]
fn snd_signed_div_int_min_neg_one() {
    let func = Function {
        name: "signed_div_overflow".to_string(),
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
                    BinOp::Div,
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_2")),
                ),
            )],
            terminator: Terminator::Return,
        }],
        // Only require divisor != 0, but don't guard against INT_MIN/-1
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_2 != 0".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
        },
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    // The overflow VCs include both div-by-zero and INT_MIN/-1.
    // With _2 != 0 precondition, the div-by-zero check is UNSAT (safe),
    // but the INT_MIN/-1 check should be SAT (still possible).
    let overflow_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("overflow"))
        .collect();
    assert!(
        !overflow_vcs.is_empty(),
        "snd_signed_div_int_min_neg_one: expected overflow VCs"
    );
    // At least one overflow VC should be SAT (the INT_MIN/-1 case)
    let mut found_sat = false;
    for vc in &overflow_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 error on signed div overflow VC");
        if result.is_sat() {
            found_sat = true;
        }
    }
    assert!(
        found_sat,
        "snd_signed_div_int_min_neg_one: expected at least one SAT VC for INT_MIN/-1"
    );
}

/// 17. i32::MIN % -1 overflow (the fix from Task 1)
#[test]
fn snd_signed_rem_int_min_neg_one() {
    let func = Function {
        name: "signed_rem_overflow".to_string(),
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
                    BinOp::Rem,
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_2")),
                ),
            )],
            terminator: Terminator::Return,
        }],
        // Only require divisor != 0, but don't guard against INT_MIN%-1
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_2 != 0".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
        },
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    let overflow_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("overflow"))
        .collect();
    assert!(
        !overflow_vcs.is_empty(),
        "snd_signed_rem_int_min_neg_one: expected overflow VCs"
    );
    let mut found_sat = false;
    for vc in &overflow_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 error on signed rem overflow VC");
        if result.is_sat() {
            found_sat = true;
        }
    }
    assert!(
        found_sat,
        "snd_signed_rem_int_min_neg_one: expected SAT for INT_MIN%-1 overflow"
    );
}

/// 18. Arithmetic on unrestricted signed inputs can overflow
#[test]
fn snd_unrestricted_input_overflow() {
    // fn compute(a: i32, b: i32) -> i32 { a + b + a }
    // Two additions, both can overflow
    let func = Function {
        name: "unrestricted_overflow".to_string(),
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
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        basic_blocks: vec![BasicBlock {
            statements: vec![
                // _3 = _1 + _2
                Statement::Assign(
                    Place::local("_3"),
                    Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_2")),
                    ),
                ),
                // _0 = _3 + _1
                Statement::Assign(
                    Place::local("_0"),
                    Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local("_3")),
                        Operand::Copy(Place::local("_1")),
                    ),
                ),
            ],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_overflow_sat(&vcs, &solver, "snd_unrestricted_input_overflow");
}

/// 19. Nested branches with wrong postcondition
///     fn quad(a: i32, b: i32) -> i32 { if a > 0 { if b > 0 { 3 } else { 2 } } else { if b > 0 { 1 } else { 0 } } }
///     ensures: result >= 1  -- wrong when a <= 0 && b <= 0 (returns 0)
#[test]
fn snd_nested_branch_wrong_result() {
    let func = Function {
        name: "quad_wrong_post".to_string(),
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
        locals: vec![
            Local {
                name: "_3".to_string(),
                ty: Ty::Bool,
                is_ghost: false,
            },
            Local {
                name: "_4".to_string(),
                ty: Ty::Bool,
                is_ghost: false,
            },
            Local {
                name: "_5".to_string(),
                ty: Ty::Bool,
                is_ghost: false,
            },
        ],
        basic_blocks: vec![
            // bb0: _3 = _1 > 0; switchInt
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_3")),
                    targets: vec![(1, 1)],
                    otherwise: 4,
                },
            },
            // bb1: _4 = _2 > 0; switchInt
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_4"),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local("_2")),
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_4")),
                    targets: vec![(1, 2)],
                    otherwise: 3,
                },
            },
            // bb2: _0 = 3; goto bb7
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(3, IntTy::I32))),
                )],
                terminator: Terminator::Goto(7),
            },
            // bb3: _0 = 2; goto bb7
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(2, IntTy::I32))),
                )],
                terminator: Terminator::Goto(7),
            },
            // bb4: _5 = _2 > 0; switchInt
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_5"),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local("_2")),
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_5")),
                    targets: vec![(1, 5)],
                    otherwise: 6,
                },
            },
            // bb5: _0 = 1; goto bb7
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(1, IntTy::I32))),
                )],
                terminator: Terminator::Goto(7),
            },
            // bb6: _0 = 0; goto bb7
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
                )],
                terminator: Terminator::Goto(7),
            },
            // bb7: return
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result >= 1".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
        },
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_postcondition_sat(&vcs, &solver, "snd_nested_branch_wrong_result");
}

/// 20. Unsigned remainder without guarding INT_MIN%-1 style case
///     fn unsafe_urem(a: u32, b: u32) -> u32 { a % b }
///     No precondition on b => division by zero possible
#[test]
fn snd_unsigned_rem_div_by_zero() {
    let func = Function {
        name: "unsafe_urem".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Uint(UintTy::U32),
            is_ghost: false,
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Uint(UintTy::U32),
                is_ghost: false,
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Uint(UintTy::U32),
                is_ghost: false,
            },
        ],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::BinaryOp(
                    BinOp::Rem,
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_2")),
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_overflow_sat(&vcs, &solver, "snd_unsigned_rem_div_by_zero");
}

// ===========================================================================
// Additional soundness tests (to reach 20+)
// ===========================================================================

/// 21. Unsigned right shift with out-of-bounds shift amount
#[test]
fn snd_shr_overflow() {
    let func = Function {
        name: "shr_overflow".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Uint(UintTy::U32),
            is_ghost: false,
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Uint(UintTy::U32),
                is_ghost: false,
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Uint(UintTy::U32),
                is_ghost: false,
            },
        ],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::BinaryOp(
                    BinOp::Shr,
                    Operand::Copy(Place::local("_1")),
                    Operand::Copy(Place::local("_2")),
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_overflow_sat(&vcs, &solver, "snd_shr_overflow");
}

/// 22. Wrong postcondition: result <= _1 on fn returning _1 + _2 with _2 > 0
#[test]
fn snd_add_wrong_upper_bound() {
    let func = Function {
        name: "add_wrong_upper".to_string(),
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
            requires: vec![
                SpecExpr {
                    raw: "_1 >= 0 && _1 <= 50".to_string(),
                },
                SpecExpr {
                    raw: "_2 >= 1 && _2 <= 50".to_string(),
                },
            ],
            ensures: vec![SpecExpr {
                raw: "result <= _1".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
        },
        generic_params: vec![],
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_postcondition_sat(&vcs, &solver, "snd_add_wrong_upper_bound");
}
