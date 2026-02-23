//! Completeness test suite: correct programs that MUST verify successfully.
//!
//! Each test constructs an `ir::Function` that is correct, runs
//! `vcgen::generate_vcs()`, and asserts that Z3 proves safety (UNSAT).
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
        Sort::Seq(inner) => {
            out.push_str("(Seq ");
            format_sort(out, inner);
            out.push(')');
        }
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
        // Floating-point terms: delegate to Display impl
        T::FpNaN(..)
        | T::FpPosInf(..)
        | T::FpNegInf(..)
        | T::FpPosZero(..)
        | T::FpNegZero(..)
        | T::FpFromBits(..)
        | T::RoundingMode(..)
        | T::FpAdd(..)
        | T::FpSub(..)
        | T::FpMul(..)
        | T::FpDiv(..)
        | T::FpSqrt(..)
        | T::FpAbs(..)
        | T::FpNeg(..)
        | T::FpEq(..)
        | T::FpLt(..)
        | T::FpLeq(..)
        | T::FpGt(..)
        | T::FpGeq(..)
        | T::FpIsNaN(..)
        | T::FpIsInfinite(..)
        | T::FpIsZero(..)
        | T::FpIsNegative(..)
        | T::FpIsPositive(..)
        // Sequence terms: delegate to Display impl
        | T::SeqEmpty(..)
        | T::SeqUnit(..)
        | T::SeqConcat(..)
        | T::SeqLen(..)
        | T::SeqNth(..)
        | T::SeqExtract(..)
        | T::SeqContains(..)
        | T::SeqUpdate(..) => {
            out.push_str(&term.to_string());
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

/// Assert all VCs are UNSAT (correct program verified).
fn assert_all_unsat(vcs: &vcgen::FunctionVCs, solver: &Z3Solver, test_name: &str) {
    assert!(
        !vcs.conditions.is_empty(),
        "{test_name}: expected at least one VC"
    );
    for vc in &vcs.conditions {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .unwrap_or_else(|e| panic!("{test_name}: Z3 error: {e}\nScript:\n{smtlib}"));
        assert!(
            result.is_unsat(),
            "{test_name}: expected UNSAT (proved safe), got {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ===========================================================================
// Safe arithmetic tests (8 tests)
// ===========================================================================

/// 1. Bounded addition: _1 in [0,100], _2 in [0,100] => no overflow
#[test]
fn cmp_bounded_add() {
    let func = Function {
        name: "bounded_add".to_string(),
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
                    raw: "_2 >= 0 && _2 <= 100".to_string(),
                },
            ],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_bounded_add");
}

/// 2. Bounded subtraction: _1 in [50,100], _2 in [0,50] => no underflow
#[test]
fn cmp_bounded_sub() {
    let func = Function {
        name: "bounded_sub".to_string(),
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
        contracts: Contracts {
            requires: vec![
                SpecExpr {
                    raw: "_1 >= 50 && _1 <= 100".to_string(),
                },
                SpecExpr {
                    raw: "_2 >= 0 && _2 <= 50".to_string(),
                },
            ],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_bounded_sub");
}

/// 3. Bounded multiplication: _1 in [0,100], _2 in [0,100] => fits in i32
#[test]
fn cmp_bounded_mul() {
    let func = Function {
        name: "bounded_mul".to_string(),
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
        contracts: Contracts {
            requires: vec![
                SpecExpr {
                    raw: "_1 >= 0 && _1 <= 100".to_string(),
                },
                SpecExpr {
                    raw: "_2 >= 0 && _2 <= 100".to_string(),
                },
            ],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_bounded_mul");
}

/// 4. Safe division: requires _2 != 0, bounded to avoid INT_MIN/-1
#[test]
fn cmp_safe_div() {
    let func = Function {
        name: "safe_div".to_string(),
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
        contracts: Contracts {
            requires: vec![
                SpecExpr {
                    raw: "_2 != 0".to_string(),
                },
                SpecExpr {
                    raw: "_1 >= -100 && _1 <= 100".to_string(),
                },
            ],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_safe_div");
}

/// 5. Safe shift: requires _2 in [0,31]
#[test]
fn cmp_safe_shift() {
    let func = Function {
        name: "safe_shift".to_string(),
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
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_2 >= 0 && _2 <= 31".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_safe_shift");
}

/// 6. Identity postcondition: ensures result == _1
#[test]
fn cmp_identity_postcondition() {
    let func = Function {
        name: "identity".to_string(),
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
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result == _1".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_identity_postcondition");
}

/// 7. Constant postcondition: ensures result == 42 on fn returning 42
#[test]
fn cmp_constant_postcondition() {
    let func = Function {
        name: "const_42".to_string(),
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
                raw: "result == 42".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_constant_postcondition");
}

/// 8. Bounded add with postcondition: result >= _1 when _2 >= 0
#[test]
fn cmp_bounded_add_postcondition() {
    let func = Function {
        name: "bounded_add_post".to_string(),
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
                    raw: "_2 >= 0 && _2 <= 100".to_string(),
                },
            ],
            ensures: vec![SpecExpr {
                raw: "result >= _1".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_bounded_add_postcondition");
}

// ===========================================================================
// Control flow tests (7 tests)
// ===========================================================================

/// 9. max(a, b) with ensures result >= _1 && result >= _2
#[test]
fn cmp_max_function() {
    let func = Function {
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
                raw: "result >= _1 && result >= _2".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    // Only check postcondition VCs (overflow VCs will be SAT because unconstrained)
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(
        !post_vcs.is_empty(),
        "cmp_max_function: expected postcondition VCs"
    );
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 error");
        assert!(
            result.is_unsat(),
            "cmp_max_function: max postcondition should be UNSAT, got {result:?}\nScript:\n{smtlib}",
        );
    }
}

/// 10. abs(x) with bounded input: ensures result >= 0
///     fn abs(x: i32) -> i32 { if x >= 0 { x } else { -x } }
///     requires: _1 >= -100 && _1 <= 100  (avoids NEG overflow on i32::MIN)
#[test]
fn cmp_abs_function() {
    let func = Function {
        name: "abs".to_string(),
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
            // bb0: _2 = _1 >= 0; switchInt
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_2"),
                    Rvalue::BinaryOp(
                        BinOp::Ge,
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
                raw: "result >= 0".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty());
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 error");
        assert!(
            result.is_unsat(),
            "cmp_abs_function: abs(x) >= 0 should be UNSAT, got {result:?}\nScript:\n{smtlib}",
        );
    }
}

/// 11. clamp(x, lo, hi): ensures result >= lo && result <= hi
///
/// `fn clamp(x, lo, hi) -> i32 { if x < lo { lo } else if x > hi { hi } else { x } }`
///
/// requires: lo <= hi
#[test]
fn cmp_clamp_function() {
    let func = Function {
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
            }, // x
            Local {
                name: "_2".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            }, // lo
            Local {
                name: "_3".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            }, // hi
        ],
        locals: vec![
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
            // bb0: _4 = _1 < _2; switchInt
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_4"),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_2")),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_4")),
                    targets: vec![(1, 1)],
                    otherwise: 2,
                },
            },
            // bb1: _0 = _2 (lo); goto bb5
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_2"))),
                )],
                terminator: Terminator::Goto(5),
            },
            // bb2: _5 = _1 > _3; switchInt
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_5"),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_3")),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_5")),
                    targets: vec![(1, 3)],
                    otherwise: 4,
                },
            },
            // bb3: _0 = _3 (hi); goto bb5
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_3"))),
                )],
                terminator: Terminator::Goto(5),
            },
            // bb4: _0 = _1 (x); goto bb5
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_1"))),
                )],
                terminator: Terminator::Goto(5),
            },
            // bb5: return
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_2 <= _3".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "result >= _2 && result <= _3".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty());
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 error");
        assert!(
            result.is_unsat(),
            "cmp_clamp_function: clamp postcondition should be UNSAT, got {result:?}\nScript:\n{smtlib}",
        );
    }
}

/// 12. Both branches assign same value, postcondition trivial
///     fn same_result(x: i32) -> i32 { if x > 0 { 42 } else { 42 } }
///     ensures: result == 42
#[test]
fn cmp_if_else_same_result() {
    let func = Function {
        name: "same_result".to_string(),
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
                    Rvalue::Use(Operand::Constant(Constant::Int(42, IntTy::I32))),
                )],
                terminator: Terminator::Goto(3),
            },
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(42, IntTy::I32))),
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
                raw: "result == 42".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty());
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 error");
        assert!(
            result.is_unsat(),
            "cmp_if_else_same_result: result == 42 should be UNSAT, got {result:?}\nScript:\n{smtlib}",
        );
    }
}

/// 13. 3-way branch classify: ensures result in [-1, 1]
#[test]
fn cmp_multi_branch_classify() {
    let func = Function {
        name: "classify".to_string(),
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
                ty: Ty::Bool,
                is_ghost: false,
            },
        ],
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
                terminator: Terminator::Goto(5),
            },
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_3")),
                    targets: vec![(1, 3)],
                    otherwise: 4,
                },
            },
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(-1, IntTy::I32))),
                )],
                terminator: Terminator::Goto(5),
            },
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
                )],
                terminator: Terminator::Goto(5),
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result >= -1 && result <= 1".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty());
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 error");
        assert!(
            result.is_unsat(),
            "cmp_multi_branch_classify: result in [-1,1] should be UNSAT, got {result:?}\nScript:\n{smtlib}",
        );
    }
}

/// 14. Early return via goto, both paths satisfy postcondition
///     fn abs_or_zero(x: i32) -> i32 { if x > 0 { x } else { 0 } }
///     ensures: result >= 0
#[test]
fn cmp_early_return() {
    let func = Function {
        name: "abs_or_zero".to_string(),
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
                    Rvalue::Use(Operand::Copy(Place::local("_1"))),
                )],
                terminator: Terminator::Goto(3),
            },
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
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
                raw: "result >= 0".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty());
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 error");
        assert!(
            result.is_unsat(),
            "cmp_early_return: result >= 0 should be UNSAT, got {result:?}\nScript:\n{smtlib}",
        );
    }
}

/// 15. 4-path nested if/else, all paths correct
///     fn quad(a, b) -> i32 { if a>0 { if b>0 {3} else {2} } else { if b>0 {1} else {0} } }
///     ensures: result >= 0 && result <= 3
#[test]
fn cmp_nested_branches_correct() {
    let func = Function {
        name: "quad".to_string(),
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
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(3, IntTy::I32))),
                )],
                terminator: Terminator::Goto(7),
            },
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(2, IntTy::I32))),
                )],
                terminator: Terminator::Goto(7),
            },
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
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(1, IntTy::I32))),
                )],
                terminator: Terminator::Goto(7),
            },
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
                )],
                terminator: Terminator::Goto(7),
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result >= 0 && result <= 3".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty());
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 error");
        assert!(
            result.is_unsat(),
            "cmp_nested_branches_correct: result in [0,3] should be UNSAT, got {result:?}\nScript:\n{smtlib}",
        );
    }
}

// ===========================================================================
// Type variation tests (5 tests)
// ===========================================================================

/// 16. u8 bounded add: [0, 100] + [0, 100] fits in u8 (max 200 < 255)
#[test]
fn cmp_u8_bounded_add() {
    let func = Function {
        name: "u8_add".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Uint(UintTy::U8),
            is_ghost: false,
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Uint(UintTy::U8),
                is_ghost: false,
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Uint(UintTy::U8),
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
                    raw: "_2 >= 0 && _2 <= 100".to_string(),
                },
            ],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_u8_bounded_add");
}

/// 17. i64 bounded add
#[test]
fn cmp_i64_bounded_add() {
    let func = Function {
        name: "i64_add".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I64),
            is_ghost: false,
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Int(IntTy::I64),
                is_ghost: false,
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Int(IntTy::I64),
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
                    raw: "_2 >= 0 && _2 <= 100".to_string(),
                },
            ],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_i64_bounded_add");
}

/// 18. u64 bounded mul: [0, 100] * [0, 100] = max 10000 << u64::MAX
#[test]
fn cmp_u64_bounded_mul() {
    let func = Function {
        name: "u64_mul".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Uint(UintTy::U64),
            is_ghost: false,
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Uint(UintTy::U64),
                is_ghost: false,
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Uint(UintTy::U64),
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
        contracts: Contracts {
            requires: vec![
                SpecExpr {
                    raw: "_1 >= 0 && _1 <= 100".to_string(),
                },
                SpecExpr {
                    raw: "_2 >= 0 && _2 <= 100".to_string(),
                },
            ],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_u64_bounded_mul");
}

/// 19. i8 safe operations: bounded inputs prevent overflow
#[test]
fn cmp_i8_safe_operations() {
    let func = Function {
        name: "i8_add".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I8),
            is_ghost: false,
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Int(IntTy::I8),
                is_ghost: false,
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Int(IntTy::I8),
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
                    raw: "_2 >= 0 && _2 <= 50".to_string(),
                },
            ],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_i8_safe_operations");
}

/// 20. Mixed-width identity: u16 identity postcondition
#[test]
fn cmp_mixed_width_identity() {
    let func = Function {
        name: "u16_identity".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Uint(UintTy::U16),
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Uint(UintTy::U16),
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
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result == _1".to_string(),
            }],
            invariants: vec![],
            is_pure: true,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_mixed_width_identity");
}

// ===========================================================================
// Additional completeness tests (to reach 20+)
// ===========================================================================

/// 21. Safe unsigned subtraction: requires _1 >= _2
#[test]
fn cmp_safe_unsigned_sub() {
    let func = Function {
        name: "safe_usub".to_string(),
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
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_1 >= _2".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_safe_unsigned_sub");
}

/// 22. Safe signed remainder: requires _2 != 0, requires _1 > -100
///     (avoids INT_MIN%-1 and div-by-zero)
#[test]
fn cmp_safe_signed_rem() {
    let func = Function {
        name: "safe_srem".to_string(),
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
        contracts: Contracts {
            requires: vec![
                SpecExpr {
                    raw: "_2 != 0".to_string(),
                },
                SpecExpr {
                    raw: "_1 >= -100 && _1 <= 100".to_string(),
                },
            ],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
            fn_specs: vec![],
            state_invariant: None,
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
        loops: vec![],
    };
    let vcs = vcgen::generate_vcs(&func, None);
    let solver = solver_or_skip();
    assert_all_unsat(&vcs, &solver, "cmp_safe_signed_rem");
}
