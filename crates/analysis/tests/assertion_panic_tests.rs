//! End-to-end integration tests for assertion verification and panic detection.
//!
//! These tests exercise the enhanced Assert terminator handling:
//!   IR construction (with AssertKind) -> VCGen -> SMT-LIB -> Z3
//!
//! Each test builds an `ir::Function` with Assert terminators of specific
//! AssertKind variants, runs `vcgen::generate_vcs`, and checks against Z3.
//!
//! The tests verify:
//!   1. User assertions (assert!(x > 0)) are statically verified
//!   2. Bounds checks detect out-of-bounds access
//!   3. Division-by-zero is caught
//!   4. unwrap() on None is caught
//!   5. Error messages are specific to the panic kind

use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen;
use rust_fv_solver::Z3Solver;

// ---------------------------------------------------------------------------
// Helpers (self-contained, duplicated per established test pattern)
// ---------------------------------------------------------------------------

/// Create a `Z3Solver` or skip the test if Z3 is not installed.
fn solver_or_skip() -> Z3Solver {
    match Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Skipping test -- Z3 not available: {e}");
            panic!("Z3_NOT_AVAILABLE: {e}");
        }
    }
}

/// Render a `Script` to its SMT-LIB2 text representation.
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
        SmtCmd::DeclareDatatype { name, variants } => {
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
        Sort::Seq(inner) => {
            out.push_str("(Seq ");
            format_sort(out, inner);
            out.push(')');
        }
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
        // Floating-point terms: delegate to Display impl
        Term::FpNaN(..)
        | Term::FpPosInf(..)
        | Term::FpNegInf(..)
        | Term::FpPosZero(..)
        | Term::FpNegZero(..)
        | Term::FpFromBits(..)
        | Term::RoundingMode(..)
        | Term::FpAdd(..)
        | Term::FpSub(..)
        | Term::FpMul(..)
        | Term::FpDiv(..)
        | Term::FpSqrt(..)
        | Term::FpAbs(..)
        | Term::FpNeg(..)
        | Term::FpEq(..)
        | Term::FpLt(..)
        | Term::FpLeq(..)
        | Term::FpGt(..)
        | Term::FpGeq(..)
        | Term::FpIsNaN(..)
        | Term::FpIsInfinite(..)
        | Term::FpIsZero(..)
        | Term::FpIsNegative(..)
        | Term::FpIsPositive(..)
        // Sequence terms: delegate to Display impl
        | Term::SeqEmpty(..)
        | Term::SeqUnit(..)
        | Term::SeqConcat(..)
        | Term::SeqLen(..)
        | Term::SeqNth(..)
        | Term::SeqExtract(..)
        | Term::SeqContains(..)
        | Term::SeqUpdate(..) => {
            out.push_str(&term.to_string());
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
// Test 1: User assertion verified (assert!(x > 0) with precondition x > 0)
// ---------------------------------------------------------------------------

/// Function: `fn check(x: i32) { assert!(x > 0); }`
/// Precondition: `_1 > 0`
///
/// CFG:
///   bb0: _3 = _1 > 0; assert(_3 == true) -> bb1
///   bb1: return
///
/// With precondition x > 0, the assertion always holds. VC should be UNSAT.
#[test]
fn test_assert_true_verified() {
    let func = Function {
        name: "check".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Unit,
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        locals: vec![Local {
            name: "_3".to_string(),
            ty: Ty::Bool,
            is_ghost: false,
        }],
        basic_blocks: vec![
            // bb0: _3 = _1 > 0; assert(_3 == true) -> bb1
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local("_3")),
                    expected: true,
                    target: 1,
                    kind: AssertKind::UserAssert,
                },
            },
            // bb1: return
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_1 > 0".to_string(),
            }],
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let assert_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("assertion"))
        .collect();

    assert!(
        !assert_vcs.is_empty(),
        "Expected assertion VC, got: {:?}",
        vcs.conditions
            .iter()
            .map(|vc| &vc.description)
            .collect::<Vec<_>>(),
    );

    let solver = solver_or_skip();
    for vc in &assert_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_unsat(),
            "Assertion with precondition x>0 should be UNSAT: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 2: User assertion fails (assert!(x > 0) without precondition)
// ---------------------------------------------------------------------------

/// Same as above but NO precondition. Z3 should find x <= 0 as counterexample.
#[test]
fn test_assert_false_counterexample() {
    let func = Function {
        name: "check_unconstrained".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Unit,
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
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
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local("_3")),
                    expected: true,
                    target: 1,
                    kind: AssertKind::UserAssert,
                },
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts::default(), // No precondition
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let assert_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("assertion"))
        .collect();

    assert!(!assert_vcs.is_empty(), "Expected assertion VC");

    let solver = solver_or_skip();
    for vc in &assert_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_sat(),
            "Unconstrained assert!(x > 0) should be SAT (counterexample x <= 0): {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 3: Assertion after computation (let y = x + 1; assert!(y > x))
// ---------------------------------------------------------------------------

/// CFG:
///   bb0: _3 = _1 + 1; _4 = _3 > _1; assert(_4 == true) -> bb1
///   bb1: return
///
/// This is only valid when x + 1 doesn't overflow. With bounded x < i32::MAX,
/// the assertion holds.
#[test]
fn test_assert_after_computation() {
    let func = Function {
        name: "after_comp".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Unit,
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        locals: vec![
            Local {
                name: "_3".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
            Local {
                name: "_4".to_string(),
                ty: Ty::Bool,
                is_ghost: false,
            },
        ],
        basic_blocks: vec![
            BasicBlock {
                statements: vec![
                    // _3 = _1 + 1
                    Statement::Assign(
                        Place::local("_3"),
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local("_1")),
                            Operand::Constant(Constant::Int(1, IntTy::I32)),
                        ),
                    ),
                    // _4 = _3 > _1
                    Statement::Assign(
                        Place::local("_4"),
                        Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local("_3")),
                            Operand::Copy(Place::local("_1")),
                        ),
                    ),
                ],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local("_4")),
                    expected: true,
                    target: 1,
                    kind: AssertKind::UserAssert,
                },
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_1 >= 0".to_string(),
            }],
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let assert_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("assertion"))
        .collect();

    assert!(!assert_vcs.is_empty(), "Expected assertion VC");

    // With _1 >= 0, _1 + 1 can overflow at i32::MAX. So this should be SAT
    // (Z3 can find _1 = 0x7FFFFFFF where _1 + 1 wraps negative).
    // To make it UNSAT, we'd need _1 < 0x7FFFFFFF. Let's verify it IS SAT.
    let solver = solver_or_skip();
    for vc in &assert_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        // With only _1 >= 0, x + 1 can still overflow at INT_MAX
        assert!(
            result.is_sat(),
            "assert!(y > x) after y = x + 1 should be SAT (overflow at INT_MAX): {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 4: Bounds check safe (array access with index < len precondition)
// ---------------------------------------------------------------------------

/// Models: `fn access(arr_len: i32, idx: i32) { assert!(idx < arr_len); }`
/// Precondition: `_2 >= 0 && _2 < _1` and `_1 > 0`
///
/// CFG:
///   bb0: _3 = _2 < _1; assert(_3 == true, BoundsCheck) -> bb1
///   bb1: return
#[test]
fn test_array_bounds_safe() {
    let func = Function {
        name: "safe_access".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Unit,
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
                        BinOp::Lt,
                        Operand::Copy(Place::local("_2")),
                        Operand::Copy(Place::local("_1")),
                    ),
                )],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local("_3")),
                    expected: true,
                    target: 1,
                    kind: AssertKind::BoundsCheck {
                        len: Operand::Copy(Place::local("_1")),
                        index: Operand::Copy(Place::local("_2")),
                    },
                },
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![
                SpecExpr {
                    raw: "_1 > 0".to_string(),
                },
                SpecExpr {
                    raw: "_2 >= 0".to_string(),
                },
                SpecExpr {
                    raw: "_2 < _1".to_string(),
                },
            ],
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let bounds_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("array index out of bounds"))
        .collect();

    assert!(!bounds_vcs.is_empty(), "Expected bounds check VC");

    let solver = solver_or_skip();
    for vc in &bounds_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_unsat(),
            "Safe bounds check should be UNSAT: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 5: Bounds check unsafe (array access without bounds precondition)
// ---------------------------------------------------------------------------

/// Same structure but NO precondition constraining index < len.
#[test]
fn test_array_bounds_unsafe() {
    let func = Function {
        name: "unsafe_access".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Unit,
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
                        BinOp::Lt,
                        Operand::Copy(Place::local("_2")),
                        Operand::Copy(Place::local("_1")),
                    ),
                )],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local("_3")),
                    expected: true,
                    target: 1,
                    kind: AssertKind::BoundsCheck {
                        len: Operand::Copy(Place::local("_1")),
                        index: Operand::Copy(Place::local("_2")),
                    },
                },
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts::default(), // No precondition
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let bounds_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("array index out of bounds"))
        .collect();

    assert!(!bounds_vcs.is_empty(), "Expected bounds check VC");

    let solver = solver_or_skip();
    for vc in &bounds_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_sat(),
            "Unsafe bounds check should be SAT (counterexample): {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 6: Division by zero safe (a / b with precondition b != 0)
// ---------------------------------------------------------------------------

/// CFG:
///   bb0: _4 = _2 != 0; assert(_4 == true, DivisionByZero) -> bb1
///   bb1: _0 = _1 / _2; return
#[test]
fn test_div_by_zero_safe() {
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
        locals: vec![Local {
            name: "_4".to_string(),
            ty: Ty::Bool,
            is_ghost: false,
        }],
        basic_blocks: vec![
            // bb0: _4 = _2 != 0; assert(_4 == true) -> bb1
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_4"),
                    Rvalue::BinaryOp(
                        BinOp::Ne,
                        Operand::Copy(Place::local("_2")),
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local("_4")),
                    expected: true,
                    target: 1,
                    kind: AssertKind::DivisionByZero,
                },
            },
            // bb1: _0 = _1 / _2; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_2")),
                    ),
                )],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_2 != 0".to_string(),
            }],
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let div_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("division by zero"))
        .collect();

    assert!(!div_vcs.is_empty(), "Expected division by zero VC");

    let solver = solver_or_skip();
    for vc in &div_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_unsat(),
            "Division with b != 0 precondition should be UNSAT: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 7: Division by zero unsafe (a / b without precondition)
// ---------------------------------------------------------------------------

#[test]
fn test_div_by_zero_unsafe() {
    let func = Function {
        name: "unsafe_div".to_string(),
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
            name: "_4".to_string(),
            ty: Ty::Bool,
            is_ghost: false,
        }],
        basic_blocks: vec![
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_4"),
                    Rvalue::BinaryOp(
                        BinOp::Ne,
                        Operand::Copy(Place::local("_2")),
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local("_4")),
                    expected: true,
                    target: 1,
                    kind: AssertKind::DivisionByZero,
                },
            },
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_2")),
                    ),
                )],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts::default(), // No precondition
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let div_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("division by zero"))
        .collect();

    assert!(!div_vcs.is_empty(), "Expected division by zero VC");

    let solver = solver_or_skip();
    for vc in &div_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_sat(),
            "Division without precondition should be SAT (b=0 counterexample): {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 8: Unwrap safe (discriminant guaranteed to be Some)
// ---------------------------------------------------------------------------

/// Models unwrap() as: `assert!(discriminant == 1, UnwrapNone)`
/// where discriminant 1 = Some variant.
/// Precondition: `_1 == 1` (we know it's Some).
///
/// CFG:
///   bb0: _3 = _1 == 1; assert(_3 == true, UnwrapNone) -> bb1
///   bb1: return
#[test]
fn test_unwrap_safe() {
    let func = Function {
        name: "safe_unwrap".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Unit,
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32), // discriminant as i32,
            is_ghost: false,
        }],
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
                        BinOp::Eq,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(1, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local("_3")),
                    expected: true,
                    target: 1,
                    kind: AssertKind::UnwrapNone,
                },
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_1 == 1".to_string(),
            }],
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let unwrap_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("unwrap"))
        .collect();

    assert!(!unwrap_vcs.is_empty(), "Expected unwrap VC");

    let solver = solver_or_skip();
    for vc in &unwrap_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_unsat(),
            "Safe unwrap (discriminant guaranteed Some) should be UNSAT: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 9: Unwrap unsafe (no precondition on discriminant)
// ---------------------------------------------------------------------------

#[test]
fn test_unwrap_unsafe() {
    let func = Function {
        name: "unsafe_unwrap".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Unit,
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
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
                        BinOp::Eq,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(1, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local("_3")),
                    expected: true,
                    target: 1,
                    kind: AssertKind::UnwrapNone,
                },
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts::default(), // No precondition
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let unwrap_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("unwrap"))
        .collect();

    assert!(!unwrap_vcs.is_empty(), "Expected unwrap VC");

    let solver = solver_or_skip();
    for vc in &unwrap_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_sat(),
            "Unsafe unwrap should be SAT (discriminant != 1 counterexample): {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 10: Error message specificity
// ---------------------------------------------------------------------------

/// Verify that VCs for different AssertKinds produce different description strings.
#[test]
fn test_error_message_specificity() {
    // Build functions with different AssertKind variants
    let make_func = |name: &str, kind: AssertKind| Function {
        name: name.to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Unit,
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
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
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local("_3")),
                    expected: true,
                    target: 1,
                    kind,
                },
            },
            BasicBlock {
                statements: vec![],
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
        loops: vec![],
    };

    // UserAssert
    let func1 = make_func("user_assert", AssertKind::UserAssert);
    let vcs1 = vcgen::generate_vcs(&func1, None);
    let desc1 = vcs1
        .conditions
        .iter()
        .find(|vc| vc.description.contains("assertion"))
        .map(|vc| vc.description.clone());
    assert!(
        desc1
            .as_ref()
            .is_some_and(|d| d.contains("assertion might fail")),
        "UserAssert should produce 'assertion might fail', got: {desc1:?}"
    );

    // BoundsCheck
    let func2 = make_func(
        "bounds",
        AssertKind::BoundsCheck {
            len: Operand::Constant(Constant::Int(10, IntTy::I32)),
            index: Operand::Copy(Place::local("_1")),
        },
    );
    let vcs2 = vcgen::generate_vcs(&func2, None);
    let desc2 = vcs2
        .conditions
        .iter()
        .find(|vc| vc.description.contains("array"))
        .map(|vc| vc.description.clone());
    assert!(
        desc2
            .as_ref()
            .is_some_and(|d| d.contains("array index out of bounds")),
        "BoundsCheck should produce 'array index out of bounds', got: {desc2:?}"
    );

    // DivisionByZero
    let func3 = make_func("div_zero", AssertKind::DivisionByZero);
    let vcs3 = vcgen::generate_vcs(&func3, None);
    let desc3 = vcs3
        .conditions
        .iter()
        .find(|vc| vc.description.contains("division"))
        .map(|vc| vc.description.clone());
    assert!(
        desc3
            .as_ref()
            .is_some_and(|d| d.contains("division by zero")),
        "DivisionByZero should produce 'division by zero', got: {desc3:?}"
    );

    // UnwrapNone
    let func4 = make_func("unwrap", AssertKind::UnwrapNone);
    let vcs4 = vcgen::generate_vcs(&func4, None);
    let desc4 = vcs4
        .conditions
        .iter()
        .find(|vc| vc.description.contains("unwrap"))
        .map(|vc| vc.description.clone());
    assert!(
        desc4
            .as_ref()
            .is_some_and(|d| d.contains("unwrap() called on None")),
        "UnwrapNone should produce 'unwrap() called on None', got: {desc4:?}"
    );

    // Overflow
    let func5 = make_func("overflow", AssertKind::Overflow(BinOp::Add));
    let vcs5 = vcgen::generate_vcs(&func5, None);
    let desc5 = vcs5
        .conditions
        .iter()
        .find(|vc| vc.description.contains("arithmetic overflow"))
        .map(|vc| vc.description.clone());
    assert!(
        desc5
            .as_ref()
            .is_some_and(|d| d.contains("arithmetic overflow in Add")),
        "Overflow(Add) should produce 'arithmetic overflow in Add', got: {desc5:?}"
    );

    // Verify all descriptions are distinct
    let all_descs = [&desc1, &desc2, &desc3, &desc4, &desc5];
    for i in 0..all_descs.len() {
        for j in (i + 1)..all_descs.len() {
            assert_ne!(
                all_descs[i], all_descs[j],
                "Descriptions should be distinct: {:?} vs {:?}",
                all_descs[i], all_descs[j]
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Test 11: Remainder by zero
// ---------------------------------------------------------------------------

/// Models: `a % b` with AssertKind::RemainderByZero
/// Without precondition, Z3 should find b=0.
#[test]
fn test_remainder_by_zero_unsafe() {
    let func = Function {
        name: "unsafe_rem".to_string(),
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
            name: "_4".to_string(),
            ty: Ty::Bool,
            is_ghost: false,
        }],
        basic_blocks: vec![
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_4"),
                    Rvalue::BinaryOp(
                        BinOp::Ne,
                        Operand::Copy(Place::local("_2")),
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local("_4")),
                    expected: true,
                    target: 1,
                    kind: AssertKind::RemainderByZero,
                },
            },
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::BinaryOp(
                        BinOp::Rem,
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_2")),
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
        loops: vec![],
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let rem_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("remainder by zero"))
        .collect();

    assert!(!rem_vcs.is_empty(), "Expected remainder by zero VC");

    let solver = solver_or_skip();
    for vc in &rem_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_sat(),
            "Remainder without precondition should be SAT: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}
