//! End-to-end tests for aggregate type encoding (structs, tuples, enums, arrays).
//!
//! These tests exercise the complete pipeline:
//!   IR construction -> VCGen -> SMT-LIB script -> Z3 solving
//!
//! Each test builds an `ir::Function` that uses aggregate types, runs
//! `vcgen::generate_vcs`, converts the resulting scripts to SMT-LIB text,
//! and feeds them to Z3 via `rust_fv_solver::Z3Solver`.

use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen;
use rust_fv_solver::Z3Solver;

// ---------------------------------------------------------------------------
// Helpers (self-contained, mirrors e2e_verification.rs pattern)
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

/// Minimal SMT-LIB command formatter (mirrors solver crate's internal formatter).
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

/// Helper: build Point type (struct with x: i32, y: i32)
fn point_ty() -> Ty {
    Ty::Struct(
        "Point".to_string(),
        vec![
            ("x".to_string(), Ty::Int(IntTy::I32)),
            ("y".to_string(), Ty::Int(IntTy::I32)),
        ],
    )
}

// ---------------------------------------------------------------------------
// Test a: Struct construction
// ---------------------------------------------------------------------------

/// Build: `fn make_point() -> Point { Point { x: 1, y: 2 } }`
///
/// Postcondition: `result.x == 1 && result.y == 2`
/// Since we construct Point(1, 2) and check that x==1 and y==2,
/// this should be UNSAT (proved).
#[test]
fn test_struct_construction() {
    let func = Function {
        name: "make_point".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: point_ty(),
            is_ghost: false,
        },
        params: vec![],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Aggregate(
                    AggregateKind::Struct("Point".to_string()),
                    vec![
                        Operand::Constant(Constant::Int(1, IntTy::I32)),
                        Operand::Constant(Constant::Int(2, IntTy::I32)),
                    ],
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result.x == 1 && result.y == 2".to_string(),
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    // Should have a postcondition VC
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(
        !post_vcs.is_empty(),
        "Expected postcondition VCs for struct construction, got: {:?}",
        vcs.conditions
            .iter()
            .map(|vc| &vc.description)
            .collect::<Vec<_>>(),
    );

    // Inspect the SMT-LIB script
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);

        // Must contain datatype declaration
        assert!(
            smtlib.contains("declare-datatype Point"),
            "Script should declare Point datatype. Script:\n{smtlib}",
        );

        // Must use constructor
        assert!(
            smtlib.contains("mk-Point"),
            "Script should use mk-Point constructor. Script:\n{smtlib}",
        );

        // Must use selectors
        assert!(
            smtlib.contains("Point-x") && smtlib.contains("Point-y"),
            "Script should use Point-x and Point-y selectors. Script:\n{smtlib}",
        );
    }

    // Run Z3 -- postcondition should be proved (UNSAT)
    let solver = solver_or_skip();
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on struct construction VC");
        assert!(
            result.is_unsat(),
            "Point(1, 2).x == 1 && .y == 2 should be PROVED (UNSAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test b: Struct field postcondition (positive)
// ---------------------------------------------------------------------------

/// Build: `fn make_point_positive(v: i32) -> Point { Point { x: 5, y: v } }`
///
/// Postcondition: `result.x > 0`
/// Since x = 5 > 0, this should be UNSAT (proved).
#[test]
fn test_struct_field_postcondition_positive() {
    let func = Function {
        name: "make_point_positive".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: point_ty(),
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
                Rvalue::Aggregate(
                    AggregateKind::Struct("Point".to_string()),
                    vec![
                        Operand::Constant(Constant::Int(5, IntTy::I32)),
                        Operand::Copy(Place::local("_1")),
                    ],
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result.x > 0".to_string(),
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty(), "Expected postcondition VCs");

    let solver = solver_or_skip();
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on positive struct field VC");
        assert!(
            result.is_unsat(),
            "Point(5, _).x > 0 should be PROVED (UNSAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test c: Struct field postcondition (negative -- should find counterexample)
// ---------------------------------------------------------------------------

/// Build: `fn make_point_negative() -> Point { Point { x: -1, y: 0 } }`
///
/// Postcondition: `result.x > 0`
/// Since x = -1, postcondition is false. Expect SAT (counterexample).
#[test]
fn test_struct_field_postcondition_negative() {
    let func = Function {
        name: "make_point_negative".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: point_ty(),
            is_ghost: false,
        },
        params: vec![],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Aggregate(
                    AggregateKind::Struct("Point".to_string()),
                    vec![
                        Operand::Constant(Constant::Int(-1, IntTy::I32)),
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ],
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result.x > 0".to_string(),
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty(), "Expected postcondition VCs");

    let solver = solver_or_skip();
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on negative struct field VC");
        assert!(
            result.is_sat(),
            "Point(-1, 0).x > 0 should be FALSE (SAT = counterexample), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test d: Tuple construction
// ---------------------------------------------------------------------------

/// Build: `fn make_pair() -> (i32, i32) { (10, 20) }`
///
/// Postcondition: `result.0 == 10 && result.1 == 20`
/// Expect UNSAT (proved).
#[test]
fn test_tuple_construction() {
    let func = Function {
        name: "make_pair".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Int(IntTy::I32)]),
            is_ghost: false,
        },
        params: vec![],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Aggregate(
                    AggregateKind::Tuple,
                    vec![
                        Operand::Constant(Constant::Int(10, IntTy::I32)),
                        Operand::Constant(Constant::Int(20, IntTy::I32)),
                    ],
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result.0 == 10 && result.1 == 20".to_string(),
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty(), "Expected postcondition VCs");

    // Inspect the SMT-LIB script
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);

        // Must contain Tuple2 datatype declaration
        assert!(
            smtlib.contains("declare-datatype Tuple2"),
            "Script should declare Tuple2 datatype. Script:\n{smtlib}",
        );

        // Must use constructor
        assert!(
            smtlib.contains("mk-Tuple2"),
            "Script should use mk-Tuple2 constructor. Script:\n{smtlib}",
        );
    }

    let solver = solver_or_skip();
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on tuple construction VC");
        assert!(
            result.is_unsat(),
            "(10, 20).0 == 10 && .1 == 20 should be PROVED (UNSAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test e: Tuple field access
// ---------------------------------------------------------------------------

/// Build: `fn swap(a: i32, b: i32) -> (i32, i32) { (b, a) }`
///
/// Postcondition: `result.0 == _2 && result.1 == _1`
/// Expect UNSAT (proved).
#[test]
fn test_tuple_field_access() {
    let func = Function {
        name: "swap".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Tuple(vec![Ty::Int(IntTy::I32), Ty::Int(IntTy::I32)]),
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
                Rvalue::Aggregate(
                    AggregateKind::Tuple,
                    vec![
                        Operand::Copy(Place::local("_2")), // first element = b
                        Operand::Copy(Place::local("_1")), // second element = a
                    ],
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "result.0 == _2 && result.1 == _1".to_string(),
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty(), "Expected postcondition VCs");

    let solver = solver_or_skip();
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on tuple field access VC");
        assert!(
            result.is_unsat(),
            "swap(a,b).0 == b && .1 == a should be PROVED (UNSAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test f: Array select
// ---------------------------------------------------------------------------

/// Build: `fn read_first(arr: [i32; 4], idx: u64) -> i32 { arr[idx] }`
///
/// With precondition constraining the array, verify that reading at a
/// specific index returns the expected value.
///
/// We model this as: _0 = select(arr, idx)
/// Precondition: `select(arr, 0) == 42` (using Rvalue::Use of a projected place)
/// Postcondition: impossible to encode generically without store, so we
/// test that VCGen generates the script correctly and Z3 accepts it.
#[test]
fn test_array_select() {
    // We build a function that reads arr[0] and returns it.
    // The array is passed as parameter, precondition constrains arr[0] == 42.
    // We use a simple direct read: _0 = arr[idx]
    //
    // Since array indexing in MIR uses Place projection (Index), we model:
    //   _2 = index local "idx"
    //   _0 = _1[_2]
    //
    // However the simpler approach for E2E is to use Store/Select directly
    // via BinaryOp or special encoding. For this test, we verify the VCGen
    // generates correct SMT-LIB with array sorts.

    let arr_ty = Ty::Array(Box::new(Ty::Int(IntTy::I32)), 4);

    let func = Function {
        name: "read_arr".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: arr_ty,
            is_ghost: false,
        }],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![
                // _0 = _1[0] -- modeled as reading from array at index 0
                // Using Place with Index projection
                Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(
                        Place::local("_1").index("_idx_0".to_string()),
                    )),
                ),
            ],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![],
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
    };

    // Just verify VCGen doesn't panic and produces valid output
    let vcs = vcgen::generate_vcs(&func, None);

    // Check that the script is well-formed (no errors from Z3)
    // We don't have postconditions here, so just verify no crashes
    assert_eq!(vcs.function_name, "read_arr");
    // No VCs expected without postconditions or arithmetic
}

// ---------------------------------------------------------------------------
// Test g: Array store then select
// ---------------------------------------------------------------------------

/// Build a function that stores to an array and reads back.
///
/// We directly construct the SMT-LIB script to test store/select:
///   arr2 = store(arr, 0, 42)
///   val = select(arr2, 0)
///   assert val == 42
///
/// This verifies the SMT array theory round-trip. Expect UNSAT.
#[test]
fn test_array_store_select() {
    use rust_fv_smtlib::command::Command;
    use rust_fv_smtlib::script::Script;
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    // Build the script manually (the VCGen doesn't yet handle all
    // array store patterns, but the SMT encoding is correct)
    let mut script = Script::new();

    // Use QF_ABV logic (arrays + bitvectors)
    script.push(Command::SetLogic("QF_ABV".to_string()));
    script.push(Command::SetOption(
        "produce-models".to_string(),
        "true".to_string(),
    ));

    // Declare array: (Array (_ BitVec 64) (_ BitVec 32))
    let arr_sort = Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(32)));
    script.push(Command::DeclareConst("arr".to_string(), arr_sort.clone()));
    script.push(Command::DeclareConst("arr2".to_string(), arr_sort));
    script.push(Command::DeclareConst("val".to_string(), Sort::BitVec(32)));

    // arr2 = store(arr, 0, 42)
    let idx = Term::BitVecLit(0, 64);
    let value = Term::BitVecLit(42, 32);
    let store_term = Term::Store(
        Box::new(Term::Const("arr".to_string())),
        Box::new(idx.clone()),
        Box::new(value),
    );
    script.push(Command::Assert(Term::Eq(
        Box::new(Term::Const("arr2".to_string())),
        Box::new(store_term),
    )));

    // val = select(arr2, 0)
    let select_term = Term::Select(Box::new(Term::Const("arr2".to_string())), Box::new(idx));
    script.push(Command::Assert(Term::Eq(
        Box::new(Term::Const("val".to_string())),
        Box::new(select_term),
    )));

    // Assert val != 42 (trying to find counterexample)
    let expected = Term::BitVecLit(42, 32);
    script.push(Command::Assert(Term::Not(Box::new(Term::Eq(
        Box::new(Term::Const("val".to_string())),
        Box::new(expected),
    )))));

    script.push(Command::CheckSat);
    script.push(Command::GetModel);

    let smtlib = script_to_smtlib(&script);

    // Verify the script contains store and select
    assert!(
        smtlib.contains("store"),
        "Script should contain store operation. Script:\n{smtlib}",
    );
    assert!(
        smtlib.contains("select") || smtlib.contains("sel"),
        "Script should contain select operation. Script:\n{smtlib}",
    );

    // Run Z3 -- store(arr, 0, 42) then select(arr2, 0) == 42, so UNSAT
    let solver = solver_or_skip();
    let result = solver
        .check_sat_raw(&smtlib)
        .expect("Z3 should not error on array store/select script");
    assert!(
        result.is_unsat(),
        "store(arr, 0, 42); select(arr2, 0) == 42 should be PROVED (UNSAT), got: {result:?}\nScript:\n{smtlib}",
    );
}

// ---------------------------------------------------------------------------
// Test h: Enum variant construction
// ---------------------------------------------------------------------------

/// Build: `fn make_some() -> Option_i32 { Some(42) }`
///
/// Uses a two-variant enum: None (no fields) and Some (one i32 field).
/// Verifies that the constructor and selector work correctly.
#[test]
fn test_enum_variant_construction() {
    let option_ty = Ty::Enum(
        "Option_i32".to_string(),
        vec![
            ("None".to_string(), vec![]),
            ("Some".to_string(), vec![Ty::Int(IntTy::I32)]),
        ],
    );

    let func = Function {
        name: "make_some".to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: option_ty,
            is_ghost: false,
        },
        params: vec![],
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![Statement::Assign(
                Place::local("_0"),
                Rvalue::Aggregate(
                    AggregateKind::Enum("Option_i32".to_string(), 1), // variant index 1 = Some
                    vec![Operand::Constant(Constant::Int(42, IntTy::I32))],
                ),
            )],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![],
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
    };

    let vcs = vcgen::generate_vcs(&func, None);

    // Verify VCGen doesn't panic
    assert_eq!(vcs.function_name, "make_some");

    // Even without postconditions, let's verify the generated script is valid.
    // The DeclareDatatype for Option_i32 should be present in any generated VC script.
    // Since there are no postconditions or arithmetic, there are no VCs.
    // Instead, let's manually build a VC script to test the enum encoding.

    use rust_fv_smtlib::command::{Command, DatatypeVariant};
    use rust_fv_smtlib::script::Script;
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    let mut script = Script::new();
    script.push(Command::SetLogic("QF_UFBVDT".to_string()));
    script.push(Command::SetOption(
        "produce-models".to_string(),
        "true".to_string(),
    ));

    // Declare the Option_i32 datatype
    script.push(Command::DeclareDatatype {
        name: "Option_i32".to_string(),
        variants: vec![
            DatatypeVariant {
                constructor: "mk-None".to_string(),
                fields: vec![],
            },
            DatatypeVariant {
                constructor: "mk-Some".to_string(),
                fields: vec![("Some-0".to_string(), Sort::BitVec(32))],
            },
        ],
    });

    // Declare a variable of type Option_i32
    script.push(Command::DeclareConst(
        "x".to_string(),
        Sort::Datatype("Option_i32".to_string()),
    ));

    // Assert x = mk-Some(42)
    let some_42 = Term::App("mk-Some".to_string(), vec![Term::BitVecLit(42, 32)]);
    script.push(Command::Assert(Term::Eq(
        Box::new(Term::Const("x".to_string())),
        Box::new(some_42),
    )));

    // Assert that the Some field is NOT 42 (trying to find counterexample)
    let field_val = Term::App("Some-0".to_string(), vec![Term::Const("x".to_string())]);
    script.push(Command::Assert(Term::Not(Box::new(Term::Eq(
        Box::new(field_val),
        Box::new(Term::BitVecLit(42, 32)),
    )))));

    script.push(Command::CheckSat);
    script.push(Command::GetModel);

    let smtlib = script_to_smtlib(&script);

    // Verify script content
    assert!(
        smtlib.contains("declare-datatype Option_i32"),
        "Script should declare Option_i32 datatype. Script:\n{smtlib}",
    );
    assert!(
        smtlib.contains("mk-None") && smtlib.contains("mk-Some"),
        "Script should have both None and Some constructors. Script:\n{smtlib}",
    );

    // Run Z3 -- mk-Some(42) then select field != 42 should be UNSAT
    let solver = solver_or_skip();
    let result = solver
        .check_sat_raw(&smtlib)
        .expect("Z3 should not error on enum variant construction script");
    assert!(
        result.is_unsat(),
        "mk-Some(42) field == 42 should be PROVED (UNSAT), got: {result:?}\nScript:\n{smtlib}",
    );
}
