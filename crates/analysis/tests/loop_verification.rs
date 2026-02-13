//! End-to-end integration tests for loop invariant verification.
//!
//! These tests exercise the loop invariant verification pipeline:
//!   IR construction (with LoopInfo) -> VCGen (3-VC generation) -> SMT-LIB -> Z3
//!
//! Each test builds an `ir::Function` with loop structure and invariants,
//! runs `vcgen::generate_vcs`, and checks the VCs against Z3.
//!
//! The 3 VCs for each loop are:
//!   1. Initialization: precondition + pre-loop => invariant
//!   2. Preservation: invariant + condition + body => invariant
//!   3. Exit/sufficiency: invariant + NOT condition => postcondition

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
// Loop IR construction helpers
// ---------------------------------------------------------------------------

/// Build a simple counter loop:
/// ```text
/// fn counter(n: i32) -> i32 {
///     let mut i: i32 = 0;
///     while i < n { i = i + 1; }
///     return i;
/// }
/// ```
///
/// CFG:
///   bb0: _3 = 0 (i = 0); goto bb1
///   bb1 (header): _4 = _3 < _1; switchInt(_4) -> [1: bb2, otherwise: bb3]
///   bb2 (body): _3 = _3 + 1; goto bb1 (back-edge)
///   bb3 (exit): _0 = _3; return
fn make_counter_loop(invariants: Vec<SpecExpr>, contracts: Contracts) -> Function {
    Function {
        name: "counter".to_string(),
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
            // bb0: _3 = 0; goto bb1
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
                )],
                terminator: Terminator::Goto(1),
            },
            // bb1 (header): _4 = _3 < _1; switchInt(_4) -> [1: bb2, otherwise: bb3]
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_4"),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local("_3")),
                        Operand::Copy(Place::local("_1")),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_4")),
                    targets: vec![(1, 2)], // true -> body (bb2)
                    otherwise: 3,          // false -> exit (bb3)
                },
            },
            // bb2 (body): _3 = _3 + 1; goto bb1 (back-edge)
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local("_3")),
                        Operand::Constant(Constant::Int(1, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Goto(1),
            },
            // bb3 (exit): _0 = _3; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_3"))),
                )],
                terminator: Terminator::Return,
            },
        ],
        contracts,
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        loops: vec![LoopInfo {
            header_block: 1,
            back_edge_blocks: vec![2],
            invariants,
        }],
    }
}

/// Build a countdown loop:
/// ```text
/// fn countdown(n: i32) -> i32 {
///     let mut i: i32 = n;
///     while i > 0 { i = i - 1; }
///     return i;
/// }
/// ```
///
/// CFG:
///   bb0: _3 = _1 (i = n); goto bb1
///   bb1 (header): _4 = _3 > 0; switchInt(_4) -> [1: bb2, otherwise: bb3]
///   bb2 (body): _3 = _3 - 1; goto bb1
///   bb3 (exit): _0 = _3; return
fn make_countdown_loop(invariants: Vec<SpecExpr>, contracts: Contracts) -> Function {
    Function {
        name: "countdown".to_string(),
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
            // bb0: _3 = _1; goto bb1
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::Use(Operand::Copy(Place::local("_1"))),
                )],
                terminator: Terminator::Goto(1),
            },
            // bb1 (header): _4 = _3 > 0; switchInt(_4) -> [1: bb2, otherwise: bb3]
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_4"),
                    Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place::local("_3")),
                        Operand::Constant(Constant::Int(0, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_4")),
                    targets: vec![(1, 2)],
                    otherwise: 3,
                },
            },
            // bb2 (body): _3 = _3 - 1; goto bb1
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::BinaryOp(
                        BinOp::Sub,
                        Operand::Copy(Place::local("_3")),
                        Operand::Constant(Constant::Int(1, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Goto(1),
            },
            // bb3 (exit): _0 = _3; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_3"))),
                )],
                terminator: Terminator::Return,
            },
        ],
        contracts,
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        loops: vec![LoopInfo {
            header_block: 1,
            back_edge_blocks: vec![2],
            invariants,
        }],
    }
}

// ---------------------------------------------------------------------------
// Test 1: Simple counter loop with correct invariant
// ---------------------------------------------------------------------------

/// `while i < n { i += 1 }` with invariant `_3 <= _1` (i <= n)
/// and postcondition `result == _1` (i == n).
/// Precondition: `_1 >= 0` (n >= 0).
///
/// All 3 VCs should be UNSAT (invariant is correct).
#[test]
fn test_simple_counter_loop() {
    let func = make_counter_loop(
        vec![SpecExpr {
            raw: "_3 <= _1".to_string(),
        }],
        Contracts {
            requires: vec![SpecExpr {
                raw: "_1 >= 0".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "result == _1".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
    );

    let vcs = vcgen::generate_vcs(&func, None);

    // Should have loop invariant VCs
    let loop_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("loop invariant"))
        .collect();

    assert!(
        loop_vcs.len() >= 3,
        "Expected at least 3 loop invariant VCs (init, preserve, exit), got {}: {:?}",
        loop_vcs.len(),
        loop_vcs
            .iter()
            .map(|vc| &vc.description)
            .collect::<Vec<_>>(),
    );

    // Verify labels are present
    assert!(
        loop_vcs
            .iter()
            .any(|vc| vc.description.contains("initialization")),
        "Expected initialization VC label"
    );
    assert!(
        loop_vcs
            .iter()
            .any(|vc| vc.description.contains("preservation")),
        "Expected preservation VC label"
    );
    assert!(
        loop_vcs
            .iter()
            .any(|vc| vc.description.contains("sufficiency") || vc.description.contains("exit")),
        "Expected exit/sufficiency VC label"
    );

    // All loop VCs should be UNSAT (invariant is correct)
    let solver = solver_or_skip();
    for vc in &loop_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on loop invariant VC");
        assert!(
            result.is_unsat(),
            "Loop VC should be UNSAT (invariant correct): {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 2: Sum loop with correct invariant
// ---------------------------------------------------------------------------

/// Two-variable loop: `let mut count = 0; let mut i = 0; while i < n { count += 1; i += 1; }`
/// This models a loop with two coupled variables where `count` always equals `i`.
///
/// Invariant: `_3 >= 0 && _3 <= _1 && _5 == _3`
///   (i >= 0, i <= n, count == i)
/// Precondition: `_1 >= 0` (n >= 0)
/// Postcondition: `result == _1` (count == n)
///
/// This tests multi-variable loop invariants with a provable relational invariant.
/// All VCs should be UNSAT.
#[test]
fn test_two_variable_loop() {
    // _3 = i, _5 = count
    let func = Function {
        name: "two_var_loop".to_string(),
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
                name: "_3".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
            Local {
                name: "_4".to_string(),
                ty: Ty::Bool,
                is_ghost: false,
            },
            Local {
                name: "_5".to_string(),
                ty: Ty::Int(IntTy::I32),
                is_ghost: false,
            },
        ],
        basic_blocks: vec![
            // bb0: _3 = 0; _5 = 0; goto bb1
            BasicBlock {
                statements: vec![
                    Statement::Assign(
                        Place::local("_3"),
                        Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
                    ),
                    Statement::Assign(
                        Place::local("_5"),
                        Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
                    ),
                ],
                terminator: Terminator::Goto(1),
            },
            // bb1 (header): _4 = _3 < _1; switchInt -> [1: bb2, otherwise: bb3]
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_4"),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local("_3")),
                        Operand::Copy(Place::local("_1")),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_4")),
                    targets: vec![(1, 2)],
                    otherwise: 3,
                },
            },
            // bb2 (body): _5 = _5 + 1; _3 = _3 + 1; goto bb1
            BasicBlock {
                statements: vec![
                    Statement::Assign(
                        Place::local("_5"),
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local("_5")),
                            Operand::Constant(Constant::Int(1, IntTy::I32)),
                        ),
                    ),
                    Statement::Assign(
                        Place::local("_3"),
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local("_3")),
                            Operand::Constant(Constant::Int(1, IntTy::I32)),
                        ),
                    ),
                ],
                terminator: Terminator::Goto(1),
            },
            // bb3 (exit): _0 = _5; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_5"))),
                )],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![SpecExpr {
                raw: "_1 >= 0".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "result == _1".to_string(),
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
        loops: vec![LoopInfo {
            header_block: 1,
            back_edge_blocks: vec![2],
            invariants: vec![
                SpecExpr {
                    raw: "_3 >= 0".to_string(),
                },
                SpecExpr {
                    raw: "_3 <= _1".to_string(),
                },
                SpecExpr {
                    raw: "_5 == _3".to_string(),
                },
            ],
        }],
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let loop_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("loop invariant"))
        .collect();

    assert!(
        loop_vcs.len() >= 3,
        "Expected at least 3 loop VCs, got {}: {:?}",
        loop_vcs.len(),
        loop_vcs
            .iter()
            .map(|vc| &vc.description)
            .collect::<Vec<_>>(),
    );

    let solver = solver_or_skip();
    for vc in &loop_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on two-variable loop VC");
        assert!(
            result.is_unsat(),
            "Two-variable loop VC should be UNSAT: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 3: Countdown loop with correct invariant
// ---------------------------------------------------------------------------

/// `while i > 0 { i -= 1 }` with invariant `_3 >= 0` (i >= 0)
/// Postcondition: `result == 0`
/// Precondition: `_1 >= 0` (n >= 0)
#[test]
fn test_countdown_loop() {
    let func = make_countdown_loop(
        vec![SpecExpr {
            raw: "_3 >= 0".to_string(),
        }],
        Contracts {
            requires: vec![SpecExpr {
                raw: "_1 >= 0".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "result == 0".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
    );

    let vcs = vcgen::generate_vcs(&func, None);

    let loop_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("loop invariant"))
        .collect();

    assert!(
        loop_vcs.len() >= 3,
        "Expected at least 3 loop VCs for countdown, got {}",
        loop_vcs.len(),
    );

    let solver = solver_or_skip();
    for vc in &loop_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on countdown loop VC");
        assert!(
            result.is_unsat(),
            "Countdown loop VC should be UNSAT: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 4: Wrong initialization invariant (should SAT on init VC)
// ---------------------------------------------------------------------------

/// Counter loop with invariant `_3 == _1` (i == n).
/// This is FALSE on entry when i starts at 0 and n > 0.
/// The initialization VC should be SAT (counterexample found).
#[test]
fn test_wrong_init_invariant() {
    let func = make_counter_loop(
        vec![SpecExpr {
            raw: "_3 == _1".to_string(),
        }],
        Contracts {
            requires: vec![SpecExpr {
                raw: "_1 >= 1".to_string(), // n >= 1 ensures i=0 != n
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
    );

    let vcs = vcgen::generate_vcs(&func, None);

    let init_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("initialization"))
        .collect();

    assert!(!init_vcs.is_empty(), "Expected initialization VC");

    let solver = solver_or_skip();
    for vc in &init_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on wrong init invariant VC");
        assert!(
            result.is_sat(),
            "Wrong initialization invariant should be SAT (counterexample): {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 5: Wrong preservation invariant (should SAT on preservation VC)
// ---------------------------------------------------------------------------

/// Counter loop with invariant `_3 == 0` (i == 0).
/// This holds initially (i starts at 0) but breaks after one iteration
/// (i becomes 1). The preservation VC should be SAT.
#[test]
fn test_wrong_preservation_invariant() {
    let func = make_counter_loop(
        vec![SpecExpr {
            raw: "_3 == 0".to_string(),
        }],
        Contracts {
            requires: vec![SpecExpr {
                raw: "_1 >= 1".to_string(), // n >= 1 so loop executes
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
    );

    let vcs = vcgen::generate_vcs(&func, None);

    let pres_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("preservation"))
        .collect();

    assert!(!pres_vcs.is_empty(), "Expected preservation VC");

    let solver = solver_or_skip();
    for vc in &pres_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on wrong preservation VC");
        assert!(
            result.is_sat(),
            "Wrong preservation invariant (_3 == 0) should be SAT: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 6: Wrong exit postcondition (should SAT on exit VC)
// ---------------------------------------------------------------------------

/// Counter loop with correct invariant `_3 <= _1` but wrong postcondition
/// `result > _1` (should be `result == _1`).
/// The exit VC should be SAT.
#[test]
fn test_wrong_exit_postcondition() {
    let func = make_counter_loop(
        vec![SpecExpr {
            raw: "_3 <= _1".to_string(),
        }],
        Contracts {
            requires: vec![SpecExpr {
                raw: "_1 >= 0".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "result > _1".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
    );

    let vcs = vcgen::generate_vcs(&func, None);

    let exit_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("sufficiency") || vc.description.contains("exit"))
        .collect();

    assert!(!exit_vcs.is_empty(), "Expected exit/sufficiency VC");

    let solver = solver_or_skip();
    for vc in &exit_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on wrong exit postcondition VC");
        assert!(
            result.is_sat(),
            "Wrong exit postcondition (result > _1) should be SAT: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 7: Loop without invariant annotation (should be skipped)
// ---------------------------------------------------------------------------

/// A loop with NO invariant annotation should produce no loop-specific VCs.
/// Only overflow and other standard VCs should be generated.
#[test]
fn test_loop_without_invariant_skipped() {
    let func = Function {
        name: "no_invariant_loop".to_string(),
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
            // bb0: _3 = 0; goto bb1
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
                )],
                terminator: Terminator::Goto(1),
            },
            // bb1 (header): _4 = _3 < _1; switchInt -> [1: bb2, otherwise: bb3]
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_4"),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local("_3")),
                        Operand::Copy(Place::local("_1")),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_4")),
                    targets: vec![(1, 2)],
                    otherwise: 3,
                },
            },
            // bb2 (body): _3 = _3 + 1; goto bb1
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local("_3")),
                        Operand::Constant(Constant::Int(1, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Goto(1),
            },
            // bb3 (exit): _0 = _3; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_3"))),
                )],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts::default(),
        // Loop detected but NO invariants
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        loops: vec![LoopInfo {
            header_block: 1,
            back_edge_blocks: vec![2],
            invariants: vec![], // No invariant
        }],
    };

    let vcs = vcgen::generate_vcs(&func, None);

    let loop_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("loop invariant"))
        .collect();

    assert!(
        loop_vcs.is_empty(),
        "Loops without invariants should produce no loop-specific VCs, got: {:?}",
        loop_vcs
            .iter()
            .map(|vc| &vc.description)
            .collect::<Vec<_>>(),
    );
}

// ---------------------------------------------------------------------------
// Test 8: Zero-iteration loop
// ---------------------------------------------------------------------------

/// Counter loop where n == 0, so the loop condition is immediately false.
/// Init VC should still be checked (invariant must hold on entry).
/// With invariant `_3 <= _1` and _1 = 0, _3 = 0, invariant is trivially true.
/// All VCs should be UNSAT.
#[test]
fn test_zero_iteration_loop() {
    let func = make_counter_loop(
        vec![SpecExpr {
            raw: "_3 <= _1".to_string(),
        }],
        Contracts {
            requires: vec![SpecExpr {
                raw: "_1 == 0".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "result == 0".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
    );

    let vcs = vcgen::generate_vcs(&func, None);

    let loop_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("loop invariant"))
        .collect();

    // Even for zero-iteration loops, all 3 VCs should be generated
    assert!(
        loop_vcs.len() >= 3,
        "Expected at least 3 loop VCs even for zero-iteration loop, got {}",
        loop_vcs.len(),
    );

    let solver = solver_or_skip();
    for vc in &loop_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on zero-iteration loop VC");
        assert!(
            result.is_unsat(),
            "Zero-iteration loop VC should be UNSAT: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 9: Loop detection from CFG (auto-detect back-edges)
// ---------------------------------------------------------------------------

/// Test that detect_loops correctly finds the loop header when
/// loops are NOT pre-populated (relying on back-edge detection).
#[test]
fn test_loop_detection_from_cfg() {
    let func = Function {
        name: "auto_detect".to_string(),
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
            // bb0: _3 = 0; goto bb1
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
                )],
                terminator: Terminator::Goto(1),
            },
            // bb1 (header): _4 = _3 < _1; switchInt -> [1: bb2, otherwise: bb3]
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_4"),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place::local("_3")),
                        Operand::Copy(Place::local("_1")),
                    ),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_4")),
                    targets: vec![(1, 2)],
                    otherwise: 3,
                },
            },
            // bb2 (body): _3 = _3 + 1; goto bb1 (BACK-EDGE)
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_3"),
                    Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local("_3")),
                        Operand::Constant(Constant::Int(1, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Goto(1),
            },
            // bb3 (exit): _0 = _3; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_3"))),
                )],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![],
            invariants: vec![SpecExpr {
                raw: "_3 <= _1".to_string(),
            }],
            is_pure: false,
            decreases: None,
        },
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        loops: vec![], // Empty -- should be auto-detected
    };

    let detected = vcgen::detect_loops(&func);

    assert_eq!(detected.len(), 1, "Should detect exactly 1 loop");
    assert_eq!(detected[0].header_block, 1, "Loop header should be block 1");
    assert!(
        detected[0].back_edge_blocks.contains(&2),
        "Back-edge should be from block 2"
    );
    assert_eq!(
        detected[0].invariants.len(),
        1,
        "Should inherit invariants from contracts"
    );
}

// ---------------------------------------------------------------------------
// Test 10: VC description labels are specific
// ---------------------------------------------------------------------------

/// Verify that the three loop VCs have distinguishable labels
/// so users can identify which check failed.
#[test]
fn test_vc_description_labels() {
    let func = make_counter_loop(
        vec![SpecExpr {
            raw: "_3 <= _1".to_string(),
        }],
        Contracts {
            requires: vec![SpecExpr {
                raw: "_1 >= 0".to_string(),
            }],
            ensures: vec![SpecExpr {
                raw: "result == _1".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
    );

    let vcs = vcgen::generate_vcs(&func, None);

    let loop_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("loop invariant"))
        .collect();

    // Extract unique label types
    let has_init = loop_vcs
        .iter()
        .any(|vc| vc.description.contains("initialization"));
    let has_preserve = loop_vcs
        .iter()
        .any(|vc| vc.description.contains("preservation"));
    let has_exit = loop_vcs
        .iter()
        .any(|vc| vc.description.contains("sufficiency") || vc.description.contains("exit"));

    assert!(has_init, "Expected VC with 'initialization' label");
    assert!(has_preserve, "Expected VC with 'preservation' label");
    assert!(has_exit, "Expected VC with 'sufficiency'/'exit' label");

    // Verify all labels include the function name
    for vc in &loop_vcs {
        assert!(
            vc.description.contains("counter"),
            "VC description should include function name, got: {}",
            vc.description,
        );
    }

    // Verify all labels include the block index
    for vc in &loop_vcs {
        assert!(
            vc.description.contains("block 1"),
            "VC description should include block index, got: {}",
            vc.description,
        );
    }
}
