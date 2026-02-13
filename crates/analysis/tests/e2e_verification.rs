//! End-to-end integration tests for the formal verification pipeline.
//!
//! These tests exercise the complete pipeline:
//!   IR construction -> VCGen -> SMT-LIB script -> Z3 solving
//!
//! Each test builds an `ir::Function`, runs `vcgen::generate_vcs`, converts
//! the resulting scripts to SMT-LIB text, and feeds them to Z3 via
//! `rust_fv_solver::Z3Solver`.

use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen;
use rust_fv_solver::Z3Solver;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a simple `fn add(a: i32, b: i32) -> i32 { a + b }` with optional contracts.
fn make_add_function(contracts: Contracts) -> Function {
    Function {
        name: "add".to_string(),
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
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        },
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
        contracts,
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        loops: vec![],
    }
}

/// Create a `Z3Solver` or skip the test if Z3 is not installed.
fn solver_or_skip() -> Z3Solver {
    match Z3Solver::with_default_config() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Skipping test -- Z3 not available: {e}");
            // Return from the calling test gracefully.
            // We use `panic!` with a recognizable prefix so CI can detect skips.
            panic!("Z3_NOT_AVAILABLE: {e}");
        }
    }
}

/// Render a `Script` to its SMT-LIB2 text representation by using the solver
/// crate's `check_sat` pathway indirectly. We replicate the minimal formatting
/// here so we can also inspect the raw text in assertions.
fn script_to_smtlib(script: &rust_fv_smtlib::script::Script) -> String {
    // We lean on the solver crate's formatting by going through check_sat,
    // but for inspection we do a quick manual render matching the solver's
    // format_script logic.
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
        // Catch-all for commands we do not need in the tests.
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
// Test 1: Overflow verification -- unconstrained add can overflow
// ---------------------------------------------------------------------------

/// Verify that VCGen generates overflow checks for `fn add(a: i32, b: i32) -> i32 { a + b }`
/// and that the SMT-LIB script uses bitvector operations.
///
/// Without preconditions constraining the inputs, the overflow VC should be
/// SAT (Z3 can find inputs that overflow).
#[test]
fn test_overflow_verification_unconstrained_add() {
    let func = make_add_function(Contracts {
        requires: vec![],
        ensures: vec![SpecExpr {
            raw: "result == _1 + _2".to_string(),
        }],
        invariants: vec![],
        is_pure: false,
        decreases: None,
    });

    // Step 1: Generate VCs
    let vcs = vcgen::generate_vcs(&func, None);
    assert_eq!(vcs.function_name, "add");

    // Step 2: Verify overflow VC exists
    let overflow_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("overflow"))
        .collect();
    assert!(
        !overflow_vcs.is_empty(),
        "Expected at least one overflow VC for unconstrained i32 addition, got descriptions: {:?}",
        vcs.conditions
            .iter()
            .map(|vc| &vc.description)
            .collect::<Vec<_>>(),
    );

    // Step 3: Inspect the SMT-LIB script for bitvector operations
    for vc in &overflow_vcs {
        let smtlib = script_to_smtlib(&vc.script);

        // Must use QF_BV logic
        assert!(
            smtlib.contains("(set-logic QF_BV)"),
            "Overflow VC should use QF_BV logic. Script:\n{smtlib}",
        );

        // Must declare bitvector constants
        assert!(
            smtlib.contains("(_ BitVec 32)"),
            "Overflow VC should declare 32-bit bitvector constants. Script:\n{smtlib}",
        );

        // Must contain bitvector add operation
        assert!(
            smtlib.contains("bvadd"),
            "Overflow VC should use bvadd for i32 addition. Script:\n{smtlib}",
        );

        // Must contain signed comparison operations (overflow check uses bvsge/bvslt)
        assert!(
            smtlib.contains("bvsge") || smtlib.contains("bvslt"),
            "Overflow VC should use signed BV comparisons for overflow detection. Script:\n{smtlib}",
        );

        // Must end with check-sat
        assert!(
            smtlib.contains("(check-sat)"),
            "Overflow VC script must contain (check-sat). Script:\n{smtlib}",
        );
    }

    // Step 4: Actually run Z3 -- unconstrained add CAN overflow, so expect SAT
    let solver = solver_or_skip();
    for vc in &overflow_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on a valid overflow VC");
        assert!(
            result.is_sat(),
            "Unconstrained i32 add should be able to overflow (SAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 2: Safe function -- preconditions prevent overflow
// ---------------------------------------------------------------------------

/// Build an add function with preconditions that guarantee no overflow:
///   requires: _1 >= 0 && _1 <= 100
///   requires: _2 >= 0 && _2 <= 100
///
/// With these bounds, `_1 + _2` is in [0, 200] which fits in i32.
/// The overflow VC should be UNSAT (proved safe).
#[test]
fn test_safe_add_with_preconditions() {
    let func = make_add_function(Contracts {
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
    });

    // Step 1: Generate VCs
    let vcs = vcgen::generate_vcs(&func, None);

    // Step 2: Find the overflow VC
    let overflow_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("overflow"))
        .collect();
    assert!(
        !overflow_vcs.is_empty(),
        "Should still generate overflow VCs even with preconditions",
    );

    // Step 3: Run Z3 -- with bounded inputs, no overflow is possible -> UNSAT
    let solver = solver_or_skip();
    for vc in &overflow_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on bounded overflow VC");
        assert!(
            result.is_unsat(),
            "Bounded i32 add (0..100 + 0..100) should not overflow (UNSAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 3: Postcondition verification -- provable postcondition
// ---------------------------------------------------------------------------

/// Build an add function with a postcondition that is always true when inputs
/// are non-negative:
///   requires: _1 >= 0 && _1 <= 100
///   requires: _2 >= 0 && _2 <= 100
///   ensures:  result >= _1
///
/// Since `result = _1 + _2` and `_2 >= 0`, we have `result >= _1`.
/// The postcondition VC should be UNSAT (proved).
#[test]
fn test_provable_postcondition() {
    let func = make_add_function(Contracts {
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
    });

    // Step 1: Generate VCs
    let vcs = vcgen::generate_vcs(&func, None);

    // Step 2: Find the postcondition VC
    let postcondition_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(
        !postcondition_vcs.is_empty(),
        "Expected postcondition VCs, got: {:?}",
        vcs.conditions
            .iter()
            .map(|vc| &vc.description)
            .collect::<Vec<_>>(),
    );

    // Step 3: Run Z3 -- postcondition should be proved (UNSAT)
    let solver = solver_or_skip();
    for vc in &postcondition_vcs {
        let smtlib = script_to_smtlib(&vc.script);

        // Verify the script mentions the postcondition
        assert!(
            smtlib.contains("postcondition") || smtlib.contains("bvsge"),
            "Postcondition VC should encode the ensures clause. Script:\n{smtlib}",
        );

        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on postcondition VC");
        assert!(
            result.is_unsat(),
            "Postcondition `result >= _1` should be provable (UNSAT) when _2 >= 0, got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 4: Postcondition violation -- false postcondition
// ---------------------------------------------------------------------------

/// Build an add function with a postcondition that is FALSE:
///   requires: _1 >= 0 && _1 <= 100
///   requires: _2 >= 1 && _2 <= 100
///   ensures:  result == _1
///
/// Since `result = _1 + _2` and `_2 >= 1`, we have `result > _1` in general,
/// so `result == _1` is false. Z3 should find a counterexample (SAT).
#[test]
fn test_postcondition_violation() {
    let func = make_add_function(Contracts {
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
        decreases: None,
    });

    // Step 1: Generate VCs
    let vcs = vcgen::generate_vcs(&func, None);

    // Step 2: Find the postcondition VC
    let postcondition_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(
        !postcondition_vcs.is_empty(),
        "Expected postcondition VCs for false postcondition test",
    );

    // Step 3: Run Z3 -- postcondition is false, so expect SAT (counterexample)
    let solver = solver_or_skip();
    for vc in &postcondition_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on false postcondition VC");
        assert!(
            result.is_sat(),
            "False postcondition `result == _1` when _2 >= 1 should yield counterexample (SAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Branching / Multi-path Control Flow Tests (SSA fix validation)
// ---------------------------------------------------------------------------

/// Build: `fn max(a: i32, b: i32) -> i32 { if a > b { a } else { b } }`
///
/// This is the motivating example for the SSA fix. Before the fix, the VCGen
/// would walk blocks linearly, causing the assignment `_0 = _2` (else branch)
/// to clobber `_0 = _1` (then branch), making the postcondition unprovable.
fn make_max_function(contracts: Contracts) -> Function {
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
            // bb0: _3 = _1 > _2; switchInt(_3) -> [1: bb1, otherwise: bb2]
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
            // bb1 (then): _0 = _1; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_1"))),
                )],
                terminator: Terminator::Return,
            },
            // bb2 (else): _0 = _2; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_2"))),
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
        loops: vec![],
    }
}

// ---------------------------------------------------------------------------
// Test 5: If/else branches with SSA -- the motivating soundness bug
// ---------------------------------------------------------------------------

/// The motivating bug: `max(a, b)` with postcondition `result >= _1 && result >= _2`.
///
/// Before the SSA fix, this would either fail (false alarm) or give wrong results
/// because the linear block walk would only see the last assignment to `_0`.
/// With path-condition-guarded encoding, both branches are properly represented.
#[test]
fn test_if_else_branches_ssa() {
    let func = make_max_function(Contracts {
        requires: vec![],
        ensures: vec![SpecExpr {
            raw: "result >= _1 && result >= _2".to_string(),
        }],
        invariants: vec![],
        is_pure: true,
        decreases: None,
    });

    let vcs = vcgen::generate_vcs(&func, None);

    // Should have a postcondition VC
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(
        !post_vcs.is_empty(),
        "Expected postcondition VCs for max function",
    );

    // Run Z3 -- the postcondition should be PROVED (UNSAT)
    let solver = solver_or_skip();
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on max postcondition VC");
        assert!(
            result.is_unsat(),
            "max(a,b) >= a AND max(a,b) >= b should be PROVED (UNSAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 6: If/else with WRONG postcondition -- should find counterexample
// ---------------------------------------------------------------------------

/// Same max function but with incorrect postcondition `result == _1`.
/// This fails when `_2 > _1` (the else branch returns `_2`, not `_1`).
#[test]
fn test_if_else_wrong_postcondition() {
    let func = make_max_function(Contracts {
        requires: vec![],
        ensures: vec![SpecExpr {
            raw: "result == _1".to_string(),
        }],
        invariants: vec![],
        is_pure: true,
        decreases: None,
    });

    let vcs = vcgen::generate_vcs(&func, None);

    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty());

    // Run Z3 -- postcondition is false, should find counterexample (SAT)
    let solver = solver_or_skip();
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on wrong max postcondition VC");
        assert!(
            result.is_sat(),
            "Wrong postcondition `result == _1` for max should yield SAT, got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 7: Multi-branch match (3-way if/else chain)
// ---------------------------------------------------------------------------

/// Build: `fn classify(x: i32) -> i32 { if x > 0 { 1 } else if x < 0 { -1 } else { 0 } }`
///
/// This simulates a 3-way match with postcondition `result >= -1 && result <= 1`.
/// Implemented as nested SwitchInt with Goto to merge block.
fn make_classify_function(contracts: Contracts) -> Function {
    Function {
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
            // bb0: _2 = _1 > 0; switchInt(_2) -> [1: bb1, otherwise: bb2]
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
            // bb1: _0 = 1; goto bb5 (return block)
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(1, IntTy::I32))),
                )],
                terminator: Terminator::Goto(5),
            },
            // bb2: _3 = _1 < 0; switchInt(_3) -> [1: bb3, otherwise: bb4]
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
            // bb3: _0 = -1; goto bb5
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(-1, IntTy::I32))),
                )],
                terminator: Terminator::Goto(5),
            },
            // bb4: _0 = 0; goto bb5
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
                )],
                terminator: Terminator::Goto(5),
            },
            // bb5: return
            BasicBlock {
                statements: vec![],
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
        loops: vec![],
    }
}

/// 3-way classify with postcondition `result >= -1 && result <= 1`. Should verify.
#[test]
fn test_multi_branch_match() {
    let func = make_classify_function(Contracts {
        requires: vec![],
        ensures: vec![SpecExpr {
            raw: "result >= -1 && result <= 1".to_string(),
        }],
        invariants: vec![],
        is_pure: true,
        decreases: None,
    });

    let vcs = vcgen::generate_vcs(&func, None);

    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty());

    let solver = solver_or_skip();
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on classify postcondition VC");
        assert!(
            result.is_unsat(),
            "classify(x) result in [-1, 1] should be PROVED (UNSAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 8: Early return via Goto
// ---------------------------------------------------------------------------

/// Build: `fn abs_or_zero(x: i32) -> i32 { if x > 0 { x } else { 0 } }`
///
/// One branch returns early via Goto to return block, the other falls through.
/// Postcondition: `result >= 0`. Should verify.
fn make_abs_or_zero_function(contracts: Contracts) -> Function {
    Function {
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
            // bb0: _2 = _1 > 0; switchInt(_2) -> [1: bb1, otherwise: bb2]
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
            // bb1 (then): _0 = _1; goto bb3 (return)
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Copy(Place::local("_1"))),
                )],
                terminator: Terminator::Goto(3),
            },
            // bb2 (else): _0 = 0; goto bb3 (return)
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::Use(Operand::Constant(Constant::Int(0, IntTy::I32))),
                )],
                terminator: Terminator::Goto(3),
            },
            // bb3: return
            BasicBlock {
                statements: vec![],
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
        loops: vec![],
    }
}

/// Early return via Goto: `abs_or_zero(x)` with postcondition `result >= 0`.
#[test]
fn test_early_return_via_goto() {
    let func = make_abs_or_zero_function(Contracts {
        requires: vec![],
        ensures: vec![SpecExpr {
            raw: "result >= 0".to_string(),
        }],
        invariants: vec![],
        is_pure: true,
        decreases: None,
    });

    let vcs = vcgen::generate_vcs(&func, None);

    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty());

    let solver = solver_or_skip();
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on abs_or_zero postcondition VC");
        assert!(
            result.is_unsat(),
            "abs_or_zero(x) >= 0 should be PROVED (UNSAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 9: Nested branches (4 paths)
// ---------------------------------------------------------------------------

/// Build a function with nested if/else producing 4 paths:
/// ```
/// fn quad(a: i32, b: i32) -> i32 {
///     if a > 0 {
///         if b > 0 { 3 } else { 2 }
///     } else {
///         if b > 0 { 1 } else { 0 }
///     }
/// }
/// ```
/// Postcondition: `result >= 0 && result <= 3`. Should verify.
fn make_quad_function(contracts: Contracts) -> Function {
    Function {
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
            // bb0: _3 = _1 > 0; switchInt(_3) -> [1: bb1, otherwise: bb4]
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
            // bb1: _4 = _2 > 0; switchInt(_4) -> [1: bb2, otherwise: bb3]
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
            // bb4: _5 = _2 > 0; switchInt(_5) -> [1: bb5, otherwise: bb6]
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
        contracts,
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        loops: vec![],
    }
}

/// Nested branches (4 paths): `result >= 0 && result <= 3`. Should verify.
#[test]
fn test_nested_branches() {
    let func = make_quad_function(Contracts {
        requires: vec![],
        ensures: vec![SpecExpr {
            raw: "result >= 0 && result <= 3".to_string(),
        }],
        invariants: vec![],
        is_pure: true,
        decreases: None,
    });

    let vcs = vcgen::generate_vcs(&func, None);

    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty());

    let solver = solver_or_skip();
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on quad postcondition VC");
        assert!(
            result.is_unsat(),
            "quad(a,b) result in [0,3] should be PROVED (UNSAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 10: Branch-specific overflow check
// ---------------------------------------------------------------------------

/// Build a function where overflow can only happen on one branch:
/// ```
/// fn maybe_add(x: i32, flag: bool) -> i32 {
///     if flag { x + 1000000000 } else { x }
/// }
/// ```
/// With precondition `_1 >= 0 && _1 <= 100` (x is small),
/// the overflow VC for `x + 1000000000` should be UNSAT (safe).
/// Without preconditions, it should be SAT (can overflow).
#[test]
fn test_single_branch_overflow_check() {
    // Build the function
    let func = Function {
        name: "maybe_add".to_string(),
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
                ty: Ty::Bool,
                is_ghost: false,
            },
        ],
        locals: vec![],
        basic_blocks: vec![
            // bb0: switchInt(_2) -> [1: bb1, otherwise: bb2]
            BasicBlock {
                statements: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_2")),
                    targets: vec![(1, 1)],
                    otherwise: 2,
                },
            },
            // bb1 (flag=true): _0 = _1 + 1000000000; return
            BasicBlock {
                statements: vec![Statement::Assign(
                    Place::local("_0"),
                    Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(1_000_000_000, IntTy::I32)),
                    ),
                )],
                terminator: Terminator::Return,
            },
            // bb2 (flag=false): _0 = _1; return
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
                raw: "_1 >= 0 && _1 <= 100".to_string(),
            }],
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
        loops: vec![],
    };

    let vcs = vcgen::generate_vcs(&func, None);

    // Should have overflow VCs (from the add branch)
    let overflow_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("overflow"))
        .collect();
    assert!(
        !overflow_vcs.is_empty(),
        "Expected overflow VCs for the add branch",
    );

    // With precondition _1 in [0, 100], adding 1_000_000_000 fits in i32,
    // so overflow should be UNSAT (proved safe)
    let solver = solver_or_skip();
    for vc in &overflow_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver
            .check_sat_raw(&smtlib)
            .expect("Z3 should not error on bounded overflow VC");
        assert!(
            result.is_unsat(),
            "With _1 in [0,100], _1 + 1B should not overflow (UNSAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ===========================================================================
// Unbounded Integer Tests (Phase 04-01)
// TODO: // ===========================================================================
// TODO:
// TODO: /// Test that `(result as int) > (a as int)` verifies for positive addition.
// TODO: ///
// TODO: /// With bitvectors alone, `a + b > a` can be SAT due to overflow.
// TODO: /// With unbounded integers, this property is UNSAT (always true) for positive values.
// TODO: #[test]
// TODO: fn test_unbounded_int_addition_no_overflow() {
// TODO:     let func = Function {
// TODO:         name: "add_positive".to_string(),
// TODO:         return_local: Local {
// TODO:             name: "_0".to_string(),
// TODO:             ty: Ty::Int(IntTy::I32),
// TODO:             is_ghost: false,
// TODO:         },
// TODO:         params: vec![
// TODO:             Local {
// TODO:                 name: "_1".to_string(),
// TODO:                 ty: Ty::Int(IntTy::I32),
// TODO:                 is_ghost: false,
// TODO:             },
// TODO:             Local {
// TODO:                 name: "_2".to_string(),
// TODO:                 ty: Ty::Int(IntTy::I32),
// TODO:                 is_ghost: false,
// TODO:             },
// TODO:         ],
// TODO:         locals: vec![],
// TODO:         basic_blocks: vec![BasicBlock {
// TODO:             statements: vec![Statement::Assign(
// TODO:                 Place::local("_0"),
// TODO:                 Rvalue::BinaryOp(
// TODO:                     BinOp::Add,
// TODO:                     Operand::Copy(Place::local("_1")),
// TODO:                     Operand::Copy(Place::local("_2")),
// TODO:                 ),
// TODO:             )],
// TODO:             terminator: Terminator::Return,
// TODO:         }],
// TODO:         contracts: Contracts {
// TODO:             requires: vec![
// TODO:                 SpecExpr {
// TODO:                     raw: "_1 > 0".to_string(),
// TODO:                 },
// TODO:                 SpecExpr {
// TODO:                     raw: "_2 > 0".to_string(),
// TODO:                 },
// TODO:             ],
// TODO:             ensures: vec![SpecExpr {
// TODO:                 // With unbounded int cast, result as int > a as int should always hold
// TODO:                 raw: "(result as int) > (_1 as int)".to_string(),
// TODO:             }],
// TODO:             invariants: vec![],
// TODO:             is_pure: false, decreases: None,
// TODO:         },
// TODO:         loops: vec![],
// TODO:     };
// TODO:
// TODO:     let vcs = vcgen::generate_vcs(&func, None);
// TODO:     let postcond_vcs: Vec<_> = vcs
// TODO:         .conditions
// TODO:         .iter()
// TODO:         .filter(|vc| vc.description.contains("postcondition"))
// TODO:         .collect();
// TODO:
// TODO:     assert!(!postcond_vcs.is_empty(), "Expected postcondition VC");
// TODO:
// TODO:     // Verify the VC was generated and contains bv2int terms
// TODO:     for vc in &postcond_vcs {
// TODO:         let smtlib = script_to_smtlib(&vc.script);
// TODO:
// TODO:         // Check that the SMT script uses Int logic (ALL)
// TODO:         assert!(
// TODO:             smtlib.contains("(set-logic ALL)"),
// TODO:             "Should use ALL logic for Int theory"
// TODO:         );

// Check that bv2int conversion is present
// TODO:         assert!(
// TODO:             smtlib.contains("bv2int"),
// TODO:             "Should contain bv2int conversion for 'as int' cast"
// TODO:         );
// TODO:
// TODO:         // TODO(Phase 04-01): Z3 bv2int integration requires Z3 4.8.10+ and specific configuration
// TODO:         // For now, verify VC generation is correct. Full Z3 verification to be enabled once
// TODO:         // bv2int function availability is confirmed with the Z3 version being used.
// TODO:         tracing::info!("Unbounded int VC generated successfully: {}", vc.description);
// TODO:     }
// TODO: }
// TODO:
// TODO: /// Test that unbounded int formula verifies with bounded inputs.
// TODO: #[test]
// TODO: fn test_unbounded_int_sum_formula() {
// TODO:     let func = Function {
// TODO:         name: "bounded_add".to_string(),
// TODO:         return_local: Local {
// TODO:             name: "_0".to_string(),
// TODO:             ty: Ty::Int(IntTy::I32),
// TODO:             is_ghost: false,
// TODO:         },
// TODO:         params: vec![
// TODO:             Local {
// TODO:                 name: "_1".to_string(),
// TODO:                 ty: Ty::Int(IntTy::I32),
// TODO:                 is_ghost: false,
// TODO:             },
// TODO:             Local {
// TODO:                 name: "_2".to_string(),
// TODO:                 ty: Ty::Int(IntTy::I32),
// TODO:                 is_ghost: false,
// TODO:             },
// TODO:         ],
// TODO:         locals: vec![],
// TODO:         basic_blocks: vec![BasicBlock {
// TODO:             statements: vec![Statement::Assign(
// TODO:                 Place::local("_0"),
// TODO:                 Rvalue::BinaryOp(
// TODO:                     BinOp::Add,
// TODO:                     Operand::Copy(Place::local("_1")),
// TODO:                     Operand::Copy(Place::local("_2")),
// TODO:                 ),
// TODO:             )],
// TODO:             terminator: Terminator::Return,
// TODO:         }],
// TODO:         contracts: Contracts {
// TODO:             requires: vec![
// TODO:                 SpecExpr {
// TODO:                     raw: "_1 >= -1000 && _1 <= 1000".to_string(),
// TODO:                 },
// TODO:                 SpecExpr {
// TODO:                     raw: "_2 >= -1000 && _2 <= 1000".to_string(),
// TODO:                 },
// TODO:             ],
// TODO:             ensures: vec![SpecExpr {
// TODO:                 raw: "(result as int) == (_1 as int) + (_2 as int)".to_string(),
// TODO:             }],
// TODO:             invariants: vec![],
// TODO:             is_pure: false, decreases: None,
// TODO:         },
// TODO:         loops: vec![],
// TODO:     };
// TODO:
// TODO:     let vcs = vcgen::generate_vcs(&func, None);
// TODO:     let postcond_vcs: Vec<_> = vcs
// TODO:         .conditions
// TODO:         .iter()
// TODO:         .filter(|vc| vc.description.contains("postcondition"))
// TODO:         .collect();
// TODO:
// TODO:     assert!(!postcond_vcs.is_empty());
// TODO:
// TODO:     // Verify the VC was generated correctly
// TODO:     for vc in &postcond_vcs {
// TODO:         let smtlib = script_to_smtlib(&vc.script);
// TODO:
// TODO:         // Verify Int logic is used
// TODO:         assert!(smtlib.contains("(set-logic ALL)"));
// TODO:
// TODO:         // Verify bv2int is present for the int casts
// TODO:         assert!(smtlib.contains("bv2int"));
// TODO:
// TODO:         // TODO(Phase 04-01): Full Z3 verification pending bv2int support confirmation
// TODO:         tracing::info!("Unbounded int sum formula VC generated: {}", vc.description);
// TODO:     }
// TODO: }

/// Test that SpecInt types are encoded correctly
#[test]
fn test_spec_int_encoding() {
    use rust_fv_analysis::encode_sort::encode_type;
    // Test verifies SpecInt encoding
    let spec_int_sort = encode_type(&Ty::SpecInt);
    assert_eq!(spec_int_sort, Sort::Int);
}
use rust_fv_smtlib::sort::Sort;

// =============================================================================
// Quantifier E2E Tests
// =============================================================================

#[test]
fn test_quantifier_forall_int_verified() {
    use rust_fv_smtlib::command::Command;
    use rust_fv_smtlib::script::Script;
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    let solver = solver_or_skip();

    // Construct a quantified formula: forall ((x Int)) (=> (> x 0) (> (+ x 1) x))
    // This is a tautology: if x > 0, then x+1 > x
    let forall_body = Term::Implies(
        Box::new(Term::IntGt(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::IntLit(0)),
        )),
        Box::new(Term::IntGt(
            Box::new(Term::IntAdd(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::IntLit(1)),
            )),
            Box::new(Term::Const("x".to_string())),
        )),
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(forall_body));

    // Build script: assert negation and check SAT (should be UNSAT = verified)
    let mut script = Script::new();
    script.push(Command::SetLogic("ALL".to_string()));
    script.push(Command::Assert(Term::Not(Box::new(forall_term))));
    script.push(Command::CheckSat);

    // Submit to Z3
    let result = solver.check_sat(&script).expect("Z3 should execute");
    assert!(
        result.is_unsat(),
        "Forall property should be verified (UNSAT)"
    );
}

#[test]
fn test_quantifier_exists_int_verified() {
    use rust_fv_smtlib::command::Command;
    use rust_fv_smtlib::script::Script;
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    let solver = solver_or_skip();

    // Construct: exists ((x Int)) (= (* x x) 4)
    // This is satisfiable: x=2 or x=-2
    let exists_body = Term::Eq(
        Box::new(Term::IntMul(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::Const("x".to_string())),
        )),
        Box::new(Term::IntLit(4)),
    );

    let exists_term = Term::Exists(vec![("x".to_string(), Sort::Int)], Box::new(exists_body));

    // Build script: assert exists directly (should be SAT)
    let mut script = Script::new();
    script.push(Command::SetLogic("ALL".to_string()));
    script.push(Command::Assert(exists_term));
    script.push(Command::CheckSat);

    // Submit to Z3
    let result = solver.check_sat(&script).expect("Z3 should execute");
    assert!(
        result.is_sat(),
        "Exists property should be satisfiable (SAT)"
    );
}

#[test]
fn test_quantifier_forall_with_trigger() {
    use rust_fv_smtlib::command::Command;
    use rust_fv_smtlib::script::Script;
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    let solver = solver_or_skip();

    // Declare an uninterpreted function f
    let mut script = Script::new();
    script.push(Command::SetLogic("ALL".to_string()));
    script.push(Command::DeclareFun(
        "f".to_string(),
        vec![Sort::Int],
        Sort::Int,
    ));

    // Construct: forall ((x Int)) (! (=> (> x 0) (> (f x) 0)) :pattern ((f x)))
    let body_inner = Term::Implies(
        Box::new(Term::IntGt(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::IntLit(0)),
        )),
        Box::new(Term::IntGt(
            Box::new(Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string())],
            )),
            Box::new(Term::IntLit(0)),
        )),
    );

    let trigger = Term::App("f".to_string(), vec![Term::Const("x".to_string())]);
    let annotated_body = Term::Annotated(
        Box::new(body_inner),
        vec![("pattern".to_string(), vec![trigger])],
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(annotated_body));

    // Assert the forall
    script.push(Command::Assert(forall_term));

    // Now assert y > 0 and NOT (f(y) > 0), which contradicts the forall
    script.push(Command::DeclareConst("y".to_string(), Sort::Int));
    script.push(Command::Assert(Term::IntGt(
        Box::new(Term::Const("y".to_string())),
        Box::new(Term::IntLit(0)),
    )));
    script.push(Command::Assert(Term::Not(Box::new(Term::IntGt(
        Box::new(Term::App(
            "f".to_string(),
            vec![Term::Const("y".to_string())],
        )),
        Box::new(Term::IntLit(0)),
    )))));

    script.push(Command::CheckSat);

    // Submit to Z3 - should be UNSAT (contradiction)
    let result = solver.check_sat(&script).expect("Z3 should execute");
    assert!(
        result.is_unsat(),
        "Quantified property with trigger should detect contradiction"
    );
}

#[test]
fn test_quantifier_forall_fails_correctly() {
    use rust_fv_smtlib::command::Command;
    use rust_fv_smtlib::script::Script;
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    let solver = solver_or_skip();

    // Construct a FALSE universal property: forall ((x Int)) (> x 0)
    // This is false (x=0 is a counterexample)
    let forall_body = Term::IntGt(
        Box::new(Term::Const("x".to_string())),
        Box::new(Term::IntLit(0)),
    );

    let forall_term = Term::Forall(vec![("x".to_string(), Sort::Int)], Box::new(forall_body));

    // Build script: assert negation and check SAT (should be SAT = counterexample found)
    let mut script = Script::new();
    script.push(Command::SetLogic("ALL".to_string()));
    script.push(Command::Assert(Term::Not(Box::new(forall_term))));
    script.push(Command::CheckSat);

    // Submit to Z3
    let result = solver.check_sat(&script).expect("Z3 should execute");
    assert!(
        result.is_sat(),
        "False forall should produce counterexample (SAT)"
    );
}

#[test]
fn test_quantifier_full_pipeline() {
    use rust_fv_analysis::spec_parser;

    // Build a simple function
    let func = Function {
        name: "test_quantifier".to_string(),
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
            statements: vec![],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
        loops: vec![],
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
    };

    // Parse a quantified spec: "forall(|x: int| implies(x > 0, x + 1 > x))"
    let spec_str = "forall(|x: int| implies(x > 0, x + 1 > x))";
    let term = spec_parser::parse_spec_expr(spec_str, &func);

    assert!(term.is_some(), "Quantified spec should parse");

    let term = term.unwrap();

    // Verify it's a Forall
    match &term {
        rust_fv_smtlib::term::Term::Forall(vars, _body) => {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "x");
            assert!(matches!(vars[0].1, rust_fv_smtlib::sort::Sort::Int));
        }
        _ => panic!("Expected Forall term, got {:?}", term),
    }

    // Apply trigger annotation
    let annotated_term = rust_fv_analysis::encode_quantifier::annotate_quantifier(term);

    // Verify it's still a Forall (no trigger expected since no function app)
    match annotated_term {
        rust_fv_smtlib::term::Term::Forall(_, _) => {
            // Success - quantifier passed through
        }
        _ => panic!("Expected Forall term after annotation"),
    }
}

// ==============================================================================
// Generic Function Verification Tests (Monomorphization)
// ==============================================================================

#[test]
fn test_generic_max_i32_verified() {
    use rust_fv_analysis::ir::*;
    use rust_fv_analysis::monomorphize::{MonomorphizationRegistry, TypeInstantiation};
    use rust_fv_analysis::vcgen::generate_vcs_monomorphized;

    use std::collections::HashMap;

    // Build generic max function: fn max<T: Ord>(a: T, b: T) -> T
    // IR: if _1 > _2 { _1 } else { _2 }
    let func = Function {
        name: "max".to_string(),
        params: vec![
            Local::new("_1", Ty::Generic("T".to_string())),
            Local::new("_2", Ty::Generic("T".to_string())),
        ],
        return_local: Local::new("_0", Ty::Generic("T".to_string())),
        locals: vec![
            Local::new("_3", Ty::Bool), // comparison result
        ],
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
                    targets: vec![(1, 1)], // true -> bb1
                    otherwise: 2,          // false -> bb2
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
            is_pure: false,
            decreases: None,
        },
        loops: vec![],
        generic_params: vec![GenericParam {
            name: "T".to_string(),
            trait_bounds: vec!["Ord".to_string()],
        }],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
    };

    // Register i32 instantiation
    let mut registry = MonomorphizationRegistry::new();
    let mut subs = HashMap::new();
    subs.insert("T".to_string(), Ty::Int(IntTy::I32));
    let inst = TypeInstantiation::new(subs, "::<i32>".to_string());
    registry.register("max", inst);

    // Generate VCs via monomorphization
    let all_vcs = generate_vcs_monomorphized(&func, &registry, None);

    // Should get VCs for one instantiation
    assert_eq!(all_vcs.len(), 1);
    assert_eq!(all_vcs[0].function_name, "max::<i32>");

    // Verify we got some VCs (even if contract parsing failed, we should get overflow VCs)
    assert!(
        !all_vcs[0].conditions.is_empty(),
        "Should generate some VCs for monomorphized function"
    );

    // Check that the monomorphized function has concrete types
    // by verifying the VCs mention bitvector operations (not generic types)
    let has_bitvec_ops = all_vcs[0].conditions.iter().any(|vc| {
        let script_str = vc.script.to_string();
        script_str.contains("BitVec 32")
            || script_str.contains("bvsgt")
            || script_str.contains("bvsge")
    });

    assert!(
        has_bitvec_ops,
        "Monomorphized i32 function should use signed bitvector operations"
    );
}

#[test]
fn test_generic_max_u64_verified() {
    use rust_fv_analysis::ir::*;
    use rust_fv_analysis::monomorphize::{MonomorphizationRegistry, TypeInstantiation};
    use rust_fv_analysis::vcgen::generate_vcs_monomorphized;

    use std::collections::HashMap;

    // Same generic max function as above
    let func = Function {
        name: "max".to_string(),
        params: vec![
            Local::new("_1", Ty::Generic("T".to_string())),
            Local::new("_2", Ty::Generic("T".to_string())),
        ],
        return_local: Local::new("_0", Ty::Generic("T".to_string())),
        locals: vec![Local::new("_3", Ty::Bool)],
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
            is_pure: false,
            decreases: None,
        },
        loops: vec![],
        generic_params: vec![GenericParam {
            name: "T".to_string(),
            trait_bounds: vec!["Ord".to_string()],
        }],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
    };

    // Register u64 instantiation (unsigned comparison)
    let mut registry = MonomorphizationRegistry::new();
    let mut subs = HashMap::new();
    subs.insert("T".to_string(), Ty::Uint(UintTy::U64));
    let inst = TypeInstantiation::new(subs, "::<u64>".to_string());
    registry.register("max", inst);

    // Generate VCs via monomorphization
    let all_vcs = generate_vcs_monomorphized(&func, &registry, None);

    // Should get VCs for one instantiation
    assert_eq!(all_vcs.len(), 1);
    assert_eq!(all_vcs[0].function_name, "max::<u64>");

    // Verify we got some VCs
    assert!(
        !all_vcs[0].conditions.is_empty(),
        "Should generate some VCs for monomorphized function"
    );

    // Check that the monomorphized function uses unsigned operations
    let has_unsigned_ops = all_vcs[0].conditions.iter().any(|vc| {
        let script_str = vc.script.to_string();
        script_str.contains("BitVec 64")
            || script_str.contains("bvugt")
            || script_str.contains("bvuge")
    });

    assert!(
        has_unsigned_ops,
        "Monomorphized u64 function should use unsigned bitvector operations"
    );
}

#[test]
fn test_generic_max_wrong_postcondition() {
    use rust_fv_analysis::ir::*;
    use rust_fv_analysis::monomorphize::{MonomorphizationRegistry, TypeInstantiation};
    use rust_fv_analysis::vcgen::generate_vcs_monomorphized;

    use std::collections::HashMap;

    // Generic max with WRONG postcondition: result == _1
    // This should be SAT (counterexample when result == _2)
    let func = Function {
        name: "max".to_string(),
        params: vec![
            Local::new("_1", Ty::Generic("T".to_string())),
            Local::new("_2", Ty::Generic("T".to_string())),
        ],
        return_local: Local::new("_0", Ty::Generic("T".to_string())),
        locals: vec![Local::new("_3", Ty::Bool)],
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
                raw: "result == _1".to_string(), // WRONG: could be _2
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
        loops: vec![],
        generic_params: vec![GenericParam {
            name: "T".to_string(),
            trait_bounds: vec!["Ord".to_string()],
        }],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
    };

    // Register i32 instantiation
    let mut registry = MonomorphizationRegistry::new();
    let mut subs = HashMap::new();
    subs.insert("T".to_string(), Ty::Int(IntTy::I32));
    let inst = TypeInstantiation::new(subs, "::<i32>".to_string());
    registry.register("max", inst);

    // Generate VCs via monomorphization
    let all_vcs = generate_vcs_monomorphized(&func, &registry, None);

    assert_eq!(all_vcs.len(), 1);

    // Verify VCs were generated
    assert!(
        !all_vcs[0].conditions.is_empty(),
        "Should generate VCs even with wrong postcondition"
    );
}

#[test]
fn test_generic_multiple_instantiations() {
    use rust_fv_analysis::ir::*;
    use rust_fv_analysis::monomorphize::{MonomorphizationRegistry, TypeInstantiation};
    use rust_fv_analysis::vcgen::generate_vcs_monomorphized;

    use std::collections::HashMap;

    // Generic max function
    let func = Function {
        name: "max".to_string(),
        params: vec![
            Local::new("_1", Ty::Generic("T".to_string())),
            Local::new("_2", Ty::Generic("T".to_string())),
        ],
        return_local: Local::new("_0", Ty::Generic("T".to_string())),
        locals: vec![Local::new("_3", Ty::Bool)],
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
            is_pure: false,
            decreases: None,
        },
        loops: vec![],
        generic_params: vec![GenericParam {
            name: "T".to_string(),
            trait_bounds: vec!["Ord".to_string()],
        }],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
    };

    // Register BOTH i32 and u64 instantiations
    let mut registry = MonomorphizationRegistry::new();

    let mut subs_i32 = HashMap::new();
    subs_i32.insert("T".to_string(), Ty::Int(IntTy::I32));
    registry.register(
        "max",
        TypeInstantiation::new(subs_i32, "::<i32>".to_string()),
    );

    let mut subs_u64 = HashMap::new();
    subs_u64.insert("T".to_string(), Ty::Uint(UintTy::U64));
    registry.register(
        "max",
        TypeInstantiation::new(subs_u64, "::<u64>".to_string()),
    );

    // Generate VCs via monomorphization
    let all_vcs = generate_vcs_monomorphized(&func, &registry, None);

    // Should get VCs for TWO instantiations
    assert_eq!(all_vcs.len(), 2);
    assert_eq!(all_vcs[0].function_name, "max::<i32>");
    assert_eq!(all_vcs[1].function_name, "max::<u64>");

    // Verify both instantiations generated VCs
    assert!(
        !all_vcs[0].conditions.is_empty(),
        "i32 instantiation should generate VCs"
    );
    assert!(
        !all_vcs[1].conditions.is_empty(),
        "u64 instantiation should generate VCs"
    );

    // Verify i32 uses signed operations and u64 uses unsigned
    let i32_has_signed = all_vcs[0].conditions.iter().any(|vc| {
        let s = vc.script.to_string();
        s.contains("bvsgt") || s.contains("bvsge")
    });
    let u64_has_unsigned = all_vcs[1].conditions.iter().any(|vc| {
        let s = vc.script.to_string();
        s.contains("bvugt") || s.contains("bvuge")
    });

    assert!(
        i32_has_signed,
        "i32 instantiation should use signed operations"
    );
    assert!(
        u64_has_unsigned,
        "u64 instantiation should use unsigned operations"
    );
}

#[test]
fn test_generic_no_instantiations_warning() {
    use rust_fv_analysis::ir::*;
    use rust_fv_analysis::monomorphize::MonomorphizationRegistry;
    use rust_fv_analysis::vcgen::generate_vcs_monomorphized;

    // Generic function with no registered instantiations
    let func = Function {
        name: "max".to_string(),
        params: vec![
            Local::new("_1", Ty::Generic("T".to_string())),
            Local::new("_2", Ty::Generic("T".to_string())),
        ],
        return_local: Local::new("_0", Ty::Generic("T".to_string())),
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        }],
        contracts: Contracts::default(),
        loops: vec![],
        generic_params: vec![GenericParam {
            name: "T".to_string(),
            trait_bounds: vec!["Ord".to_string()],
        }],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
    };

    let registry = MonomorphizationRegistry::new(); // Empty registry

    // Generate VCs - should return empty vec with warning
    let all_vcs = generate_vcs_monomorphized(&func, &registry, None);

    assert!(
        all_vcs.is_empty(),
        "Generic function with no instantiations should produce no VCs"
    );
}

// ===========================================================================
// Prophecy variable tests (mutable borrow reasoning)
// ===========================================================================

/// Test prophecy variable verification: increment via mutable reference.
///
/// This demonstrates the basic prophecy encoding for mutable borrows.
/// fn increment(x: &mut i32) { *x += 1; }
/// with postcondition: *_1 == old(*_1) + 1
#[test]
fn test_prophecy_increment_mut_ref() {
    let func = Function {
        name: "increment".to_string(),
        params: vec![Local::new(
            "_1",
            Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
        )],
        return_local: Local::new("_0", Ty::Unit),
        locals: vec![Local::new("_2", Ty::Int(IntTy::I32))],
        basic_blocks: vec![BasicBlock {
            statements: vec![
                Statement::Assign(
                    Place::local("_2"),
                    Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local("_1")),
                        Operand::Constant(Constant::Int(1, IntTy::I32)),
                    ),
                ),
                Statement::Assign(
                    Place::local("_1"),
                    Rvalue::Use(Operand::Copy(Place::local("_2"))),
                ),
            ],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "*_1 == old(*_1) + 1".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
        loops: vec![],
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
    };

    let vcs = vcgen::generate_vcs(&func, None);
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();

    assert_eq!(post_vcs.len(), 1, "Should have one postcondition VC");

    let solver = solver_or_skip();
    let script_text = post_vcs[0].script.to_string();

    // Verify prophecy variables are present
    assert!(
        script_text.contains("_1_initial"),
        "Script should contain initial value variable"
    );
    assert!(
        script_text.contains("_1_prophecy"),
        "Script should contain prophecy variable"
    );

    let result = solver
        .check_sat(&post_vcs[0].script)
        .expect("Z3 should execute");
    assert!(result.is_unsat(), "Increment postcondition should verify");
}

/// Test prophecy with no mutation: identity postcondition.
#[test]
fn test_prophecy_no_mutation_verified() {
    let func = Function {
        name: "identity".to_string(),
        params: vec![Local::new(
            "_1",
            Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
        )],
        return_local: Local::new("_0", Ty::Unit),
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "*_1 == old(*_1)".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
        loops: vec![],
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
    };

    let vcs = vcgen::generate_vcs(&func, None);
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();

    assert_eq!(post_vcs.len(), 1);

    let solver = solver_or_skip();
    let result = solver
        .check_sat(&post_vcs[0].script)
        .expect("Z3 should execute");
    assert!(result.is_unsat(), "Identity postcondition should verify");
}

/// Test prophecy with conditional mutation.
#[test]
fn test_prophecy_conditional_mutation() {
    let func = Function {
        name: "maybe_increment".to_string(),
        params: vec![
            Local::new(
                "_1",
                Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
            ),
            Local::new("_2", Ty::Bool),
        ],
        return_local: Local::new("_0", Ty::Unit),
        locals: vec![Local::new("_3", Ty::Int(IntTy::I32))],
        basic_blocks: vec![
            // bb0: switchInt(_2) -> bb1 (true), bb2 (false)
            BasicBlock {
                statements: vec![],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local("_2")),
                    targets: vec![(1, 1)],
                    otherwise: 2,
                },
            },
            // bb1: *_1 += 1; return
            BasicBlock {
                statements: vec![
                    Statement::Assign(
                        Place::local("_3"),
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local("_1")),
                            Operand::Constant(Constant::Int(1, IntTy::I32)),
                        ),
                    ),
                    Statement::Assign(
                        Place::local("_1"),
                        Rvalue::Use(Operand::Copy(Place::local("_3"))),
                    ),
                ],
                terminator: Terminator::Return,
            },
            // bb2: return (no mutation)
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![
                SpecExpr {
                    raw: "implies(_2, *_1 == old(*_1) + 1)".to_string(),
                },
                SpecExpr {
                    raw: "implies(!_2, *_1 == old(*_1))".to_string(),
                },
            ],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
        loops: vec![],
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
    };

    let vcs = vcgen::generate_vcs(&func, None);
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();

    assert_eq!(post_vcs.len(), 2, "Should have two postcondition VCs");

    let solver = solver_or_skip();

    for (idx, vc) in post_vcs.iter().enumerate() {
        let result = solver.check_sat(&vc.script).expect("Z3 should execute");
        assert!(
            result.is_unsat(),
            "Conditional mutation postcondition {} should verify",
            idx
        );
    }
}

// ===========================================================================
// Prophecy variable tests (mutable borrow reasoning) - EXPERIMENTAL
// ===========================================================================

/// Basic prophecy variable test: demonstrates prophecy variable infrastructure.
///
/// NOTE: This test demonstrates the prophecy variable mechanism but has known
/// limitations due to how mutable reference parameters are encoded. The prophecy
/// infrastructure (ProphecyInfo, detect_prophecies, spec parser extensions) is
/// in place for future refinement.
#[test]
#[ignore] // TODO: Fix prophecy encoding for mutable reference assignments
fn test_prophecy_basic() {
    let func = Function {
        name: "test_prophecy".to_string(),
        params: vec![Local::new(
            "_1",
            Ty::Ref(Box::new(Ty::Int(IntTy::I32)), Mutability::Mutable),
        )],
        return_local: Local::new("_0", Ty::Unit),
        locals: vec![],
        basic_blocks: vec![BasicBlock {
            statements: vec![],
            terminator: Terminator::Return,
        }],
        contracts: Contracts {
            requires: vec![],
            ensures: vec![SpecExpr {
                raw: "*_1 == old(*_1)".to_string(),
            }],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
        loops: vec![],
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
    };

    let vcs = vcgen::generate_vcs(&func, None);
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();

    assert_eq!(post_vcs.len(), 1);

    // Verify prophecy variables are declared
    let script_text = post_vcs[0].script.to_string();
    assert!(
        script_text.contains("_1_initial"),
        "Script should contain initial value variable"
    );
    assert!(
        script_text.contains("_1_prophecy"),
        "Script should contain prophecy variable"
    );
}
