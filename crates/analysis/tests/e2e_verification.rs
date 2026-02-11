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
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Int(IntTy::I32),
            },
        ],
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
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
        is_pure: false,
    });

    // Step 1: Generate VCs
    let vcs = vcgen::generate_vcs(&func);
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
        is_pure: false,
    });

    // Step 1: Generate VCs
    let vcs = vcgen::generate_vcs(&func);

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
        is_pure: false,
    });

    // Step 1: Generate VCs
    let vcs = vcgen::generate_vcs(&func);

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
        is_pure: false,
    });

    // Step 1: Generate VCs
    let vcs = vcgen::generate_vcs(&func);

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
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Int(IntTy::I32),
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Int(IntTy::I32),
            },
        ],
        locals: vec![Local {
            name: "_3".to_string(),
            ty: Ty::Bool,
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
        is_pure: true,
    });

    let vcs = vcgen::generate_vcs(&func);

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
        is_pure: true,
    });

    let vcs = vcgen::generate_vcs(&func);

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
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
        }],
        locals: vec![
            Local {
                name: "_2".to_string(),
                ty: Ty::Bool,
            },
            Local {
                name: "_3".to_string(),
                ty: Ty::Bool,
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
        is_pure: true,
    });

    let vcs = vcgen::generate_vcs(&func);

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
        },
        params: vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
        }],
        locals: vec![Local {
            name: "_2".to_string(),
            ty: Ty::Bool,
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
        is_pure: true,
    });

    let vcs = vcgen::generate_vcs(&func);

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
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Int(IntTy::I32),
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Int(IntTy::I32),
            },
        ],
        locals: vec![
            Local {
                name: "_3".to_string(),
                ty: Ty::Bool,
            },
            Local {
                name: "_4".to_string(),
                ty: Ty::Bool,
            },
            Local {
                name: "_5".to_string(),
                ty: Ty::Bool,
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
        is_pure: true,
    });

    let vcs = vcgen::generate_vcs(&func);

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
        },
        params: vec![
            Local {
                name: "_1".to_string(),
                ty: Ty::Int(IntTy::I32),
            },
            Local {
                name: "_2".to_string(),
                ty: Ty::Bool,
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
            is_pure: true,
        },
    };

    let vcs = vcgen::generate_vcs(&func);

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
