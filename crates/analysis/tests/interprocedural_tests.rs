//! End-to-end integration tests for inter-procedural verification.
//!
//! These tests exercise the modular verification pipeline:
//!   IR construction -> ContractDatabase -> VCGen (call-site encoding) -> SMT-LIB -> Z3
//!
//! Each test constructs IR Functions manually, builds a ContractDatabase with
//! callee contracts, and verifies with Z3 that the modular call-site encoding
//! (assert precondition, havoc return, assume postcondition) works correctly.

use rust_fv_analysis::contract_db::{ContractDatabase, FunctionSummary};
use rust_fv_analysis::ir::*;
use rust_fv_analysis::vcgen;
use rust_fv_solver::Z3Solver;

// ---------------------------------------------------------------------------
// Helpers
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

/// Build a simple function with a call to another function.
///
/// caller_name: Name of the calling function
/// caller_contracts: Contracts on the caller
/// callee_name: Name of the function being called (used in Terminator::Call)
/// caller_params: Parameters of the caller
/// caller_locals: Local variables of the caller
/// basic_blocks: Basic blocks for the caller
fn make_caller_function(
    caller_name: &str,
    caller_contracts: Contracts,
    caller_params: Vec<Local>,
    caller_locals: Vec<Local>,
    basic_blocks: Vec<BasicBlock>,
) -> Function {
    Function {
        name: caller_name.to_string(),
        return_local: Local {
            name: "_0".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        },
        params: caller_params,
        locals: caller_locals,
        basic_blocks,
        contracts: caller_contracts,
        generic_params: vec![],
        prophecies: vec![],
        lifetime_params: vec![],
        outlives_constraints: vec![],
        borrow_info: vec![],
        reborrow_chains: vec![],
        loops: vec![],
    }
}

/// Build a contract database entry for a callee function.
fn make_callee_summary(
    contracts: Contracts,
    param_names: Vec<&str>,
    param_types: Vec<Ty>,
    return_ty: Ty,
) -> FunctionSummary {
    FunctionSummary {
        contracts,
        param_names: param_names.into_iter().map(|s| s.to_string()).collect(),
        param_types,
        return_ty,
    }
}

// ---------------------------------------------------------------------------
// Test 1: Call site precondition satisfied
// ---------------------------------------------------------------------------

/// Caller `foo(x: i32)` with `#[requires(x > 0)]` calls `bar(y: i32)` with
/// `#[requires(y > 0)]`, passing `x` as argument. Since foo's precondition
/// implies bar's precondition, verification should succeed (all VCs UNSAT).
#[test]
fn test_call_site_precondition_satisfied() {
    // Build caller: foo(x) requires x > 0, calls bar(x), returns result of bar
    let caller = make_caller_function(
        "foo",
        Contracts {
            requires: vec![SpecExpr {
                raw: "_1 > 0".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
        vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        vec![],
        vec![
            // bb0: call bar(_1) -> _0, target bb1
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "bar".to_string(),
                    args: vec![Operand::Copy(Place::local("_1"))],
                    destination: Place::local("_0"),
                    target: 1,
                },
            },
            // bb1: return
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
    );

    // Build contract database: bar requires y > 0
    let mut db = ContractDatabase::new();
    db.insert(
        "bar".to_string(),
        make_callee_summary(
            Contracts {
                requires: vec![SpecExpr {
                    raw: "_1 > 0".to_string(),
                }],
                ensures: vec![],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            vec!["_1"],
            vec![Ty::Int(IntTy::I32)],
            Ty::Int(IntTy::I32),
        ),
    );

    let vcs = vcgen::generate_vcs(&caller, Some(&db));

    // Find call-site precondition VCs
    let call_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("call to bar"))
        .collect();
    assert!(
        !call_vcs.is_empty(),
        "Expected call-site precondition VCs, got: {:?}",
        vcs.conditions
            .iter()
            .map(|vc| &vc.description)
            .collect::<Vec<_>>(),
    );

    // All call-site VCs should be UNSAT (precondition satisfied)
    let solver = solver_or_skip();
    for vc in &call_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_unsat(),
            "foo's precondition x > 0 should imply bar's precondition y > 0 (UNSAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 2: Call site precondition violated
// ---------------------------------------------------------------------------

/// Caller `baz(x: i32)` with `#[requires(x > 0)]` calls `bar(y: i32)` with
/// `#[requires(y > 10)]`, passing `x`. Since `x > 0` does NOT imply `x > 10`,
/// the precondition VC should be SAT (violation detected).
#[test]
fn test_call_site_precondition_violated() {
    let caller = make_caller_function(
        "baz",
        Contracts {
            requires: vec![SpecExpr {
                raw: "_1 > 0".to_string(),
            }],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
        vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        vec![],
        vec![
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "bar".to_string(),
                    args: vec![Operand::Copy(Place::local("_1"))],
                    destination: Place::local("_0"),
                    target: 1,
                },
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
    );

    let mut db = ContractDatabase::new();
    db.insert(
        "bar".to_string(),
        make_callee_summary(
            Contracts {
                requires: vec![SpecExpr {
                    raw: "_1 > 10".to_string(),
                }],
                ensures: vec![],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            vec!["_1"],
            vec![Ty::Int(IntTy::I32)],
            Ty::Int(IntTy::I32),
        ),
    );

    let vcs = vcgen::generate_vcs(&caller, Some(&db));

    let call_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("call to bar"))
        .collect();
    assert!(!call_vcs.is_empty(), "Expected call-site precondition VCs");

    let solver = solver_or_skip();
    for vc in &call_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_sat(),
            "x > 0 does NOT imply x > 10, so precondition VC should be SAT, got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 3: Call site postcondition assumed
// ---------------------------------------------------------------------------

/// Caller `compute(a: i32, b: i32)` calls `add(x: i32, y: i32)` which has
/// `#[ensures(result == x + y)]`. Caller has `#[ensures(result == a + b)]`
/// and assigns the return of add to `_0`. With postcondition assumption,
/// the caller's postcondition should verify.
#[test]
fn test_call_site_postcondition_assumed() {
    // compute(a, b): calls add(a, b), stores result in _0
    // requires a >= 0 && a <= 100, b >= 0 && b <= 100 (to avoid overflow)
    // ensures result == _1 + _2
    let caller = Function {
        name: "compute".to_string(),
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
        basic_blocks: vec![
            // bb0: call add(_1, _2) -> _0, target bb1
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "add".to_string(),
                    args: vec![
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_2")),
                    ],
                    destination: Place::local("_0"),
                    target: 1,
                },
            },
            // bb1: return
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
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
                raw: "result == _1 + _2".to_string(),
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
        loops: vec![],
    };

    // add(x, y) ensures result == x + y
    let mut db = ContractDatabase::new();
    db.insert(
        "add".to_string(),
        make_callee_summary(
            Contracts {
                requires: vec![],
                ensures: vec![SpecExpr {
                    raw: "result == _1 + _2".to_string(),
                }],
                invariants: vec![],
                is_pure: true,
                decreases: None,
            },
            vec!["_1", "_2"],
            vec![Ty::Int(IntTy::I32), Ty::Int(IntTy::I32)],
            Ty::Int(IntTy::I32),
        ),
    );

    let vcs = vcgen::generate_vcs(&caller, Some(&db));

    // Find postcondition VCs
    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty(), "Expected postcondition VCs");

    let solver = solver_or_skip();
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_unsat(),
            "With add's postcondition assumed, compute's postcondition should verify (UNSAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 4: Postcondition NOT assumed without contract database
// ---------------------------------------------------------------------------

/// Same as test 3 but pass `None` for contract_db. The caller's postcondition
/// should NOT verify because the destination is unconstrained.
#[test]
fn test_call_site_postcondition_not_assumed_without_db() {
    let caller = Function {
        name: "compute".to_string(),
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
        basic_blocks: vec![
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "add".to_string(),
                    args: vec![
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_2")),
                    ],
                    destination: Place::local("_0"),
                    target: 1,
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
                    raw: "_1 >= 0 && _1 <= 100".to_string(),
                },
                SpecExpr {
                    raw: "_2 >= 0 && _2 <= 100".to_string(),
                },
            ],
            ensures: vec![SpecExpr {
                raw: "result == _1 + _2".to_string(),
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
        loops: vec![],
    };

    // No contract database -- call destination is unconstrained
    let vcs = vcgen::generate_vcs(&caller, None);

    let post_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("postcondition"))
        .collect();
    assert!(!post_vcs.is_empty(), "Expected postcondition VCs");

    let solver = solver_or_skip();
    for vc in &post_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_sat(),
            "Without contract DB, _0 is unconstrained so postcondition should FAIL (SAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 5: Call chain -- no exponential blowup
// ---------------------------------------------------------------------------

/// Build a chain of 5 functions, each calling the next, with simple contracts.
/// All should verify. This demonstrates modular verification scales linearly.
#[test]
fn test_call_chain_no_blowup() {
    // Chain: f1 -> f2 -> f3 -> f4 -> f5
    // Each function: requires x > 0, ensures result > 0
    // Each calls the next with its argument and returns the result

    let mut db = ContractDatabase::new();

    // Register f2..f5 in the contract database
    for i in 2..=5 {
        db.insert(
            format!("f{i}"),
            make_callee_summary(
                Contracts {
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
                vec!["_1"],
                vec![Ty::Int(IntTy::I32)],
                Ty::Int(IntTy::I32),
            ),
        );
    }

    // Build f1: calls f2, has same contracts
    let f1 = Function {
        name: "f1".to_string(),
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
        basic_blocks: vec![
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "f2".to_string(),
                    args: vec![Operand::Copy(Place::local("_1"))],
                    destination: Place::local("_0"),
                    target: 1,
                },
            },
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
        loops: vec![],
    };

    let start = std::time::Instant::now();
    let vcs = vcgen::generate_vcs(&f1, Some(&db));
    let elapsed = start.elapsed();

    // Verify all VCs pass
    let solver = solver_or_skip();
    for vc in &vcs.conditions {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_unsat(),
            "Chain verification should succeed (UNSAT), got: {result:?}\nVC: {}\nScript:\n{smtlib}",
            vc.description,
        );
    }

    // Should complete quickly (well under 5 seconds)
    assert!(
        elapsed.as_secs() < 5,
        "Modular verification of 5-function chain took {:?}, expected < 5s",
        elapsed,
    );
}

// ---------------------------------------------------------------------------
// Test 6: Call without contracts treated as opaque
// ---------------------------------------------------------------------------

/// Caller calls a function not in the ContractDatabase. The call destination
/// remains unconstrained. No crash, no VC generated for the call site.
#[test]
fn test_call_without_contracts_treated_as_opaque() {
    let caller = Function {
        name: "caller".to_string(),
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
        basic_blocks: vec![
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "unknown_func".to_string(),
                    args: vec![Operand::Copy(Place::local("_1"))],
                    destination: Place::local("_0"),
                    target: 1,
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
        loops: vec![],
    };

    // Empty contract database -- unknown_func has no entry
    let db = ContractDatabase::new();
    let vcs = vcgen::generate_vcs(&caller, Some(&db));

    // No call-site VCs should be generated for an unknown function
    let call_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("call to"))
        .collect();
    assert!(
        call_vcs.is_empty(),
        "Should not generate call-site VCs for unknown functions, got: {:?}",
        call_vcs
            .iter()
            .map(|vc| &vc.description)
            .collect::<Vec<_>>(),
    );

    // Compare with None contract_db -- should produce identical VCs
    let vcs_none = vcgen::generate_vcs(&caller, None);
    assert_eq!(
        vcs.conditions.len(),
        vcs_none.conditions.len(),
        "Opaque call (empty DB) should produce same VCs as None DB"
    );
}

// ---------------------------------------------------------------------------
// Test 7: Precondition violation reports callee name
// ---------------------------------------------------------------------------

/// When a precondition VC is SAT, the VC description includes the callee
/// function name and the specific precondition string.
#[test]
fn test_precondition_violation_reports_callee_name() {
    let caller = make_caller_function(
        "my_caller",
        Contracts {
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
        vec![Local {
            name: "_1".to_string(),
            ty: Ty::Int(IntTy::I32),
            is_ghost: false,
        }],
        vec![],
        vec![
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "specific_callee".to_string(),
                    args: vec![Operand::Copy(Place::local("_1"))],
                    destination: Place::local("_0"),
                    target: 1,
                },
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
    );

    let mut db = ContractDatabase::new();
    db.insert(
        "specific_callee".to_string(),
        make_callee_summary(
            Contracts {
                requires: vec![SpecExpr {
                    raw: "_1 > 42".to_string(),
                }],
                ensures: vec![],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            vec!["_1"],
            vec![Ty::Int(IntTy::I32)],
            Ty::Int(IntTy::I32),
        ),
    );

    let vcs = vcgen::generate_vcs(&caller, Some(&db));

    let call_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("call to"))
        .collect();
    assert!(!call_vcs.is_empty());

    // Check that description includes callee name and precondition
    for vc in &call_vcs {
        assert!(
            vc.description.contains("specific_callee"),
            "VC description should contain callee name: {}",
            vc.description,
        );
        assert!(
            vc.description.contains("_1 > 42"),
            "VC description should contain precondition spec: {}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 8: Multiple preconditions each checked
// ---------------------------------------------------------------------------

/// Callee has two preconditions. Each gets its own VC.
#[test]
fn test_multiple_preconditions_each_checked() {
    let caller = make_caller_function(
        "multi_pre_caller",
        Contracts {
            requires: vec![
                SpecExpr {
                    raw: "_1 > 0".to_string(),
                },
                SpecExpr {
                    raw: "_2 > 0".to_string(),
                },
            ],
            ensures: vec![],
            invariants: vec![],
            is_pure: false,
            decreases: None,
        },
        vec![
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
        vec![],
        vec![
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "multi_pre_callee".to_string(),
                    args: vec![
                        Operand::Copy(Place::local("_1")),
                        Operand::Copy(Place::local("_2")),
                    ],
                    destination: Place::local("_0"),
                    target: 1,
                },
            },
            BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            },
        ],
    );

    let mut db = ContractDatabase::new();
    db.insert(
        "multi_pre_callee".to_string(),
        make_callee_summary(
            Contracts {
                requires: vec![
                    SpecExpr {
                        raw: "_1 > 0".to_string(),
                    },
                    SpecExpr {
                        raw: "_2 > 0".to_string(),
                    },
                ],
                ensures: vec![],
                invariants: vec![],
                is_pure: false,
                decreases: None,
            },
            vec!["_1", "_2"],
            vec![Ty::Int(IntTy::I32), Ty::Int(IntTy::I32)],
            Ty::Int(IntTy::I32),
        ),
    );

    let vcs = vcgen::generate_vcs(&caller, Some(&db));

    let call_vcs: Vec<_> = vcs
        .conditions
        .iter()
        .filter(|vc| vc.description.contains("call to multi_pre_callee"))
        .collect();

    // Should have exactly 2 VCs (one per precondition)
    assert_eq!(
        call_vcs.len(),
        2,
        "Expected 2 call-site VCs (one per precondition), got: {:?}",
        call_vcs
            .iter()
            .map(|vc| &vc.description)
            .collect::<Vec<_>>(),
    );

    // Both should include different precondition indices
    assert!(call_vcs[0].description.contains("precondition 0"));
    assert!(call_vcs[1].description.contains("precondition 1"));

    // Both should verify (caller's preconditions imply callee's)
    let solver = solver_or_skip();
    for vc in &call_vcs {
        let smtlib = script_to_smtlib(&vc.script);
        let result = solver.check_sat_raw(&smtlib).expect("Z3 should not error");
        assert!(
            result.is_unsat(),
            "Caller's preconditions should satisfy callee's (UNSAT), got: {result:?}\nVC: {}",
            vc.description,
        );
    }
}

// ---------------------------------------------------------------------------
// Test 9: normalize_callee_name unit tests
// ---------------------------------------------------------------------------

#[test]
fn test_normalize_callee_name() {
    assert_eq!(vcgen::normalize_callee_name("const add"), "add");
    assert_eq!(
        vcgen::normalize_callee_name("const my_module::helper"),
        "helper"
    );
    assert_eq!(vcgen::normalize_callee_name("add"), "add");
    assert_eq!(
        vcgen::normalize_callee_name("const std::ops::Add::add"),
        "add"
    );
    assert_eq!(vcgen::normalize_callee_name("  const foo  "), "foo");
    assert_eq!(
        vcgen::normalize_callee_name("const a::b::c::deep_fn"),
        "deep_fn"
    );
}

// ---------------------------------------------------------------------------
// Test 10: substitute_term unit tests
// ---------------------------------------------------------------------------

#[test]
fn test_substitute_term() {
    use rust_fv_smtlib::term::Term;
    use std::collections::HashMap;

    let mut subs = HashMap::new();
    subs.insert("_1".to_string(), Term::Const("_3".to_string()));
    subs.insert("_2".to_string(), Term::BitVecLit(42, 32));

    // Simple constant substitution
    let t = Term::Const("_1".to_string());
    let result = vcgen::substitute_term(&t, &subs);
    assert_eq!(result, Term::Const("_3".to_string()));

    // No substitution for unmapped constant
    let t = Term::Const("_5".to_string());
    let result = vcgen::substitute_term(&t, &subs);
    assert_eq!(result, Term::Const("_5".to_string()));

    // Substitution in nested terms
    let t = Term::BvSGt(
        Box::new(Term::Const("_1".to_string())),
        Box::new(Term::BitVecLit(0, 32)),
    );
    let result = vcgen::substitute_term(&t, &subs);
    assert_eq!(
        result,
        Term::BvSGt(
            Box::new(Term::Const("_3".to_string())),
            Box::new(Term::BitVecLit(0, 32)),
        )
    );

    // Substitution in And
    let t = Term::And(vec![
        Term::Const("_1".to_string()),
        Term::Const("_2".to_string()),
    ]);
    let result = vcgen::substitute_term(&t, &subs);
    assert_eq!(
        result,
        Term::And(vec![Term::Const("_3".to_string()), Term::BitVecLit(42, 32),])
    );

    // Literal passthrough
    let t = Term::BitVecLit(100, 32);
    let result = vcgen::substitute_term(&t, &subs);
    assert_eq!(result, Term::BitVecLit(100, 32));

    // Eq substitution
    let t = Term::Eq(
        Box::new(Term::Const("_0".to_string())),
        Box::new(Term::BvAdd(
            Box::new(Term::Const("_1".to_string())),
            Box::new(Term::Const("_2".to_string())),
        )),
    );
    let result = vcgen::substitute_term(&t, &subs);
    assert_eq!(
        result,
        Term::Eq(
            Box::new(Term::Const("_0".to_string())),
            Box::new(Term::BvAdd(
                Box::new(Term::Const("_3".to_string())),
                Box::new(Term::BitVecLit(42, 32)),
            )),
        )
    );
}
