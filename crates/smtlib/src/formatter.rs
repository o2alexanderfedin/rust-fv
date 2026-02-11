//! SMT-LIB2 text formatting for AST types.
//!
//! Implements `Display` for [`Sort`], [`Term`], [`Command`], and [`Script`],
//! producing valid SMT-LIB2 output that can be parsed by solvers such as Z3.

use std::fmt;

use crate::command::Command;
use crate::script::Script;
use crate::sort::Sort;
use crate::term::Term;

// ---------------------------------------------------------------------------
// Sort
// ---------------------------------------------------------------------------

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "Bool"),
            Sort::Int => write!(f, "Int"),
            Sort::Real => write!(f, "Real"),
            Sort::BitVec(width) => write!(f, "(_ BitVec {width})"),
            Sort::Array(index, element) => write!(f, "(Array {index} {element})"),
            Sort::Datatype(name) => write!(f, "{name}"),
            Sort::Float(e, s) => write!(f, "(_ FloatingPoint {e} {s})"),
            Sort::Uninterpreted(name) => write!(f, "{name}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Term
// ---------------------------------------------------------------------------

/// Format a bitvector literal. Negative values are converted to their
/// two's-complement unsigned representation for the given bit-width.
fn fmt_bv_lit(value: i128, width: u32, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let unsigned = if value < 0 {
        // Two's complement: wrap into [0, 2^width)
        let modulus: u128 = 1u128 << width;
        ((modulus as i128) + value) as u128
    } else {
        value as u128
    };
    write!(f, "(_ bv{unsigned} {width})")
}

/// Write a binary SMT-LIB operator: `(op lhs rhs)`.
fn fmt_binop(op: &str, lhs: &Term, rhs: &Term, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "({op} {lhs} {rhs})")
}

/// Write a unary SMT-LIB operator: `(op arg)`.
fn fmt_unop(op: &str, arg: &Term, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "({op} {arg})")
}

/// Write sorted variable bindings: `((x Sort) (y Sort) ...)`.
fn fmt_sorted_vars(vars: &[(String, Sort)], f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "(")?;
    for (i, (name, sort)) in vars.iter().enumerate() {
        if i > 0 {
            write!(f, " ")?;
        }
        write!(f, "({name} {sort})")?;
    }
    write!(f, ")")
}

/// Write let-bindings: `((x term) (y term) ...)`.
fn fmt_let_bindings(bindings: &[(String, Term)], f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "(")?;
    for (i, (name, term)) in bindings.iter().enumerate() {
        if i > 0 {
            write!(f, " ")?;
        }
        write!(f, "({name} {term})")?;
    }
    write!(f, ")")
}

/// Write a space-separated list of terms.
fn fmt_term_list(terms: &[Term], f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for (i, t) in terms.iter().enumerate() {
        if i > 0 {
            write!(f, " ")?;
        }
        write!(f, "{t}")?;
    }
    Ok(())
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // --- Literals ---
            Term::BoolLit(true) => write!(f, "true"),
            Term::BoolLit(false) => write!(f, "false"),
            Term::IntLit(n) => {
                if *n < 0 {
                    // SMT-LIB represents negative integers as `(- N)`
                    write!(f, "(- {})", -n)
                } else {
                    write!(f, "{n}")
                }
            }
            Term::BitVecLit(value, width) => fmt_bv_lit(*value, *width, f),

            // --- Variables ---
            Term::Const(name) => write!(f, "{name}"),

            // --- Boolean operations ---
            Term::Not(inner) => fmt_unop("not", inner, f),
            Term::And(terms) => {
                if terms.is_empty() {
                    write!(f, "true")
                } else {
                    write!(f, "(and ")?;
                    fmt_term_list(terms, f)?;
                    write!(f, ")")
                }
            }
            Term::Or(terms) => {
                if terms.is_empty() {
                    write!(f, "false")
                } else {
                    write!(f, "(or ")?;
                    fmt_term_list(terms, f)?;
                    write!(f, ")")
                }
            }
            Term::Implies(lhs, rhs) => fmt_binop("=>", lhs, rhs, f),
            Term::Iff(lhs, rhs) => fmt_binop("=", lhs, rhs, f),

            // --- Core ---
            Term::Eq(lhs, rhs) => fmt_binop("=", lhs, rhs, f),
            Term::Distinct(terms) => {
                write!(f, "(distinct ")?;
                fmt_term_list(terms, f)?;
                write!(f, ")")
            }
            Term::Ite(cond, then_branch, else_branch) => {
                write!(f, "(ite {cond} {then_branch} {else_branch})")
            }

            // --- Bitvector arithmetic ---
            Term::BvAdd(a, b) => fmt_binop("bvadd", a, b, f),
            Term::BvSub(a, b) => fmt_binop("bvsub", a, b, f),
            Term::BvMul(a, b) => fmt_binop("bvmul", a, b, f),
            Term::BvSDiv(a, b) => fmt_binop("bvsdiv", a, b, f),
            Term::BvUDiv(a, b) => fmt_binop("bvudiv", a, b, f),
            Term::BvSRem(a, b) => fmt_binop("bvsrem", a, b, f),
            Term::BvURem(a, b) => fmt_binop("bvurem", a, b, f),
            Term::BvNeg(a) => fmt_unop("bvneg", a, f),

            // --- Bitvector comparison (signed) ---
            Term::BvSLt(a, b) => fmt_binop("bvslt", a, b, f),
            Term::BvSLe(a, b) => fmt_binop("bvsle", a, b, f),
            Term::BvSGt(a, b) => fmt_binop("bvsgt", a, b, f),
            Term::BvSGe(a, b) => fmt_binop("bvsge", a, b, f),

            // --- Bitvector comparison (unsigned) ---
            Term::BvULt(a, b) => fmt_binop("bvult", a, b, f),
            Term::BvULe(a, b) => fmt_binop("bvule", a, b, f),
            Term::BvUGt(a, b) => fmt_binop("bvugt", a, b, f),
            Term::BvUGe(a, b) => fmt_binop("bvuge", a, b, f),

            // --- Bitvector bitwise ---
            Term::BvAnd(a, b) => fmt_binop("bvand", a, b, f),
            Term::BvOr(a, b) => fmt_binop("bvor", a, b, f),
            Term::BvXor(a, b) => fmt_binop("bvxor", a, b, f),
            Term::BvNot(a) => fmt_unop("bvnot", a, f),
            Term::BvShl(a, b) => fmt_binop("bvshl", a, b, f),
            Term::BvLShr(a, b) => fmt_binop("bvlshr", a, b, f),
            Term::BvAShr(a, b) => fmt_binop("bvashr", a, b, f),

            // --- Bitvector conversion ---
            Term::ZeroExtend(n, a) => {
                write!(f, "((_ zero_extend {n}) {a})")
            }
            Term::SignExtend(n, a) => {
                write!(f, "((_ sign_extend {n}) {a})")
            }
            Term::Extract(hi, lo, a) => {
                write!(f, "((_ extract {hi} {lo}) {a})")
            }
            Term::Concat(a, b) => fmt_binop("concat", a, b, f),

            // --- Integer arithmetic ---
            Term::IntAdd(a, b) => fmt_binop("+", a, b, f),
            Term::IntSub(a, b) => fmt_binop("-", a, b, f),
            Term::IntMul(a, b) => fmt_binop("*", a, b, f),
            Term::IntDiv(a, b) => fmt_binop("div", a, b, f),
            Term::IntMod(a, b) => fmt_binop("mod", a, b, f),
            Term::IntNeg(a) => fmt_unop("-", a, f),
            Term::IntLt(a, b) => fmt_binop("<", a, b, f),
            Term::IntLe(a, b) => fmt_binop("<=", a, b, f),
            Term::IntGt(a, b) => fmt_binop(">", a, b, f),
            Term::IntGe(a, b) => fmt_binop(">=", a, b, f),

            // --- Array operations ---
            Term::Select(arr, idx) => fmt_binop("select", arr, idx, f),
            Term::Store(arr, idx, val) => {
                write!(f, "(store {arr} {idx} {val})")
            }

            // --- Quantifiers ---
            Term::Forall(vars, body) => {
                write!(f, "(forall ")?;
                fmt_sorted_vars(vars, f)?;
                write!(f, " {body})")
            }
            Term::Exists(vars, body) => {
                write!(f, "(exists ")?;
                fmt_sorted_vars(vars, f)?;
                write!(f, " {body})")
            }

            // --- Let bindings ---
            Term::Let(bindings, body) => {
                write!(f, "(let ")?;
                fmt_let_bindings(bindings, f)?;
                write!(f, " {body})")
            }

            // --- Function application ---
            Term::App(name, args) => {
                if args.is_empty() {
                    write!(f, "{name}")
                } else {
                    write!(f, "({name} ")?;
                    fmt_term_list(args, f)?;
                    write!(f, ")")
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Command
// ---------------------------------------------------------------------------

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Command::SetLogic(logic) => write!(f, "(set-logic {logic})"),
            Command::SetOption(key, value) => write!(f, "(set-option :{key} {value})"),
            Command::DeclareSort(name, arity) => {
                write!(f, "(declare-sort {name} {arity})")
            }
            Command::DefineSort(name, params, body) => {
                write!(f, "(define-sort {name} (")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{p}")?;
                }
                write!(f, ") {body})")
            }
            Command::DeclareConst(name, sort) => {
                write!(f, "(declare-const {name} {sort})")
            }
            Command::DeclareFun(name, param_sorts, return_sort) => {
                write!(f, "(declare-fun {name} (")?;
                for (i, s) in param_sorts.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{s}")?;
                }
                write!(f, ") {return_sort})")
            }
            Command::DefineFun(name, params, return_sort, body) => {
                write!(f, "(define-fun {name} ")?;
                fmt_sorted_vars(params, f)?;
                write!(f, " {return_sort} {body})")
            }
            Command::Assert(term) => write!(f, "(assert {term})"),
            Command::CheckSat => write!(f, "(check-sat)"),
            Command::GetModel => write!(f, "(get-model)"),
            Command::GetValue(terms) => {
                write!(f, "(get-value (")?;
                fmt_term_list(terms, f)?;
                write!(f, "))")
            }
            Command::Push(n) => write!(f, "(push {n})"),
            Command::Pop(n) => write!(f, "(pop {n})"),
            Command::Echo(msg) => write!(f, "(echo \"{msg}\")"),
            Command::Comment(text) => write!(f, ";; {text}"),
            Command::Exit => write!(f, "(exit)"),
        }
    }
}

// ---------------------------------------------------------------------------
// Script
// ---------------------------------------------------------------------------

impl fmt::Display for Script {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, cmd) in self.commands().iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            write!(f, "{cmd}")?;
        }
        Ok(())
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use crate::command::Command;
    use crate::script::Script;
    use crate::sort::Sort;
    use crate::term::Term;

    // -----------------------------------------------------------------------
    // Sort formatting
    // -----------------------------------------------------------------------

    #[test]
    fn sort_bool() {
        assert_eq!(Sort::Bool.to_string(), "Bool");
    }

    #[test]
    fn sort_int() {
        assert_eq!(Sort::Int.to_string(), "Int");
    }

    #[test]
    fn sort_real() {
        assert_eq!(Sort::Real.to_string(), "Real");
    }

    #[test]
    fn sort_bitvec() {
        assert_eq!(Sort::BitVec(32).to_string(), "(_ BitVec 32)");
        assert_eq!(Sort::BitVec(1).to_string(), "(_ BitVec 1)");
        assert_eq!(Sort::BitVec(64).to_string(), "(_ BitVec 64)");
    }

    #[test]
    fn sort_array() {
        let s = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool));
        assert_eq!(s.to_string(), "(Array Int Bool)");
    }

    #[test]
    fn sort_array_nested() {
        let inner = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int));
        let outer = Sort::Array(Box::new(Sort::BitVec(8)), Box::new(inner));
        assert_eq!(outer.to_string(), "(Array (_ BitVec 8) (Array Int Int))");
    }

    #[test]
    fn sort_datatype() {
        assert_eq!(Sort::Datatype("MyList".into()).to_string(), "MyList");
    }

    #[test]
    fn sort_float() {
        assert_eq!(Sort::Float(8, 24).to_string(), "(_ FloatingPoint 8 24)");
        assert_eq!(Sort::Float(11, 53).to_string(), "(_ FloatingPoint 11 53)");
    }

    #[test]
    fn sort_uninterpreted() {
        assert_eq!(Sort::Uninterpreted("U".into()).to_string(), "U");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Literals
    // -----------------------------------------------------------------------

    #[test]
    fn term_bool_lit() {
        assert_eq!(Term::BoolLit(true).to_string(), "true");
        assert_eq!(Term::BoolLit(false).to_string(), "false");
    }

    #[test]
    fn term_int_lit_positive() {
        assert_eq!(Term::IntLit(0).to_string(), "0");
        assert_eq!(Term::IntLit(42).to_string(), "42");
    }

    #[test]
    fn term_int_lit_negative() {
        assert_eq!(Term::IntLit(-1).to_string(), "(- 1)");
        assert_eq!(Term::IntLit(-99).to_string(), "(- 99)");
    }

    #[test]
    fn term_bitvec_lit_positive() {
        assert_eq!(Term::BitVecLit(0, 8).to_string(), "(_ bv0 8)");
        assert_eq!(Term::BitVecLit(255, 8).to_string(), "(_ bv255 8)");
        assert_eq!(Term::BitVecLit(42, 32).to_string(), "(_ bv42 32)");
    }

    #[test]
    fn term_bitvec_lit_negative() {
        // -1 in 8-bit two's complement = 255
        assert_eq!(Term::BitVecLit(-1, 8).to_string(), "(_ bv255 8)");
        // -128 in 8-bit = 128
        assert_eq!(Term::BitVecLit(-128, 8).to_string(), "(_ bv128 8)");
        // -1 in 32-bit = 4294967295
        assert_eq!(Term::BitVecLit(-1, 32).to_string(), "(_ bv4294967295 32)");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Variables
    // -----------------------------------------------------------------------

    #[test]
    fn term_const() {
        assert_eq!(Term::Const("x".into()).to_string(), "x");
        assert_eq!(Term::Const("my_var".into()).to_string(), "my_var");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Boolean operations
    // -----------------------------------------------------------------------

    #[test]
    fn term_not() {
        let t = Term::Not(Box::new(Term::BoolLit(true)));
        assert_eq!(t.to_string(), "(not true)");
    }

    #[test]
    fn term_and() {
        let t = Term::And(vec![Term::Const("a".into()), Term::Const("b".into())]);
        assert_eq!(t.to_string(), "(and a b)");
    }

    #[test]
    fn term_and_empty() {
        let t = Term::And(vec![]);
        assert_eq!(t.to_string(), "true");
    }

    #[test]
    fn term_or() {
        let t = Term::Or(vec![
            Term::Const("a".into()),
            Term::Const("b".into()),
            Term::Const("c".into()),
        ]);
        assert_eq!(t.to_string(), "(or a b c)");
    }

    #[test]
    fn term_or_empty() {
        let t = Term::Or(vec![]);
        assert_eq!(t.to_string(), "false");
    }

    #[test]
    fn term_implies() {
        let t = Term::Implies(
            Box::new(Term::Const("p".into())),
            Box::new(Term::Const("q".into())),
        );
        assert_eq!(t.to_string(), "(=> p q)");
    }

    #[test]
    fn term_iff() {
        let t = Term::Iff(
            Box::new(Term::Const("p".into())),
            Box::new(Term::Const("q".into())),
        );
        assert_eq!(t.to_string(), "(= p q)");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Core
    // -----------------------------------------------------------------------

    #[test]
    fn term_eq() {
        let t = Term::Eq(Box::new(Term::Const("x".into())), Box::new(Term::IntLit(5)));
        assert_eq!(t.to_string(), "(= x 5)");
    }

    #[test]
    fn term_distinct() {
        let t = Term::Distinct(vec![
            Term::Const("a".into()),
            Term::Const("b".into()),
            Term::Const("c".into()),
        ]);
        assert_eq!(t.to_string(), "(distinct a b c)");
    }

    #[test]
    fn term_ite() {
        let t = Term::Ite(
            Box::new(Term::Const("c".into())),
            Box::new(Term::IntLit(1)),
            Box::new(Term::IntLit(0)),
        );
        assert_eq!(t.to_string(), "(ite c 1 0)");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Bitvector arithmetic
    // -----------------------------------------------------------------------

    #[test]
    fn term_bvadd() {
        let t = Term::BvAdd(
            Box::new(Term::Const("x".into())),
            Box::new(Term::Const("y".into())),
        );
        assert_eq!(t.to_string(), "(bvadd x y)");
    }

    #[test]
    fn term_bvsub() {
        let t = Term::BvSub(
            Box::new(Term::Const("x".into())),
            Box::new(Term::Const("y".into())),
        );
        assert_eq!(t.to_string(), "(bvsub x y)");
    }

    #[test]
    fn term_bvmul() {
        let t = Term::BvMul(
            Box::new(Term::Const("x".into())),
            Box::new(Term::Const("y".into())),
        );
        assert_eq!(t.to_string(), "(bvmul x y)");
    }

    #[test]
    fn term_bvsdiv() {
        let t = Term::BvSDiv(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvsdiv a b)");
    }

    #[test]
    fn term_bvudiv() {
        let t = Term::BvUDiv(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvudiv a b)");
    }

    #[test]
    fn term_bvsrem() {
        let t = Term::BvSRem(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvsrem a b)");
    }

    #[test]
    fn term_bvurem() {
        let t = Term::BvURem(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvurem a b)");
    }

    #[test]
    fn term_bvneg() {
        let t = Term::BvNeg(Box::new(Term::Const("x".into())));
        assert_eq!(t.to_string(), "(bvneg x)");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Bitvector comparison (signed)
    // -----------------------------------------------------------------------

    #[test]
    fn term_bvslt() {
        let t = Term::BvSLt(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvslt a b)");
    }

    #[test]
    fn term_bvsle() {
        let t = Term::BvSLe(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvsle a b)");
    }

    #[test]
    fn term_bvsgt() {
        let t = Term::BvSGt(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvsgt a b)");
    }

    #[test]
    fn term_bvsge() {
        let t = Term::BvSGe(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvsge a b)");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Bitvector comparison (unsigned)
    // -----------------------------------------------------------------------

    #[test]
    fn term_bvult() {
        let t = Term::BvULt(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvult a b)");
    }

    #[test]
    fn term_bvule() {
        let t = Term::BvULe(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvule a b)");
    }

    #[test]
    fn term_bvugt() {
        let t = Term::BvUGt(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvugt a b)");
    }

    #[test]
    fn term_bvuge() {
        let t = Term::BvUGe(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvuge a b)");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Bitvector bitwise
    // -----------------------------------------------------------------------

    #[test]
    fn term_bvand() {
        let t = Term::BvAnd(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvand a b)");
    }

    #[test]
    fn term_bvor() {
        let t = Term::BvOr(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvor a b)");
    }

    #[test]
    fn term_bvxor() {
        let t = Term::BvXor(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvxor a b)");
    }

    #[test]
    fn term_bvnot() {
        let t = Term::BvNot(Box::new(Term::Const("x".into())));
        assert_eq!(t.to_string(), "(bvnot x)");
    }

    #[test]
    fn term_bvshl() {
        let t = Term::BvShl(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvshl a b)");
    }

    #[test]
    fn term_bvlshr() {
        let t = Term::BvLShr(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvlshr a b)");
    }

    #[test]
    fn term_bvashr() {
        let t = Term::BvAShr(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(bvashr a b)");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Bitvector conversion
    // -----------------------------------------------------------------------

    #[test]
    fn term_zero_extend() {
        let t = Term::ZeroExtend(8, Box::new(Term::Const("x".into())));
        assert_eq!(t.to_string(), "((_ zero_extend 8) x)");
    }

    #[test]
    fn term_sign_extend() {
        let t = Term::SignExtend(16, Box::new(Term::Const("x".into())));
        assert_eq!(t.to_string(), "((_ sign_extend 16) x)");
    }

    #[test]
    fn term_extract() {
        let t = Term::Extract(7, 0, Box::new(Term::Const("x".into())));
        assert_eq!(t.to_string(), "((_ extract 7 0) x)");
    }

    #[test]
    fn term_concat() {
        let t = Term::Concat(
            Box::new(Term::Const("hi".into())),
            Box::new(Term::Const("lo".into())),
        );
        assert_eq!(t.to_string(), "(concat hi lo)");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Integer arithmetic
    // -----------------------------------------------------------------------

    #[test]
    fn term_int_add() {
        let t = Term::IntAdd(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(+ a b)");
    }

    #[test]
    fn term_int_sub() {
        let t = Term::IntSub(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(- a b)");
    }

    #[test]
    fn term_int_mul() {
        let t = Term::IntMul(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(* a b)");
    }

    #[test]
    fn term_int_div() {
        let t = Term::IntDiv(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(div a b)");
    }

    #[test]
    fn term_int_mod() {
        let t = Term::IntMod(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(mod a b)");
    }

    #[test]
    fn term_int_neg() {
        let t = Term::IntNeg(Box::new(Term::Const("x".into())));
        assert_eq!(t.to_string(), "(- x)");
    }

    #[test]
    fn term_int_lt() {
        let t = Term::IntLt(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(< a b)");
    }

    #[test]
    fn term_int_le() {
        let t = Term::IntLe(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(<= a b)");
    }

    #[test]
    fn term_int_gt() {
        let t = Term::IntGt(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(> a b)");
    }

    #[test]
    fn term_int_ge() {
        let t = Term::IntGe(
            Box::new(Term::Const("a".into())),
            Box::new(Term::Const("b".into())),
        );
        assert_eq!(t.to_string(), "(>= a b)");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Array operations
    // -----------------------------------------------------------------------

    #[test]
    fn term_select() {
        let t = Term::Select(
            Box::new(Term::Const("arr".into())),
            Box::new(Term::IntLit(3)),
        );
        assert_eq!(t.to_string(), "(select arr 3)");
    }

    #[test]
    fn term_store() {
        let t = Term::Store(
            Box::new(Term::Const("arr".into())),
            Box::new(Term::IntLit(0)),
            Box::new(Term::IntLit(42)),
        );
        assert_eq!(t.to_string(), "(store arr 0 42)");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Quantifiers
    // -----------------------------------------------------------------------

    #[test]
    fn term_forall() {
        let t = Term::Forall(
            vec![("x".into(), Sort::Int), ("y".into(), Sort::Int)],
            Box::new(Term::Eq(
                Box::new(Term::Const("x".into())),
                Box::new(Term::Const("y".into())),
            )),
        );
        assert_eq!(t.to_string(), "(forall ((x Int) (y Int)) (= x y))");
    }

    #[test]
    fn term_exists() {
        let t = Term::Exists(
            vec![("x".into(), Sort::Bool)],
            Box::new(Term::Const("x".into())),
        );
        assert_eq!(t.to_string(), "(exists ((x Bool)) x)");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Let bindings
    // -----------------------------------------------------------------------

    #[test]
    fn term_let() {
        let t = Term::Let(
            vec![("a".into(), Term::IntLit(10))],
            Box::new(Term::IntAdd(
                Box::new(Term::Const("a".into())),
                Box::new(Term::IntLit(1)),
            )),
        );
        assert_eq!(t.to_string(), "(let ((a 10)) (+ a 1))");
    }

    #[test]
    fn term_let_multiple_bindings() {
        let t = Term::Let(
            vec![("a".into(), Term::IntLit(1)), ("b".into(), Term::IntLit(2))],
            Box::new(Term::IntAdd(
                Box::new(Term::Const("a".into())),
                Box::new(Term::Const("b".into())),
            )),
        );
        assert_eq!(t.to_string(), "(let ((a 1) (b 2)) (+ a b))");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Function application
    // -----------------------------------------------------------------------

    #[test]
    fn term_app_no_args() {
        let t = Term::App("f".into(), vec![]);
        assert_eq!(t.to_string(), "f");
    }

    #[test]
    fn term_app_with_args() {
        let t = Term::App("f".into(), vec![Term::Const("x".into()), Term::IntLit(3)]);
        assert_eq!(t.to_string(), "(f x 3)");
    }

    // -----------------------------------------------------------------------
    // Term formatting — Nested expressions
    // -----------------------------------------------------------------------

    #[test]
    fn term_nested_bv() {
        // (bvadd (bvmul x y) z)
        let t = Term::BvAdd(
            Box::new(Term::BvMul(
                Box::new(Term::Const("x".into())),
                Box::new(Term::Const("y".into())),
            )),
            Box::new(Term::Const("z".into())),
        );
        assert_eq!(t.to_string(), "(bvadd (bvmul x y) z)");
    }

    #[test]
    fn term_deeply_nested() {
        // (not (=> (and a b) (or c d)))
        let t = Term::Not(Box::new(Term::Implies(
            Box::new(Term::And(vec![
                Term::Const("a".into()),
                Term::Const("b".into()),
            ])),
            Box::new(Term::Or(vec![
                Term::Const("c".into()),
                Term::Const("d".into()),
            ])),
        )));
        assert_eq!(t.to_string(), "(not (=> (and a b) (or c d)))");
    }

    #[test]
    fn term_nested_ite_with_comparisons() {
        // (ite (bvslt x y) (bvadd x (_ bv1 32)) (bvsub y (_ bv1 32)))
        let bv1 = Term::BitVecLit(1, 32);
        let t = Term::Ite(
            Box::new(Term::BvSLt(
                Box::new(Term::Const("x".into())),
                Box::new(Term::Const("y".into())),
            )),
            Box::new(Term::BvAdd(
                Box::new(Term::Const("x".into())),
                Box::new(bv1.clone()),
            )),
            Box::new(Term::BvSub(
                Box::new(Term::Const("y".into())),
                Box::new(bv1),
            )),
        );
        assert_eq!(
            t.to_string(),
            "(ite (bvslt x y) (bvadd x (_ bv1 32)) (bvsub y (_ bv1 32)))"
        );
    }

    // -----------------------------------------------------------------------
    // Command formatting
    // -----------------------------------------------------------------------

    #[test]
    fn cmd_set_logic() {
        assert_eq!(
            Command::SetLogic("QF_BV".into()).to_string(),
            "(set-logic QF_BV)"
        );
    }

    #[test]
    fn cmd_set_option() {
        assert_eq!(
            Command::SetOption("produce-models".into(), "true".into()).to_string(),
            "(set-option :produce-models true)"
        );
    }

    #[test]
    fn cmd_declare_sort() {
        assert_eq!(
            Command::DeclareSort("Pair".into(), 0).to_string(),
            "(declare-sort Pair 0)"
        );
    }

    #[test]
    fn cmd_define_sort() {
        assert_eq!(
            Command::DefineSort("BV8".into(), vec![], Sort::BitVec(8)).to_string(),
            "(define-sort BV8 () (_ BitVec 8))"
        );
    }

    #[test]
    fn cmd_define_sort_with_params() {
        assert_eq!(
            Command::DefineSort(
                "MyArray".into(),
                vec!["T".into()],
                Sort::Array(
                    Box::new(Sort::Int),
                    Box::new(Sort::Uninterpreted("T".into())),
                ),
            )
            .to_string(),
            "(define-sort MyArray (T) (Array Int T))"
        );
    }

    #[test]
    fn cmd_declare_const() {
        assert_eq!(
            Command::DeclareConst("x".into(), Sort::Int).to_string(),
            "(declare-const x Int)"
        );
    }

    #[test]
    fn cmd_declare_fun_no_params() {
        assert_eq!(
            Command::DeclareFun("c".into(), vec![], Sort::Bool).to_string(),
            "(declare-fun c () Bool)"
        );
    }

    #[test]
    fn cmd_declare_fun_with_params() {
        assert_eq!(
            Command::DeclareFun("f".into(), vec![Sort::Int, Sort::Int], Sort::Bool,).to_string(),
            "(declare-fun f (Int Int) Bool)"
        );
    }

    #[test]
    fn cmd_define_fun() {
        let cmd = Command::DefineFun(
            "double".into(),
            vec![("x".into(), Sort::Int)],
            Sort::Int,
            Term::IntAdd(
                Box::new(Term::Const("x".into())),
                Box::new(Term::Const("x".into())),
            ),
        );
        assert_eq!(cmd.to_string(), "(define-fun double ((x Int)) Int (+ x x))");
    }

    #[test]
    fn cmd_assert() {
        let cmd = Command::Assert(Term::BoolLit(true));
        assert_eq!(cmd.to_string(), "(assert true)");
    }

    #[test]
    fn cmd_check_sat() {
        assert_eq!(Command::CheckSat.to_string(), "(check-sat)");
    }

    #[test]
    fn cmd_get_model() {
        assert_eq!(Command::GetModel.to_string(), "(get-model)");
    }

    #[test]
    fn cmd_get_value() {
        let cmd = Command::GetValue(vec![Term::Const("x".into()), Term::Const("y".into())]);
        assert_eq!(cmd.to_string(), "(get-value (x y))");
    }

    #[test]
    fn cmd_push() {
        assert_eq!(Command::Push(1).to_string(), "(push 1)");
    }

    #[test]
    fn cmd_pop() {
        assert_eq!(Command::Pop(2).to_string(), "(pop 2)");
    }

    #[test]
    fn cmd_echo() {
        assert_eq!(
            Command::Echo("hello".into()).to_string(),
            "(echo \"hello\")"
        );
    }

    #[test]
    fn cmd_comment() {
        assert_eq!(
            Command::Comment("this is a comment".into()).to_string(),
            ";; this is a comment"
        );
    }

    #[test]
    fn cmd_exit() {
        assert_eq!(Command::Exit.to_string(), "(exit)");
    }

    // -----------------------------------------------------------------------
    // Script formatting
    // -----------------------------------------------------------------------

    #[test]
    fn script_empty() {
        let s = Script::new();
        assert_eq!(s.to_string(), "");
    }

    #[test]
    fn script_single_command() {
        let s = Script::with_commands(vec![Command::CheckSat]);
        assert_eq!(s.to_string(), "(check-sat)");
    }

    #[test]
    fn script_multiple_commands() {
        let s = Script::with_commands(vec![
            Command::SetLogic("QF_BV".into()),
            Command::DeclareConst("x".into(), Sort::BitVec(32)),
            Command::Assert(Term::Eq(
                Box::new(Term::Const("x".into())),
                Box::new(Term::BitVecLit(42, 32)),
            )),
            Command::CheckSat,
            Command::GetModel,
            Command::Exit,
        ]);
        assert_eq!(
            s.to_string(),
            "\
(set-logic QF_BV)\n\
(declare-const x (_ BitVec 32))\n\
(assert (= x (_ bv42 32)))\n\
(check-sat)\n\
(get-model)\n\
(exit)"
        );
    }

    #[test]
    fn script_with_comment() {
        let s = Script::with_commands(vec![
            Command::Comment("Example".into()),
            Command::SetLogic("QF_LIA".into()),
            Command::DeclareConst("n".into(), Sort::Int),
            Command::Assert(Term::IntGe(
                Box::new(Term::Const("n".into())),
                Box::new(Term::IntLit(0)),
            )),
            Command::CheckSat,
        ]);
        let expected = "\
;; Example\n\
(set-logic QF_LIA)\n\
(declare-const n Int)\n\
(assert (>= n 0))\n\
(check-sat)";
        assert_eq!(s.to_string(), expected);
    }

    // -----------------------------------------------------------------------
    // Edge cases
    // -----------------------------------------------------------------------

    #[test]
    fn term_and_single_element() {
        let t = Term::And(vec![Term::BoolLit(true)]);
        assert_eq!(t.to_string(), "(and true)");
    }

    #[test]
    fn term_or_single_element() {
        let t = Term::Or(vec![Term::BoolLit(false)]);
        assert_eq!(t.to_string(), "(or false)");
    }

    #[test]
    fn term_bitvec_lit_zero_width_1() {
        assert_eq!(Term::BitVecLit(0, 1).to_string(), "(_ bv0 1)");
        assert_eq!(Term::BitVecLit(1, 1).to_string(), "(_ bv1 1)");
    }

    #[test]
    fn term_bitvec_lit_negative_1bit() {
        // -1 in 1-bit two's complement = 1
        assert_eq!(Term::BitVecLit(-1, 1).to_string(), "(_ bv1 1)");
    }

    #[test]
    fn term_extract_single_bit() {
        let t = Term::Extract(0, 0, Box::new(Term::Const("x".into())));
        assert_eq!(t.to_string(), "((_ extract 0 0) x)");
    }

    #[test]
    fn term_forall_with_bitvec_sort() {
        let t = Term::Forall(
            vec![("x".into(), Sort::BitVec(8))],
            Box::new(Term::Eq(
                Box::new(Term::Const("x".into())),
                Box::new(Term::Const("x".into())),
            )),
        );
        assert_eq!(t.to_string(), "(forall ((x (_ BitVec 8))) (= x x))");
    }

    #[test]
    fn term_let_nested_in_forall() {
        let t = Term::Forall(
            vec![("x".into(), Sort::Int)],
            Box::new(Term::Let(
                vec![(
                    "y".into(),
                    Term::IntAdd(Box::new(Term::Const("x".into())), Box::new(Term::IntLit(1))),
                )],
                Box::new(Term::IntGt(
                    Box::new(Term::Const("y".into())),
                    Box::new(Term::Const("x".into())),
                )),
            )),
        );
        assert_eq!(
            t.to_string(),
            "(forall ((x Int)) (let ((y (+ x 1))) (> y x)))"
        );
    }

    #[test]
    fn term_store_nested() {
        // (select (store arr 0 42) 0)
        let t = Term::Select(
            Box::new(Term::Store(
                Box::new(Term::Const("arr".into())),
                Box::new(Term::IntLit(0)),
                Box::new(Term::IntLit(42)),
            )),
            Box::new(Term::IntLit(0)),
        );
        assert_eq!(t.to_string(), "(select (store arr 0 42) 0)");
    }

    #[test]
    fn cmd_define_fun_no_params() {
        let cmd = Command::DefineFun("const_five".into(), vec![], Sort::Int, Term::IntLit(5));
        assert_eq!(cmd.to_string(), "(define-fun const_five () Int 5)");
    }

    #[test]
    fn cmd_get_value_single() {
        let cmd = Command::GetValue(vec![Term::Const("x".into())]);
        assert_eq!(cmd.to_string(), "(get-value (x))");
    }
}
