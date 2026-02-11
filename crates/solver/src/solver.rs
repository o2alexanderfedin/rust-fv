use std::io::Write;
use std::process::{Command, Stdio};

use rust_fv_smtlib::script::Script;

use crate::config::SolverConfig;
use crate::error::SolverError;
use crate::parser::parse_solver_output;
use crate::result::SolverResult;

/// Z3 SMT solver interface.
///
/// Communicates with Z3 by spawning it as a subprocess and piping SMT-LIB2 text.
#[derive(Debug)]
pub struct Z3Solver {
    config: SolverConfig,
}

impl Z3Solver {
    /// Create a new `Z3Solver` with the given configuration.
    pub fn new(config: SolverConfig) -> Self {
        Self { config }
    }

    /// Create a `Z3Solver` with auto-detected Z3 location and default settings.
    pub fn with_default_config() -> Result<Self, SolverError> {
        let config = SolverConfig::auto_detect()?;
        Ok(Self { config })
    }

    /// Get a reference to the solver configuration.
    pub fn config(&self) -> &SolverConfig {
        &self.config
    }

    /// Check satisfiability of a Script.
    ///
    /// Formats the script to SMT-LIB2 text using `Display`, appends `(check-sat)`
    /// and `(get-model)` if not already present, and runs Z3.
    pub fn check_sat(&self, script: &Script) -> Result<SolverResult, SolverError> {
        // Format the script commands to SMT-LIB2
        let mut smtlib = format_script(script);

        // Ensure (check-sat) and (get-model) are appended
        ensure_check_sat_and_get_model(&mut smtlib, script);

        self.check_sat_raw(&smtlib)
    }

    /// Check satisfiability from a raw SMT-LIB2 string.
    ///
    /// This is useful when:
    /// - The formatter (`Display` impl) is not yet available
    /// - You want to pass hand-crafted SMT-LIB2 directly
    pub fn check_sat_raw(&self, smtlib: &str) -> Result<SolverResult, SolverError> {
        self.config.validate()?;

        let mut args = vec!["-in".to_string()];

        // Add timeout flag if configured
        if self.config.timeout_ms > 0 {
            args.push(format!("-t:{}", self.config.timeout_ms));
        }

        // Add extra arguments
        args.extend(self.config.extra_args.iter().cloned());

        // Spawn Z3 process
        let mut child = Command::new(&self.config.z3_path)
            .args(&args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| SolverError::ProcessError(format!("Failed to start Z3: {e}")))?;

        // Write SMT-LIB to stdin
        {
            let stdin = child
                .stdin
                .as_mut()
                .ok_or_else(|| SolverError::ProcessError("Failed to open Z3 stdin".to_string()))?;
            stdin.write_all(smtlib.as_bytes()).map_err(|e| {
                SolverError::ProcessError(format!("Failed to write to Z3 stdin: {e}"))
            })?;
        }

        // Wait for Z3 to finish and collect output
        let output = child
            .wait_with_output()
            .map_err(|e| SolverError::ProcessError(format!("Failed to wait for Z3: {e}")))?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // Check for timeout in stderr
        if stderr.contains("timeout") || stdout.trim() == "timeout" {
            return Ok(SolverResult::Unknown("timeout".to_string()));
        }

        parse_solver_output(&stdout, &stderr)
    }
}

/// Format a `Script` to SMT-LIB2 text.
///
/// Uses the `Display` implementation on `Script`. If `Display` is not yet implemented,
/// this will produce an empty or stub string, and callers should use `check_sat_raw` instead.
fn format_script(script: &Script) -> String {
    // Format manually for robustness (Display might be a stub in the smtlib crate)
    let mut output = String::new();
    for cmd in script.commands() {
        format_command(&mut output, cmd);
        output.push('\n');
    }
    output
}

/// Format a single command to SMT-LIB2 text.
fn format_command(output: &mut String, cmd: &rust_fv_smtlib::command::Command) {
    use rust_fv_smtlib::command::Command as SmtCmd;

    match cmd {
        SmtCmd::SetLogic(logic) => {
            output.push_str(&format!("(set-logic {logic})"));
        }
        SmtCmd::SetOption(key, value) => {
            output.push_str(&format!("(set-option :{key} {value})"));
        }
        SmtCmd::DeclareSort(name, arity) => {
            output.push_str(&format!("(declare-sort {name} {arity})"));
        }
        SmtCmd::DefineSort(name, params, sort) => {
            let params_str = params.join(" ");
            output.push_str(&format!("(define-sort {name} ({params_str}) "));
            format_sort(output, sort);
            output.push(')');
        }
        SmtCmd::DeclareConst(name, sort) => {
            output.push_str(&format!("(declare-const {name} "));
            format_sort(output, sort);
            output.push(')');
        }
        SmtCmd::DeclareFun(name, param_sorts, ret_sort) => {
            output.push_str(&format!("(declare-fun {name} ("));
            for (i, s) in param_sorts.iter().enumerate() {
                if i > 0 {
                    output.push(' ');
                }
                format_sort(output, s);
            }
            output.push_str(") ");
            format_sort(output, ret_sort);
            output.push(')');
        }
        SmtCmd::DefineFun(name, params, ret_sort, body) => {
            output.push_str(&format!("(define-fun {name} ("));
            for (i, (pname, psort)) in params.iter().enumerate() {
                if i > 0 {
                    output.push(' ');
                }
                output.push_str(&format!("({pname} "));
                format_sort(output, psort);
                output.push(')');
            }
            output.push_str(") ");
            format_sort(output, ret_sort);
            output.push(' ');
            format_term(output, body);
            output.push(')');
        }
        SmtCmd::Assert(term) => {
            output.push_str("(assert ");
            format_term(output, term);
            output.push(')');
        }
        SmtCmd::CheckSat => {
            output.push_str("(check-sat)");
        }
        SmtCmd::GetModel => {
            output.push_str("(get-model)");
        }
        SmtCmd::GetValue(terms) => {
            output.push_str("(get-value (");
            for (i, t) in terms.iter().enumerate() {
                if i > 0 {
                    output.push(' ');
                }
                format_term(output, t);
            }
            output.push_str("))");
        }
        SmtCmd::Push(n) => {
            output.push_str(&format!("(push {n})"));
        }
        SmtCmd::Pop(n) => {
            output.push_str(&format!("(pop {n})"));
        }
        SmtCmd::Echo(msg) => {
            output.push_str(&format!("(echo \"{msg}\")"));
        }
        SmtCmd::Comment(text) => {
            output.push_str(&format!(";; {text}"));
        }
        SmtCmd::Exit => {
            output.push_str("(exit)");
        }
    }
}

/// Format a Sort to SMT-LIB2 text.
fn format_sort(output: &mut String, sort: &rust_fv_smtlib::sort::Sort) {
    use rust_fv_smtlib::sort::Sort;

    match sort {
        Sort::Bool => output.push_str("Bool"),
        Sort::Int => output.push_str("Int"),
        Sort::Real => output.push_str("Real"),
        Sort::BitVec(n) => output.push_str(&format!("(_ BitVec {n})")),
        Sort::Array(idx, elem) => {
            output.push_str("(Array ");
            format_sort(output, idx);
            output.push(' ');
            format_sort(output, elem);
            output.push(')');
        }
        Sort::Datatype(name) => output.push_str(name),
        Sort::Float(e, s) => output.push_str(&format!("(_ FloatingPoint {e} {s})")),
        Sort::Uninterpreted(name) => output.push_str(name),
    }
}

/// Format a Term to SMT-LIB2 text.
fn format_term(output: &mut String, term: &rust_fv_smtlib::term::Term) {
    use rust_fv_smtlib::term::Term;

    match term {
        Term::BoolLit(true) => output.push_str("true"),
        Term::BoolLit(false) => output.push_str("false"),
        Term::IntLit(n) => {
            if *n < 0 {
                output.push_str(&format!("(- {})", -n));
            } else {
                output.push_str(&format!("{n}"));
            }
        }
        Term::BitVecLit(val, width) => {
            // Format as hex if it fits neatly, otherwise use binary
            let hex_digits = (*width as usize).div_ceil(4);
            let mask = if *width >= 128 {
                i128::MAX // avoid overflow
            } else {
                (1i128 << width) - 1
            };
            let unsigned = val & mask;
            output.push_str(&format!("#x{:0>width$x}", unsigned, width = hex_digits));
        }
        Term::Const(name) => output.push_str(name),
        Term::Not(t) => {
            output.push_str("(not ");
            format_term(output, t);
            output.push(')');
        }
        Term::And(terms) => format_nary(output, "and", terms),
        Term::Or(terms) => format_nary(output, "or", terms),
        Term::Implies(a, b) => format_binary(output, "=>", a, b),
        Term::Iff(a, b) => format_binary(output, "=", a, b),
        Term::Eq(a, b) => format_binary(output, "=", a, b),
        Term::Distinct(terms) => format_nary(output, "distinct", terms),
        Term::Ite(cond, then, els) => {
            output.push_str("(ite ");
            format_term(output, cond);
            output.push(' ');
            format_term(output, then);
            output.push(' ');
            format_term(output, els);
            output.push(')');
        }
        Term::BvAdd(a, b) => format_binary(output, "bvadd", a, b),
        Term::BvSub(a, b) => format_binary(output, "bvsub", a, b),
        Term::BvMul(a, b) => format_binary(output, "bvmul", a, b),
        Term::BvSDiv(a, b) => format_binary(output, "bvsdiv", a, b),
        Term::BvUDiv(a, b) => format_binary(output, "bvudiv", a, b),
        Term::BvSRem(a, b) => format_binary(output, "bvsrem", a, b),
        Term::BvURem(a, b) => format_binary(output, "bvurem", a, b),
        Term::BvNeg(a) => {
            output.push_str("(bvneg ");
            format_term(output, a);
            output.push(')');
        }
        Term::BvSLt(a, b) => format_binary(output, "bvslt", a, b),
        Term::BvSLe(a, b) => format_binary(output, "bvsle", a, b),
        Term::BvSGt(a, b) => format_binary(output, "bvsgt", a, b),
        Term::BvSGe(a, b) => format_binary(output, "bvsge", a, b),
        Term::BvULt(a, b) => format_binary(output, "bvult", a, b),
        Term::BvULe(a, b) => format_binary(output, "bvule", a, b),
        Term::BvUGt(a, b) => format_binary(output, "bvugt", a, b),
        Term::BvUGe(a, b) => format_binary(output, "bvuge", a, b),
        Term::BvAnd(a, b) => format_binary(output, "bvand", a, b),
        Term::BvOr(a, b) => format_binary(output, "bvor", a, b),
        Term::BvXor(a, b) => format_binary(output, "bvxor", a, b),
        Term::BvNot(a) => {
            output.push_str("(bvnot ");
            format_term(output, a);
            output.push(')');
        }
        Term::BvShl(a, b) => format_binary(output, "bvshl", a, b),
        Term::BvLShr(a, b) => format_binary(output, "bvlshr", a, b),
        Term::BvAShr(a, b) => format_binary(output, "bvashr", a, b),
        Term::ZeroExtend(n, a) => {
            output.push_str(&format!("((_ zero_extend {n}) "));
            format_term(output, a);
            output.push(')');
        }
        Term::SignExtend(n, a) => {
            output.push_str(&format!("((_ sign_extend {n}) "));
            format_term(output, a);
            output.push(')');
        }
        Term::Extract(hi, lo, a) => {
            output.push_str(&format!("((_ extract {hi} {lo}) "));
            format_term(output, a);
            output.push(')');
        }
        Term::Concat(a, b) => format_binary(output, "concat", a, b),
        Term::IntAdd(a, b) => format_binary(output, "+", a, b),
        Term::IntSub(a, b) => format_binary(output, "-", a, b),
        Term::IntMul(a, b) => format_binary(output, "*", a, b),
        Term::IntDiv(a, b) => format_binary(output, "div", a, b),
        Term::IntMod(a, b) => format_binary(output, "mod", a, b),
        Term::IntNeg(a) => {
            output.push_str("(- ");
            format_term(output, a);
            output.push(')');
        }
        Term::IntLt(a, b) => format_binary(output, "<", a, b),
        Term::IntLe(a, b) => format_binary(output, "<=", a, b),
        Term::IntGt(a, b) => format_binary(output, ">", a, b),
        Term::IntGe(a, b) => format_binary(output, ">=", a, b),
        Term::Select(arr, idx) => format_binary(output, "select", arr, idx),
        Term::Store(arr, idx, val) => {
            output.push_str("(store ");
            format_term(output, arr);
            output.push(' ');
            format_term(output, idx);
            output.push(' ');
            format_term(output, val);
            output.push(')');
        }
        Term::Forall(bindings, body) => {
            output.push_str("(forall (");
            for (i, (name, sort)) in bindings.iter().enumerate() {
                if i > 0 {
                    output.push(' ');
                }
                output.push_str(&format!("({name} "));
                format_sort(output, sort);
                output.push(')');
            }
            output.push_str(") ");
            format_term(output, body);
            output.push(')');
        }
        Term::Exists(bindings, body) => {
            output.push_str("(exists (");
            for (i, (name, sort)) in bindings.iter().enumerate() {
                if i > 0 {
                    output.push(' ');
                }
                output.push_str(&format!("({name} "));
                format_sort(output, sort);
                output.push(')');
            }
            output.push_str(") ");
            format_term(output, body);
            output.push(')');
        }
        Term::Let(bindings, body) => {
            output.push_str("(let (");
            for (i, (name, val)) in bindings.iter().enumerate() {
                if i > 0 {
                    output.push(' ');
                }
                output.push_str(&format!("({name} "));
                format_term(output, val);
                output.push(')');
            }
            output.push_str(") ");
            format_term(output, body);
            output.push(')');
        }
        Term::App(func, args) => {
            output.push_str(&format!("({func}"));
            for arg in args {
                output.push(' ');
                format_term(output, arg);
            }
            output.push(')');
        }
    }
}

/// Format a binary operation.
fn format_binary(
    output: &mut String,
    op: &str,
    a: &rust_fv_smtlib::term::Term,
    b: &rust_fv_smtlib::term::Term,
) {
    output.push_str(&format!("({op} "));
    format_term(output, a);
    output.push(' ');
    format_term(output, b);
    output.push(')');
}

/// Format an n-ary operation.
fn format_nary(output: &mut String, op: &str, terms: &[rust_fv_smtlib::term::Term]) {
    output.push_str(&format!("({op}"));
    for t in terms {
        output.push(' ');
        format_term(output, t);
    }
    output.push(')');
}

/// Ensure the SMT-LIB text includes `(check-sat)` and `(get-model)`.
fn ensure_check_sat_and_get_model(smtlib: &mut String, script: &Script) {
    use rust_fv_smtlib::command::Command as SmtCmd;

    let has_check_sat = script
        .commands()
        .iter()
        .any(|c| matches!(c, SmtCmd::CheckSat));
    let has_get_model = script
        .commands()
        .iter()
        .any(|c| matches!(c, SmtCmd::GetModel));

    if !has_check_sat {
        smtlib.push_str("(check-sat)\n");
    }
    if !has_get_model {
        smtlib.push_str("(get-model)\n");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_fv_smtlib::command::Command as SmtCmd;
    use rust_fv_smtlib::sort::Sort;
    use rust_fv_smtlib::term::Term;

    // ---- Unit tests for formatting ----

    #[test]
    fn format_sort_bool() {
        let mut s = String::new();
        format_sort(&mut s, &Sort::Bool);
        assert_eq!(s, "Bool");
    }

    #[test]
    fn format_sort_bitvec() {
        let mut s = String::new();
        format_sort(&mut s, &Sort::BitVec(32));
        assert_eq!(s, "(_ BitVec 32)");
    }

    #[test]
    fn format_sort_array() {
        let mut s = String::new();
        format_sort(
            &mut s,
            &Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)),
        );
        assert_eq!(s, "(Array Int Int)");
    }

    #[test]
    fn format_term_bool_lit() {
        let mut s = String::new();
        format_term(&mut s, &Term::BoolLit(true));
        assert_eq!(s, "true");
    }

    #[test]
    fn format_term_int_lit() {
        let mut s = String::new();
        format_term(&mut s, &Term::IntLit(42));
        assert_eq!(s, "42");
    }

    #[test]
    fn format_term_negative_int_lit() {
        let mut s = String::new();
        format_term(&mut s, &Term::IntLit(-5));
        assert_eq!(s, "(- 5)");
    }

    #[test]
    fn format_term_bitvec_lit() {
        let mut s = String::new();
        format_term(&mut s, &Term::BitVecLit(0x0a, 8));
        assert_eq!(s, "#x0a");
    }

    #[test]
    fn format_term_and() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::And(vec![
                Term::Const("a".to_string()),
                Term::Const("b".to_string()),
            ]),
        );
        assert_eq!(s, "(and a b)");
    }

    #[test]
    fn format_term_bvadd() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvAdd(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            ),
        );
        assert_eq!(s, "(bvadd x y)");
    }

    #[test]
    fn format_command_declare_const() {
        let mut s = String::new();
        format_command(&mut s, &SmtCmd::DeclareConst("x".to_string(), Sort::Int));
        assert_eq!(s, "(declare-const x Int)");
    }

    #[test]
    fn format_command_assert() {
        let mut s = String::new();
        format_command(
            &mut s,
            &SmtCmd::Assert(Term::Eq(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::IntLit(5)),
            )),
        );
        assert_eq!(s, "(assert (= x 5))");
    }

    #[test]
    fn format_full_script() {
        let mut script = Script::new();
        script.push(SmtCmd::SetLogic("QF_LIA".to_string()));
        script.push(SmtCmd::DeclareConst("x".to_string(), Sort::Int));
        script.push(SmtCmd::Assert(Term::IntGt(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::IntLit(0)),
        )));

        let text = format_script(&script);
        assert!(text.contains("(set-logic QF_LIA)"));
        assert!(text.contains("(declare-const x Int)"));
        assert!(text.contains("(assert (> x 0))"));
    }

    #[test]
    fn ensure_appends_check_sat() {
        let script = Script::new();
        let mut smtlib = String::new();
        ensure_check_sat_and_get_model(&mut smtlib, &script);
        assert!(smtlib.contains("(check-sat)"));
        assert!(smtlib.contains("(get-model)"));
    }

    #[test]
    fn ensure_does_not_duplicate_check_sat() {
        let mut script = Script::new();
        script.push(SmtCmd::CheckSat);
        script.push(SmtCmd::GetModel);
        let mut smtlib = String::new();
        ensure_check_sat_and_get_model(&mut smtlib, &script);
        assert!(!smtlib.contains("(check-sat)"));
        assert!(!smtlib.contains("(get-model)"));
    }
}
