use std::io::Write;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::Duration;

use rust_fv_smtlib::script::Script;

use crate::config::{SolverConfig, SolverKind};
use crate::error::SolverError;
use crate::parser::parse_solver_output;
use crate::result::SolverResult;

/// Generic CLI-based SMT solver interface.
///
/// Communicates with any SMT-LIB2 compatible solver (Z3, CVC5, Yices)
/// by spawning it as a subprocess and piping SMT-LIB2 text.
#[derive(Debug)]
pub struct CliSolver {
    config: SolverConfig,
}

impl CliSolver {
    /// Create a new `CliSolver` with the given configuration.
    pub fn new(config: SolverConfig) -> Self {
        Self { config }
    }

    /// Create a `CliSolver` with auto-detected solver location.
    pub fn with_default_config_for(kind: SolverKind) -> Result<Self, SolverError> {
        let config = SolverConfig::auto_detect_for(kind)?;
        Ok(Self { config })
    }

    /// Get a reference to the solver configuration.
    pub fn config(&self) -> &SolverConfig {
        &self.config
    }

    /// Get the solver kind.
    pub fn kind(&self) -> SolverKind {
        self.config.kind
    }

    /// Check satisfiability of a Script.
    ///
    /// Formats the script to SMT-LIB2 text, appends `(check-sat)`
    /// and `(get-model)` if not already present, and runs the solver.
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

        let args = self.config.build_args();
        let solver_name = self.config.kind.to_string();

        // Spawn solver process
        let mut child = Command::new(&self.config.solver_path)
            .args(&args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| {
                SolverError::ProcessError(format!("Failed to start {solver_name}: {e}"))
            })?;

        // Write SMT-LIB to stdin and close it so the solver sees EOF
        {
            let stdin = child.stdin.take().ok_or_else(|| {
                SolverError::ProcessError(format!("Failed to open {solver_name} stdin"))
            })?;
            let mut stdin = stdin;
            stdin.write_all(smtlib.as_bytes()).map_err(|e| {
                SolverError::ProcessError(format!("Failed to write to {solver_name} stdin: {e}"))
            })?;
            // stdin is dropped here, closing the pipe and signaling EOF to the solver
        }

        // If a timeout is configured, enforce it at the OS level via a background thread.
        // Z3's internal -t: flag is a solver heuristic: it can be ignored on hard problems
        // or older Z3 versions (e.g. Ubuntu apt z3 4.8.x with QF_NIA). Without an OS-level
        // timeout the test thread blocks in wait_with_output() indefinitely.
        let timeout_ms = self.config.timeout_ms;
        if timeout_ms > 0 {
            // Capture the OS PID before moving `child` into the background thread.
            // This lets us kill the process by PID when the OS-level timeout fires,
            // guaranteeing termination even when Z3 ignores its internal -t: flag.
            let child_pid = child.id();

            let (tx, rx) = mpsc::channel();
            // Move child into background thread that waits for the solver
            let handle = std::thread::spawn(move || {
                let result = child.wait_with_output();
                // Send result; ignore send error if receiver timed out and dropped
                let _ = tx.send(result);
            });

            // Add a generous OS-level margin: give the solver 3x its configured timeout
            // to account for startup overhead and allow the solver's own timeout to fire first.
            // Cap at a minimum of 10 seconds so tiny timeouts still have room to work.
            let os_timeout_ms = (timeout_ms * 3).max(10_000);
            match rx.recv_timeout(Duration::from_millis(os_timeout_ms)) {
                Ok(wait_result) => {
                    let output = wait_result.map_err(|e| {
                        SolverError::ProcessError(format!("Failed to wait for {solver_name}: {e}"))
                    })?;
                    let stdout = String::from_utf8_lossy(&output.stdout);
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    if stderr.contains("timeout") || stdout.trim() == "timeout" {
                        return Ok(SolverResult::Unknown("timeout".to_string()));
                    }
                    // Background thread finished; ignore join result
                    let _ = handle.join();
                    return parse_solver_output(&stdout, &stderr);
                }
                Err(_) => {
                    // OS-level timeout expired. Kill the solver process by PID to guarantee
                    // it terminates. The background thread unblocks once the child exits,
                    // preventing thread and process leaks in CI.
                    kill_process(child_pid);
                    // Give the background thread a moment to notice the kill and unblock.
                    let _ = handle.join();
                    return Ok(SolverResult::Unknown(format!(
                        "OS-level timeout after {}ms: {solver_name} process killed after {}ms",
                        timeout_ms, os_timeout_ms
                    )));
                }
            }
        }

        // No timeout configured — wait indefinitely (original behavior)
        let output = child.wait_with_output().map_err(|e| {
            SolverError::ProcessError(format!("Failed to wait for {solver_name}: {e}"))
        })?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        // Check for timeout in stderr
        if stderr.contains("timeout") || stdout.trim() == "timeout" {
            return Ok(SolverResult::Unknown("timeout".to_string()));
        }

        parse_solver_output(&stdout, &stderr)
    }
}

/// Backward-compatible type alias for Z3-specific solver.
pub type Z3Solver = CliSolver;

/// Convenience constructors for Z3Solver (backward compatibility).
impl CliSolver {
    /// Create a Z3 solver with auto-detected location and default settings.
    pub fn with_default_config() -> Result<Self, SolverError> {
        Self::with_default_config_for(SolverKind::Z3)
    }
}

/// Kill a process by PID at the OS level.
///
/// On Unix-like systems, sends SIGKILL (unconditional kill).
/// On Windows, calls TerminateProcess.
///
/// This is used as a backstop when a solver process does not terminate within
/// the configured timeout. Errors are intentionally ignored: if the process
/// already exited, killing it is a no-op.
fn kill_process(pid: u32) {
    #[cfg(unix)]
    {
        // Safety: SIGKILL(9) is always valid; pid is obtained from a live child.
        // Ignore ESRCH (process already dead) and other errors.
        unsafe {
            libc::kill(pid as libc::pid_t, libc::SIGKILL);
        }
    }
    #[cfg(windows)]
    {
        use windows_sys::Win32::Foundation::CloseHandle;
        use windows_sys::Win32::System::Threading::{
            OpenProcess, PROCESS_TERMINATE, TerminateProcess,
        };
        // SAFETY: OpenProcess/TerminateProcess are safe with valid PID and access rights.
        unsafe {
            let handle = OpenProcess(PROCESS_TERMINATE, 0, pid);
            if handle != 0 {
                TerminateProcess(handle, 1);
                CloseHandle(handle);
            }
        }
    }
    #[cfg(not(any(unix, windows)))]
    {
        // Unsupported platform: no-op; OS may eventually reap the orphan.
        let _ = pid;
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
        SmtCmd::DeclareDatatype { name, variants } => {
            output.push_str(&format!("(declare-datatype {name} ("));
            for (i, variant) in variants.iter().enumerate() {
                if i > 0 {
                    output.push(' ');
                }
                if variant.fields.is_empty() {
                    output.push_str(&format!("({})", variant.constructor));
                } else {
                    output.push_str(&format!("({}", variant.constructor));
                    for (field_name, field_sort) in &variant.fields {
                        output.push_str(&format!(" ({field_name} "));
                        format_sort(output, field_sort);
                        output.push(')');
                    }
                    output.push(')');
                }
            }
            output.push_str("))");
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
        Sort::Seq(inner) => {
            output.push_str("(Seq ");
            format_sort(output, inner);
            output.push(')');
        }
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
        Term::Bv2Int(a) => {
            output.push_str("(bv2int ");
            format_term(output, a);
            output.push(')');
        }
        Term::Int2Bv(n, a) => {
            output.push_str(&format!("((_ int2bv {n}) "));
            format_term(output, a);
            output.push(')');
        }
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
        Term::Annotated(body, annotations) => {
            if annotations.is_empty() {
                format_term(output, body);
            } else {
                output.push_str("(! ");
                format_term(output, body);
                for (key, values) in annotations {
                    output.push_str(&format!(" :{key} ("));
                    for (i, val) in values.iter().enumerate() {
                        if i > 0 {
                            output.push(' ');
                        }
                        format_term(output, val);
                    }
                    output.push(')');
                }
                output.push(')');
            }
        }
        // Floating-point terms: use Display impl from smtlib
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
        // Sequence terms: use Display impl from smtlib
        | Term::SeqEmpty(..)
        | Term::SeqUnit(..)
        | Term::SeqConcat(..)
        | Term::SeqLen(..)
        | Term::SeqNth(..)
        | Term::SeqExtract(..)
        | Term::SeqContains(..)
        | Term::SeqUpdate(..) => {
            // Delegate to Term's Display impl for floating-point and sequence terms
            output.push_str(&term.to_string());
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

    // ---- Sort formatting: remaining variants ----

    #[test]
    fn format_sort_int() {
        let mut s = String::new();
        format_sort(&mut s, &Sort::Int);
        assert_eq!(s, "Int");
    }

    #[test]
    fn format_sort_real() {
        let mut s = String::new();
        format_sort(&mut s, &Sort::Real);
        assert_eq!(s, "Real");
    }

    #[test]
    fn format_sort_datatype() {
        let mut s = String::new();
        format_sort(&mut s, &Sort::Datatype("MyType".to_string()));
        assert_eq!(s, "MyType");
    }

    #[test]
    fn format_sort_float() {
        let mut s = String::new();
        format_sort(&mut s, &Sort::Float(8, 24));
        assert_eq!(s, "(_ FloatingPoint 8 24)");
    }

    #[test]
    fn format_sort_float_double() {
        let mut s = String::new();
        format_sort(&mut s, &Sort::Float(11, 53));
        assert_eq!(s, "(_ FloatingPoint 11 53)");
    }

    #[test]
    fn format_sort_uninterpreted() {
        let mut s = String::new();
        format_sort(&mut s, &Sort::Uninterpreted("U".to_string()));
        assert_eq!(s, "U");
    }

    #[test]
    fn format_sort_nested_array() {
        let mut s = String::new();
        let inner = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Bool));
        let outer = Sort::Array(Box::new(Sort::BitVec(8)), Box::new(inner));
        format_sort(&mut s, &outer);
        assert_eq!(s, "(Array (_ BitVec 8) (Array Int Bool))");
    }

    // ---- Term formatting: boolean and core operations ----

    #[test]
    fn format_term_bool_lit_false() {
        let mut s = String::new();
        format_term(&mut s, &Term::BoolLit(false));
        assert_eq!(s, "false");
    }

    #[test]
    fn format_term_const() {
        let mut s = String::new();
        format_term(&mut s, &Term::Const("my_var".to_string()));
        assert_eq!(s, "my_var");
    }

    #[test]
    fn format_term_not() {
        let mut s = String::new();
        format_term(&mut s, &Term::Not(Box::new(Term::Const("a".to_string()))));
        assert_eq!(s, "(not a)");
    }

    #[test]
    fn format_term_or() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Or(vec![
                Term::Const("a".to_string()),
                Term::Const("b".to_string()),
                Term::Const("c".to_string()),
            ]),
        );
        assert_eq!(s, "(or a b c)");
    }

    #[test]
    fn format_term_implies() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Implies(
                Box::new(Term::Const("p".to_string())),
                Box::new(Term::Const("q".to_string())),
            ),
        );
        assert_eq!(s, "(=> p q)");
    }

    #[test]
    fn format_term_iff() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Iff(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(= a b)");
    }

    #[test]
    fn format_term_distinct() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Distinct(vec![
                Term::Const("a".to_string()),
                Term::Const("b".to_string()),
                Term::Const("c".to_string()),
            ]),
        );
        assert_eq!(s, "(distinct a b c)");
    }

    #[test]
    fn format_term_ite() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Ite(
                Box::new(Term::Const("c".to_string())),
                Box::new(Term::IntLit(1)),
                Box::new(Term::IntLit(0)),
            ),
        );
        assert_eq!(s, "(ite c 1 0)");
    }

    // ---- Term formatting: bitvector arithmetic ----

    #[test]
    fn format_term_bvsub() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvSub(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            ),
        );
        assert_eq!(s, "(bvsub x y)");
    }

    #[test]
    fn format_term_bvmul() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvMul(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::Const("y".to_string())),
            ),
        );
        assert_eq!(s, "(bvmul x y)");
    }

    #[test]
    fn format_term_bvsdiv() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvSDiv(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvsdiv a b)");
    }

    #[test]
    fn format_term_bvudiv() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvUDiv(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvudiv a b)");
    }

    #[test]
    fn format_term_bvsrem() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvSRem(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvsrem a b)");
    }

    #[test]
    fn format_term_bvurem() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvURem(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvurem a b)");
    }

    #[test]
    fn format_term_bvneg() {
        let mut s = String::new();
        format_term(&mut s, &Term::BvNeg(Box::new(Term::Const("x".to_string()))));
        assert_eq!(s, "(bvneg x)");
    }

    // ---- Term formatting: bitvector comparisons (signed) ----

    #[test]
    fn format_term_bvslt() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvSLt(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvslt a b)");
    }

    #[test]
    fn format_term_bvsle() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvSLe(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvsle a b)");
    }

    #[test]
    fn format_term_bvsgt() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvSGt(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvsgt a b)");
    }

    #[test]
    fn format_term_bvsge() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvSGe(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvsge a b)");
    }

    // ---- Term formatting: bitvector comparisons (unsigned) ----

    #[test]
    fn format_term_bvult() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvULt(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvult a b)");
    }

    #[test]
    fn format_term_bvule() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvULe(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvule a b)");
    }

    #[test]
    fn format_term_bvugt() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvUGt(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvugt a b)");
    }

    #[test]
    fn format_term_bvuge() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvUGe(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvuge a b)");
    }

    // ---- Term formatting: bitvector bitwise ----

    #[test]
    fn format_term_bvand() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvAnd(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvand a b)");
    }

    #[test]
    fn format_term_bvor() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvOr(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvor a b)");
    }

    #[test]
    fn format_term_bvxor() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvXor(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvxor a b)");
    }

    #[test]
    fn format_term_bvnot() {
        let mut s = String::new();
        format_term(&mut s, &Term::BvNot(Box::new(Term::Const("x".to_string()))));
        assert_eq!(s, "(bvnot x)");
    }

    #[test]
    fn format_term_bvshl() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvShl(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvshl a b)");
    }

    #[test]
    fn format_term_bvlshr() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvLShr(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvlshr a b)");
    }

    #[test]
    fn format_term_bvashr() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::BvAShr(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(bvashr a b)");
    }

    // ---- Term formatting: bitvector conversions ----

    #[test]
    fn format_term_zero_extend() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::ZeroExtend(8, Box::new(Term::Const("x".to_string()))),
        );
        assert_eq!(s, "((_ zero_extend 8) x)");
    }

    #[test]
    fn format_term_sign_extend() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::SignExtend(16, Box::new(Term::Const("x".to_string()))),
        );
        assert_eq!(s, "((_ sign_extend 16) x)");
    }

    #[test]
    fn format_term_extract() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Extract(7, 0, Box::new(Term::Const("x".to_string()))),
        );
        assert_eq!(s, "((_ extract 7 0) x)");
    }

    #[test]
    fn format_term_concat() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Concat(
                Box::new(Term::Const("hi".to_string())),
                Box::new(Term::Const("lo".to_string())),
            ),
        );
        assert_eq!(s, "(concat hi lo)");
    }

    #[test]
    fn format_term_bv2int() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Bv2Int(Box::new(Term::Const("x".to_string()))),
        );
        assert_eq!(s, "(bv2int x)");
    }

    #[test]
    fn format_term_int2bv() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Int2Bv(32, Box::new(Term::Const("x".to_string()))),
        );
        assert_eq!(s, "((_ int2bv 32) x)");
    }

    // ---- Term formatting: integer arithmetic ----

    #[test]
    fn format_term_int_add() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::IntAdd(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(+ a b)");
    }

    #[test]
    fn format_term_int_sub() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::IntSub(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(- a b)");
    }

    #[test]
    fn format_term_int_mul() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::IntMul(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(* a b)");
    }

    #[test]
    fn format_term_int_div() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::IntDiv(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(div a b)");
    }

    #[test]
    fn format_term_int_mod() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::IntMod(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(mod a b)");
    }

    #[test]
    fn format_term_int_neg() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::IntNeg(Box::new(Term::Const("x".to_string()))),
        );
        assert_eq!(s, "(- x)");
    }

    #[test]
    fn format_term_int_lt() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::IntLt(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(< a b)");
    }

    #[test]
    fn format_term_int_le() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::IntLe(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(<= a b)");
    }

    #[test]
    fn format_term_int_ge() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::IntGe(
                Box::new(Term::Const("a".to_string())),
                Box::new(Term::Const("b".to_string())),
            ),
        );
        assert_eq!(s, "(>= a b)");
    }

    // ---- Term formatting: array operations ----

    #[test]
    fn format_term_select() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Select(
                Box::new(Term::Const("arr".to_string())),
                Box::new(Term::IntLit(3)),
            ),
        );
        assert_eq!(s, "(select arr 3)");
    }

    #[test]
    fn format_term_store() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Store(
                Box::new(Term::Const("arr".to_string())),
                Box::new(Term::IntLit(0)),
                Box::new(Term::IntLit(42)),
            ),
        );
        assert_eq!(s, "(store arr 0 42)");
    }

    // ---- Term formatting: quantifiers ----

    #[test]
    fn format_term_forall() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Forall(
                vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
                Box::new(Term::Eq(
                    Box::new(Term::Const("x".to_string())),
                    Box::new(Term::Const("y".to_string())),
                )),
            ),
        );
        assert_eq!(s, "(forall ((x Int) (y Int)) (= x y))");
    }

    #[test]
    fn format_term_exists() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Exists(
                vec![("x".to_string(), Sort::Bool)],
                Box::new(Term::Const("x".to_string())),
            ),
        );
        assert_eq!(s, "(exists ((x Bool)) x)");
    }

    // ---- Term formatting: let bindings ----

    #[test]
    fn format_term_let() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Let(
                vec![("a".to_string(), Term::IntLit(10))],
                Box::new(Term::IntAdd(
                    Box::new(Term::Const("a".to_string())),
                    Box::new(Term::IntLit(1)),
                )),
            ),
        );
        assert_eq!(s, "(let ((a 10)) (+ a 1))");
    }

    #[test]
    fn format_term_let_multiple_bindings() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Let(
                vec![
                    ("a".to_string(), Term::IntLit(1)),
                    ("b".to_string(), Term::IntLit(2)),
                ],
                Box::new(Term::IntAdd(
                    Box::new(Term::Const("a".to_string())),
                    Box::new(Term::Const("b".to_string())),
                )),
            ),
        );
        assert_eq!(s, "(let ((a 1) (b 2)) (+ a b))");
    }

    // ---- Term formatting: function application ----

    #[test]
    fn format_term_app_with_args() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::App(
                "f".to_string(),
                vec![Term::Const("x".to_string()), Term::IntLit(3)],
            ),
        );
        assert_eq!(s, "(f x 3)");
    }

    #[test]
    fn format_term_app_no_args() {
        let mut s = String::new();
        format_term(&mut s, &Term::App("f".to_string(), vec![]));
        // App with no args just outputs the function name in parens
        assert_eq!(s, "(f)");
    }

    // ---- Term formatting: annotations ----

    #[test]
    fn format_term_annotated_empty() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Annotated(Box::new(Term::Const("x".to_string())), vec![]),
        );
        assert_eq!(s, "x");
    }

    #[test]
    fn format_term_annotated_with_pattern() {
        let mut s = String::new();
        let body = Term::IntGt(
            Box::new(Term::Const("x".to_string())),
            Box::new(Term::IntLit(0)),
        );
        let trigger = Term::App("f".to_string(), vec![Term::Const("x".to_string())]);
        format_term(
            &mut s,
            &Term::Annotated(Box::new(body), vec![("pattern".to_string(), vec![trigger])]),
        );
        assert_eq!(s, "(! (> x 0) :pattern ((f x)))");
    }

    // ---- Term formatting: bitvec lit edge cases ----

    #[test]
    fn format_term_bitvec_lit_large_width() {
        // Test width >= 128 to exercise the overflow branch
        let mut s = String::new();
        format_term(&mut s, &Term::BitVecLit(0xff, 128));
        // width=128 -> hex_digits = 32, mask = i128::MAX
        let hex_digits = 32;
        let mask = i128::MAX;
        let unsigned = 0xffi128 & mask;
        let expected = format!("#x{:0>width$x}", unsigned, width = hex_digits);
        assert_eq!(s, expected);
    }

    #[test]
    fn format_term_int_lit_zero() {
        let mut s = String::new();
        format_term(&mut s, &Term::IntLit(0));
        assert_eq!(s, "0");
    }

    // ---- Command formatting: remaining variants ----

    #[test]
    fn format_command_set_logic() {
        let mut s = String::new();
        format_command(&mut s, &SmtCmd::SetLogic("QF_BV".to_string()));
        assert_eq!(s, "(set-logic QF_BV)");
    }

    #[test]
    fn format_command_set_option() {
        let mut s = String::new();
        format_command(
            &mut s,
            &SmtCmd::SetOption("produce-models".to_string(), "true".to_string()),
        );
        assert_eq!(s, "(set-option :produce-models true)");
    }

    #[test]
    fn format_command_declare_sort() {
        let mut s = String::new();
        format_command(&mut s, &SmtCmd::DeclareSort("Pair".to_string(), 0));
        assert_eq!(s, "(declare-sort Pair 0)");
    }

    #[test]
    fn format_command_define_sort() {
        let mut s = String::new();
        format_command(
            &mut s,
            &SmtCmd::DefineSort("BV8".to_string(), vec![], Sort::BitVec(8)),
        );
        assert_eq!(s, "(define-sort BV8 () (_ BitVec 8))");
    }

    #[test]
    fn format_command_define_sort_with_params() {
        let mut s = String::new();
        format_command(
            &mut s,
            &SmtCmd::DefineSort(
                "MyArray".to_string(),
                vec!["T".to_string()],
                Sort::Array(
                    Box::new(Sort::Int),
                    Box::new(Sort::Uninterpreted("T".to_string())),
                ),
            ),
        );
        assert_eq!(s, "(define-sort MyArray (T) (Array Int T))");
    }

    #[test]
    fn format_command_declare_fun_no_params() {
        let mut s = String::new();
        format_command(
            &mut s,
            &SmtCmd::DeclareFun("c".to_string(), vec![], Sort::Bool),
        );
        assert_eq!(s, "(declare-fun c () Bool)");
    }

    #[test]
    fn format_command_declare_fun_with_params() {
        let mut s = String::new();
        format_command(
            &mut s,
            &SmtCmd::DeclareFun("f".to_string(), vec![Sort::Int, Sort::Int], Sort::Bool),
        );
        assert_eq!(s, "(declare-fun f (Int Int) Bool)");
    }

    #[test]
    fn format_command_define_fun() {
        let mut s = String::new();
        format_command(
            &mut s,
            &SmtCmd::DefineFun(
                "double".to_string(),
                vec![("x".to_string(), Sort::Int)],
                Sort::Int,
                Term::IntAdd(
                    Box::new(Term::Const("x".to_string())),
                    Box::new(Term::Const("x".to_string())),
                ),
            ),
        );
        assert_eq!(s, "(define-fun double ((x Int)) Int (+ x x))");
    }

    #[test]
    fn format_command_define_fun_multi_params() {
        let mut s = String::new();
        format_command(
            &mut s,
            &SmtCmd::DefineFun(
                "add".to_string(),
                vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
                Sort::Int,
                Term::IntAdd(
                    Box::new(Term::Const("x".to_string())),
                    Box::new(Term::Const("y".to_string())),
                ),
            ),
        );
        assert_eq!(s, "(define-fun add ((x Int) (y Int)) Int (+ x y))");
    }

    #[test]
    fn format_command_check_sat() {
        let mut s = String::new();
        format_command(&mut s, &SmtCmd::CheckSat);
        assert_eq!(s, "(check-sat)");
    }

    #[test]
    fn format_command_get_model() {
        let mut s = String::new();
        format_command(&mut s, &SmtCmd::GetModel);
        assert_eq!(s, "(get-model)");
    }

    #[test]
    fn format_command_get_value() {
        let mut s = String::new();
        format_command(
            &mut s,
            &SmtCmd::GetValue(vec![
                Term::Const("x".to_string()),
                Term::Const("y".to_string()),
            ]),
        );
        assert_eq!(s, "(get-value (x y))");
    }

    #[test]
    fn format_command_push() {
        let mut s = String::new();
        format_command(&mut s, &SmtCmd::Push(1));
        assert_eq!(s, "(push 1)");
    }

    #[test]
    fn format_command_pop() {
        let mut s = String::new();
        format_command(&mut s, &SmtCmd::Pop(2));
        assert_eq!(s, "(pop 2)");
    }

    #[test]
    fn format_command_echo() {
        let mut s = String::new();
        format_command(&mut s, &SmtCmd::Echo("hello".to_string()));
        assert_eq!(s, "(echo \"hello\")");
    }

    #[test]
    fn format_command_comment() {
        let mut s = String::new();
        format_command(&mut s, &SmtCmd::Comment("this is a comment".to_string()));
        assert_eq!(s, ";; this is a comment");
    }

    #[test]
    fn format_command_exit() {
        let mut s = String::new();
        format_command(&mut s, &SmtCmd::Exit);
        assert_eq!(s, "(exit)");
    }

    #[test]
    fn format_command_declare_datatype_enum() {
        use rust_fv_smtlib::command::DatatypeVariant;
        let mut s = String::new();
        format_command(
            &mut s,
            &SmtCmd::DeclareDatatype {
                name: "Color".to_string(),
                variants: vec![
                    DatatypeVariant {
                        constructor: "Red".to_string(),
                        fields: vec![],
                    },
                    DatatypeVariant {
                        constructor: "Green".to_string(),
                        fields: vec![],
                    },
                    DatatypeVariant {
                        constructor: "Blue".to_string(),
                        fields: vec![],
                    },
                ],
            },
        );
        assert_eq!(s, "(declare-datatype Color ((Red) (Green) (Blue)))");
    }

    #[test]
    fn format_command_declare_datatype_with_fields() {
        use rust_fv_smtlib::command::DatatypeVariant;
        let mut s = String::new();
        format_command(
            &mut s,
            &SmtCmd::DeclareDatatype {
                name: "Point".to_string(),
                variants: vec![DatatypeVariant {
                    constructor: "mk-Point".to_string(),
                    fields: vec![
                        ("Point-x".to_string(), Sort::BitVec(32)),
                        ("Point-y".to_string(), Sort::BitVec(32)),
                    ],
                }],
            },
        );
        assert_eq!(
            s,
            "(declare-datatype Point ((mk-Point (Point-x (_ BitVec 32)) (Point-y (_ BitVec 32)))))"
        );
    }

    #[test]
    fn format_command_declare_datatype_mixed() {
        use rust_fv_smtlib::command::DatatypeVariant;
        let mut s = String::new();
        format_command(
            &mut s,
            &SmtCmd::DeclareDatatype {
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
            },
        );
        assert_eq!(
            s,
            "(declare-datatype Option_i32 ((mk-None) (mk-Some (Some-0 (_ BitVec 32)))))"
        );
    }

    // ---- ensure_check_sat_and_get_model edge cases ----

    #[test]
    fn ensure_only_check_sat_present() {
        let mut script = Script::new();
        script.push(SmtCmd::CheckSat);
        // No GetModel
        let mut smtlib = String::new();
        ensure_check_sat_and_get_model(&mut smtlib, &script);
        assert!(!smtlib.contains("(check-sat)"));
        assert!(smtlib.contains("(get-model)"));
    }

    #[test]
    fn ensure_only_get_model_present() {
        let mut script = Script::new();
        script.push(SmtCmd::GetModel);
        // No CheckSat
        let mut smtlib = String::new();
        ensure_check_sat_and_get_model(&mut smtlib, &script);
        assert!(smtlib.contains("(check-sat)"));
        assert!(!smtlib.contains("(get-model)"));
    }

    // ---- format_script integration ----

    #[test]
    fn format_script_empty() {
        let script = Script::new();
        let text = format_script(&script);
        assert_eq!(text, "");
    }

    #[test]
    fn format_script_multiple_commands() {
        let mut script = Script::new();
        script.push(SmtCmd::SetLogic("QF_BV".to_string()));
        script.push(SmtCmd::DeclareConst("x".to_string(), Sort::BitVec(32)));
        script.push(SmtCmd::CheckSat);
        script.push(SmtCmd::Exit);
        let text = format_script(&script);
        assert!(text.contains("(set-logic QF_BV)\n"));
        assert!(text.contains("(declare-const x (_ BitVec 32))\n"));
        assert!(text.contains("(check-sat)\n"));
        assert!(text.contains("(exit)\n"));
    }

    // ---- Eq term formatting ----

    #[test]
    fn format_term_eq() {
        let mut s = String::new();
        format_term(
            &mut s,
            &Term::Eq(
                Box::new(Term::Const("x".to_string())),
                Box::new(Term::IntLit(5)),
            ),
        );
        assert_eq!(s, "(= x 5)");
    }
}
