use crate::error::SolverError;
use crate::model::Model;
use crate::result::SolverResult;

/// Parse Z3's stdout output into a `SolverResult`.
///
/// Expected output format:
/// - First line: `sat`, `unsat`, or `unknown`
/// - If `sat`: subsequent lines contain the model from `(get-model)`
pub fn parse_solver_output(stdout: &str, stderr: &str) -> Result<SolverResult, SolverError> {
    let stdout = stdout.trim();

    if stdout.is_empty() {
        // Check stderr for clues
        if stderr.contains("timeout") {
            return Ok(SolverResult::Unknown("timeout".to_string()));
        }
        return Err(SolverError::ParseError(format!(
            "Empty solver output. stderr: {stderr}"
        )));
    }

    // Find the first meaningful line (sat/unsat/unknown)
    let first_line = stdout
        .lines()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .unwrap_or("");

    match first_line {
        "unsat" => Ok(SolverResult::Unsat),
        "sat" => {
            // Try to parse model from remaining output
            let model = parse_model(stdout)?;
            Ok(SolverResult::Sat(model))
        }
        "unknown" => {
            // Try to extract reason from output or stderr
            let reason = extract_unknown_reason(stdout, stderr);
            Ok(SolverResult::Unknown(reason))
        }
        "timeout" => Ok(SolverResult::Unknown("timeout".to_string())),
        _ => Err(SolverError::ParseError(format!(
            "Unexpected solver output: {first_line}"
        ))),
    }
}

/// Extract the reason string for an "unknown" result.
fn extract_unknown_reason(stdout: &str, stderr: &str) -> String {
    // Z3 sometimes prints the reason after "unknown"
    let after_unknown = stdout
        .lines()
        .skip_while(|line| line.trim() != "unknown")
        .skip(1)
        .map(str::trim)
        .find(|line| !line.is_empty());

    if let Some(reason) = after_unknown {
        // Clean up parenthesized reasons like "(timeout)"
        reason
            .trim_start_matches('(')
            .trim_end_matches(')')
            .to_string()
    } else if !stderr.is_empty() {
        stderr.trim().to_string()
    } else {
        "unknown".to_string()
    }
}

/// Parse a Z3 model from solver output.
///
/// Z3 outputs models in two known formats:
///
/// **Format 1** (Z3 4.15+):
/// ```text
/// (
///   (define-fun x () Int
///     5)
/// )
/// ```
///
/// **Format 2** (older Z3):
/// ```text
/// (model
///   (define-fun x () Int 5)
/// )
/// ```
///
/// For Phase 1, we parse only nullary `define-fun` (constants with no parameters).
fn parse_model(output: &str) -> Result<Option<Model>, SolverError> {
    // Find the model section. It starts after "sat\n" and is enclosed in parens.
    // Look for "(define-fun" as the reliable indicator of model content.
    if !output.contains("(define-fun ") {
        return Ok(None);
    }

    // Find the model block: either "(model" or a top-level "(" after "sat"
    let model_text = find_model_block(output)?;

    let mut assignments = Vec::new();

    // Parse each define-fun in the model
    let mut pos = 0;

    while pos < model_text.len() {
        if let Some(def_pos) = model_text[pos..].find("(define-fun ") {
            let abs_pos = pos + def_pos;
            let after_define = abs_pos + "(define-fun ".len();

            // Find the closing paren of this define-fun by matching parens
            let define_fun_end = find_sexp_end(model_text, abs_pos);

            if let Some(end) = define_fun_end {
                // end points AFTER the closing ')'; body excludes both the
                // opening `(define-fun ` and the final `)`
                let body_end = end - 1; // skip the closing ')'
                let define_fun_body = &model_text[after_define..body_end];
                if let Some((name, value)) = parse_define_fun(define_fun_body) {
                    assignments.push((name, value));
                }
                pos = end;
            } else {
                pos = after_define;
            }
        } else {
            break;
        }
    }

    if assignments.is_empty() {
        Ok(None)
    } else {
        Ok(Some(Model::with_assignments(assignments)))
    }
}

/// Find the model block in the output text.
/// Returns the substring containing the model.
fn find_model_block(output: &str) -> Result<&str, SolverError> {
    // Try "(model" first (older Z3 format)
    if let Some(start) = output.find("(model") {
        return Ok(&output[start..]);
    }

    // For newer Z3: find the "(" that starts the model block after "sat"
    // The model is the content after "sat\n"
    let after_sat = output.find("sat").map(|i| &output[i + 3..]).unwrap_or("");

    let trimmed = after_sat.trim();
    if trimmed.starts_with('(') {
        Ok(trimmed)
    } else {
        Ok(output)
    }
}

/// Find the end of an S-expression starting at `start`.
/// Returns the index AFTER the closing paren.
fn find_sexp_end(input: &str, start: usize) -> Option<usize> {
    let bytes = input.as_bytes();
    if start >= bytes.len() || bytes[start] != b'(' {
        return None;
    }

    let mut depth = 1;
    let mut i = start + 1;
    while i < bytes.len() && depth > 0 {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => depth -= 1,
            _ => {}
        }
        i += 1;
    }

    if depth == 0 { Some(i) } else { None }
}

/// Parse a single `define-fun` entry.
///
/// Input is the body of the define-fun (after `(define-fun `), up to but not
/// including the closing paren.
///
/// Z3 may format this across multiple lines:
/// ```text
/// x () Int
///     5
/// ```
/// or on one line: `x () Int 5`
///
/// Returns `(name, value_string)` if it's a nullary function (constant).
fn parse_define_fun(input: &str) -> Option<(String, String)> {
    // Normalize whitespace: collapse all whitespace to single spaces
    let normalized: String = input.split_whitespace().collect::<Vec<_>>().join(" ");
    let input = normalized.trim();

    if input.is_empty() {
        return None;
    }

    // Extract name: first token
    let name_end = input.find(|c: char| c.is_whitespace())?;
    let name = input[..name_end].to_string();
    let rest = input[name_end..].trim_start();

    // Expect `()` for nullary function (constant)
    if !rest.starts_with("()") {
        // Has parameters -- skip non-constant functions for Phase 1
        return None;
    }
    let rest = rest[2..].trim_start();

    // Skip the sort, then extract the value.
    // The sort could be simple like `Int`, `Bool`, `Real`,
    // or compound like `(_ BitVec 32)`, `(Array Int Int)`.
    let (value, _) = extract_value_after_sort(rest)?;
    Some((name, value))
}

/// Skip the sort and extract the value string from the remaining text.
///
/// Input examples (after normalizing whitespace):
/// - `"Int 5"` -> value = "5"
/// - `"(_ BitVec 32) #x00000005"` -> value = "#x00000005"
/// - `"Bool true"` -> value = "true"
/// - `"Int (- 3)"` -> value = "(- 3)"
fn extract_value_after_sort(input: &str) -> Option<(String, usize)> {
    let mut pos = 0;

    // Skip the sort
    pos = skip_sexp(input, pos)?;

    // Skip whitespace
    let bytes = input.as_bytes();
    while pos < bytes.len() && bytes[pos].is_ascii_whitespace() {
        pos += 1;
    }

    if pos >= bytes.len() {
        return None;
    }

    // The value is everything from here to the end of the input
    let value = input[pos..].trim().to_string();
    if value.is_empty() {
        return None;
    }

    Some((value, input.len()))
}

/// Skip one S-expression starting at `pos`.
/// Returns the position after the S-expression.
fn skip_sexp(input: &str, pos: usize) -> Option<usize> {
    let bytes = input.as_bytes();
    if pos >= bytes.len() {
        return None;
    }

    if bytes[pos] == b'(' {
        // Compound: skip to matching close paren
        let mut depth = 1;
        let mut i = pos + 1;
        while i < bytes.len() && depth > 0 {
            match bytes[i] {
                b'(' => depth += 1,
                b')' => depth -= 1,
                _ => {}
            }
            i += 1;
        }
        Some(i)
    } else {
        // Atom: skip to next whitespace or paren
        let mut i = pos;
        while i < bytes.len()
            && !bytes[i].is_ascii_whitespace()
            && bytes[i] != b'('
            && bytes[i] != b')'
        {
            i += 1;
        }
        Some(i)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- parse_solver_output tests ----

    #[test]
    fn parse_unsat() {
        let result = parse_solver_output("unsat\n", "").unwrap();
        assert_eq!(result, SolverResult::Unsat);
    }

    #[test]
    fn parse_sat_no_model() {
        let result = parse_solver_output("sat\n", "").unwrap();
        assert_eq!(result, SolverResult::Sat(None));
    }

    #[test]
    fn parse_unknown() {
        let result = parse_solver_output("unknown\n", "").unwrap();
        assert!(result.is_unknown());
    }

    #[test]
    fn parse_unknown_with_reason() {
        let output = "unknown\n(timeout)\n";
        let result = parse_solver_output(output, "").unwrap();
        assert_eq!(result, SolverResult::Unknown("timeout".to_string()));
    }

    #[test]
    fn parse_empty_output_error() {
        let result = parse_solver_output("", "");
        assert!(result.is_err());
    }

    #[test]
    fn parse_unexpected_output_error() {
        let result = parse_solver_output("garbage output\n", "");
        assert!(result.is_err());
    }

    // ---- Model parsing: older Z3 format with "(model" ----

    #[test]
    fn parse_sat_with_model_old_format() {
        let output = "\
sat
(model
  (define-fun x () Int 5)
  (define-fun y () Bool true)
)";
        let result = parse_solver_output(output, "").unwrap();
        assert!(result.is_sat());
        let model = result.model().unwrap();
        assert_eq!(model.get("x"), Some("5"));
        assert_eq!(model.get("y"), Some("true"));
    }

    #[test]
    fn parse_sat_with_bitvec_model_old_format() {
        let output = "\
sat
(model
  (define-fun x () (_ BitVec 32) #x00000005)
  (define-fun y () (_ BitVec 8) #b00001010)
)";
        let result = parse_solver_output(output, "").unwrap();
        assert!(result.is_sat());
        let model = result.model().unwrap();
        assert_eq!(model.get("x"), Some("#x00000005"));
        assert_eq!(model.get("y"), Some("#b00001010"));
    }

    #[test]
    fn parse_sat_with_negative_value_old_format() {
        let output = "\
sat
(model
  (define-fun x () Int (- 3))
)";
        let result = parse_solver_output(output, "").unwrap();
        assert!(result.is_sat());
        let model = result.model().unwrap();
        assert_eq!(model.get("x"), Some("(- 3)"));
    }

    // ---- Model parsing: newer Z3 4.15+ format (no "model" keyword) ----

    #[test]
    fn parse_sat_with_model_new_format() {
        let output = "\
sat
(
  (define-fun x () Int
    5)
)";
        let result = parse_solver_output(output, "").unwrap();
        assert!(result.is_sat());
        let model = result.model().unwrap();
        assert_eq!(model.get("x"), Some("5"));
    }

    #[test]
    fn parse_sat_with_bitvec_model_new_format() {
        let output = "\
sat
(
  (define-fun x () (_ BitVec 32)
    #x00000005)
)";
        let result = parse_solver_output(output, "").unwrap();
        assert!(result.is_sat());
        let model = result.model().unwrap();
        assert_eq!(model.get("x"), Some("#x00000005"));
    }

    #[test]
    fn parse_sat_with_negative_value_new_format() {
        let output = "\
sat
(
  (define-fun x () Int
    (- 42))
)";
        let result = parse_solver_output(output, "").unwrap();
        assert!(result.is_sat());
        let model = result.model().unwrap();
        assert_eq!(model.get("x"), Some("(- 42)"));
    }

    #[test]
    fn parse_sat_with_bool_model_new_format() {
        let output = "\
sat
(
  (define-fun p () Bool
    true)
  (define-fun q () Bool
    false)
)";
        let result = parse_solver_output(output, "").unwrap();
        assert!(result.is_sat());
        let model = result.model().unwrap();
        assert_eq!(model.get("p"), Some("true"));
        assert_eq!(model.get("q"), Some("false"));
    }

    #[test]
    fn parse_sat_multi_var_new_format() {
        let output = "\
sat
(
  (define-fun a () Int
    10)
  (define-fun b () Int
    20)
  (define-fun c () Bool
    true)
)";
        let result = parse_solver_output(output, "").unwrap();
        assert!(result.is_sat());
        let model = result.model().unwrap();
        assert_eq!(model.get("a"), Some("10"));
        assert_eq!(model.get("b"), Some("20"));
        assert_eq!(model.get("c"), Some("true"));
    }

    // ---- parse_define_fun unit tests ----

    #[test]
    fn parse_define_fun_int() {
        let result = parse_define_fun("x () Int 5");
        assert_eq!(result, Some(("x".to_string(), "5".to_string())));
    }

    #[test]
    fn parse_define_fun_bool() {
        let result = parse_define_fun("flag () Bool true");
        assert_eq!(result, Some(("flag".to_string(), "true".to_string())));
    }

    #[test]
    fn parse_define_fun_bitvec() {
        let result = parse_define_fun("val () (_ BitVec 32) #x0000000a");
        assert_eq!(result, Some(("val".to_string(), "#x0000000a".to_string())));
    }

    #[test]
    fn parse_define_fun_negative() {
        let result = parse_define_fun("n () Int (- 42)");
        assert_eq!(result, Some(("n".to_string(), "(- 42)".to_string())));
    }

    #[test]
    fn parse_define_fun_multiline() {
        let result = parse_define_fun("x () Int\n    5");
        assert_eq!(result, Some(("x".to_string(), "5".to_string())));
    }

    #[test]
    fn parse_define_fun_bitvec_multiline() {
        let result = parse_define_fun("x () (_ BitVec 32)\n    #x00000005");
        assert_eq!(result, Some(("x".to_string(), "#x00000005".to_string())));
    }

    #[test]
    fn parse_define_fun_with_params_skipped() {
        // Functions with parameters should be skipped
        let result = parse_define_fun("f ((x Int)) Int (+ x 1)");
        assert_eq!(result, None);
    }

    // ---- skip_sexp tests ----

    #[test]
    fn skip_sexp_atom() {
        assert_eq!(skip_sexp("Int 5)", 0), Some(3));
    }

    #[test]
    fn skip_sexp_compound() {
        assert_eq!(skip_sexp("(_ BitVec 32) #x05)", 0), Some(13));
    }

    #[test]
    fn skip_sexp_nested() {
        assert_eq!(skip_sexp("(Array (Int) (Bool)) val", 0), Some(20));
    }

    // ---- find_sexp_end tests ----

    #[test]
    fn find_sexp_end_simple() {
        let input = "(define-fun x () Int 5)";
        assert_eq!(find_sexp_end(input, 0), Some(23));
    }

    #[test]
    fn find_sexp_end_nested() {
        let input = "(define-fun x () (_ BitVec 32) #x05)";
        assert_eq!(find_sexp_end(input, 0), Some(36));
    }
}
