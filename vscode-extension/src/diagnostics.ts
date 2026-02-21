import * as vscode from 'vscode';
import * as path from 'path';
import { JsonVerificationReport, JsonFailure, JsonAssignment, JsonCexVariable } from './verifier';

/**
 * Convert JsonVerificationReport to VSCode Diagnostics grouped by file URI.
 *
 * @param report - The verification report from cargo verify JSON output
 * @param crateRoot - The absolute path to the crate root (where Cargo.toml lives)
 * @returns Map from file URI string to array of diagnostics
 */
export function convertToDiagnostics(
  report: JsonVerificationReport,
  crateRoot: string
): Map<string, vscode.Diagnostic[]> {
  const diagnosticsByFile = new Map<string, vscode.Diagnostic[]>();

  for (const func of report.functions) {
    if (func.status === 'ok' || func.failures.length === 0) {
      continue; // No diagnostics for passing functions
    }

    for (const failure of func.failures) {
      const diagnostic = createDiagnostic(failure);

      // Resolve source file path
      let fileUri: string;
      if (failure.source_file) {
        const absolutePath = path.resolve(crateRoot, failure.source_file);
        fileUri = vscode.Uri.file(absolutePath).toString();
      } else {
        // No source file provided - create a synthetic diagnostic location
        // This shouldn't happen in normal operation, but handle it gracefully
        fileUri = vscode.Uri.file(path.join(crateRoot, 'unknown')).toString();
      }

      // Add to diagnostics collection
      if (!diagnosticsByFile.has(fileUri)) {
        diagnosticsByFile.set(fileUri, []);
      }
      diagnosticsByFile.get(fileUri)!.push(diagnostic);
    }
  }

  return diagnosticsByFile;
}

/**
 * Render a single typed variable from a v2 counterexample.
 *
 * Handles three cases:
 * 1. display-only: variable with a single known value (e.g. function parameter not mutated)
 * 2. initial+at_failure: variable mutated between initial state and failure point
 * 3. initial-only: parameter with known initial value but no mutation tracked
 */
function renderTypedVariable(v: JsonCexVariable): string {
  // Single-value case: variable with one known value (e.g. function parameter that was not mutated)
  if (v.display !== undefined) {
    return `${v.name}: ${v.type} = ${v.display}`;
  }
  // Two-value case: variable mutated between initial state and failure point
  if (v.initial && v.at_failure) {
    return `${v.name}: ${v.type} = ${v.initial.display} (initial) → ${v.at_failure.display} (at failure)`;
  }
  // Initial-only case: parameter with known initial value but no mutation tracked
  if (v.initial) {
    return `${v.name}: ${v.type} = ${v.initial.display}`;
  }
  return `${v.name}: ${v.type} = (unknown)`;
}

/**
 * Render counterexample variables as human-readable lines.
 *
 * Prefers the typed v2 schema (Phase 19-04 output) when present.
 * Falls back to the legacy flat assignment list for backward compatibility
 * with older binaries or timeout/UNSAT scenarios.
 *
 * @param failure - The JsonFailure containing counterexample data
 * @returns Array of formatted lines, e.g. ["x: i32 = 5", "flag: bool = false"]
 */
export function renderCounterexampleLines(failure: JsonFailure): string[] {
  // Prefer typed v2 schema (Phase 19-04 output)
  if (failure.counterexample_v2 && failure.counterexample_v2.variables.length > 0) {
    return failure.counterexample_v2.variables.map(renderTypedVariable);
  }
  // Fallback to legacy flat assignments (backward compat: older binary or timeout/UNSAT)
  if (failure.counterexample && failure.counterexample.length > 0) {
    return failure.counterexample.map((a: JsonAssignment) => `${a.variable} = ${a.value}`);
  }
  return [];
}

/**
 * Create a VSCode Diagnostic from a JsonFailure.
 *
 * @param failure - The failure from cargo verify JSON output
 * @returns VSCode Diagnostic with Error severity
 */
function createDiagnostic(failure: JsonFailure): vscode.Diagnostic {
  // VSCode uses 0-indexed lines, rust-fv JSON uses 1-indexed
  const line = (failure.source_line ?? 1) - 1;
  const range = new vscode.Range(line, 0, line, 100);

  // Build diagnostic message
  let message = failure.description;

  if (failure.contract) {
    message += `\nContract: ${failure.contract}`;
  }

  const cexLines = renderCounterexampleLines(failure);
  if (cexLines.length > 0) {
    message += `\nCounterexample:\n  ${cexLines.join('\n  ')}`;
  }

  if (failure.suggestion) {
    message += `\nSuggestion: ${failure.suggestion}`;
  }

  const diagnostic = new vscode.Diagnostic(
    range,
    message,
    vscode.DiagnosticSeverity.Error
  );

  diagnostic.source = 'rust-fv';
  diagnostic.code = failure.vc_kind;

  return diagnostic;
}

/**
 * Format counterexample assignments as a human-readable string.
 *
 * @param assignments - Array of variable assignments from counterexample
 * @returns Formatted string like "x = 42, y = -1"
 */
export function formatCounterexample(assignments: JsonAssignment[]): string {
  return assignments
    .map((a) => `${a.variable} = ${a.value}`)
    .join(', ');
}
