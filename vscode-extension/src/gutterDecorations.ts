import * as vscode from 'vscode';
import { JsonVerificationReport, JsonFunctionResult } from './verifier';

/**
 * Gutter decoration management for verified functions.
 *
 * Shows green checkmark icons next to function definitions that passed verification.
 */

/**
 * Create the decoration type for verified functions.
 *
 * @param context - Extension context for resource path resolution
 * @returns TextEditorDecorationType for verified function gutter icons
 */
export function createVerifiedDecorationType(context: vscode.ExtensionContext): vscode.TextEditorDecorationType {
  const iconPath = context.asAbsolutePath('resources/verified.svg');

  return vscode.window.createTextEditorDecorationType({
    gutterIconPath: iconPath,
    gutterIconSize: 'contain',
  });
}

/**
 * Update gutter decorations for verified functions in the active editor.
 *
 * Note: The current JSON schema does not include source_line for successful functions,
 * only for failures. This implementation searches for function definitions by name.
 *
 * @param editor - The text editor to decorate
 * @param report - The verification report
 * @param decorationType - The decoration type to apply
 */
export function updateGutterDecorations(
  editor: vscode.TextEditor,
  report: JsonVerificationReport,
  decorationType: vscode.TextEditorDecorationType
): void {
  // Find all functions with status === "ok"
  const verifiedFunctions = report.functions.filter((f) => f.status === 'ok');

  if (verifiedFunctions.length === 0) {
    // No verified functions - clear decorations
    editor.setDecorations(decorationType, []);
    return;
  }

  // Find line numbers for each verified function
  const document = editor.document;
  const ranges: vscode.Range[] = [];

  for (const func of verifiedFunctions) {
    const lineNumber = findFunctionDefinitionLine(document, func.name);
    if (lineNumber !== undefined) {
      const range = new vscode.Range(lineNumber, 0, lineNumber, 0);
      ranges.push(range);
    }
  }

  // Apply decorations
  editor.setDecorations(decorationType, ranges);
}

/**
 * Clear gutter decorations from an editor.
 *
 * @param editor - The text editor to clear decorations from
 * @param decorationType - The decoration type to clear
 */
export function clearGutterDecorations(
  editor: vscode.TextEditor,
  decorationType: vscode.TextEditorDecorationType
): void {
  editor.setDecorations(decorationType, []);
}

/**
 * Find the line number where a function is defined.
 *
 * Searches for function signatures matching the pattern:
 * fn function_name<...>(...) or fn function_name(...)
 *
 * @param document - The text document to search
 * @param functionName - The function name to find
 * @returns The line number (0-indexed) or undefined if not found
 */
function findFunctionDefinitionLine(document: vscode.TextDocument, functionName: string): number | undefined {
  // Escape special regex characters in function name
  const escapedName = functionName.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

  // Pattern: fn function_name followed by < or (
  // This handles both generic and non-generic functions
  const pattern = new RegExp(`\\bfn\\s+${escapedName}\\s*[<(]`);

  // Search through document lines
  for (let i = 0; i < document.lineCount; i++) {
    const line = document.lineAt(i);
    if (pattern.test(line.text)) {
      return i;
    }
  }

  return undefined;
}
