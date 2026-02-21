import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { JsonVerificationReport, JsonFunctionResult } from './verifier';
import { renderCounterexampleLines } from './diagnostics';

/**
 * Output panel management for structured and raw verification output.
 */

let structuredChannel: vscode.OutputChannel | undefined;
let rawChannel: vscode.OutputChannel | undefined;

/**
 * Create both output channels for verification results.
 *
 * @returns Tuple of [structured channel, raw channel]
 */
export function createOutputPanels(): [vscode.OutputChannel, vscode.OutputChannel] {
  if (!structuredChannel) {
    structuredChannel = vscode.window.createOutputChannel('Rust FV: Failures');
  }
  if (!rawChannel) {
    rawChannel = vscode.window.createOutputChannel('Rust FV: Raw Output');
  }
  return [structuredChannel, rawChannel];
}

/**
 * Update structured output panel with verification report.
 *
 * @param report - The JSON verification report from cargo verify
 */
export function updateStructuredOutput(report: JsonVerificationReport): void {
  if (!structuredChannel) {
    throw new Error('Output channels not initialized. Call createOutputPanels() first.');
  }

  structuredChannel.clear();
  structuredChannel.appendLine(`Verification Report for ${report.crate_name}`);
  structuredChannel.appendLine('='.repeat(60));
  structuredChannel.appendLine('');

  // Group functions by status for better readability
  const passed = report.functions.filter((f) => f.status === 'ok');
  const failed = report.functions.filter((f) => f.status === 'fail');
  const timedOut = report.functions.filter((f) => f.status === 'timeout');

  // Show failures first (most important)
  if (failed.length > 0) {
    structuredChannel.appendLine('FAILURES:');
    structuredChannel.appendLine('');
    for (const func of failed) {
      formatFailedFunction(structuredChannel, func);
    }
    structuredChannel.appendLine('');
  }

  // Show timeouts
  if (timedOut.length > 0) {
    structuredChannel.appendLine('TIMEOUTS:');
    structuredChannel.appendLine('');
    for (const func of timedOut) {
      structuredChannel.appendLine(`  [TIMEOUT] ${func.name}`);
      structuredChannel.appendLine(`    Note: Verification exceeded time limit. Consider simplifying contracts or using manual triggers.`);
      structuredChannel.appendLine('');
    }
    structuredChannel.appendLine('');
  }

  // Show passed functions (brief, not verbose)
  if (passed.length > 0) {
    structuredChannel.appendLine('VERIFIED:');
    for (const func of passed) {
      structuredChannel.appendLine(`  [OK] ${func.name}`);
    }
    structuredChannel.appendLine('');
  }

  // Summary line
  structuredChannel.appendLine('='.repeat(60));
  structuredChannel.appendLine(
    `Summary: ${report.summary.ok} verified, ${report.summary.fail} failed, ${report.summary.timeout} timeout`
  );

  // Show the structured channel (preserveFocus = true)
  structuredChannel.show(true);
}

/**
 * Format a failed function with detailed failure information.
 *
 * @param channel - The output channel to write to
 * @param func - The failed function result
 */
function formatFailedFunction(channel: vscode.OutputChannel, func: JsonFunctionResult): void {
  channel.appendLine(`  [FAIL] ${func.name}`);
  channel.appendLine(`    Verified: ${func.verified_count}/${func.vc_count} verification conditions`);
  channel.appendLine('');

  // Show each failure
  for (const failure of func.failures) {
    channel.appendLine(`    ${failure.vc_kind}: ${failure.description}`);

    // Show contract if available
    if (failure.contract) {
      channel.appendLine(`    Contract: ${failure.contract}`);
    }

    // Show source location if available
    if (failure.source_file && failure.source_line) {
      channel.appendLine(`    Location: ${failure.source_file}:${failure.source_line}`);
    }

    // Show counterexample if available (prefer typed v2 schema, fallback to legacy)
    const cexLines = renderCounterexampleLines(failure);
    if (cexLines.length > 0) {
      channel.appendLine('    Counterexample:');
      for (const line of cexLines) {
        channel.appendLine(`      ${line}`);
      }
    }

    // Show violated spec from v2 counterexample if present
    if (failure.counterexample_v2?.violated_spec) {
      channel.appendLine(`    Violated spec: ${failure.counterexample_v2.violated_spec}`);
    }

    // Show suggestion if available
    if (failure.suggestion) {
      channel.appendLine(`    Suggestion: ${failure.suggestion}`);
    }

    channel.appendLine('');
  }
}

/**
 * Update raw output panel with stderr and stdout from cargo verify.
 *
 * @param stderr - The stderr content (progress messages)
 * @param stdout - The stdout content (JSON output)
 */
export function updateRawOutput(stderr: string, stdout: string): void {
  if (!rawChannel) {
    throw new Error('Output channels not initialized. Call createOutputPanels() first.');
  }

  rawChannel.clear();
  rawChannel.appendLine('=== Cargo Verify Raw Output ===');
  rawChannel.appendLine('');

  // Show stderr (progress output)
  if (stderr.trim()) {
    rawChannel.appendLine('--- stderr (progress) ---');
    rawChannel.appendLine(stderr);
    rawChannel.appendLine('');
  }

  // Optionally show JSON stdout
  if (stdout.trim()) {
    rawChannel.appendLine('--- stdout (JSON) ---');
    rawChannel.appendLine(stdout);
  }
}

/**
 * Show SMT-LIB content in a new editor tab.
 *
 * Note: Current JSON schema does not include SMT-LIB content per failure.
 * This implementation reads the most recent .smt2 file from cargo verify output.
 *
 * @param crateRoot - The crate root directory
 */
export async function showSmtLib(crateRoot: string): Promise<void> {
  // Try to find .smt2 files in target/verify/ directory
  const targetDir = path.join(crateRoot, 'target', 'verify');

  try {
    // Check if target/verify exists
    if (!fs.existsSync(targetDir)) {
      vscode.window.showInformationMessage(
        'No SMT-LIB output available. Run cargo verify --verbose to generate .smt2 files.'
      );
      return;
    }

    // Find all .smt2 files
    const files = fs.readdirSync(targetDir);
    const smtFiles = files.filter((f) => f.endsWith('.smt2'));

    if (smtFiles.length === 0) {
      vscode.window.showInformationMessage(
        'No .smt2 files found. Run cargo verify --verbose to generate SMT-LIB output.'
      );
      return;
    }

    // Get the most recent .smt2 file (by mtime)
    const smtFilePaths = smtFiles.map((f) => path.join(targetDir, f));
    const mostRecent = smtFilePaths.reduce((latest, current) => {
      const latestStat = fs.statSync(latest);
      const currentStat = fs.statSync(current);
      return currentStat.mtime > latestStat.mtime ? current : latest;
    });

    // Read the SMT-LIB content
    const smtContent = fs.readFileSync(mostRecent, 'utf-8');

    // Create a virtual document with SMT-LIB content
    const doc = await vscode.workspace.openTextDocument({
      content: smtContent,
      language: 'lisp', // SMT-LIB uses Lisp syntax
    });

    // Show in a new editor tab (preview mode)
    await vscode.window.showTextDocument(doc, { preview: true });
  } catch (error) {
    vscode.window.showErrorMessage(`Failed to open SMT-LIB file: ${error}`);
  }
}
