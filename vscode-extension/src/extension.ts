import * as vscode from 'vscode';
import * as path from 'path';
import { runVerification, checkCargoVerifyInstalled, JsonVerificationReport, VerificationResult } from './verifier';
import { convertToDiagnostics } from './diagnostics';
import { createStatusBar, showVerifying, showSuccess, showFailure, showCancelled } from './statusBar';
import { isEnabled, isAutoVerifyEnabled, getTimeout } from './config';
import { createOutputPanels, updateStructuredOutput, updateRawOutput, showSmtLib } from './outputPanel';
import { getZ3Path, ensureZ3Executable, isZ3Available } from './z3';
import { createVerifiedDecorationType, updateGutterDecorations, updateGutterDecorationsFromDiagnostics, clearGutterDecorations } from './gutterDecorations';
import { initRustAnalyzerMode, getCurrentMode, VerificationMode } from './raMode';

/**
 * Tracks the current verification state for cancellation support.
 */
interface VerificationState {
  cancelTokenSource: vscode.CancellationTokenSource;
}

let diagnosticCollection: vscode.DiagnosticCollection;
let statusBarItem: vscode.StatusBarItem;
let currentVerification: VerificationState | undefined;
let structuredOutputChannel: vscode.OutputChannel;
let rawOutputChannel: vscode.OutputChannel;
let lastCrateRoot: string | undefined; // For SMT-LIB command
let verifiedDecorationType: vscode.TextEditorDecorationType;
let lastVerificationReport: JsonVerificationReport | undefined;
let extensionContext: vscode.ExtensionContext;

export function activate(context: vscode.ExtensionContext) {
  console.log('rust-fv extension activated');

  // Store context for use in verification
  extensionContext = context;

  // Create diagnostic collection for verification errors
  diagnosticCollection = vscode.languages.createDiagnosticCollection('rust-fv');
  context.subscriptions.push(diagnosticCollection);

  // Create status bar item
  statusBarItem = createStatusBar();
  context.subscriptions.push(statusBarItem);

  // Create output panels
  [structuredOutputChannel, rawOutputChannel] = createOutputPanels();
  context.subscriptions.push(structuredOutputChannel);
  context.subscriptions.push(rawOutputChannel);

  // Create gutter decoration type for verified functions
  verifiedDecorationType = createVerifiedDecorationType(context);
  context.subscriptions.push(verifiedDecorationType);

  // Check Z3 availability and ensure it's executable
  checkZ3Availability(context);

  // Check if cargo-verify is installed on first activation
  checkCargoVerifyOnStartup(context);

  // --- Standalone on-save handler (can be enabled/disabled by RA mode) ---
  let onSaveDisposable: vscode.Disposable | undefined;

  function registerOnSaveHandler(): void {
    if (onSaveDisposable) {
      return; // Already registered
    }
    onSaveDisposable = vscode.workspace.onDidSaveTextDocument(async (document) => {
      if (document.languageId !== 'rust') {
        return;
      }

      // Check if verification is enabled
      if (!isEnabled() || !isAutoVerifyEnabled()) {
        return;
      }

      // Find workspace folder containing the saved file
      const workspaceFolder = vscode.workspace.getWorkspaceFolder(document.uri);
      if (!workspaceFolder) {
        return;
      }

      // Find crate root (directory containing Cargo.toml)
      const crateRoot = await findCrateRoot(document.uri, workspaceFolder.uri);
      if (!crateRoot) {
        console.warn('rust-fv: Could not find Cargo.toml for', document.uri.fsPath);
        return;
      }

      // Cancel any running verification
      if (currentVerification) {
        currentVerification.cancelTokenSource.cancel();
        currentVerification.cancelTokenSource.dispose();
        currentVerification = undefined;
      }

      // Clear gutter decorations before starting new verification
      if (vscode.window.activeTextEditor && vscode.window.activeTextEditor.document.languageId === 'rust') {
        clearGutterDecorations(vscode.window.activeTextEditor, verifiedDecorationType);
      }

      // Start new verification
      await startVerification(crateRoot);
    });
    context.subscriptions.push(onSaveDisposable);
  }

  function unregisterOnSaveHandler(): void {
    if (onSaveDisposable) {
      onSaveDisposable.dispose();
      onSaveDisposable = undefined;
    }
  }

  // --- Initialize RA mode integration ---
  initRustAnalyzerMode(context, {
    enableStandaloneOnSave: registerOnSaveHandler,
    disableStandaloneOnSave: unregisterOnSaveHandler,
    clearStandaloneDiagnostics: () => diagnosticCollection.clear(),
  });

  // Only register standalone on-save if not in RA mode
  if (getCurrentMode() !== VerificationMode.RustAnalyzer) {
    registerOnSaveHandler();
  }

  // --- Listen for diagnostic changes to update gutter decorations in RA mode ---
  context.subscriptions.push(
    vscode.languages.onDidChangeDiagnostics((e) => {
      if (getCurrentMode() !== VerificationMode.RustAnalyzer) {
        return;
      }

      const editor = vscode.window.activeTextEditor;
      if (!editor || editor.document.languageId !== 'rust') {
        return;
      }

      // Check if any changed URIs match the active editor
      const activeUri = editor.document.uri.toString();
      const relevant = e.uris.some((uri) => uri.toString() === activeUri);
      if (!relevant) {
        return;
      }

      // Get all diagnostics for this file and filter to rust-fv
      const allDiags = vscode.languages.getDiagnostics(editor.document.uri);
      const rustfvDiags = allDiags.filter((d) => d.source === 'rust-fv');

      // Update gutter decorations from RA diagnostic changes
      updateGutterDecorationsFromDiagnostics(editor, rustfvDiags, verifiedDecorationType);

      // Update status bar based on RA-mode diagnostics
      updateStatusBarFromDiagnostics(rustfvDiags);
    })
  );

  // Register editor change listener to reapply decorations
  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      if (!editor || editor.document.languageId !== 'rust') {
        return;
      }

      if (getCurrentMode() === VerificationMode.RustAnalyzer) {
        // In RA mode: update from current diagnostics
        const allDiags = vscode.languages.getDiagnostics(editor.document.uri);
        const rustfvDiags = allDiags.filter((d) => d.source === 'rust-fv');
        updateGutterDecorationsFromDiagnostics(editor, rustfvDiags, verifiedDecorationType);
      } else if (lastVerificationReport) {
        // In standalone mode: update from last report
        updateGutterDecorations(editor, lastVerificationReport, verifiedDecorationType);
      }
    })
  );

  // Register commands
  context.subscriptions.push(
    vscode.commands.registerCommand('rust-fv.cancelVerification', () => {
      if (currentVerification) {
        currentVerification.cancelTokenSource.cancel();
        currentVerification.cancelTokenSource.dispose();
        currentVerification = undefined;
        showCancelled(statusBarItem);
      }
    })
  );

  // Output panel commands
  context.subscriptions.push(
    vscode.commands.registerCommand('rust-fv.showOutput', () => {
      structuredOutputChannel.show(true);
    })
  );

  context.subscriptions.push(
    vscode.commands.registerCommand('rust-fv.toggleRawOutput', () => {
      rawOutputChannel.show(true);
    })
  );

  context.subscriptions.push(
    vscode.commands.registerCommand('rust-fv.showSmtLib', async () => {
      if (!lastCrateRoot) {
        vscode.window.showInformationMessage('No verification run yet. Save a Rust file to trigger verification.');
        return;
      }
      await showSmtLib(lastCrateRoot);
    })
  );
}

export function deactivate() {
  console.log('rust-fv extension deactivated');

  // Cancel any running verification
  if (currentVerification) {
    currentVerification.cancelTokenSource.cancel();
    currentVerification.cancelTokenSource.dispose();
    currentVerification = undefined;
  }

  // Dispose status bar
  if (statusBarItem) {
    statusBarItem.dispose();
  }

  // Note: We intentionally leave rust-analyzer.check.overrideCommand in place
  // on deactivation. Removing it would be surprising since the user explicitly
  // enabled it. It only gets removed when the user disables via setting.
}

/**
 * Update status bar based on rust-fv diagnostics in RA mode.
 *
 * In RA mode, we don't have a JsonVerificationReport -- we infer status
 * from the diagnostic collection that rust-analyzer publishes.
 *
 * @param rustfvDiagnostics - Diagnostics filtered to source 'rust-fv'
 */
function updateStatusBarFromDiagnostics(rustfvDiagnostics: vscode.Diagnostic[]): void {
  const failureCount = rustfvDiagnostics.filter(
    (d) => d.severity === vscode.DiagnosticSeverity.Error
  ).length;

  if (failureCount === 0) {
    statusBarItem.text = '$(check) Verified (RA mode)';
    statusBarItem.tooltip = 'rust-analyzer: All verification conditions proved';
    statusBarItem.command = 'rust-fv.showOutput';
    statusBarItem.backgroundColor = undefined;
    statusBarItem.show();

    // Auto-hide after 5 seconds
    setTimeout(() => {
      statusBarItem.hide();
    }, 5000);
  } else {
    statusBarItem.text = `$(x) ${failureCount} verification failure${failureCount === 1 ? '' : 's'} (RA mode)`;
    statusBarItem.tooltip = 'rust-analyzer: Click to see failure details';
    statusBarItem.command = 'rust-fv.showOutput';
    statusBarItem.backgroundColor = new vscode.ThemeColor('statusBarItem.errorBackground');
    statusBarItem.show();
  }
}

/**
 * Check if Z3 is available and warn if not.
 */
function checkZ3Availability(context: vscode.ExtensionContext): void {
  const z3Path = getZ3Path(context);

  if (!isZ3Available(z3Path)) {
    // Z3 not found - this can happen in dev mode or if download-z3.sh wasn't run
    const configuredPath = vscode.workspace.getConfiguration('rust-fv').get<string>('z3Path');

    if (configuredPath && configuredPath.trim() !== '') {
      // User configured a path, but it doesn't exist
      vscode.window.showWarningMessage(
        `Z3 not found at configured path: ${z3Path}. Please check rust-fv.z3Path setting.`
      );
    } else {
      // No bundled Z3 (likely dev mode)
      console.warn('rust-fv: Z3 binary not bundled. Set rust-fv.z3Path or run scripts/download-z3.sh');
    }
  } else {
    // Z3 exists - ensure it's executable
    ensureZ3Executable(z3Path);
  }
}

/**
 * Check if cargo-verify is installed and prompt user to install if missing.
 */
async function checkCargoVerifyOnStartup(context: vscode.ExtensionContext) {
  // Only check once per session
  const checkedKey = 'rust-fv.cargoVerifyChecked';
  if (context.globalState.get(checkedKey)) {
    return;
  }

  // Find a workspace folder with a Cargo.toml to run the check
  const workspaceFolders = vscode.workspace.workspaceFolders;
  if (!workspaceFolders || workspaceFolders.length === 0) {
    return;
  }

  const firstWorkspace = workspaceFolders[0].uri.fsPath;
  const installed = await checkCargoVerifyInstalled(firstWorkspace);

  if (!installed) {
    const action = await vscode.window.showWarningMessage(
      'cargo-verify is not installed. The Rust FV extension requires cargo-verify to function.',
      'Install via Cargo',
      'Dismiss'
    );

    if (action === 'Install via Cargo') {
      const terminal = vscode.window.createTerminal('Rust FV Setup');
      terminal.show();
      terminal.sendText('cargo install --path crates/driver && echo "cargo-verify installed successfully!"');
    }
  }

  // Mark as checked
  context.globalState.update(checkedKey, true);
}

/**
 * Find the crate root (directory containing Cargo.toml) for a given file.
 *
 * @param fileUri - The URI of the file being verified
 * @param workspaceUri - The workspace folder URI
 * @returns The crate root path, or undefined if not found
 */
async function findCrateRoot(
  fileUri: vscode.Uri,
  workspaceUri: vscode.Uri
): Promise<string | undefined> {
  let currentDir = path.dirname(fileUri.fsPath);
  const workspaceRoot = workspaceUri.fsPath;

  // Walk up directory tree looking for Cargo.toml
  while (currentDir.startsWith(workspaceRoot)) {
    const cargoToml = path.join(currentDir, 'Cargo.toml');
    try {
      await vscode.workspace.fs.stat(vscode.Uri.file(cargoToml));
      return currentDir; // Found Cargo.toml
    } catch {
      // Not found, go up one level
      const parentDir = path.dirname(currentDir);
      if (parentDir === currentDir) {
        break; // Reached root
      }
      currentDir = parentDir;
    }
  }

  return undefined;
}

/**
 * Start a new verification run.
 *
 * @param crateRoot - The directory containing Cargo.toml
 */
async function startVerification(crateRoot: string): Promise<void> {
  const cancelTokenSource = new vscode.CancellationTokenSource();
  currentVerification = { cancelTokenSource };

  // Store crate root for SMT-LIB command
  lastCrateRoot = crateRoot;

  // Update status bar to show verification is running
  showVerifying(statusBarItem);

  try {
    const timeout = getTimeout();

    // Get Z3 path to pass to cargo verify
    let z3Path: string | undefined;
    const resolvedPath = getZ3Path(extensionContext);
    if (isZ3Available(resolvedPath)) {
      z3Path = resolvedPath;
    }

    const result: VerificationResult = await runVerification(crateRoot, cancelTokenSource.token, timeout, z3Path);

    // Convert report to diagnostics
    const diagnosticsByFile = convertToDiagnostics(result.report, crateRoot);

    // Clear old diagnostics
    diagnosticCollection.clear();

    // Set new diagnostics per file
    for (const [fileUriString, diagnostics] of diagnosticsByFile.entries()) {
      const fileUri = vscode.Uri.parse(fileUriString);
      diagnosticCollection.set(fileUri, diagnostics);
    }

    // Update output panels
    updateStructuredOutput(result.report);
    updateRawOutput(result.stderr, result.stdout);

    // Store last verification report for gutter decorations
    lastVerificationReport = result.report;

    // Update gutter decorations for verified functions
    const activeEditor = vscode.window.activeTextEditor;
    if (activeEditor && activeEditor.document.languageId === 'rust') {
      updateGutterDecorations(activeEditor, result.report, verifiedDecorationType);
    }

    // Update status bar based on results
    if (result.report.summary.fail > 0 || result.report.summary.timeout > 0) {
      showFailure(statusBarItem, result.report.summary);
    } else {
      showSuccess(statusBarItem, result.report.summary);
    }
  } catch (error) {
    if (error instanceof Error) {
      if (error.message === 'Verification cancelled') {
        // User cancelled - status bar already updated by command handler
        return;
      }

      if (error.message.includes('Failed to spawn cargo verify')) {
        // cargo-verify not found
        vscode.window.showErrorMessage(
          'cargo-verify command not found. Please install cargo-verify to use this extension.'
        );
        statusBarItem.hide();
        return;
      }

      // Other errors (timeout, invalid JSON, etc.)
      vscode.window.showErrorMessage(`Verification failed: ${error.message}`);
      statusBarItem.hide();
    }
  } finally {
    // Clean up current verification state
    if (currentVerification && currentVerification.cancelTokenSource === cancelTokenSource) {
      cancelTokenSource.dispose();
      currentVerification = undefined;
    }
  }
}
