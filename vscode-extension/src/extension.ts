import * as vscode from 'vscode';
import * as path from 'path';
import { runVerification, checkCargoVerifyInstalled, JsonVerificationReport } from './verifier';
import { convertToDiagnostics } from './diagnostics';
import { createStatusBar, showVerifying, showSuccess, showFailure, showCancelled } from './statusBar';
import { isEnabled, isAutoVerifyEnabled, getTimeout } from './config';

/**
 * Tracks the current verification state for cancellation support.
 */
interface VerificationState {
  cancelTokenSource: vscode.CancellationTokenSource;
}

let diagnosticCollection: vscode.DiagnosticCollection;
let statusBarItem: vscode.StatusBarItem;
let currentVerification: VerificationState | undefined;

export function activate(context: vscode.ExtensionContext) {
  console.log('rust-fv extension activated');

  // Create diagnostic collection for verification errors
  diagnosticCollection = vscode.languages.createDiagnosticCollection('rust-fv');
  context.subscriptions.push(diagnosticCollection);

  // Create status bar item
  statusBarItem = createStatusBar();
  context.subscriptions.push(statusBarItem);

  // Check if cargo-verify is installed on first activation
  checkCargoVerifyOnStartup(context);

  // Register on-save verification handler
  context.subscriptions.push(
    vscode.workspace.onDidSaveTextDocument(async (document) => {
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

      // Start new verification
      await startVerification(crateRoot);
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

  // Stub commands for Plan 02 implementation
  context.subscriptions.push(
    vscode.commands.registerCommand('rust-fv.showOutput', () => {
      vscode.window.showInformationMessage('Output panel coming in Plan 02');
    })
  );

  context.subscriptions.push(
    vscode.commands.registerCommand('rust-fv.toggleRawOutput', () => {
      vscode.window.showInformationMessage('Raw output toggle coming in Plan 02');
    })
  );

  context.subscriptions.push(
    vscode.commands.registerCommand('rust-fv.showSmtLib', () => {
      vscode.window.showInformationMessage('SMT-LIB viewer coming in Plan 02');
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
      'Install Instructions'
    );

    if (action === 'Install Instructions') {
      vscode.env.openExternal(vscode.Uri.parse('https://github.com/hapyy/rust-fv#installation'));
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

  // Update status bar to show verification is running
  showVerifying(statusBarItem);

  try {
    const timeout = getTimeout();
    const report = await runVerification(crateRoot, cancelTokenSource.token, timeout);

    // Convert report to diagnostics
    const diagnosticsByFile = convertToDiagnostics(report, crateRoot);

    // Clear old diagnostics
    diagnosticCollection.clear();

    // Set new diagnostics per file
    for (const [fileUriString, diagnostics] of diagnosticsByFile.entries()) {
      const fileUri = vscode.Uri.parse(fileUriString);
      diagnosticCollection.set(fileUri, diagnostics);
    }

    // Update status bar based on results
    if (report.summary.fail > 0 || report.summary.timeout > 0) {
      showFailure(statusBarItem, report.summary);
    } else {
      showSuccess(statusBarItem, report.summary);
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
