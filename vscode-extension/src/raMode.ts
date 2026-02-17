import * as vscode from 'vscode';
import { isEnabled, isRaEnabled, isRaAutoVerifyEnabled } from './config';

/**
 * Verification mode for the rust-fv extension.
 *
 * Standalone: Extension runs cargo verify directly on save.
 * RustAnalyzer: rust-analyzer runs cargo verify via check.overrideCommand.
 * Disabled: No verification active.
 */
export enum VerificationMode {
  Standalone = 'standalone',
  RustAnalyzer = 'rust-analyzer',
  Disabled = 'disabled',
}

/**
 * Callbacks from raMode back to extension.ts to control standalone behavior.
 * This pattern avoids circular imports between raMode.ts and extension.ts.
 */
export interface RaModeCallbacks {
  enableStandaloneOnSave: () => void;
  disableStandaloneOnSave: () => void;
  clearStandaloneDiagnostics: () => void;
}

/** The cargo verify override command for rust-analyzer flycheck. */
const CARGO_VERIFY_OVERRIDE_CMD = ['cargo', 'verify', '--message-format=json'];

let currentMode: VerificationMode = VerificationMode.Standalone;

/**
 * Check if the rust-analyzer extension is installed and active.
 */
export function isRustAnalyzerAvailable(): boolean {
  const raExtension = vscode.extensions.getExtension('rust-lang.rust-analyzer');
  return raExtension !== undefined && raExtension.isActive;
}

/**
 * Detect the current verification mode based on extension availability and settings.
 */
export function detectMode(): VerificationMode {
  const standaloneEnabled = isEnabled();
  const raAvailable = isRustAnalyzerAvailable();
  const raEnabled = isRaEnabled();

  if (raAvailable && raEnabled) {
    return VerificationMode.RustAnalyzer;
  }

  if (standaloneEnabled) {
    return VerificationMode.Standalone;
  }

  return VerificationMode.Disabled;
}

/**
 * Configure rust-analyzer's check.overrideCommand to use cargo verify.
 *
 * Uses workspace-scoped configuration (not global) so it only affects
 * the current project.
 */
export async function configureOverrideCommand(): Promise<void> {
  if (!isRaAutoVerifyEnabled()) {
    return;
  }

  const raConfig = vscode.workspace.getConfiguration('rust-analyzer');
  const currentOverride = raConfig.get<string[]>('check.overrideCommand');

  // Don't overwrite if already set to cargo verify
  if (currentOverride && isCargoVerifyCommand(currentOverride)) {
    return;
  }

  await raConfig.update(
    'check.overrideCommand',
    CARGO_VERIFY_OVERRIDE_CMD,
    vscode.ConfigurationTarget.Workspace
  );
}

/**
 * Remove the cargo verify override command, restoring default cargo check behavior.
 *
 * Only resets if the current value is a cargo verify command (don't overwrite
 * user's custom overrideCommand).
 */
export async function disableOverrideCommand(): Promise<void> {
  const raConfig = vscode.workspace.getConfiguration('rust-analyzer');
  const currentOverride = raConfig.get<string[]>('check.overrideCommand');

  if (currentOverride && isCargoVerifyCommand(currentOverride)) {
    await raConfig.update(
      'check.overrideCommand',
      undefined,
      vscode.ConfigurationTarget.Workspace
    );
  }
}

/**
 * Check if a command array represents a cargo verify command.
 */
function isCargoVerifyCommand(command: string[]): boolean {
  return command.some((arg) => arg === 'verify' || arg.includes('verify'));
}

/**
 * Get the current verification mode.
 */
export function getCurrentMode(): VerificationMode {
  return currentMode;
}

/**
 * Initialize rust-analyzer mode integration.
 *
 * Detects the initial mode, configures overrideCommand if RA mode is active,
 * and registers listeners for configuration changes to dynamically switch modes.
 *
 * @param context - Extension context for disposable registration
 * @param callbacks - Callbacks to control standalone mode behavior
 */
export function initRustAnalyzerMode(
  context: vscode.ExtensionContext,
  callbacks: RaModeCallbacks
): void {
  // Detect initial mode
  currentMode = detectMode();
  console.log(`rust-fv: Initial verification mode: ${currentMode}`);

  // If RA mode: configure overrideCommand and disable standalone
  if (currentMode === VerificationMode.RustAnalyzer) {
    configureOverrideCommand();
    callbacks.disableStandaloneOnSave();
  }

  // Listen for configuration changes to dynamically switch modes
  context.subscriptions.push(
    vscode.workspace.onDidChangeConfiguration((e) => {
      if (
        e.affectsConfiguration('rust-analyzer.rustfv') ||
        e.affectsConfiguration('rust-fv.enable') ||
        e.affectsConfiguration('rust-analyzer.check.overrideCommand')
      ) {
        handleModeChange(callbacks);
      }
    })
  );

  // Listen for extension activation changes (RA may activate after us)
  context.subscriptions.push(
    vscode.extensions.onDidChange(() => {
      handleModeChange(callbacks);
    })
  );
}

/**
 * Handle a mode change due to configuration or extension state changes.
 */
function handleModeChange(callbacks: RaModeCallbacks): void {
  const previousMode = currentMode;
  currentMode = detectMode();

  if (previousMode === currentMode) {
    return; // No change
  }

  console.log(`rust-fv: Mode changed: ${previousMode} -> ${currentMode}`);

  // Transition from Standalone to RustAnalyzer
  if (previousMode === VerificationMode.Standalone && currentMode === VerificationMode.RustAnalyzer) {
    callbacks.disableStandaloneOnSave();
    callbacks.clearStandaloneDiagnostics();
    configureOverrideCommand();
    return;
  }

  // Transition from RustAnalyzer to Standalone
  if (previousMode === VerificationMode.RustAnalyzer && currentMode === VerificationMode.Standalone) {
    disableOverrideCommand();
    callbacks.enableStandaloneOnSave();
    return;
  }

  // Transition to Disabled
  if (currentMode === VerificationMode.Disabled) {
    if (previousMode === VerificationMode.RustAnalyzer) {
      disableOverrideCommand();
    }
    callbacks.disableStandaloneOnSave();
    callbacks.clearStandaloneDiagnostics();
    return;
  }

  // Transition from Disabled to active mode
  if (previousMode === VerificationMode.Disabled) {
    if (currentMode === VerificationMode.RustAnalyzer) {
      configureOverrideCommand();
    } else {
      callbacks.enableStandaloneOnSave();
    }
  }
}
