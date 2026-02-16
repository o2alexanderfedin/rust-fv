import * as vscode from 'vscode';

/**
 * Extension configuration helpers for rust-fv settings.
 */

export function getConfig(): vscode.WorkspaceConfiguration {
  return vscode.workspace.getConfiguration('rust-fv');
}

export function isEnabled(): boolean {
  return getConfig().get<boolean>('enable', true);
}

export function getTimeout(): number {
  return getConfig().get<number>('timeout', 30000);
}

export function getZ3Path(): string {
  return getConfig().get<string>('z3Path', '');
}

export function isVerbose(): boolean {
  return getConfig().get<boolean>('verbose', false);
}

export function isAutoVerifyEnabled(): boolean {
  return getConfig().get<boolean>('autoVerifyOnSave', true);
}
