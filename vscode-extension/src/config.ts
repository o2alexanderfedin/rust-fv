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

/**
 * rust-analyzer mode configuration helpers.
 *
 * These control RA-mode integration separately from standalone settings.
 */

export function getRaConfig(): vscode.WorkspaceConfiguration {
  return vscode.workspace.getConfiguration('rust-analyzer.rustfv');
}

export function isRaEnabled(): boolean {
  return getRaConfig().get<boolean>('enable', true);
}

export function isRaAutoVerifyEnabled(): boolean {
  return getRaConfig().get<boolean>('autoVerifyOnSave', true);
}
