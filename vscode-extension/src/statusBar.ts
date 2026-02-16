import * as vscode from 'vscode';
import { JsonSummary } from './verifier';

/**
 * Create a status bar item for verification progress and results.
 *
 * @returns VSCode StatusBarItem initialized but hidden
 */
export function createStatusBar(): vscode.StatusBarItem {
  const item = vscode.window.createStatusBarItem(
    vscode.StatusBarAlignment.Left,
    100
  );
  // Initially hidden until first verification starts
  return item;
}

/**
 * Show "Verifying..." with spinner animation.
 *
 * @param item - The status bar item to update
 */
export function showVerifying(item: vscode.StatusBarItem): void {
  item.text = '$(sync~spin) Verifying...';
  item.tooltip = 'Rust FV: Click to cancel verification';
  item.command = 'rust-fv.cancelVerification';
  item.backgroundColor = undefined;
  item.show();
}

/**
 * Show successful verification result.
 *
 * @param item - The status bar item to update
 * @param summary - Verification summary with counts
 */
export function showSuccess(item: vscode.StatusBarItem, summary: JsonSummary): void {
  item.text = `$(check) Verified (${summary.ok}/${summary.total})`;
  item.tooltip = 'All verification conditions proved';
  item.command = 'rust-fv.showOutput';
  item.backgroundColor = undefined;
  item.show();

  // Auto-hide after 5 seconds if all pass
  if (summary.fail === 0 && summary.timeout === 0) {
    setTimeout(() => {
      item.hide();
    }, 5000);
  }
}

/**
 * Show verification failure result.
 *
 * @param item - The status bar item to update
 * @param summary - Verification summary with failure count
 */
export function showFailure(item: vscode.StatusBarItem, summary: JsonSummary): void {
  const failureCount = summary.fail + summary.timeout;
  item.text = `$(x) Verification failed (${failureCount} failure${failureCount === 1 ? '' : 's'})`;
  item.tooltip = 'Click to see failure details';
  item.command = 'rust-fv.showOutput';
  item.backgroundColor = new vscode.ThemeColor('statusBarItem.errorBackground');
  item.show();
  // Do NOT auto-hide on failure
}

/**
 * Show cancelled verification status.
 *
 * @param item - The status bar item to update
 */
export function showCancelled(item: vscode.StatusBarItem): void {
  item.text = '$(circle-slash) Verification cancelled';
  item.tooltip = 'Verification was cancelled';
  item.command = undefined;
  item.backgroundColor = undefined;
  item.show();

  // Auto-hide after 2 seconds
  setTimeout(() => {
    item.hide();
  }, 2000);
}
