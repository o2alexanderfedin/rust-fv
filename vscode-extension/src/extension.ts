import * as vscode from 'vscode';

export function activate(context: vscode.ExtensionContext) {
  console.log('rust-fv extension activated');
}

export function deactivate() {
  console.log('rust-fv extension deactivated');
}
