import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { getZ3Path as getZ3PathConfig } from './config';

/**
 * Cache for permission fix to avoid repeated chmod calls.
 */
let permissionsFixed = false;

/**
 * Get the path to the Z3 binary.
 *
 * First checks user configuration, then falls back to bundled binary based on platform.
 *
 * @param context - Extension context for resolving bundled paths
 * @returns Absolute path to Z3 binary
 */
export function getZ3Path(context: vscode.ExtensionContext): string {
  // Check user configuration first
  const configuredPath = getZ3PathConfig();
  if (configuredPath && configuredPath.trim() !== '') {
    return configuredPath;
  }

  // Fall back to bundled Z3 binary based on platform/arch
  const platform = process.platform;
  const arch = process.arch;

  let binaryName: string;

  if (platform === 'darwin') {
    if (arch === 'arm64') {
      binaryName = 'bin/z3-darwin-arm64';
    } else {
      binaryName = 'bin/z3-darwin-x64';
    }
  } else if (platform === 'linux') {
    binaryName = 'bin/z3-linux-x64';
  } else if (platform === 'win32') {
    binaryName = 'bin/z3-win32-x64.exe';
  } else {
    throw new Error(`Unsupported platform: ${platform}-${arch}`);
  }

  return context.asAbsolutePath(binaryName);
}

/**
 * Ensure the Z3 binary is executable.
 *
 * On Linux/macOS, sets executable permission if not already set.
 * On Windows, this is a no-op.
 *
 * @param z3Path - Path to Z3 binary
 */
export function ensureZ3Executable(z3Path: string): void {
  // Skip on Windows (no permission bits needed)
  if (process.platform === 'win32') {
    return;
  }

  // Skip if we've already fixed permissions
  if (permissionsFixed) {
    return;
  }

  try {
    const stats = fs.statSync(z3Path);
    // Check if executable bit is set (mode & 0o111 checks user/group/other execute bits)
    const isExecutable = (stats.mode & 0o111) !== 0;

    if (!isExecutable) {
      fs.chmodSync(z3Path, 0o755);
      console.log(`rust-fv: Set executable permission on ${z3Path}`);
    }

    permissionsFixed = true;
  } catch (error) {
    console.warn(`rust-fv: Failed to set executable permission on ${z3Path}:`, error);
  }
}

/**
 * Check if Z3 is available at the given path.
 *
 * @param z3Path - Path to check
 * @returns true if file exists, false otherwise
 */
export function isZ3Available(z3Path: string): boolean {
  try {
    return fs.existsSync(z3Path);
  } catch {
    return false;
  }
}
