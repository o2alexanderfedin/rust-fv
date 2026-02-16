import { spawn, ChildProcess } from 'child_process';
import * as vscode from 'vscode';

/**
 * TypeScript interfaces matching json_output.rs schema exactly.
 */

export interface JsonVerificationReport {
  crate_name: string;
  functions: JsonFunctionResult[];
  summary: JsonSummary;
}

export interface JsonFunctionResult {
  name: string;
  status: string; // "ok", "fail", "timeout"
  vc_count: number;
  verified_count: number;
  failures: JsonFailure[];
}

export interface JsonFailure {
  vc_kind: string; // "precondition", "postcondition", "overflow", etc.
  description: string;
  contract?: string;
  source_file?: string;
  source_line?: number;
  counterexample?: JsonAssignment[];
  suggestion?: string;
}

export interface JsonAssignment {
  variable: string;
  value: string;
}

export interface JsonSummary {
  total: number;
  ok: number;
  fail: number;
  timeout: number;
}

/**
 * Run cargo verify --output-format json and parse the result.
 *
 * @param crateRoot - The directory containing Cargo.toml
 * @param cancelToken - VSCode cancellation token for abort support
 * @param timeout - Verification timeout in milliseconds
 * @returns Promise resolving to JsonVerificationReport
 */
export function runVerification(
  crateRoot: string,
  cancelToken: vscode.CancellationToken,
  timeout: number
): Promise<JsonVerificationReport> {
  return new Promise((resolve, reject) => {
    const cargoVerify: ChildProcess = spawn(
      'cargo',
      ['verify', '--output-format', 'json'],
      { cwd: crateRoot }
    );

    let stdout = '';
    let stderr = '';
    let timeoutHandle: NodeJS.Timeout | undefined;

    // Accumulate stdout (JSON output)
    cargoVerify.stdout?.on('data', (chunk: Buffer) => {
      stdout += chunk.toString();
    });

    // Capture stderr separately (progress messages)
    cargoVerify.stderr?.on('data', (chunk: Buffer) => {
      stderr += chunk.toString();
    });

    // Handle process exit
    cargoVerify.on('close', (code: number | null) => {
      if (timeoutHandle) {
        clearTimeout(timeoutHandle);
      }

      // cargo verify returns non-zero on verification failures, but still outputs valid JSON
      try {
        const report: JsonVerificationReport = JSON.parse(stdout);
        resolve(report);
      } catch (e) {
        reject(new Error(`Invalid JSON output from cargo verify: ${e}\nStdout: ${stdout}\nStderr: ${stderr}`));
      }
    });

    // Handle process errors
    cargoVerify.on('error', (err: Error) => {
      if (timeoutHandle) {
        clearTimeout(timeoutHandle);
      }
      reject(new Error(`Failed to spawn cargo verify: ${err.message}`));
    });

    // Handle cancellation
    cancelToken.onCancellationRequested(() => {
      if (timeoutHandle) {
        clearTimeout(timeoutHandle);
      }
      cargoVerify.kill('SIGTERM');
      reject(new Error('Verification cancelled'));
    });

    // Handle timeout
    timeoutHandle = setTimeout(() => {
      cargoVerify.kill('SIGTERM');
      reject(new Error(`Verification timeout after ${timeout}ms`));
    }, timeout);
  });
}

/**
 * Check if cargo-verify is installed.
 *
 * @param crateRoot - The directory to run the check in
 * @returns Promise resolving to true if cargo-verify is available
 */
export function checkCargoVerifyInstalled(crateRoot: string): Promise<boolean> {
  return new Promise((resolve) => {
    const cargoVerify = spawn('cargo', ['verify', '--version'], { cwd: crateRoot });

    cargoVerify.on('close', (code: number | null) => {
      resolve(code === 0);
    });

    cargoVerify.on('error', () => {
      resolve(false);
    });
  });
}
