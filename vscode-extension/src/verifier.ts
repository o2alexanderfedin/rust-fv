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
  counterexample?: JsonAssignment[];        // keep — backward compat
  counterexample_v2?: JsonCounterexample;   // new — rich schema
  suggestion?: string;
}

export interface JsonAssignment {
  variable: string;
  value: string;
}

/** Structured counterexample with typed variables and metadata (v2 schema). */
export interface JsonCounterexample {
  variables: JsonCexVariable[];
  failing_location: JsonLocation;
  vc_kind: string;
  violated_spec?: string;
  /** For async VCs: which poll iteration (0-based state_id) triggered the violation. */
  poll_iteration?: number;
  /** For async VCs: "pre_await" (suspension) or "post_await" (resumption) side. */
  await_side?: string;
}

/** A single variable in a counterexample. */
export interface JsonCexVariable {
  name: string;
  type: string;
  /** Present when variable has a single value at point of failure. */
  display?: string;
  /** Present when variable has a single value at point of failure. */
  raw?: unknown;
  /** Present when variable has an initial (parameter entry) value. */
  initial?: JsonCexValue;
  /** Present when variable has a value at point of failure distinct from initial. */
  at_failure?: JsonCexValue;
}

/** A single typed value with display string and raw JSON tree. */
export interface JsonCexValue {
  display: string;
  raw: unknown;
}

/** Source location with file, line, and column. */
export interface JsonLocation {
  file: string;
  line: number;
  column: number;
}

export interface JsonSummary {
  total: number;
  ok: number;
  fail: number;
  timeout: number;
}

/**
 * Result of running verification including both report and raw output.
 */
export interface VerificationResult {
  report: JsonVerificationReport;
  stderr: string;
  stdout: string;
}

/**
 * Run cargo verify --output-format json and parse the result.
 *
 * @param crateRoot - The directory containing Cargo.toml
 * @param cancelToken - VSCode cancellation token for abort support
 * @param timeout - Verification timeout in milliseconds
 * @param z3Path - Optional path to Z3 binary (passed via RUST_FV_Z3_PATH env var)
 * @returns Promise resolving to VerificationResult with report and raw output
 */
export function runVerification(
  crateRoot: string,
  cancelToken: vscode.CancellationToken,
  timeout: number,
  z3Path?: string
): Promise<VerificationResult> {
  return new Promise((resolve, reject) => {
    // Prepare environment with Z3 path if provided
    const env = { ...process.env };
    if (z3Path) {
      env.RUST_FV_Z3_PATH = z3Path;
    }

    const cargoVerify: ChildProcess = spawn(
      'cargo',
      ['verify', '--output-format', 'json'],
      { cwd: crateRoot, env }
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
        resolve({ report, stderr, stdout });
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
