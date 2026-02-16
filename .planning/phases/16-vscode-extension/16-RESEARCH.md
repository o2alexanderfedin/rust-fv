# Phase 16: VSCode Extension - Research

**Researched:** 2026-02-16
**Domain:** VSCode extension development for Rust formal verification tooling
**Confidence:** HIGH

## Summary

VSCode extensions for language tooling integrate via the VS Code Extension API without requiring a full Language Server Protocol implementation. The standard architecture uses TypeScript with esbuild bundling, direct Diagnostic API integration, and platform-specific VSIX packages for distributing native binaries. The rust-analyzer extension provides the canonical example of "check-on-save" patterns with cancel-and-restart semantics and structured diagnostics rendering.

This phase implements a standalone VSCode extension (separate from Phase 17's rust-analyzer integration) that runs `cargo verify --output-format json` on save, parses the JSON output, creates VSCode diagnostics with related information pointing to code paths, displays status indicators during verification, and provides structured output panels. Z3 can be bundled platform-specifically using the vsce --target flag for zero-config installation.

**Primary recommendation:** Use the VSCode Diagnostic API directly (not full LSP) with workspace.onDidSaveTextDocument triggering cargo verify, CancellationTokenSource for cancel-on-new-save, DecorationRenderOptions for gutter icons, and platform-specific VSIX packaging with bundled Z3 binaries.

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

**Diagnostic Presentation:**
- Verification failures appear as Error severity (red squiggles) — same level as rustc errors
- Hover tooltip shows failure message + counterexample values inline
- Primary diagnostic on the contract annotation (#[ensures], #[requires]), with related information pointing to the specific code path causing the violation
- Verified functions get green checkmark gutter indicators — positive reinforcement that specs hold

**Verification Triggering:**
- Runs on save — consistent with rust-analyzer's check-on-save pattern
- If verification is running and user saves again: cancel current run and restart with latest changes

**Output & Detail Levels:**
- Output panel shows structured failure report by default with toggle to see raw cargo verify output
- SMT-LIB access via "Show SMT-LIB" command in palette — opens in a new editor tab
- Per-function timing shown only when slow (>1s)
- Counterexamples formatted as symbolic + concrete

**Extension Packaging:**
- Bundle Z3 with the extension VSIX — zero-config for users
- First launch without cargo-verify: auto-install prompt notification with "Install" button
- Published to both VSCode Marketplace AND .vsix download
- Configuration settings: enable/disable toggle, verification timeout, Z3 path override, verbose mode, auto-verify on save toggle

### Claude's Discretion

- Background process vs fresh spawn per save (pick what works best with incremental cache)
- Whole crate vs changed-file-only verification scope
- Green checkmark gutter icon design and implementation
- Exact structured output format in the panel
- Extension activation events and language server protocol details

### Deferred Ideas (OUT OF SCOPE)

None — discussion stayed within phase scope

</user_constraints>

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|------------------|
| IDE-01 | VSCode extension shows inline error highlighting (red squiggles) for verification failures | vscode.languages.createDiagnosticCollection API with DiagnosticSeverity.Error |
| IDE-02 | VSCode extension shows "Verifying..." status bar indicator with progress | window.createStatusBarItem with loading icon + window.withProgress for cancellation |
| IDE-03 | VSCode extension provides output panel with detailed VC failures and SMT-LIB | window.createOutputChannel for structured output + workspace.openTextDocument for SMT-LIB |
| IDE-06 | VSCode extension published to marketplace with configuration (enable/disable, timeout, Z3 path) | contributes.configuration in package.json + vsce package --target for platform-specific builds |

</phase_requirements>

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| TypeScript | 5.x+ | Extension implementation | VSCode extensions are TypeScript-first; type safety for API contracts |
| @types/vscode | 1.85+ | VSCode API type definitions | Official type definitions from Microsoft; always matches API version |
| esbuild | 0.19+ | Bundle extension code | 50-100x faster than webpack; official VSCode docs recommend for 2026 |
| @vscode/test-cli | latest | Extension testing framework | Official testing tool; runs Mocha tests in Extension Development Host |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| vsce | 2.9.1+ | Package and publish extensions | Required for marketplace publishing and VSIX creation |
| @vscode/vsce-sign-* | platform | Sign platform-specific packages | Marketplace distribution of native binaries (Z3) |
| colored | n/a (Rust) | Terminal output formatting | Already used in cargo-verify for colored output |
| serde/serde_json | n/a (Rust) | JSON serialization | Already used in json_output.rs for structured diagnostics |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| Direct VSCode API | Language Server Protocol | LSP adds ~1000 LOC overhead and process isolation when we only need diagnostics + commands |
| esbuild | webpack | webpack is slower (3-5s vs 100-300ms builds) but has richer ecosystem; esbuild sufficient here |
| Platform-specific VSIX | Universal VSIX with postinstall script | Postinstall requires network + permissions; bundled binaries are zero-config |

**Installation:**
```bash
npm install --save-dev @types/vscode @vscode/test-cli esbuild
npm install --save-dev @vscode/vsce
```

## Architecture Patterns

### Recommended Project Structure
```
vscode-extension/
├── src/
│   ├── extension.ts       # activate() and deactivate() entry points
│   ├── verifier.ts        # Spawn cargo verify, parse JSON output
│   ├── diagnostics.ts     # Convert JSON failures to VSCode Diagnostics
│   ├── statusBar.ts       # Status indicator management
│   ├── outputPanel.ts     # Structured failure report view
│   └── config.ts          # Extension configuration helpers
├── bin/                   # Platform-specific Z3 binaries (git-ignored, copied at build)
│   ├── z3-darwin-x64      # macOS Intel
│   ├── z3-darwin-arm64    # macOS Apple Silicon
│   ├── z3-linux-x64       # Linux x64
│   └── z3-win32-x64.exe   # Windows x64
├── package.json           # Extension manifest with contributes.configuration
├── tsconfig.json          # TypeScript compiler options
├── esbuild.js             # Bundle script
└── .vscodeignore          # Exclude src/, include dist/ in VSIX
```

### Pattern 1: On-Save Verification with Cancellation
**What:** Register save listener, spawn cargo verify as child process, cancel if new save occurs
**When to use:** User saves frequently; incremental cache makes whole-crate verification fast (<1s)
**Example:**
```typescript
// Source: VSCode API + rust-analyzer pattern
import * as vscode from 'vscode';
import { spawn } from 'child_process';

let currentVerification: { process: ChildProcess; cancel: vscode.CancellationTokenSource } | undefined;

export function activate(context: vscode.ExtensionContext) {
  const diagnosticCollection = vscode.languages.createDiagnosticCollection('rust-fv');
  context.subscriptions.push(diagnosticCollection);

  context.subscriptions.push(
    vscode.workspace.onDidSaveTextDocument(async (document) => {
      if (document.languageId !== 'rust') return;

      // Cancel any running verification
      if (currentVerification) {
        currentVerification.cancel.cancel();
        currentVerification.process.kill();
      }

      const cancelToken = new vscode.CancellationTokenSource();
      const cargoVerify = spawn('cargo', ['verify', '--output-format', 'json'], {
        cwd: vscode.workspace.getWorkspaceFolder(document.uri)?.uri.fsPath,
      });

      currentVerification = { process: cargoVerify, cancel: cancelToken };

      // Parse JSON output and update diagnostics...
    })
  );
}
```

### Pattern 2: JSON Output Parsing and Diagnostic Conversion
**What:** Read cargo verify JSON from stdout, map to VSCode Diagnostic with related information
**When to use:** cargo verify emits JsonVerificationReport to stdout with failures array
**Example:**
```typescript
// Source: Existing json_output.rs schema
interface JsonVerificationReport {
  crate_name: string;
  functions: JsonFunctionResult[];
  summary: JsonSummary;
}

interface JsonFailure {
  vc_kind: string; // "precondition", "postcondition", "overflow"
  description: string;
  contract?: string;
  source_file?: string;
  source_line?: number;
  counterexample?: JsonAssignment[];
  suggestion?: string;
}

function convertToDiagnostic(failure: JsonFailure, uri: vscode.Uri): vscode.Diagnostic {
  const line = (failure.source_line ?? 1) - 1; // 0-indexed
  const range = new vscode.Range(line, 0, line, 100);

  const diagnostic = new vscode.Diagnostic(
    range,
    failure.description,
    vscode.DiagnosticSeverity.Error
  );

  // Add counterexample to hover message
  if (failure.counterexample) {
    diagnostic.message += `\nCounterexample: ${formatCounterexample(failure.counterexample)}`;
  }

  // Add related information for code path (if available)
  // Note: Current JSON schema doesn't include code path locations yet
  // Future enhancement: add related_locations array to JsonFailure

  return diagnostic;
}
```

### Pattern 3: Status Bar with Progress and Cancellation
**What:** Show "Verifying..." with spinner during verification, clickable to cancel
**When to use:** Verification takes >500ms; user needs feedback and control
**Example:**
```typescript
// Source: VSCode status bar guidelines
const statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left);
statusBarItem.text = "$(sync~spin) Verifying...";
statusBarItem.tooltip = "Click to cancel verification";
statusBarItem.command = "rust-fv.cancelVerification";
statusBarItem.show();

// Later, on completion:
statusBarItem.text = "$(check) Verified";
setTimeout(() => statusBarItem.hide(), 2000); // Auto-hide after 2s
```

### Pattern 4: Gutter Decorations for Verified Functions
**What:** Green checkmark icon in gutter for functions that verified successfully
**When to use:** Provide positive reinforcement; show verification coverage at a glance
**Example:**
```typescript
// Source: VSCode DecorationRenderOptions API
const verifiedDecorationType = vscode.window.createTextEditorDecorationType({
  gutterIconPath: vscode.Uri.file(context.asAbsolutePath('resources/verified.svg')),
  gutterIconSize: 'contain',
});

// Apply to lines with verified function annotations
editor.setDecorations(verifiedDecorationType, [
  new vscode.Range(lineNumber, 0, lineNumber, 0)
]);
```

### Pattern 5: Platform-Specific Binary Bundling
**What:** Include Z3 binary in VSIX per platform; detect and use correct binary at runtime
**When to use:** Zero-config installation; avoid user-managed dependencies
**Example:**
```typescript
// Source: vscode-platform-specific-sample
// package.json excerpt:
// Build script creates separate VSIX per platform:
// vsce package --target darwin-x64
// vsce package --target darwin-arm64
// vsce package --target linux-x64
// vsce package --target win32-x64

function getZ3Path(context: vscode.ExtensionContext): string {
  const platform = process.platform;
  const arch = process.arch;

  let binaryName = 'z3';
  if (platform === 'darwin') {
    binaryName = arch === 'arm64' ? 'z3-darwin-arm64' : 'z3-darwin-x64';
  } else if (platform === 'linux') {
    binaryName = 'z3-linux-x64';
  } else if (platform === 'win32') {
    binaryName = 'z3-win32-x64.exe';
  }

  return context.asAbsolutePath(`bin/${binaryName}`);
}
```

### Anti-Patterns to Avoid
- **Blocking activation:** Don't run verification during activate(); use onStartupFinished or first save event
- **No cancellation:** User saves → old verification keeps running → results overwrite new run → stale diagnostics
- **Ignoring working directory:** spawn() without cwd option runs from extension root, not workspace folder
- **Unbundled extension:** Leaving src/ and node_modules/ in VSIX bloats package and slows cold activation
- **Global diagnostics:** Creating diagnostics for all files upfront; lazy-create on verification run only

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Extension bundling | Custom webpack config, manual file copying | esbuild with official sample | VSCode team maintains esbuild config; handles externals (vscode module) correctly |
| Extension testing | Custom test runner with headless VSCode | @vscode/test-cli | Handles VSCode download, version management, Mocha integration, Extension Development Host setup |
| Marketplace publishing | Manual VSIX upload, platform detection | vsce package --target | Handles Azure DevOps auth, platform naming, signing, pre-publish validation |
| JSON parsing with validation | Manual JSON.parse + runtime checks | Runtime validation with Zod or io-ts | JSON from cargo verify is untrusted; schema could change; validated parsing catches mismatches early |
| Process lifecycle management | Manual spawn + signal handling | Node.js child_process with AbortController | Handles platform differences (SIGTERM vs taskkill), cleanup on extension deactivate, zombie prevention |

**Key insight:** VSCode extension development has sharp edges around activation performance, platform compatibility, and marketplace distribution. Official tooling (vsce, @vscode/test-cli, esbuild sample) encodes years of learned patterns; custom solutions reintroduce solved problems.

## Common Pitfalls

### Pitfall 1: Extension Activation Performance
**What goes wrong:** Extension activates on startup, runs expensive initialization, slows VSCode launch by 500ms-2s
**Why it happens:** Default activation event is `*` (all files); sync file reads during activate(); bundled extension is >1MB with node_modules
**How to avoid:**
- Use specific activation events: `onLanguage:rust`, `workspaceContains:Cargo.toml`
- Move expensive work to first command invocation or onStartupFinished
- Bundle with esbuild (tree-shaking reduces 5MB node_modules to 200KB dist/)
- Lazy-load heavy modules (don't import unused features)
**Warning signs:** "Extension activation took >500ms" in Extension Host log; users report slow startup

### Pitfall 2: Diagnostic Lifecycle Management
**What goes wrong:** Diagnostics persist after file edits, or clear on unrelated file saves, or duplicate on re-verification
**Why it happens:** DiagnosticCollection.set() replaces ALL diagnostics for a URI; clearing without tracking active files removes all diagnostics
**How to avoid:**
- Track which files have active verification diagnostics (Map<Uri, Diagnostic[]>)
- Clear diagnostics only for files being re-verified: `diagnosticCollection.delete(uri)`
- Don't call `diagnosticCollection.clear()` unless closing workspace or disabling extension
- On file edit (onDidChangeTextDocument), mark diagnostics as stale but don't clear (user needs to see them until re-verification)
**Warning signs:** Diagnostics disappear when editing unrelated files; red squiggles persist after fixing code and saving

### Pitfall 3: Child Process Cleanup on Deactivate
**What goes wrong:** Extension deactivates (reload window, disable extension), cargo verify keeps running, uses CPU, holds file locks
**Why it happens:** VSCode gives extensions ~1s to deactivate; async cleanup often doesn't complete; no kill() on spawned processes
**How to avoid:**
- Store all spawned processes in context.subscriptions as Disposable wrappers
- In deactivate(), explicitly kill all running processes with SIGTERM (Linux/macOS) or taskkill /T (Windows)
- Use AbortSignal with child_process.spawn for automatic cleanup
- Test deactivation: Disable extension → check Task Manager / Activity Monitor for stray cargo/Z3 processes
**Warning signs:** cargo verify appears in process list after disabling extension; file locks prevent git checkout

### Pitfall 4: Platform-Specific Binary Permissions
**What goes wrong:** Z3 binary bundled in VSIX, extension loads, spawn() fails with EACCES (permission denied)
**Why it happens:** VSIX is a ZIP; unpacking loses executable permission bit on Linux/macOS; Windows doesn't use permission bits but may block downloaded executables
**How to avoid:**
- Linux/macOS: Run fs.chmodSync(z3Path, 0o755) on first use (cache flag to avoid repeated chmod)
- Windows: Mark Z3 binary as "unblocked" (Alternate Data Stream); better: sign binary or accept SmartScreen warnings
- Test on all platforms: CI should run extension tests on Windows, macOS Intel, macOS ARM, Linux
**Warning signs:** spawn EACCES error in Extension Host log; "command not found" on Linux; SmartScreen blocks on Windows

### Pitfall 5: Relative vs Absolute Paths in Diagnostics
**What goes wrong:** cargo verify emits source_file: "src/lib.rs", extension creates diagnostic for cwd/src/lib.rs, but file is actually workspace/crate/src/lib.rs
**Why it happens:** cargo verify runs in crate directory (where Cargo.toml lives), but VSCode workspace root might be parent directory with multiple crates
**How to avoid:**
- Always resolve source_file paths relative to the crate root (where cargo verify ran), not workspace root
- Use vscode.Uri.file(path.resolve(crateRoot, failure.source_file)) to get absolute URI
- Store crate root per verification run (don't assume single workspace folder)
**Warning signs:** Diagnostics appear in wrong files; "file not found" when clicking diagnostic; red squiggles in unrelated files

### Pitfall 6: Cargo Verify Not Installed
**What goes wrong:** Extension activates, user saves Rust file, spawn('cargo', ['verify']) fails with ENOENT (command not found)
**Why it happens:** cargo-verify is a separate installation (not bundled with rustc); users may have Rust but not cargo-verify
**How to avoid:**
- On first verification attempt, check if cargo verify exists: `spawn('cargo', ['verify', '--version'])`
- If not found, show vscode.window.showWarningMessage with "Install cargo-verify" button
- Button triggers terminal.sendText('cargo install --path .') or opens installation docs
- Cache "cargo-verify installed" flag to avoid repeated checks
**Warning signs:** "cargo: unknown subcommand 'verify'" in output panel; silent failure with no diagnostics

### Pitfall 7: JSON Output Mixed with Stderr Progress
**What goes wrong:** cargo verify emits JSON to stdout but also prints "[OK] function_name" to stderr; JSON.parse fails with "Unexpected token ["
**Why it happens:** Existing output.rs writes colored progress to stderr, but json_output.rs writes to stdout; extension reads stdout only; buffer might contain partial JSON
**How to avoid:**
- When spawning cargo verify with --output-format json, ONLY parse stdout (ignore stderr)
- Accumulate stdout chunks until process exits (don't parse line-by-line; JSON is pretty-printed across lines)
- On exit, parse full stdout as JSON: `JSON.parse(stdoutBuffer.join(''))`
- Handle parse errors gracefully: log raw stdout to output channel, show "verification output malformed" diagnostic
**Warning signs:** JSON.parse throws SyntaxError; extension shows "verification failed" but cargo verify actually succeeded

## Code Examples

Verified patterns from official sources:

### Diagnostic Creation with Related Information
```typescript
// Source: vscode-extension-samples/diagnostic-related-information-sample
// https://github.com/microsoft/vscode-extension-samples/blob/main/diagnostic-related-information-sample/src/extension.ts

import * as vscode from 'vscode';

function createDiagnosticWithRelatedInfo(
  contractLine: number,
  codePathLine: number,
  uri: vscode.Uri,
  message: string
): vscode.Diagnostic {
  const contractRange = new vscode.Range(contractLine, 0, contractLine, 100);
  const diagnostic = new vscode.Diagnostic(
    contractRange,
    message,
    vscode.DiagnosticSeverity.Error
  );

  // Related information points to code path causing violation
  diagnostic.relatedInformation = [
    new vscode.DiagnosticRelatedInformation(
      new vscode.Location(uri, new vscode.Range(codePathLine, 0, codePathLine, 100)),
      'Verification fails through this execution path'
    )
  ];

  diagnostic.source = 'rust-fv';
  return diagnostic;
}
```

### Status Bar with Progress and Cancellation
```typescript
// Source: VSCode Status Bar UX guidelines
// https://code.visualstudio.com/api/ux-guidelines/status-bar

const statusBarItem = vscode.window.createStatusBarItem(
  vscode.StatusBarAlignment.Left,
  100 // Priority (higher = further left)
);

// During verification
statusBarItem.text = "$(sync~spin) Verifying...";
statusBarItem.tooltip = "Click to cancel verification";
statusBarItem.command = "rust-fv.cancelVerification";
statusBarItem.show();

// On completion (success)
statusBarItem.text = "$(check) Verified";
statusBarItem.backgroundColor = undefined; // Default background
setTimeout(() => statusBarItem.hide(), 2000);

// On completion (failure)
statusBarItem.text = "$(x) Verification failed";
statusBarItem.backgroundColor = new vscode.ThemeColor('statusBarItem.errorBackground');
statusBarItem.command = "rust-fv.showOutput";
statusBarItem.tooltip = "Click to see failure details";
// Don't auto-hide on failure; user needs to see it
```

### Output Channel with Toggle
```typescript
// Source: VSCode Common Capabilities
// https://code.visualstudio.com/api/extension-capabilities/common-capabilities

const structuredOutput = vscode.window.createOutputChannel("Rust FV: Failures");
const rawOutput = vscode.window.createOutputChannel("Rust FV: Raw Output");

function showStructuredFailures(report: JsonVerificationReport) {
  structuredOutput.clear();
  for (const func of report.functions) {
    if (func.status !== 'ok') {
      structuredOutput.appendLine(`❌ ${func.name}`);
      for (const failure of func.failures) {
        structuredOutput.appendLine(`   ${failure.vc_kind}: ${failure.description}`);
        if (failure.counterexample) {
          structuredOutput.appendLine(`   Counterexample:`);
          for (const assign of failure.counterexample) {
            structuredOutput.appendLine(`     ${assign.variable} = ${assign.value}`);
          }
        }
      }
    }
  }
  structuredOutput.show(true); // preserveFocus = true
}

// Command to toggle between structured and raw
vscode.commands.registerCommand('rust-fv.toggleRawOutput', () => {
  if (structuredOutput.visible) {
    rawOutput.show(true);
  } else {
    structuredOutput.show(true);
  }
});
```

### Spawning Cargo Verify with Cancellation
```typescript
// Source: Node.js child_process + VSCode CancellationToken pattern
// https://nodejs.org/api/child_process.html
// https://johnwargo.com/posts/2023/vscode-extension-progress/

import { spawn } from 'child_process';
import * as vscode from 'vscode';

async function runVerification(
  crateRoot: string,
  cancelToken: vscode.CancellationToken
): Promise<JsonVerificationReport> {
  return new Promise((resolve, reject) => {
    const cargoVerify = spawn(
      'cargo',
      ['verify', '--output-format', 'json'],
      { cwd: crateRoot }
    );

    let stdout = '';
    let stderr = '';

    cargoVerify.stdout.on('data', (chunk) => {
      stdout += chunk.toString();
    });

    cargoVerify.stderr.on('data', (chunk) => {
      stderr += chunk.toString();
      // Optionally stream progress to output channel
    });

    cargoVerify.on('close', (code) => {
      if (code === 0) {
        try {
          const report = JSON.parse(stdout);
          resolve(report);
        } catch (e) {
          reject(new Error(`Invalid JSON output: ${e.message}`));
        }
      } else {
        reject(new Error(`cargo verify exited with code ${code}\n${stderr}`));
      }
    });

    // Cancellation handler
    cancelToken.onCancellationRequested(() => {
      cargoVerify.kill('SIGTERM');
      reject(new Error('Verification cancelled'));
    });
  });
}
```

### Platform-Specific VSIX Packaging
```bash
# Source: VSCode Publishing Extensions guide
# https://code.visualstudio.com/api/working-with-extensions/publishing-extension

# Build script (package.sh)
#!/bin/bash

# Supported platforms for VSCode extensions:
# darwin-x64, darwin-arm64, linux-x64, linux-arm64, win32-x64, win32-arm64

# Copy Z3 binaries to bin/ (fetched separately)
mkdir -p bin
cp ~/z3-builds/z3-macos-intel bin/z3-darwin-x64
cp ~/z3-builds/z3-macos-arm bin/z3-darwin-arm64
cp ~/z3-builds/z3-linux bin/z3-linux-x64
cp ~/z3-builds/z3-windows.exe bin/z3-win32-x64.exe

# Make binaries executable
chmod +x bin/z3-darwin-x64 bin/z3-darwin-arm64 bin/z3-linux-x64

# Bundle TypeScript source with esbuild
npm run build

# Package per platform
vsce package --target darwin-x64
vsce package --target darwin-arm64
vsce package --target linux-x64
vsce package --target win32-x64

# Publish to marketplace
vsce publish --target darwin-x64
vsce publish --target darwin-arm64
vsce publish --target linux-x64
vsce publish --target win32-x64
```

### esbuild Configuration
```javascript
// Source: VSCode Bundling Extensions guide + esbuild-sample
// https://code.visualstudio.com/api/working-with-extensions/bundling-extension
// https://github.com/microsoft/vscode-extension-samples/tree/main/esbuild-sample

const esbuild = require('esbuild');

const production = process.argv.includes('--production');
const watch = process.argv.includes('--watch');

async function main() {
  const ctx = await esbuild.context({
    entryPoints: ['src/extension.ts'],
    bundle: true,
    format: 'cjs',
    minify: production,
    sourcemap: !production,
    sourcesContent: false,
    platform: 'node',
    outfile: 'dist/extension.js',
    external: ['vscode'], // vscode module is provided by runtime
    logLevel: 'silent',
    plugins: [
      /* Optionally add plugins for progress reporting */
    ],
  });

  if (watch) {
    await ctx.watch();
  } else {
    await ctx.rebuild();
    await ctx.dispose();
  }
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| webpack bundling | esbuild | ~2023 (VSCode 1.75+) | 10-50x faster builds; official samples migrated to esbuild |
| activationEvents: "*" | onLanguage:rust, onStartupFinished | 2021 (VSCode 1.56) | Extensions no longer slow startup unless workspace uses language |
| Manual VSIX per platform | vsce package --target | 2021 (vsce 2.0) | Single command creates platform-specific packages with correct naming |
| AbortController (JS) | CancellationTokenSource (VSCode) | Always separate | VSCode uses C#-style CancellationToken; AbortController is Node.js standard but not VSCode API |
| OutputChannel (text) | LogOutputChannel | 2022 (VSCode 1.74) | LogOutputChannel adds structured log levels (info, warn, error); text-only use case still prefers OutputChannel |

**Deprecated/outdated:**
- webpack for VSCode extensions: Not deprecated but no longer recommended; esbuild is faster and official samples use it
- vscode.window.setStatusBarMessage: Replaced by createStatusBarItem for persistent status (setStatusBarMessage is temporary-only)
- Manual platform detection in code: vsce --target handles platform naming and binary selection at build time

## Open Questions

1. **Incremental verification scope (whole crate vs changed file)**
   - What we know: rust-analyzer check-on-save runs whole crate (cargo check --all-targets); incremental cache mitigates cost
   - What's unclear: Does our MIR-hash invalidation cache make whole-crate fast enough (<1s)? Or should we optimize for single-file verification?
   - Recommendation: Start with whole-crate (simpler, matches cargo check UX). If slow, add config option for file-only mode. Need telemetry to measure real-world latency.

2. **Background verification process vs fresh spawn**
   - What we know: rust-analyzer uses a persistent background process (flycheck); fresh spawn adds ~50-100ms process startup overhead
   - What's unclear: Do we benefit from persistent process if Z3 solver state is already reused via push/pop (Phase 14)?
   - Recommendation: Use fresh spawn (simpler lifecycle, no state leakage between runs). If startup overhead is measurable (>200ms p95), migrate to persistent process in later phase.

3. **Gutter icon asset format (SVG vs PNG)**
   - What we know: VSCode supports both SVG and PNG for gutter icons; SVG scales better but may render differently across themes
   - What's unclear: Do theme-specific icons require separate light/dark SVGs, or can we use a single SVG with currentColor?
   - Recommendation: Use SVG with currentColor for automatic theme adaptation. Test on light/dark/high-contrast themes. Fallback: separate light-icon.svg and dark-icon.svg in DecorationRenderOptions.

4. **Related information for code paths (not yet in JSON schema)**
   - What we know: User decision requires "related information pointing to the specific code path causing the violation"
   - What's unclear: Current JsonFailure schema has no related_locations field; VCGen doesn't track execution paths through control flow
   - Recommendation: Phase 16 initial release omits related information (shows primary diagnostic on contract only). Phase 16.5 or 17 adds code path tracking to VCGen and extends JSON schema with related_locations: Array<{file, line, message}>.

## Sources

### Primary (HIGH confidence)
- [VSCode Extension API - Language Server Guide](https://code.visualstudio.com/api/language-extensions/language-server-extension-guide) - Diagnostic creation and publishing
- [VSCode Extension API - Bundling Extensions](https://code.visualstudio.com/api/working-with-extensions/bundling-extension) - esbuild configuration and platform-specific binaries
- [VSCode Extension API - Publishing Extensions](https://code.visualstudio.com/api/working-with-extensions/publishing-extension) - vsce package --target and marketplace workflow
- [VSCode Extension API - Status Bar UX Guidelines](https://code.visualstudio.com/api/ux-guidelines/status-bar) - StatusBarItem patterns
- [VSCode Extension API - Common Capabilities](https://code.visualstudio.com/api/extension-capabilities/common-capabilities) - Output channels, commands, configuration
- [VSCode Extension Samples - Platform-Specific](https://github.com/microsoft/vscode-platform-specific-sample) - Binary bundling architecture
- [VSCode Extension Samples - Diagnostic Related Information](https://github.com/microsoft/vscode-extension-samples/tree/main/diagnostic-related-information-sample) - DiagnosticRelatedInformation usage
- [rust-analyzer package.json](https://github.com/rust-lang/rust-analyzer/blob/master/editors/code/package.json) - Check-on-save configuration patterns
- Existing codebase: `crates/driver/src/json_output.rs` - JsonVerificationReport schema (HIGH confidence)
- Existing codebase: `crates/driver/src/output.rs` - FunctionResult and colored output (HIGH confidence)

### Secondary (MEDIUM confidence)
- [Building VS Code Extensions in 2026](https://abdulkadersafi.com/blog/building-vs-code-extensions-in-2026-the-complete-modern-guide) - Modern development patterns with esbuild
- [Dafny Integrated Development Environment](https://arxiv.org/pdf/1404.6602) - Counterexample visualization patterns (blue dots, debugger-like variable view)
- [Boogie Verification Debugger](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml213.pdf) - Related information for control flow paths

### Tertiary (LOW confidence)
- WebSearch results for DiagnosticCollection, DecorationRenderOptions, child_process spawning - Verified against official docs
- rust-analyzer architecture documentation - Flycheck pattern (not directly applicable; we use simpler spawn model)

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - Official VSCode API docs, verified samples, existing TypeScript ecosystem
- Architecture: HIGH - Patterns from rust-analyzer, official samples, existing json_output.rs schema
- Pitfalls: HIGH - Common VSCode extension issues documented in GitHub issues, official guides, hands-on experience patterns
- Related information implementation: MEDIUM-LOW - User requirement is clear, but JSON schema extension and VCGen path tracking not yet designed

**Research date:** 2026-02-16
**Valid until:** ~60 days (VSCode extension API is stable; esbuild/vsce tooling changes slowly; verify vsce version when implementing)
