# Phase 17: rust-analyzer Integration - Research

**Researched:** 2026-02-16
**Domain:** rust-analyzer custom diagnostic integration via flycheck/overrideCommand
**Confidence:** MEDIUM-HIGH

## Summary

rust-analyzer can display custom tool diagnostics inline by using `rust-analyzer.check.overrideCommand` to replace the default `cargo check` command with `cargo verify --message-format=json`. This approach integrates seamlessly with rust-analyzer's existing flycheck infrastructure without requiring LSP server modifications or custom rust-analyzer plugins. The extension configures overrideCommand, rust-analyzer runs the custom check command on save, and diagnostics appear alongside rustc errors in the Problems panel.

This pattern is proven — rust-analyzer users successfully integrate clippy, custom cargo wrappers, and compiler-specific checks via overrideCommand. The diagnostic `source` field distinguishes rust-fv diagnostics from rustc, allowing visual differentiation and independent filtering. Coordination between standalone verification (Phase 16) and rust-analyzer mode happens at the DiagnosticCollection level in VSCode, where the extension can deduplicate or coexist based on which mode is active.

Performance challenge: rust-analyzer expects check commands to complete in ~1-2s for responsive UX. This relies heavily on Phase 14's incremental cache to avoid full re-verification overhead. The 2-second end-to-end target from user decision is ambitious but achievable if incremental verification hits >90% cache rate for typical edits.

**Primary recommendation:** Use `rust-analyzer.check.overrideCommand` with `cargo verify --message-format=json`, configure via `rust-analyzer.rustfv.*` settings namespace, deduplicate standalone and RA diagnostics by clearing one DiagnosticCollection when the other is active, and rely on Phase 14 incremental cache to meet 2s latency target.

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

**Diagnostic presentation:**
- Distinct visual style from rustc diagnostics — different color/style so users immediately distinguish rust-fv from rustc
- All diagnostics in the same Problems panel, tagged with a distinct diagnostic source (e.g., `rust-fv`)
- Green gutter checkmarks for verified functions (always active, part of the single extension)
- Counterexample details: Claude's discretion on inline tooltip vs output panel link, based on rust-analyzer's diagnostic model

**Verification trigger:**
- Auto-verify on save by default, with option to switch to manual-only mode
- End-to-end 2-second target from file save to diagnostics appearing (includes Z3 time, relies on Phase 14 incremental cache)
- Verification coordination between standalone and RA modes: Claude's discretion on shared vs independent runs
- Integration point (flycheck vs separate process): Claude's discretion based on rust-analyzer architecture

**Configuration UX:**
- Settings nested under `rust-analyzer.*` namespace (e.g., `rust-analyzer.rustfv.enable`) — feels native to RA users
- Enabled by default when extension installed — works out of the box
- Per-workspace overrides supported via `.vscode/settings.json` — useful for projects without contracts
- When cargo verify not installed: status bar hint showing "rust-fv: not installed" (non-intrusive but discoverable)

**Coexistence model:**
- Single extension handles both standalone and rust-analyzer integration (not two separate extensions)
- Both diagnostic channels active when rust-analyzer present, with deduplication to avoid duplicate squiggles
- Output panel (SMT-LIB viewer, structured failures) always available regardless of diagnostic mode
- Gutter checkmarks always work — part of the single extension, not tied to a specific diagnostic channel

### Claude's Discretion

- Integration architecture (flycheck hook vs separate process)
- Counterexample display in RA diagnostics (inline vs linked)
- Verification run coordination when both channels active
- Deduplication strategy for avoiding double diagnostics

### Deferred Ideas (OUT OF SCOPE)

None — discussion stayed within phase scope

</user_constraints>

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|------------------|
| IDE-04 | rust-analyzer shows rust-fv diagnostics inline via custom diagnostic source | rust-analyzer.check.overrideCommand with cargo verify --message-format=json; diagnostics have source: "rust-fv" field |
| IDE-05 | rust-analyzer runs `cargo verify` on save via flycheck integration | rust-analyzer.checkOnSave (default: true) triggers overrideCommand automatically; no explicit flycheck hook needed |

</phase_requirements>

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| rust-analyzer | 0.3.2761+ | Language server with flycheck integration | Built-in check-on-save via overrideCommand; proven pattern for custom tools (clippy, cargo-wrapper) |
| TypeScript | 5.x+ | Extension configuration logic | VSCode extensions are TypeScript; Phase 16 already uses TS stack |
| LSP 3.17 | current | Diagnostic protocol | Diagnostic.source field distinguishes rust-fv from rustc; no protocol modifications needed |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| vscode.languages API | VSCode 1.85+ | DiagnosticCollection management | Coordinate standalone vs RA diagnostics; clear one when other active |
| vscode.workspace API | VSCode 1.85+ | Configuration contribution | Register rust-analyzer.rustfv.* settings; workspace overrides |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| overrideCommand | Custom LSP server extension | LSP extension requires rust-analyzer fork/plugin system (doesn't exist); overrideCommand is zero-config |
| Nested rust-analyzer.* namespace | Top-level rustfv.* namespace | Top-level feels like separate tool; nested feels native to RA users (per user decision) |
| Deduplication (clear one collection) | Show both diagnostics simultaneously | Duplicate squiggles confuse users; single source of truth is clearer |

**Configuration:**
```json
{
  "rust-analyzer.check.overrideCommand": [
    "cargo", "verify", "--message-format=json"
  ],
  "rust-analyzer.rustfv.enable": true,
  "rust-analyzer.rustfv.autoVerifyOnSave": true
}
```

## Architecture Patterns

### Recommended Integration Model
```
┌─────────────────────────────────────────────────┐
│  VSCode Extension (single extension)            │
│  ┌──────────────┐        ┌─────────────────┐   │
│  │ Standalone   │        │ rust-analyzer   │   │
│  │ Mode         │        │ Mode            │   │
│  │              │        │                 │   │
│  │ onDidSave    │        │ overrideCommand │   │
│  │ → spawn      │        │ configured      │   │
│  │ cargo verify │        │ in settings.json│   │
│  └──────┬───────┘        └────────┬────────┘   │
│         │                         │            │
│         │  DiagnosticCollection   │            │
│         │  deduplication logic    │            │
│         └─────────┬───────────────┘            │
│                   │                            │
│         ┌─────────▼─────────┐                  │
│         │ rustfvDiagnostics │                  │
│         │ (source: rust-fv) │                  │
│         └───────────────────┘                  │
│                                                │
│  Gutter decorations, output panel,            │
│  SMT-LIB viewer — always active               │
└─────────────────────────────────────────────────┘
```

### Pattern 1: overrideCommand Configuration
**What:** Replace rust-analyzer's default cargo check with cargo verify
**When to use:** rust-analyzer installed; user wants verification diagnostics inline with rustc
**Example:**
```typescript
// Extension contributes rust-analyzer.rustfv.enable setting
// When enabled, extension writes to workspace config:
import * as vscode from 'vscode';

async function enableRustAnalyzerMode() {
  const config = vscode.workspace.getConfiguration('rust-analyzer');

  // Set overrideCommand if not already set
  const currentOverride = config.get<string[]>('check.overrideCommand');
  if (!currentOverride || currentOverride[0] !== 'cargo' || currentOverride[1] !== 'verify') {
    await config.update(
      'check.overrideCommand',
      ['cargo', 'verify', '--message-format=json'],
      vscode.ConfigurationTarget.Workspace
    );
  }
}
```

### Pattern 2: Diagnostic Deduplication
**What:** Prevent double squiggles when both standalone and RA modes could run
**When to use:** rust-analyzer is installed and overrideCommand is configured
**Example:**
```typescript
// Source: VSCode DiagnosticCollection API + deduplication pattern
let rustfvDiagnostics: vscode.DiagnosticCollection;
let isRustAnalyzerModeActive = false;

export function activate(context: vscode.ExtensionContext) {
  rustfvDiagnostics = vscode.languages.createDiagnosticCollection('rust-fv');

  // Detect rust-analyzer mode
  const raConfig = vscode.workspace.getConfiguration('rust-analyzer');
  const overrideCmd = raConfig.get<string[]>('check.overrideCommand');
  isRustAnalyzerModeActive =
    overrideCmd?.[1] === 'verify' &&
    raConfig.get<boolean>('rustfv.enable', false);

  // Register standalone on-save handler only if RA mode disabled
  if (!isRustAnalyzerModeActive) {
    context.subscriptions.push(
      vscode.workspace.onDidSaveTextDocument(runStandaloneVerification)
    );
  }

  // Clear standalone diagnostics when switching to RA mode
  vscode.workspace.onDidChangeConfiguration(e => {
    if (e.affectsConfiguration('rust-analyzer.check.overrideCommand') ||
        e.affectsConfiguration('rust-analyzer.rustfv.enable')) {
      const nowActive = checkIfRaModeActive();
      if (nowActive && !isRustAnalyzerModeActive) {
        // Switched to RA mode: clear standalone diagnostics
        rustfvDiagnostics.clear();
      }
      isRustAnalyzerModeActive = nowActive;
    }
  });
}
```

### Pattern 3: Diagnostic Source Field Styling
**What:** Use diagnostic.source = "rust-fv" to distinguish from rustc
**When to use:** LSP protocol allows source field; VSCode Problems panel filters by source
**Example:**
```typescript
// cargo verify outputs JSON with diagnostics
// Extension or rust-analyzer parses and creates VSCode diagnostics
const diagnostic = new vscode.Diagnostic(
  range,
  message,
  vscode.DiagnosticSeverity.Error
);
diagnostic.source = 'rust-fv'; // Appears in Problems panel

// VSCode shows: [rust-fv] Postcondition may not hold
//           vs: [rustc] mismatched types
```

**Visual differentiation:** VSCode doesn't provide built-in color coding by source, but:
- Problems panel displays source in brackets: `[rust-fv]` vs `[rustc]`
- Users can filter by source: type `@source:rust-fv` in Problems search
- Future enhancement: Use DiagnosticTag or custom decoration for color

### Pattern 4: Configuration Namespace Convention
**What:** Nest rust-fv settings under `rust-analyzer.*` prefix
**When to use:** Settings feel native to rust-analyzer users (per user decision)
**Example:**
```json
// package.json contributions.configuration
{
  "rust-analyzer.rustfv.enable": {
    "type": "boolean",
    "default": true,
    "description": "Enable rust-fv verification diagnostics"
  },
  "rust-analyzer.rustfv.autoVerifyOnSave": {
    "type": "boolean",
    "default": true,
    "description": "Run cargo verify automatically on file save"
  },
  "rust-analyzer.rustfv.timeout": {
    "type": "number",
    "default": 30000,
    "description": "Verification timeout in milliseconds"
  }
}
```

**Naming convention:** rust-analyzer settings use `_enable` suffix for toggles (per rust-analyzer config.rs conventions). Follow this pattern for consistency.

### Pattern 5: Incremental Verification Performance
**What:** Achieve 2s end-to-end latency via Phase 14 incremental cache
**When to use:** User saves frequently; must meet responsiveness target
**Example:**
```bash
# cargo verify with incremental cache enabled
# Phase 14 implements MIR-hash-based caching
# File save → cargo verify → only re-verify changed functions → diagnostics

# First verification (cold cache): 3-5s
cargo verify --output-format json

# Subsequent verification (hot cache, 1 function changed): <1s
# - Load cached VCs for unchanged functions
# - Generate VC only for modified function
# - Z3 solve (incremental push/pop reuses solver state)
```

**Performance budget (2s target):**
- JSON parsing: <10ms
- Incremental cache lookup: <50ms
- VC generation (changed functions only): 200-500ms
- Z3 solving (incremental): 500-1200ms
- Diagnostic creation: <50ms
- **Total: 800-1800ms** (achievable with 80-90% cache hit rate)

### Anti-Patterns to Avoid
- **Overriding check.command instead of check.overrideCommand:** `check.command` is for subcommands (check, clippy); `check.overrideCommand` fully replaces the command. Use overrideCommand for cargo verify.
- **Forgetting --message-format=json:** rust-analyzer expects JSON output for diagnostic parsing. Omitting this flag breaks integration.
- **Running both standalone and RA verification simultaneously:** Wastes CPU, confuses users with duplicate results. Deactivate one when the other is enabled.
- **Hardcoding workspace config:** Writing to `.vscode/settings.json` directly locks the workspace. Use vscode.workspace.getConfiguration().update() with ConfigurationTarget.Workspace.
- **Ignoring rust-analyzer not installed:** Extension should detect if rust-analyzer is available before enabling RA mode. Fail gracefully with informative message.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Custom flycheck hook | Patching rust-analyzer to call extension API | check.overrideCommand | overrideCommand is public API; no fork needed; works with all rust-analyzer releases |
| Diagnostic deduplication logic | Complex heuristics comparing diagnostic text/range | Clear one DiagnosticCollection when switching modes | Simple, deterministic; no false positives/negatives |
| Visual diagnostic differentiation | Custom VSCode theme, decoration overlay on squiggles | diagnostic.source field | LSP-standard; Problems panel shows [source]; filterable; no custom rendering |
| Incremental verification from scratch | Custom change tracking, file diffing, function-level caching | Phase 14 MIR-hash cache | Already implemented; soundness-preserving; handles cross-function dependencies |

**Key insight:** rust-analyzer's overrideCommand is designed for exactly this use case — integrating custom verification/linting tools that output cargo-compatible JSON diagnostics. Don't fight the architecture; lean into the proven pattern.

## Common Pitfalls

### Pitfall 1: overrideCommand Scope Confusion
**What goes wrong:** Configure `check.overrideCommand` globally in User settings; all Rust projects now run cargo verify, even those without contracts; verification fails, diagnostics show errors for unrelated projects
**Why it happens:** User settings apply to all workspaces; cargo verify requires rust-fv annotations; projects without annotations fail or produce no diagnostics
**How to avoid:**
- Default to Workspace-level configuration: extension writes to `.vscode/settings.json` or workspace config
- Detect if project uses rust-fv: search for `#[requires]`, `#[ensures]` in codebase before enabling RA mode
- Provide "Enable for this workspace only" prompt when user toggles RA mode
- Document: "rust-analyzer integration is workspace-specific; other projects unaffected"
**Warning signs:** Users report "cargo verify fails in projects without rust-fv"; diagnostics missing in non-rust-fv workspaces

### Pitfall 2: JSON Output Format Mismatch
**What goes wrong:** cargo verify outputs JSON but schema differs from rustc's diagnostic JSON; rust-analyzer fails to parse, no diagnostics appear
**Why it happens:** rustc diagnostic JSON has specific schema (rendered, spans, children); cargo verify's JsonVerificationReport doesn't match
**How to avoid:**
- **Option A:** Extend cargo verify to emit rustc-compatible JSON format (add `--message-format=rustc-json` flag)
- **Option B:** Use overrideCommand with a wrapper script that transforms JsonVerificationReport → rustc JSON
- **Option C:** Don't use rust-analyzer's built-in diagnostic parsing; extension listens for overrideCommand output and manually creates diagnostics
**Recommendation:** Option A is cleanest (rust-analyzer parses natively). Option C is simplest short-term (extension already parses JsonVerificationReport from Phase 16).
**Warning signs:** `cargo verify` runs on save but no diagnostics appear; rust-analyzer log shows JSON parse errors

### Pitfall 3: Verification Timeout Mismatch
**What goes wrong:** User sets `rust-analyzer.rustfv.timeout = 30000` (30s) but rust-analyzer's default check timeout is 10s; verification gets killed before cargo verify finishes, incomplete diagnostics
**Why it happens:** rust-analyzer has its own timeout for check commands (independent of tool-specific settings)
**How to avoid:**
- Document: "Set `rust-analyzer.checkOnSave.extraArgs` to pass timeout to cargo verify, OR increase rust-analyzer's check timeout"
- Extension should read `rustfv.timeout` and warn if > rust-analyzer check timeout
- Alternatively: Don't use rust-analyzer timeout; rely on cargo verify's internal timeout only
**Warning signs:** Long-running verifications always timeout at exactly 10s regardless of rustfv.timeout setting

### Pitfall 4: Deduplication Race Condition
**What goes wrong:** User saves file; standalone mode starts verification; mid-verification, rust-analyzer overrideCommand also starts; both complete and publish diagnostics; user sees duplicate squiggles
**Why it happens:** Switching modes doesn't cancel in-flight verification; both paths race to publish diagnostics
**How to avoid:**
- When switching modes (config change), cancel any in-flight standalone verification immediately
- Clear the deactivated DiagnosticCollection before starting the newly activated mode
- Mutex/flag to prevent simultaneous standalone + RA verification
**Warning signs:** Intermittent duplicate diagnostics; diagnostics flicker on save; both [rust-fv] sources in Problems panel

### Pitfall 5: Gutter Decorations Not Updating in RA Mode
**What goes wrong:** Standalone mode shows green checkmarks for verified functions; switch to RA mode; checkmarks disappear or show stale results
**Why it happens:** Gutter decoration logic in Phase 16 triggers on standalone verification completion; RA mode doesn't trigger the same codepath
**How to avoid:**
- Listen for rust-analyzer diagnostic publications: when diagnostics with source="rust-fv" arrive, trigger gutter decoration update
- Parse diagnostics to determine which functions verified (those with no diagnostics)
- Alternatively: Gutter decorations remain independent — always run lightweight analysis to determine verified functions (don't rely on diagnostic pathway)
**Warning signs:** Checkmarks work in standalone mode but not RA mode; checkmarks show outdated state

### Pitfall 6: Missing cargo verify Not Detected
**What goes wrong:** User enables RA mode; overrideCommand set to cargo verify; cargo verify not installed; rust-analyzer silently fails check, no diagnostics, no error message
**Why it happens:** rust-analyzer logs check command errors but doesn't surface them to user; extension doesn't validate cargo verify availability before enabling RA mode
**How to avoid:**
- Before enabling RA mode: run `cargo verify --version` to check installation
- If not installed, show modal with "cargo-verify not found. Install now?" (same pattern as standalone mode in Phase 16)
- Extension should monitor rust-analyzer status for check command failures and show notification if cargo verify fails
**Warning signs:** RA mode enabled but no diagnostics appear; rust-analyzer output channel shows "cargo: unknown subcommand 'verify'"

### Pitfall 7: Counterexample Truncation in Diagnostic Message
**What goes wrong:** Diagnostic message includes counterexample: "x = 42, y = -1, z = 100, ..."; tooltip truncates after 200 chars; user can't see full counterexample
**Why it happens:** VSCode Diagnostic.message is shown in tooltip; very long messages get truncated
**How to avoid:**
- Keep primary diagnostic message concise: "Postcondition may not hold"
- Link to output panel for full counterexample: "See Output panel for counterexample details"
- Alternatively: Use DiagnosticRelatedInformation to attach counterexample as separate detail (expands on click)
- Best: Both — brief message + related info + output panel
**Warning signs:** Users complain "can't see full counterexample"; tooltips end with "..."

## Code Examples

Verified patterns from official sources and rust-analyzer conventions:

### Detecting rust-analyzer Installation
```typescript
// Check if rust-analyzer extension is installed and active
import * as vscode from 'vscode';

function isRustAnalyzerAvailable(): boolean {
  const raExtension = vscode.extensions.getExtension('rust-lang.rust-analyzer');
  return raExtension !== undefined && raExtension.isActive;
}

async function enableRustAnalyzerIntegration(context: vscode.ExtensionContext) {
  if (!isRustAnalyzerAvailable()) {
    vscode.window.showWarningMessage(
      'rust-analyzer not found. Install rust-analyzer for inline diagnostics.',
      'Install'
    ).then(action => {
      if (action === 'Install') {
        vscode.commands.executeCommand(
          'workbench.extensions.installExtension',
          'rust-lang.rust-analyzer'
        );
      }
    });
    return;
  }

  // Proceed with configuration
  await configureOverrideCommand();
}
```

### Configuring overrideCommand Programmatically
```typescript
// Extension updates rust-analyzer.check.overrideCommand when RA mode enabled
async function configureOverrideCommand() {
  const config = vscode.workspace.getConfiguration('rust-analyzer');
  const currentOverride = config.get<string[]>('check.overrideCommand');

  // Only set if not already configured
  if (!currentOverride || !currentOverride.includes('verify')) {
    await config.update(
      'check.overrideCommand',
      ['cargo', 'verify', '--message-format=json'],
      vscode.ConfigurationTarget.Workspace
    );

    vscode.window.showInformationMessage(
      'rust-fv: rust-analyzer integration enabled. Verification runs on save.'
    );
  }
}

async function disableOverrideCommand() {
  const config = vscode.workspace.getConfiguration('rust-analyzer');
  await config.update(
    'check.overrideCommand',
    undefined, // Reset to default cargo check
    vscode.ConfigurationTarget.Workspace
  );
}
```

### Mode Detection and Deduplication
```typescript
// Detect which mode is active and coordinate diagnostics
enum VerificationMode {
  Standalone,
  RustAnalyzer,
  Disabled
}

function detectMode(): VerificationMode {
  const raConfig = vscode.workspace.getConfiguration('rust-analyzer');
  const rustfvConfig = vscode.workspace.getConfiguration('rust-analyzer.rustfv');

  const overrideCmd = raConfig.get<string[]>('check.overrideCommand');
  const raEnabled = rustfvConfig.get<boolean>('enable', false);
  const isRaAvailable = isRustAnalyzerAvailable();

  if (isRaAvailable && raEnabled && overrideCmd?.[1] === 'verify') {
    return VerificationMode.RustAnalyzer;
  }

  const standaloneEnabled = vscode.workspace.getConfiguration('rust-fv').get<boolean>('enable', true);
  if (standaloneEnabled) {
    return VerificationMode.Standalone;
  }

  return VerificationMode.Disabled;
}

// In extension activate():
let currentMode = detectMode();

vscode.workspace.onDidChangeConfiguration(e => {
  if (e.affectsConfiguration('rust-analyzer') || e.affectsConfiguration('rust-fv')) {
    const newMode = detectMode();

    if (newMode !== currentMode) {
      // Mode switched: clear diagnostics from old mode
      if (currentMode === VerificationMode.Standalone) {
        standaloneeDiagnostics.clear();
      }
      // rust-analyzer diagnostics clear themselves when overrideCommand changes

      currentMode = newMode;
    }
  }
});
```

### Listening for rust-analyzer Diagnostics (for gutter updates)
```typescript
// Update gutter decorations when rust-analyzer publishes rust-fv diagnostics
// Note: VSCode doesn't provide direct API to listen for diagnostic publications
// Workaround: poll diagnostics periodically or update on editor change

vscode.workspace.onDidChangeTextDocument(e => {
  if (e.document.languageId !== 'rust') return;

  // Debounce: only check diagnostics 500ms after last edit
  clearTimeout(gutterUpdateTimer);
  gutterUpdateTimer = setTimeout(() => {
    updateGutterDecorationsFromDiagnostics(e.document.uri);
  }, 500);
});

function updateGutterDecorationsFromDiagnostics(uri: vscode.Uri) {
  const allDiagnostics = vscode.languages.getDiagnostics(uri);
  const rustfvDiagnostics = allDiagnostics.filter(d => d.source === 'rust-fv');

  // Functions with no rust-fv diagnostics are verified
  // Parse document to find all functions, subtract failed functions
  const editor = vscode.window.activeTextEditor;
  if (editor && editor.document.uri.toString() === uri.toString()) {
    const verifiedRanges = findVerifiedFunctionRanges(editor.document, rustfvDiagnostics);
    editor.setDecorations(verifiedDecorationType, verifiedRanges);
  }
}
```

### Status Bar Hint for Missing cargo-verify
```typescript
// Show non-intrusive status bar indicator when cargo verify not installed
let cargoVerifyStatusItem: vscode.StatusBarItem;

async function checkCargoVerifyInstallation() {
  try {
    await vscode.workspace.fs.stat(vscode.Uri.file('/usr/local/bin/cargo-verify'));
    // cargo-verify found, hide status item
    cargoVerifyStatusItem.hide();
  } catch {
    // Not found in common location; try running cargo verify --version
    const result = await runCommand('cargo', ['verify', '--version']);
    if (result.exitCode !== 0) {
      // Not installed
      cargoVerifyStatusItem.text = '$(warning) rust-fv: not installed';
      cargoVerifyStatusItem.tooltip = 'Click to install cargo-verify';
      cargoVerifyStatusItem.command = 'rust-fv.install';
      cargoVerifyStatusItem.show();
    } else {
      cargoVerifyStatusItem.hide();
    }
  }
}

export function activate(context: vscode.ExtensionContext) {
  cargoVerifyStatusItem = vscode.window.createStatusBarItem(
    vscode.StatusBarAlignment.Right,
    10
  );
  context.subscriptions.push(cargoVerifyStatusItem);

  checkCargoVerifyInstallation();
}
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Custom LSP extension | check.overrideCommand | ~2022 (RA config refactor) | No rust-analyzer fork needed; custom tools integrate via standard API |
| Separate diagnostic providers | Diagnostic source field | LSP 3.15 (2020) | Multiple tools publish to same file; client filters by source |
| Global configuration only | Workspace/folder-level config | VSCode multi-root workspace support (2017) | Per-project settings; global settings don't break unrelated projects |
| Manual cargo check invocation | checkOnSave + flycheck | rust-analyzer early architecture | Automatic on-save verification; consistent UX with rustc errors |

**Deprecated/outdated:**
- `rust-analyzer.checkOnSave.command`: Replaced by `rust-analyzer.check.command` (namespace reorganization)
- `rust-analyzer.checkOnSave.overrideCommand`: Now `rust-analyzer.check.overrideCommand`
- Separate rust-analyzer.checkOnSave.enable: Now `rust-analyzer.checkOnSave` (boolean setting name changed)

**Current as of 2026-02-16:** rust-analyzer v0.3.2761+ uses `rust-analyzer.check.*` namespace. Always check current config.rs for canonical setting names.

## Open Questions

1. **JSON output format compatibility**
   - What we know: cargo verify outputs JsonVerificationReport (custom schema); rustc outputs different JSON diagnostic schema
   - What's unclear: Can rust-analyzer parse JsonVerificationReport directly, or must cargo verify emit rustc-compatible JSON?
   - Recommendation: Test with prototype — configure overrideCommand, check if diagnostics appear. If not, add `--message-format=rustc-json` flag to cargo-verify that transforms output. Extension can also parse and manually create diagnostics (Option C from Pitfall 2).

2. **Diagnostic color differentiation**
   - What we know: User decision requires "distinct visual style from rustc"; diagnostic.source field distinguishes but doesn't control color
   - What's unclear: How to make rust-fv diagnostics visually distinct (different color squiggle)? VSCode doesn't provide per-source styling by default.
   - Recommendation: Start with [rust-fv] prefix in Problems panel (built-in). Future enhancement: custom TextEditorDecorationType overlay on diagnostic ranges (requires mapping diagnostics → decorations). Research: VSCode extension API for diagnostic styling.

3. **Verification coordination (standalone + RA running simultaneously)**
   - What we know: Both modes could trigger on save; must deduplicate to avoid double squiggles
   - What's unclear: Should extension prevent both from running (mutex), or let both run and merge results?
   - Recommendation: Mutex approach (only one active at a time). Simpler to reason about, no merge logic needed. User explicitly chooses mode via `rust-analyzer.rustfv.enable` setting.

4. **Incremental cache effectiveness**
   - What we know: 2s end-to-end target is ambitious; Phase 14 cache is designed for this but not yet validated
   - What's unclear: What's the real-world cache hit rate? Does typical edit (add line, change condition) invalidate 1 function or 10?
   - Recommendation: Instrument cargo verify with telemetry (cache hit rate, per-function timing). If cache hit <80%, investigate MIR hash stability and dependency tracking. Budget analysis shows 2s is achievable with high cache hit rate.

## Sources

### Primary (HIGH confidence)
- [rust-analyzer Configuration](https://rust-analyzer.github.io/book/configuration.html) - check.overrideCommand documentation
- [rust-analyzer Diagnostics](https://rust-analyzer.github.io/book/diagnostics.html) - Diagnostic source and cargo check integration
- [rust-analyzer VS Code Integration](https://rust-analyzer.github.io/book/vs_code.html) - Extension architecture
- [LSP 3.17 Specification - Diagnostic](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/) - Diagnostic.source field definition
- [VSCode DiagnosticCollection API](https://code.visualstudio.com/api/language-extensions/programmatic-language-features) - Diagnostic management and deduplication
- [rust-analyzer config.rs source](https://github.com/rust-lang/rust-analyzer/blob/master/crates/rust-analyzer/src/config.rs) - Canonical setting names and conventions

### Secondary (MEDIUM confidence)
- [rust-analyzer check.overrideCommand examples](https://users.rust-lang.org/t/setting-cargo-command-to-fetch-metadata-in-rust-analyzer-in-vscode/88537) - Real-world custom tool integration patterns
- [VSCode Language Server Extension Guide](https://code.visualstudio.com/api/language-extensions/language-server-extension-guide) - DiagnosticCollection coordination
- [rust-analyzer flycheck architecture discussion](https://github.com/rust-lang/rust-analyzer/issues/18186) - Flycheck redesign (future changes)
- [Neovim LSP diagnostic deduplication](https://github.com/neovim/neovim/discussions/30815) - Multi-source diagnostic handling patterns

### Tertiary (LOW confidence - needs validation)
- WebSearch results on diagnostic visual differentiation - No VSCode API found for per-source styling; needs custom decoration approach
- Performance budget analysis - Based on Phase 14 design goals, not measured data; requires validation

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - rust-analyzer overrideCommand is documented, proven pattern (clippy, cargo-wrapper)
- Architecture: MEDIUM-HIGH - Deduplication strategy is sound but not tested; JSON format compatibility needs validation
- Pitfalls: MEDIUM - Based on common VSCode/rust-analyzer issues and config patterns; some edge cases (timeout mismatch) need testing
- Performance: MEDIUM-LOW - 2s target is achievable in theory (budget analysis) but depends on Phase 14 cache effectiveness (unvalidated)

**Research date:** 2026-02-16
**Valid until:** ~30 days (rust-analyzer config changes slowly; LSP spec is stable; validate overrideCommand API hasn't changed when implementing)
