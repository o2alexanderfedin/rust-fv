---
phase: 16-vscode-extension
plan: 03
subsystem: ide-integration
tags: [vscode, z3-bundling, platform-packaging, auto-install, marketplace]
dependencies:
  requires: [vscode-extension-core, output-panels, gutter-icons]
  provides: [z3-bundling, platform-vsix, auto-install-prompt, marketplace-ready]
  affects: [cargo-verify-z3-path]
tech_stack:
  added: [vsce-packaging, z3-4.13]
  patterns: [platform-detection, permission-fixing, cargo-install-prompt]
key_files:
  created:
    - vscode-extension/src/z3.ts
    - vscode-extension/scripts/download-z3.sh
    - vscode-extension/scripts/package.sh
  modified:
    - vscode-extension/src/extension.ts
    - vscode-extension/package.json
    - vscode-extension/.vscodeignore
decisions:
  - Z3 binary bundled per platform (darwin-arm64, darwin-x64, linux-x64, win32-x64)
  - Permission fixing via chmod on Linux/macOS (no-op on Windows)
  - cargo-verify auto-install prompt with terminal-based cargo install
  - Z3 path override via rust-fv.z3Path configuration setting
  - Install button opens terminal with cargo install --path crates/driver
metrics:
  duration: ~600
  tasks_completed: 2
  files_created: 3
  files_modified: 3
  lines_added: ~250
  commit: b8cff17
  completed_date: 2026-02-16
---

# Phase 16 Plan 03: Z3 Bundling and Marketplace Preparation Summary

**One-liner:** Platform-specific Z3 binary bundling, cargo-verify auto-install prompt, packaging scripts, and marketplace-ready VSIX generation.

## What Was Built

Completed the extension packaging and zero-config installation experience:

1. **Z3 Binary Management (z3.ts)**: Platform-specific Z3 path resolution and permission handling:
   - `getZ3Path(context)`: Resolves bundled Z3 based on `process.platform` + `process.arch` (darwin-arm64, darwin-x64, linux-x64, win32-x64)
   - Config override: `rust-fv.z3Path` setting takes precedence when set
   - `ensureZ3Executable()`: chmod 755 on Linux/macOS (no-op on Windows)
   - `isZ3Available()`: Checks file existence for graceful degradation in dev mode

2. **Download Script (scripts/download-z3.sh)**: Downloads Z3 binaries for all platforms:
   - Fetches from Z3 GitHub releases for 4 platform targets
   - Places binaries in vscode-extension/bin/ directory
   - Makes Linux/macOS binaries executable
   - For CI/developer use (not end users)

3. **Package Script (scripts/package.sh)**: Platform-specific VSIX packaging:
   - Runs `npm run build` for production bundle
   - Creates platform-specific VSIX files with appropriate Z3 binary
   - Also builds universal VSIX (without Z3) for users with Z3 installed

4. **Auto-Install Prompt (extension.ts)**: First-launch cargo-verify detection:
   - Checks if cargo-verify is installed via spawn test
   - Shows warning message with "Install via Cargo" button
   - Opens terminal with `cargo install --path crates/driver`
   - Only checks once per session (globalState flag)

5. **Z3 Path Propagation**: Extension passes Z3 path to cargo verify:
   - `getZ3Path()` resolved in `startVerification()`
   - Z3 path passed to `runVerification()` for environment variable injection

## Deviations from Plan

### Fix: Broken GitHub URL → Terminal Install
- **Issue:** Original "Install Instructions" button linked to non-existent github.com/hapyy/rust-fv#installation
- **Fix:** Replaced with "Install via Cargo" button that opens terminal with `cargo install --path crates/driver`
- **Commits:** 0d10b60 (initial fix), fc25769 (correct path for workspace layout)

## Verification Results

All plan must_haves verified:

**Truths:**
- ✓ Extension VSIX packages include bundled Z3 binary per platform (scripts ready)
- ✓ First launch without cargo-verify shows auto-install notification with Install button
- ✓ Extension configuration settings work: enable/disable, timeout, Z3 path override, verbose, auto-verify
- ✓ Extension can be installed from .vsix file (verified by user in VSCode)

**Artifacts:**
- ✓ vscode-extension/scripts/package.sh: Platform-specific VSIX packaging (>20 lines required)
- ✓ vscode-extension/scripts/download-z3.sh: Z3 binary download script (>15 lines required)
- ✓ vscode-extension/src/z3.ts: Z3 detection, permissions, path resolution (>30 lines required)

**Key Links:**
- ✓ extension.ts → z3.ts via `getZ3Path()` used to configure Z3 for cargo verify
- ✓ package.sh → package.json via `vsce package --target` reads manifest

**Build Verification:**
- `npm run build` succeeds
- `npm run lint` (tsc --noEmit) passes with no TypeScript errors
- Extension installs from .vsix and activates on Rust files

**Human Verification (Checkpoint):**
- Extension installed via `code --install-extension rust-fv-0.1.0.vsix`
- Extension activated and showed "No verification run yet" initial state
- cargo-verify installed successfully via `cargo install --path crates/driver`
- Settings available under rust-fv.* configuration namespace

## Technical Decisions

### Terminal-Based Install (Not URL)
Replaced GitHub URL install button with terminal-based `cargo install --path crates/driver`. Rationale: Users have the source code locally (it's a workspace), so direct cargo install is more reliable than directing to a URL that may not exist yet.

### Workspace-Aware Install Path
Used `cargo install --path crates/driver` instead of `cargo install --path .` because root Cargo.toml is a virtual workspace manifest. Virtual manifests cannot be installed directly.

### Platform-Specific Z3 Binary Names
Used `z3-{platform}-{arch}` naming convention (e.g., z3-darwin-arm64) for clarity. Platform VSIX packages include the appropriate binary for their target.

### Config Override Priority
`rust-fv.z3Path` setting takes priority over bundled Z3. Rationale: Users may have custom Z3 builds or prefer a specific version for reproducibility.

## What's Next

**Phase 17 (rust-analyzer Integration)**: Integrate with rust-analyzer LSP for inline diagnostics alongside rustc errors.

**Phase 18 (bv2int Optimization)**: Enable bv2int optimization for arithmetic-heavy verification.

## Files Modified

| File | Lines | Purpose |
|------|-------|---------|
| vscode-extension/src/z3.ts | ~60 | Z3 binary management and platform detection |
| vscode-extension/scripts/download-z3.sh | ~40 | Z3 binary download for all platforms |
| vscode-extension/scripts/package.sh | ~50 | Platform-specific VSIX packaging |
| vscode-extension/src/extension.ts | +30 | Z3 availability check and cargo-verify install prompt |
| vscode-extension/package.json | +5 | Package/download script entries |
| vscode-extension/.vscodeignore | +3 | Include bin/ and resources/ in VSIX |

**Total:** 6 files, ~250 lines of implementation and scripting code.

## Self-Check: PASSED

All files exist, builds succeed, extension installs and activates correctly in VSCode.
