---
created: 2026-02-27T21:15:57.884Z
title: Build VSCode extension in CI/CD for all platforms
area: tooling
files:
  - vscode-extension/
  - .github/workflows/ci.yml
---

## Problem

The VSCode extension (`vscode-extension/`) provides inline verification results (green/red gutter icons, counterexample values, output panel) and ships a pre-built `.vsix` package (`vscode-extension/rust-fv-0.1.0.vsix`). Currently the extension build is not part of the CI/CD pipeline, so:

- The `.vsix` package may become stale or broken as the Rust codebase evolves
- There is no automated verification that the extension builds successfully on all three supported platforms (Linux, macOS, Windows)
- No cross-platform packaging step runs on PR/push to catch breakage early

## Solution

Add a VSCode extension build job to `.github/workflows/ci.yml` that:

1. Runs on `ubuntu-latest`, `macos-latest`, `windows-latest` (matrix)
2. Sets up Node.js and installs extension dependencies (`npm ci` in `vscode-extension/`)
3. Compiles the TypeScript extension (`npx tsc --noEmit` or `npm run compile`)
4. Packages the `.vsix` (`npx vsce package`) on at least one platform (Linux) as a build artifact
5. Uploads the packaged `.vsix` as a GitHub Actions artifact for download/inspection
