---
created: 2026-02-27T20:35:00.000Z
title: Add GitHub CI/CD workflow section to README
area: docs
files:
  - README.md (root)
---

## Problem

The root README.md has no documentation on how to integrate `rust-fv` into GitHub Actions or other CI/CD workflows. Users who want to run formal verification as part of their CI pipeline (e.g., on every PR) have no guidance on:
- How to install Z3 on CI runners
- How to install the `rust-fv-driver` binary
- What a minimal GitHub Actions workflow looks like
- How to interpret exit codes / fail the build on verification failures

## Solution

Add a "CI/CD Integration" section to README.md showing:
1. Minimal GitHub Actions workflow example (Ubuntu, Z3 via apt-get)
2. Cross-platform matrix example (Linux/macOS/Windows) — referencing our own CI as prior art
3. How to use `--output-format json` for structured reporting
4. Environment variable approach (no subcommand install needed in CI):
   `RUSTC=/path/to/rust-fv-driver RUST_FV_VERIFY=1 cargo check`
5. How to cache the verification cache (`target/verify-cache/`) across runs
