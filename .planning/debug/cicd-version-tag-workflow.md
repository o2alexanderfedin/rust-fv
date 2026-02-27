---
status: investigating
trigger: "Create a CI/CD GitHub Actions workflow triggered by pushing a version tag to main"
created: 2026-02-27T00:00:00Z
updated: 2026-02-27T00:00:00Z
---

## Current Focus

hypothesis: No workflow exists; need to create one that handles nightly Rust + Z3 dependency + release artifact upload
test: Read project structure, then write workflow, then validate YAML
expecting: A working workflow at .github/workflows/release.yml
next_action: Write workflow file after gathering evidence

## Symptoms

expected: A GitHub Actions workflow at .github/workflows/ that triggers on version tags, builds, tests, and creates a GitHub Release
actual: No .github/workflows/ directory exists at all
errors: N/A
reproduction: Push tag like v0.1.0 to main
started: New requirement

## Eliminated

- hypothesis: Existing workflow might have bugs
  evidence: No workflows directory exists at all
  timestamp: 2026-02-27T00:00:00Z

## Evidence

- timestamp: 2026-02-27T00:00:00Z
  checked: .github/workflows/ directory
  found: Does not exist
  implication: Need to create from scratch

- timestamp: 2026-02-27T00:00:00Z
  checked: rust-toolchain.toml
  found: channel = "nightly-2026-02-11", components = ["rustc-dev", "llvm-tools", "rust-src", "rustfmt", "clippy"]
  implication: Must pin exact nightly channel in CI, install rustc-dev and llvm-tools (needed for rustc driver)

- timestamp: 2026-02-27T00:00:00Z
  checked: Cargo.toml (workspace)
  found: z3 = "0.19" dependency, two binaries in driver crate (cargo-verify, rust-fv-driver)
  implication: Must install Z3 on CI runner; must upload both binaries as release artifacts

- timestamp: 2026-02-27T00:00:00Z
  checked: crates/driver/Cargo.toml
  found: Two [[bin]] entries sharing same main.rs - cargo-verify and rust-fv-driver
  implication: Both binaries produced by cargo build --release -p rust-fv-driver

## Resolution

root_cause: Workflow file does not exist
fix: Create .github/workflows/release.yml with proper nightly toolchain, Z3 install, build, test, and release steps
verification: YAML syntax validated, logic reviewed for common CI bugs
files_changed:
  - .github/workflows/release.yml
