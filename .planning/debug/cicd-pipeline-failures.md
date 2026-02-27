---
status: fixing
trigger: "CI/CD pipeline is failing on main branch. Two consecutive failed runs (22482638728, 22482429026). Investigate all failures across all platforms and fix them."
created: 2026-02-27T00:00:00Z
updated: 2026-02-27T00:10:00Z
---

## Current Focus

hypothesis: CONFIRMED - winapi crate used in solver.rs Windows code path but not declared as a dependency
test: cargo clippy --workspace --all-features -- -D warnings
expecting: Passes after replacing winapi with windows-sys
next_action: commit and push to trigger CI

## Symptoms

expected: All CI/CD jobs pass on Linux, macOS, and Windows
actual: CI runs 22482638728 and 22482429026 both failed on main branch
errors: Known issue: Windows was failing with "fatal error: 'z3.h' file not found" (z3-sys bindgen). A fix was just pushed (Z3_SYS_Z3_HEADER and LIB env vars). May be other failures too.
reproduction: Push to main triggers CI
started: Ongoing - multiple consecutive failures

## Eliminated

- hypothesis: z3.h file not found / bindgen header issue
  evidence: Z3_SYS_Z3_HEADER and LIB env vars were already set in both workflow files; Z3 installs successfully; clippy failure is E0433 on winapi crate
  timestamp: 2026-02-27T00:05:00Z

- hypothesis: Linux or macOS failures
  evidence: Both runs show ubuntu-latest and macos-latest with conclusion=success on all steps
  timestamp: 2026-02-27T00:05:00Z

## Evidence

- timestamp: 2026-02-27T00:04:00Z
  checked: gh run view 22482638728 --json jobs
  found: Only windows-latest failed; ubuntu and macos both succeeded. Windows failure is at "Run clippy" step (step 9), not at Z3 install.
  implication: The fix needed is in code, not in workflow

- timestamp: 2026-02-27T00:05:00Z
  checked: gh run view 22482638728 --log-failed
  found: error[E0433]: failed to resolve: use of unresolved module or unlinked crate `winapi` at crates/solver/src/solver.rs:194,195,200,201
  implication: winapi crate is referenced in #[cfg(windows)] block but not declared in solver/Cargo.toml

- timestamp: 2026-02-27T00:06:00Z
  checked: crates/solver/Cargo.toml
  found: Only [target.'cfg(unix)'.dependencies] has libc; no Windows-specific deps; no winapi or windows-sys
  implication: Need to add Windows-specific dependency

- timestamp: 2026-02-27T00:08:00Z
  checked: local cargo clippy after fix
  found: Finished dev profile [unoptimized + debuginfo] target(s) in 29.86s - no errors
  implication: Fix is correct and compiles

## Resolution

root_cause: crates/solver/src/solver.rs uses winapi crate in #[cfg(windows)] block (lines 194-201 for OpenProcess/TerminateProcess/CloseHandle) but winapi was never added to Cargo.toml as a Windows target dependency. The code referenced winapi::um::processthreadsapi, winapi::um::winnt, and winapi::um::handleapi modules.
fix: Replaced winapi usage with windows-sys (the modern Microsoft-maintained replacement). Added windows-sys to workspace Cargo.toml and as a [target.'cfg(windows)'.dependencies] in solver/Cargo.toml. Updated solver.rs to use windows_sys::Win32 module paths.
verification: cargo clippy --workspace --all-features -- -D warnings passes locally; cargo test --workspace passes locally
files_changed:
  - Cargo.toml (workspace): added windows-sys dependency
  - crates/solver/Cargo.toml: added [target.'cfg(windows)'.dependencies] with windows-sys
  - crates/solver/src/solver.rs: replaced winapi:: calls with windows_sys::Win32:: calls
