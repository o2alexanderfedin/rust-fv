---
status: resolved
trigger: "CI/CD pipeline is failing on main branch. Two consecutive failed runs (22482638728, 22482429026). Investigate all failures across all platforms and fix them."
created: 2026-02-27T00:00:00Z
updated: 2026-02-27T11:35:00Z
---

## Current Focus

hypothesis: FULLY RESOLVED - all 4 issues found and fixed
test: CI run 22484424191 on main branch
expecting: All platforms pass
next_action: archive session

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

- timestamp: 2026-02-27T11:10:00Z
  checked: CI run 22483120874 log-failed after winapi->windows-sys fix
  found: error[E0308]: mismatched types at solver.rs:198 - handle != 0 where handle is *mut c_void
  implication: windows-sys HANDLE is a raw pointer, not integer; need is_null() not != 0

- timestamp: 2026-02-27T11:15:00Z
  checked: CI run 22483504043 log-failed after is_null() fix
  found: LINK: fatal error LNK1181: cannot open input file 'libz3.lib'
  implication: z3-sys uses Z3_LIBRARY_PATH_OVERRIDE (not LIB) for link search path; libz3.lib is in bin/ not lib/

- timestamp: 2026-02-27T11:20:00Z
  checked: z3-sys build.rs source code
  found: line 40-42 uses Z3_LIBRARY_PATH_OVERRIDE env var for cargo:rustc-link-search=native=<path>; gh-release branch shows libz3.lib is in bin/ directory
  implication: Must set Z3_LIBRARY_PATH_OVERRIDE=C:\tools\z3\bin in CI workflow

- timestamp: 2026-02-27T11:24:00Z
  checked: CI run 22483722242 log-failed after Z3_LIBRARY_PATH_OVERRIDE fix
  found: 3 tests pass, 1 fails: e2e_contract_change_transitive - "Modification failed: could not find contract in lib.rs"
  implication: Windows git checkout converts LF to CRLF; string matching fails because test searches for \n but file has \r\n

- timestamp: 2026-02-27T11:29:00Z
  checked: e2e_performance.rs and .gitattributes
  found: No .gitattributes file; Windows with core.autocrlf=true converts all text files to CRLF on checkout; modify_contract searches for literal newline but file has CRLF
  implication: Need .gitattributes to force LF AND normalize CRLF in test helpers

- timestamp: 2026-02-27T11:35:00Z
  checked: CI run 22484424191 on main
  found: ALL JOBS PASS - Rustfmt, ubuntu-latest, macos-latest, windows-latest all green
  implication: All four issues resolved

## Resolution

root_cause: Four cascading issues on Windows CI:
  1. solver.rs used winapi crate in #[cfg(windows)] block but winapi not in Cargo.toml
  2. windows-sys HANDLE (returned by OpenProcess) is *mut c_void, not integer; comparison to 0 causes E0308
  3. z3-sys build script uses Z3_LIBRARY_PATH_OVERRIDE (not LIB) for linker search path; libz3.lib is in bin/ not lib/
  4. Git on Windows converts LF to CRLF; e2e test string matching failed for multi-line patterns

fix: Four fixes applied:
  1. Replaced winapi with windows-sys in solver.rs, added windows-sys to workspace and solver Cargo.toml
  2. Changed handle != 0 to !handle.is_null() in solver.rs
  3. Changed LIB=C:\tools\z3\lib to Z3_LIBRARY_PATH_OVERRIDE=C:\tools\z3\bin in both ci.yml and release.yml
  4. Added .gitattributes (force LF) and normalized CRLF in modify_function_body/modify_contract helpers

verification: CI run 22484424191 on main branch - all 4 jobs pass (Rustfmt, ubuntu, macOS, Windows)
files_changed:
  - Cargo.toml (workspace): added windows-sys dependency
  - crates/solver/Cargo.toml: added [target.'cfg(windows)'.dependencies] with windows-sys
  - crates/solver/src/solver.rs: replaced winapi:: calls with windows_sys::Win32::; fixed HANDLE null check
  - .github/workflows/ci.yml: changed LIB to Z3_LIBRARY_PATH_OVERRIDE pointing to bin/
  - .github/workflows/release.yml: same fix as ci.yml
  - crates/driver/tests/e2e_performance.rs: added .exe extension for Windows binary path; CRLF normalization
  - .gitattributes: created to force LF line endings on all text files
