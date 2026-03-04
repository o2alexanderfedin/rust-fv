---
status: verifying
trigger: "readme-accuracy-audit"
created: 2026-02-27T00:00:00Z
updated: 2026-03-03T00:00:00Z
---

## Current Focus

hypothesis: README.md was missing v0.6/v0.7 features and three macros (infer_summary, override_contract, extend_contract)
test: Cross-checked README against all source files in crates/macros, crates/analysis, crates/driver, crates/solver
expecting: README now accurately reflects all implemented capabilities
next_action: Request human verification

## Symptoms

expected: README.md accurately describes the rust-fv project's actual capabilities, architecture, usage, and status
actual: README.md may contain stale, inaccurate, or missing information compared to what is actually implemented
errors: N/A - documentation accuracy issue
reproduction: Compare README.md claims against actual source code, tests, and build system
timeline: Unknown - documentation may have drifted from implementation over time

## Eliminated

- hypothesis: README is completely accurate
  evidence: Multiple discrepancies found between README claims and actual implementation
  timestamp: 2026-02-27

## Evidence

- timestamp: 2026-03-03
  checked: crates/macros/src/lib.rs for all exported proc macros
  found: Three macros not in README - infer_summary (line 681), override_contract (line 726), extend_contract (line 745)
  implication: README annotations section was incomplete

- timestamp: 2026-03-03
  checked: crates/analysis/src/ for v0.6 and v0.7 features
  found: monomorphize.rs (MonomorphizationRegistry), behavioral_subtyping.rs (SubtypingVc), trait_analysis.rs (TraitDatabase, sealed trait detection), encode_prophecy.rs (FnMut closure prophecies), call_graph.rs (cross-crate SCC via from_functions_with_cross_crate_db), ownership.rs (OwnershipKind classification), encode_quantifier.rs (trigger inference), differential.rs (bv2int equivalence testing), contract_db.rs (AliasPrecondition, FunctionSummary with is_inferred)
  implication: Many v0.6/v0.7 features existed in code but were not reflected in README advanced analysis section

- timestamp: 2026-03-03
  checked: Cargo.toml license field
  found: license-file = "LICENSE" (pointing to CC BY-NC-ND 4.0), dual license section in README is accurate
  implication: License section is correct (was changed from MIT to dual license since original audit)

- timestamp: 2026-03-03
  checked: vcgen.rs for OpaqueCallee and dyn dispatch
  found: VcKind::OpaqueCallee, VcKind::OpaqueCalleeUnsafe, parse_dyn_dispatch_callee function, extensive test coverage
  implication: Cross-crate opaque callee diagnostics with dyn dispatch resolution are fully implemented

- timestamp: 2026-02-27
  checked: Cargo.toml workspace
  found: Workspace has 5 crates (smtlib, macros, solver, analysis, driver). No "e2e-bench" in workspace members. License is "MIT OR Apache-2.0" not TBD.
  implication: README says "License: TBD" but Cargo.toml already has MIT OR Apache-2.0

- timestamp: 2026-02-27
  checked: rust-toolchain.toml
  found: channel = "nightly-2026-02-11" - requires ALL crates to be on nightly (driver uses rustc_private features)
  implication: README says "Only the driver crate requires nightly. All other crates compile on stable Rust 1.85+" - this is inaccurate for building from source; in practice the pinned nightly is used workspace-wide

- timestamp: 2026-02-27
  checked: crates/macros/src/lib.rs
  found: Macros implemented: requires, ensures, pure, invariant, decreases, borrow_ensures, ghost, unsafe_requires, unsafe_ensures, trusted, lock_invariant, verify (concurrent), fn_spec, state_invariant, ghost_predicate
  implication: README annotations table is incomplete - missing: borrow_ensures, unsafe_requires, unsafe_ensures, trusted, lock_invariant, verify(concurrent), fn_spec, ghost_predicate

- timestamp: 2026-02-27
  checked: crates/driver/Cargo.toml
  found: Both "rust-fv-driver" and "cargo-verify" binaries are built from the same src/main.rs
  implication: Installation instruction "cargo install --path crates/driver" produces cargo-verify binary correctly

- timestamp: 2026-02-27
  checked: crates/driver/src/cargo_verify.rs
  found: Actual CLI flags: --timeout, --output-format, --fresh, --jobs, --no-stdlib-contracts, --verbose, --message-format, --bv2int, --bv2int-report, --bv2int-threshold, clean, --help, --version
  implication: README shows --package flag but code only passes unknown args through to cargo check directly. README shows "cargo verify clean" - confirmed correct.

- timestamp: 2026-02-27
  checked: crates/driver/src/main.rs
  found: RUSTC env var + RUST_FV_VERIFY env var is correct. Comment says "cargo fv check" as future command name, not "cargo verify" - but actual code checks args[1] == "verify", so "cargo verify" is what's implemented.
  implication: README says RUSTC and RUST_FV_VERIFY which is correct

- timestamp: 2026-02-27
  checked: crates/solver/src/config.rs + backend.rs
  found: Supports Z3 (native API via z3-native feature, default), CVC5 (CLI), and Yices2 (CLI)
  implication: README only mentions Z3. CVC5 and Yices are also supported backends.

- timestamp: 2026-02-27
  checked: crates/analysis/src/lib.rs + source files
  found: Has concurrency verification (RC11 weak memory model, deadlock detection, channel verification, happens-before), async verification, lifetime analysis, separation logic, float verification, closure/HOF analysis, unsafe code analysis, stdlib contracts (Vec, HashMap, Option, Result, String, Iterator)
  implication: README "How Verification Works" section doesn't mention any of these advanced features

- timestamp: 2026-02-27
  checked: vscode-extension/ directory
  found: Directory exists with package.json, src/, dist/, compiled .vsix file (rust-fv-0.1.0.vsix)
  implication: README mentions VSCode extension, which is correct - "See vscode-extension/ for installation instructions"

- timestamp: 2026-02-27
  checked: Cargo.toml workspace.package.license
  found: "MIT OR Apache-2.0"
  implication: README License section says "TBD" - this is wrong

## Resolution

root_cause: README has these inaccuracies:
  1. License says "TBD" - should be "MIT OR Apache-2.0"
  2. Annotations table is incomplete - missing borrow_ensures, unsafe_requires, unsafe_ensures, trusted, lock_invariant, verify(concurrent), fn_spec, ghost_predicate
  3. Only mentions Z3 as solver - CVC5 and Yices are also supported
  4. Stable Rust claim is misleading - workspace uses pinned nightly for all crates
  5. Missing --no-stdlib-contracts, --bv2int, --bv2int-report, --bv2int-threshold flags
  6. Advanced analysis capabilities not mentioned at all (concurrency, async, floats, closures, unsafe, stdlib contracts)
  7. Import path in examples uses "rust_fv_macros" (with underscore) but crate name is "rust-fv-macros" (with hyphens) - this is correct Rust crate name mangling

fix: |
  1. Added missing "Cross-crate and stdlib contract annotations" table with infer_summary, override_contract, extend_contract
  2. Expanded "Advanced analysis capabilities" section to include: cross-crate verification, monomorphization, ownership-aware reasoning, quantifier trigger inference, call graph analysis, differential testing, and details for traits/closures/recursion
  3. Updated solver invocation description to mention CVC5/Yices alongside Z3
  4. Updated workspace structure description for analysis crate
verification: cargo check passes; README cross-checked against all source files in crates/macros/src/lib.rs, crates/analysis/src/*.rs, crates/driver/src/cargo_verify.rs, crates/solver/src/config.rs
files_changed: [README.md]
