# Technology Stack

**Analysis Date:** 2026-02-10

## Languages

**Primary:**
- Rust 1.85.0 (nightly-2026-02-11) - Entire codebase, formal verification engine
- SMT-LIB2 - Solver communication protocol (text-based)

**Secondary:**
- None detected

## Runtime

**Environment:**
- Rust Compiler (rustc) with rustc_private features
- Native binary execution (no VM/runtime required)

**Package Manager:**
- Cargo (Rust's package manager)
- Lockfile: `Cargo.lock` (present, version 4)

## Frameworks

**Core:**
- `proc-macro2` 1.0.106 - Procedural macro infrastructure for `#[requires]` / `#[ensures]` annotations
- `syn` 2.0.114 - Rust AST parsing (features: full, parsing, printing)
- `quote` 1.0.44 - Code generation from abstract syntax trees

**Compiler Integration:**
- `rustc_driver` (nightly) - Rustc wrapper/hook system for verification callbacks
- `rustc_hir` (nightly) - High-level intermediate representation access
- `rustc_middle` (nightly) - MIR (Mid-Level IR) analysis and type information
- `rustc_session` (nightly) - Compiler session and diagnostics
- `rustc_span` (nightly) - Source code location tracking
- `rustc_abi` (nightly) - ABI information for type layout

**SMT & Verification:**
- Z3 (external process) - SMT solver for automated theorem proving

**Build/Dev:**
- Cargo workspace resolver 2 - Multi-crate project management
- `rustfmt` (nightly) - Code formatting
- `clippy` (nightly) - Linting and code quality
- `rust-src` (nightly) - Source code for introspection
- `llvm-tools` (nightly) - Low-level optimization and code generation

## Key Dependencies

**Critical:**
- `syn` 2.0.114 - Enables parsing of verification annotations; foundational for macro system
- `proc-macro2` 1.0.106 - Mandatory for procedural macro implementation
- `quote` 1.0.44 - Code generation critical for converting specs to verification conditions

**Infrastructure:**
- `unicode-ident` 1.0.23 - Identifier parsing for macro processing

**Compiler Integration:**
- `rustc_driver`, `rustc_middle`, `rustc_hir` - Enable MIR-level verification analysis and rustc hooking via `Callbacks`

## Configuration

**Environment:**
- `RUSTC=/path/to/rust-fv-driver` - Override rustc binary location for verification pipeline
- `RUST_FV_VERIFY` - Environment variable to enable verification mode (alternative: `--rust-fv-verify` CLI flag)
- `RUST_LOG` - Logger initialization (standard rustc env logger)

**Build:**
- `Cargo.toml` (workspace root) - Workspace configuration with 5 members
- `rust-toolchain.toml` - Pinned to nightly channel with specific components
- Edition: 2024 (Rust edition)
- License: MIT OR Apache-2.0

**Z3 Configuration:**
- `SolverConfig` in `crates/solver/src/config.rs` - Auto-detects Z3 binary location:
  - Checks `which z3` in PATH first
  - Falls back to common paths: `/opt/homebrew/bin/z3`, `/usr/local/bin/z3`, `/usr/bin/z3`
  - Supports timeout configuration (milliseconds)
  - Supports custom solver arguments

## Platform Requirements

**Development:**
- macOS/Linux (Homebrew z3 path detected in config)
- Rust nightly toolchain (1.85.0+)
- Z3 binary must be installed and in PATH or common locations
- rustc_private feature support required

**Production:**
- Z3 binary availability (spawned as subprocess via `std::process::Command`)
- Timeout handling for long-running solver queries
- No external network dependencies

---

*Stack analysis: 2026-02-10*
