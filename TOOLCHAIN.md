# Nightly Toolchain Pin

## Pinned Version

| Field        | Value                 |
|--------------|-----------------------|
| Nightly date | `nightly-2026-02-11`  |
| rustc        | 1.95.0-nightly (9e79395f9 2026-02-10) |
| Pin file     | `rust-toolchain.toml` |

The nightly version is pinned to a **specific date** in `rust-toolchain.toml`. This prevents
the Rust compiler from auto-updating to a newer nightly that may break the `rustc_private` API
surface used by the `driver` crate.

## Why Nightly

The `driver` crate uses `#![feature(rustc_private)]` to access the Rust compiler's internal
MIR representation via `rustc_middle`, `rustc_interface`, and `rustc_driver`. This feature
gate is only available on nightly.

**Only the `driver` crate requires nightly.** All other crates (`smtlib`, `macros`, `solver`,
`analysis`) compile on stable Rust (edition 2024, MSRV 1.85.0).

## Required Components

| Component    | Purpose                                             |
|-------------|-----------------------------------------------------|
| `rustc-dev` | Provides `rustc_private` APIs (`rustc_middle`, etc.) |
| `llvm-tools` | Required by `rustc_driver` for LLVM backend         |
| `rust-src`  | IDE support and source-level debugging               |
| `rustfmt`   | Code formatting                                     |
| `clippy`    | Linting                                             |

## How to Update the Nightly Pin

When a new nightly is needed (e.g., for a new rustc API or a bug fix):

1. **Change the date** in `rust-toolchain.toml`:
   ```toml
   [toolchain]
   channel = "nightly-YYYY-MM-DD"
   ```

2. **Fetch the new toolchain**:
   ```bash
   rustup update
   ```

3. **Build the driver crate** (most likely to break):
   ```bash
   cargo build -p rust-fv-driver
   ```

4. **If the build fails**, check the rustc changelog for API changes in:
   - `crates/driver/src/mir_converter.rs` -- MIR type conversion
   - `crates/driver/src/callbacks.rs` -- Compiler callback interface

   Common breakage points:
   - `mir::Rvalue` variants (new variants added, existing ones renamed)
   - `TyKind` variants (type representation changes)
   - `TerminatorKind` variants (control flow changes)
   - `mir::BinOp` variants (arithmetic operation changes)

5. **Run the full test suite**:
   ```bash
   cargo test --workspace
   ```

6. **Run benchmarks** to check for performance regressions:
   ```bash
   cargo bench -p rust-fv-analysis
   ```

7. **Update the compatibility table** below with the new version.

## Stable Crate Compatibility

The following crates compile on **stable Rust** and do not depend on nightly features:

| Crate      | Edition | MSRV   | Notes                          |
|-----------|---------|--------|--------------------------------|
| `smtlib`  | 2024    | 1.85.0 | SMT-LIB AST and formatting    |
| `macros`  | 2024    | 1.85.0 | Proc macro contracts           |
| `solver`  | 2024    | 1.85.0 | Z3 subprocess interface        |
| `analysis`| 2024    | 1.85.0 | IR, VCGen, encoding            |

Only `driver` requires nightly (for `rustc_private`).

## Known Compatible Versions

| Nightly Date       | rustc Version                          | Status | Notes                          |
|-------------------|----------------------------------------|--------|--------------------------------|
| `nightly-2026-02-11` | 1.95.0-nightly (9e79395f9 2026-02-10) | Tested | Initial pin, all 248 tests pass |
