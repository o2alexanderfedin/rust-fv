# Rust Formal Verification

Formal verification as a Rust compiler plugin. Verification happens **during compilation** — annotate your functions, run `cargo verify`, and get mathematical proof (or a counterexample) without leaving your normal build workflow.

## How It Works

`rust-fv` hooks into the Rust compiler (`rustc`) at the `after_analysis` phase. When you run `cargo verify`, it replaces `rustc` with the `rust-fv-driver` binary, which:

1. Compiles your crate normally (type checking, borrow checking — all standard)
2. At the end of compilation, extracts annotated functions as SMT-LIB2 constraints
3. Submits them to Z3 (or CVC5 / Yices) and reports results alongside your build output

**Verification is not a separate step** — it runs as part of `cargo check`.

## Quick Start

### 1. Prerequisites

- Nightly Rust (pinned — see `rust-toolchain.toml`)
- [Z3](https://github.com/Z3Prover/z3) installed and on `PATH`

```bash
# Install Z3 (macOS)
brew install z3

# Install Z3 (Ubuntu/Debian)
apt-get install z3
```

### 2. Build the driver

```bash
cargo build -p rust-fv-driver --release
```

### 3. Install as a cargo subcommand

```bash
# Option A: install to ~/.cargo/bin (permanent)
cargo install --path crates/driver

# Option B: use from build output directly (for development)
alias cargo-verify="./target/release/cargo-verify"
```

### 4. Add annotations to your code

```rust
use rust_fv_macros::{requires, ensures, pure};

#[requires(x > 0)]
#[ensures(result > x)]
fn increment(x: i32) -> i32 {
    x + 1
}

#[pure]
#[requires(n >= 0)]
#[ensures(result >= 0)]
fn abs_val(n: i32) -> i32 {
    if n < 0 { -n } else { n }
}
```

### 5. Run verification

```bash
cargo verify
```

Verification runs **during compilation**. Output appears alongside your normal build output:

```
Verifying my-crate (src/lib.rs)
  [OK]      increment — all conditions verified
  [OK]      abs_val — all conditions verified

2 functions verified, 0 failed (1.2s)
```

If a postcondition fails, you get a typed counterexample:

```
  [FAIL]    increment
            Postcondition: result > x
            Counterexample: x: i32 = 2147483647
```

## Running Verification

`cargo verify` is the primary command. It wraps `cargo check` with the `rust-fv-driver` as the compiler, so **verification is always compilation**.

```bash
# Verify the current crate (default)
cargo verify

# Verify a specific package in a workspace
cargo verify --package my-lib

# Force re-verification (bypass cache)
cargo verify --fresh

# Set timeout per function in seconds (default: 30s)
cargo verify --timeout 60

# Parallel verification threads (default: num_cpus/2)
cargo verify --jobs 4

# JSON output for IDE / CI integration
cargo verify --output-format json

# Rust-analyzer compatible diagnostics (for IDE inline errors)
cargo verify --message-format json

# Show per-function timing
cargo verify --verbose

# Skip stdlib contracts (Vec, HashMap, Option, etc.)
cargo verify --no-stdlib-contracts

# Enable bitvector-to-integer translation (may improve performance)
cargo verify --bv2int

# Report which functions used bv2int translation
cargo verify --bv2int-report

# Set bv2int threshold (default: 64)
cargo verify --bv2int-threshold 32

# Clear the verification cache
cargo verify clean
```

### Environment variable alternative

If you need to run verification in a CI environment without installing the subcommand:

```bash
RUSTC=/path/to/rust-fv-driver RUST_FV_VERIFY=1 cargo check
```

This is equivalent to `cargo verify` — the subcommand sets these variables automatically. Additional env vars:

| Variable | Description |
|----------|-------------|
| `RUST_FV_VERIFY` | Enable verification mode (any non-empty value) |
| `RUST_FV_TIMEOUT` | Timeout in seconds per function |
| `RUST_FV_OUTPUT_FORMAT` | `json` for structured output, otherwise text |
| `RUST_FV_FRESH` | Bypass cache (any non-empty value) |
| `RUST_FV_JOBS` | Number of parallel verification threads |
| `RUST_FV_VERBOSE` | Show per-function timing (any non-empty value) |
| `RUST_FV_NO_STDLIB_CONTRACTS` | Disable stdlib contracts (any non-empty value) |
| `RUST_FV_BV2INT` | Enable bv2int translation (any non-empty value) |
| `RUST_FV_BV2INT_REPORT` | Report bv2int usage (any non-empty value) |
| `RUST_FV_BV2INT_THRESHOLD` | Bv2int bit-width threshold |

## Annotations

All annotations come from the `rust-fv-macros` crate. Add it as a dependency:

```toml
[dependencies]
rust-fv-macros = { path = "path/to/rust-fv-macros" }
```

### Core contract annotations

| Annotation | Meaning |
|-----------|---------|
| `#[requires(expr)]` | Precondition — must hold at the call site |
| `#[ensures(expr)]` | Postcondition — must hold when the function returns; use `result` for the return value |
| `#[pure]` | Function has no side effects (enables use in specifications) |
| `#[invariant(expr)]` | Loop or data structure invariant |
| `#[decreases(expr)]` | Termination measure for recursive functions |

### Mutable borrow annotations

| Annotation | Meaning |
|-----------|---------|
| `#[borrow_ensures(param, expr)]` | Postcondition on a mutable reference parameter's final value; use `old(*param)` for the pre-call value |

### Ghost code annotations

| Annotation | Meaning |
|-----------|---------|
| `#[ghost]` | Ghost variable or function — exists only in specifications, erased from compiled code |
| `#[ghost_predicate]` | Ghost predicate for separation logic specs; may be recursive (unfolded to depth 3) |

### Unsafe code annotations

| Annotation | Meaning |
|-----------|---------|
| `#[unsafe_requires(expr)]` | Safety precondition for an unsafe function (memory safety, not just logical correctness) |
| `#[unsafe_ensures(expr)]` | Safety postcondition for an unsafe function |
| `#[trusted]` | Mark a function as manually verified; body is skipped, call-site contracts are still checked |

### Async annotations

| Annotation | Meaning |
|-----------|---------|
| `#[state_invariant(expr)]` | Holds at every `.await` suspension and resumption point in an `async fn` |

### Concurrency annotations

| Annotation | Meaning |
|-----------|---------|
| `#[lock_invariant(expr)]` | Predicate that must hold whenever a mutex/rwlock is acquired or released |
| `#[verify(concurrent)]` | Enable bounded concurrency verification (optional params: `threads = N`, `switches = M`) |

### Higher-order function annotations

| Annotation | Meaning |
|-----------|---------|
| `#[fn_spec(f, \|x\| pre => post)]` | Contract for a closure parameter: for all `x` satisfying `pre`, `f(x)` satisfies `post` |

### Specification expressions

Expressions inside annotations are standard Rust expressions, with access to function parameters and (in `#[ensures]`) the special `result` binding:

```rust
#[requires(v.len() > 0)]
#[ensures(result < v.len())]
fn find_min_idx(v: &[i32]) -> usize { ... }

#[requires(divisor != 0)]
#[ensures(result * divisor + remainder == dividend)]
fn div_rem(dividend: i32, divisor: i32) -> (i32, i32) { ... }
```

## IDE Integration

The VSCode extension shows verification results inline as you save:

- Green gutter icons for verified functions
- Red gutter icons with counterexample values for failures
- Output panel with full verification report

See `vscode-extension/` for installation instructions. A pre-built `.vsix` package is available at `vscode-extension/rust-fv-0.1.0.vsix`.

For rust-analyzer integration (inline diagnostics without the extension):

```bash
cargo verify --message-format json
```

## How Verification Works

Verification runs as a compiler plugin — it is **not** a separate tool or external pass:

1. **Annotation expansion**: `#[requires]`/`#[ensures]` macros embed specifications as hidden doc attributes. The function body is unchanged.
2. **Compiler hook**: After Rust type-checking and borrow-checking, the driver's `after_analysis` callback fires.
3. **MIR extraction**: The function's MIR (Mid-level IR) is converted to a stable `ir::Function` representation.
4. **SMT constraint generation**: Two independent constraint sets are produced and concatenated:
   - **Set A** (code-inferred): Derived from the code AST — overflow safety, division-by-zero absence, etc.
   - **Set B** (annotation-derived): Derived from `#[requires]`/`#[ensures]` contracts.
5. **Solver invocation**: The combined constraint list is submitted to Z3. No client-side deduplication or contradiction checking — the solver handles everything.
6. **Result reporting**: `UNSAT` → verified. `SAT` → counterexample extracted and reported with typed Rust values.

### Advanced analysis capabilities

The `analysis` crate includes:

- **Concurrency verification**: RC11 weak memory model, deadlock detection, lock invariants, channel verification, happens-before tracking
- **Async/await verification**: State invariant checking at suspension points via `#[state_invariant]`
- **Separation logic**: Heap model, ownership constraints, separation logic integration
- **Closure and higher-order functions**: Defunctionalization, HOF verification condition generation
- **Recursion / termination**: Decreases-clause verification for recursive functions
- **Unsafe code**: Safety precondition checking for unsafe functions
- **Floating-point**: Float verification with dedicated encoding
- **Stdlib contracts**: Built-in contracts for `Vec`, `HashMap`, `Option`, `Result`, `String`, `Iterator`
- **Trait verification**: Behavioral subtyping for trait implementations
- **Bitvector-to-integer translation**: Optional `--bv2int` mode for better solver performance

## Caching

Verification results are cached in `target/verify-cache/`. Cache keys are SHA-256 hashes of the function name, all contracts, and the MIR representation. On subsequent runs, functions whose source hasn't changed reuse cached results and show as `[SKIP]`. Use `--fresh` to bypass the cache, or `cargo verify clean` to delete it.

## Requirements

| Requirement | Details |
|------------|---------|
| Rust toolchain | Nightly (pinned in `rust-toolchain.toml`, currently `nightly-2026-02-11`) |
| Z3 | Any recent version; auto-detected from `PATH` or common install locations |
| OS | macOS, Linux (Windows untested) |

> **Note:** The entire workspace is built with the pinned nightly toolchain. The `driver` crate requires nightly for `rustc_private` access; the other crates (`smtlib`, `macros`, `solver`, `analysis`) use only stable APIs but are built with the same pinned toolchain for consistency.

## Supported SMT Solvers

| Solver | Integration | Notes |
|--------|-------------|-------|
| Z3 | Native API (default) or CLI subprocess | Auto-detected from PATH; homebrew path also checked |
| CVC5 | CLI subprocess | Optional; must be installed separately |
| Yices2 | CLI subprocess | Optional; must be installed separately |

The default backend uses Z3's native API (via the `z3-native` feature, enabled by default) for best performance. To use Z3 as a subprocess or to use CVC5/Yices, the solver backend is selected automatically based on availability.

## Workspace Structure

| Crate | Description |
|-------|-------------|
| `rust-fv-macros` | Procedural macros for annotations (`#[requires]`, `#[ensures]`, etc.) |
| `rust-fv-smtlib` | SMT-LIB2 AST and formatter (sorts, terms, commands, scripts) |
| `rust-fv-solver` | SMT solver interface (Z3 native API + CLI backends for Z3/CVC5/Yices) |
| `rust-fv-analysis` | VCGen, IR, encoding, concurrency, closures, stdlib contracts |
| `rust-fv-driver` | `rustc` driver + `cargo-verify` subcommand |

## License

**Dual License Model**

| Use Case | License |
|----------|---------|
| Non-commercial (research, personal, academic) | [CC BY-NC-ND 4.0](LICENSE) |
| Commercial, OEM, SaaS, derivative works | [Commercial License](LICENSE-COMMERCIAL) |

For non-commercial use: free under [Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International](https://creativecommons.org/licenses/by-nc-nd/4.0/).
This means you may use and share the software with attribution, but may **not** use it commercially, nor re-engineer, re-implement, or distribute modified versions.

For commercial licensing, contact:
**Hupyy, Inc.** — [sales@hupyy.com](mailto:sales@hupyy.com)

Copyright © 2026 Alex Fedin, Hupyy, Inc.
