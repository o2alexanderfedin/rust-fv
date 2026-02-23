# Rust Formal Verification

Formal verification as a Rust compiler plugin. Verification happens **during compilation** — annotate your functions, run `cargo verify`, and get mathematical proof (or a counterexample) without leaving your normal build workflow.

## How It Works

`rust-fv` hooks into the Rust compiler (`rustc`) at the `after_analysis` phase. When you run `cargo verify`, it replaces `rustc` with the `rust-fv-driver` binary, which:

1. Compiles your crate normally (type checking, borrow checking — all standard)
2. At the end of compilation, extracts annotated functions as SMT-LIB2 constraints
3. Submits them to Z3 and reports results alongside your build output

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
alias cargo-verify="./target/release/rust-fv-driver"
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

# Set timeout per function (default: 30s)
cargo verify --timeout 60

# Parallel verification threads (default: num_cpus/2)
cargo verify --jobs 4

# JSON output for IDE / CI integration
cargo verify --output-format json

# Rust-analyzer compatible diagnostics (for IDE inline errors)
cargo verify --message-format json

# Show per-function timing
cargo verify --verbose

# Clear the verification cache
cargo verify clean
```

### Environment variable alternative

If you need to run verification in a CI environment without installing the subcommand:

```bash
RUSTC=/path/to/rust-fv-driver RUST_FV_VERIFY=1 cargo check
```

This is equivalent to `cargo verify` — the subcommand sets these variables automatically.

## Annotations

All annotations come from the `rust-fv-macros` crate. Add it as a dependency:

```toml
[dependencies]
rust-fv-macros = { path = "path/to/rust-fv-macros" }
```

| Annotation | Meaning |
|-----------|---------|
| `#[requires(expr)]` | Precondition — must hold at the call site |
| `#[ensures(expr)]` | Postcondition — must hold when the function returns; use `result` for the return value |
| `#[pure]` | Function has no side effects (enables use in specifications) |
| `#[invariant(expr)]` | Loop or data structure invariant |
| `#[decreases(expr)]` | Termination measure for recursive functions |
| `#[ghost]` | Ghost variable — exists only in specifications, erased from compiled code |
| `#[state_invariant(expr)]` | Holds at every `.await` suspension and resumption point in an `async fn` |

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

See `vscode-extension/` for installation instructions.

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

## Caching

Verification results are cached in `target/verify-cache/`. On subsequent runs, functions whose source hasn't changed reuse cached results and show as `[SKIP]`. Use `--fresh` to bypass the cache, or `cargo verify clean` to delete it.

## Requirements

| Requirement | Details |
|------------|---------|
| Rust toolchain | Nightly (pinned in `rust-toolchain.toml`) |
| Z3 | Any recent version; auto-detected from `PATH` |
| OS | macOS, Linux (Windows untested) |

Only the `driver` crate requires nightly. All other crates (`smtlib`, `macros`, `solver`, `analysis`) compile on stable Rust 1.85+.

## License

TBD
