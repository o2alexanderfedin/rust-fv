# Coding Conventions

**Analysis Date:** 2026-02-10

## Naming Patterns

**Files:**
- Snake case for all `.rs` files: `solver.rs`, `vcgen.rs`, `parser.rs`
- Test files: suffixed with `_test.rs` or placed in `tests/` directory as integration tests
- Module names match file names exactly: `mod solver;` for file `solver.rs`

**Functions:**
- Snake case: `generate_vcs`, `parse_solver_output`, `encode_term`, `with_timeout`
- Public API functions documented with doc comments starting with `///`
- Private helper functions can have simpler names but follow snake case consistently

**Variables:**
- Snake case: `z3_path`, `timeout_ms`, `param_sorts`, `return_local`
- Meaningful names preferred over abbreviations: `declarations` not `decls`, `assignments` not `assigns`
- Local mutable state cleared with scope: seen in `format_script`, `format_command` using `&mut String` pattern

**Types:**
- PascalCase for structs: `SolverConfig`, `Z3Solver`, `VerificationCondition`, `Function`, `Local`
- PascalCase for enums: `SolverError`, `SolverResult`, `Terminator`, `Statement`
- PascalCase for traits: (not prevalent in codebase)
- Type parameters: single letter uppercase (seen in generic contexts)

**Constants:**
- SCREAMING_SNAKE_CASE: `Z3_COMMON_PATHS`

## Code Style

**Formatting:**
- Rustfmt enforced via toolchain component (specified in `rust-toolchain.toml`)
- Edition: 2024 (workspace-wide setting in `Cargo.toml`)
- Line length: default rustfmt (100 chars, observed in code)
- 4-space indentation (Rust standard)

**Linting:**
- Clippy enabled in `rust-toolchain.toml`
- No `.clippy.toml` or custom configuration observed
- Default clippy rules applied
- Code passes clippy without exceptions

## Import Organization

**Order:**
1. Standard library imports (`use std::`)
2. External crate imports (workspace members, third-party)
3. Internal module imports (same crate)

**Examples from codebase:**

```rust
// solver.rs:
use std::io::Write;
use std::process::{Command, Stdio};

use rust_fv_smtlib::script::Script;

use crate::config::SolverConfig;
use crate::error::SolverError;
use crate::parser::parse_solver_output;
use crate::result::SolverResult;
```

```rust
// error.rs:
use std::fmt;
use std::path::PathBuf;

// (no external, uses only std and std::error::Error trait)

impl std::error::Error for SolverError {}
```

**Path Aliases:**
- No path aliases configured (no `[workspace.resolver]` aliases found)
- Absolute module paths used: `crate::`, `rust_fv_*::` prefixes for workspace crates

## Error Handling

**Patterns:**
- Custom error enum per crate: `SolverError` in `crates/solver/src/error.rs`
- Error variants with context: `NotFound(PathBuf)`, `ProcessError(String)`, `ParseError(String)`
- Display implementation for user-facing error messages
- `std::error::Error` trait implementation for integration with `?` operator
- PartialEq implementation on errors for testing assertions

**Error propagation:**
- Uses `Result<T, Error>` return types consistently
- `?` operator used for early returns: seen in `solver.rs` check_sat_raw
- `map_err` used to contextualize errors with additional information
- Error variants chosen to provide specific information about failure point

**Examples:**

```rust
// From solver.rs - propagating with context:
.spawn()
.map_err(|e| SolverError::ProcessError(format!("Failed to start Z3: {e}")))?

// From config.rs - validation pattern:
pub fn validate(&self) -> Result<(), SolverError> {
    if !self.z3_path.exists() {
        return Err(SolverError::NotFound(self.z3_path.clone()));
    }
    Ok(())
}
```

## Logging

**Framework:** No logging framework (println!, eprintln! for diagnostics)

**Patterns:**
- Error context printed to stderr via `eprintln!` for skipped tests: `eprintln!("Skipping test -- Z3 not available: {e}");`
- No systematic logging library (tracing, log, etc.) integrated
- Test output uses standard assertions only

## Comments

**When to Comment:**
- Module-level documentation: `//!` at crate/module start (mandatory for public APIs)
- Public items: `///` doc comments explaining purpose, parameters, return values
- Complex logic: inline comments explain "why" not "what"
- Test helpers: documented with `///` explaining test setup

**JSDoc/TSDoc:**
- Rust uses `///` for doc comments (CommonMark format)
- Patterns observed:

```rust
/// Check satisfiability of a Script.
///
/// Formats the script to SMT-LIB2 text using `Display`, appends `(check-sat)`
/// and `(get-model)` if not already present, and runs Z3.
pub fn check_sat(&self, script: &Script) -> Result<SolverResult, SolverError> {
```

- Code examples in doc comments using ` ```no_run ` for untestable examples
- Backticks for `Item` references in documentation

## Function Design

**Size:**
- Small, focused functions preferred
- Typical range: 10-50 lines
- Large functions broken into helpers (e.g., `format_script` delegates to `format_command`, `format_sort`, `format_term`)

**Parameters:**
- Pass references when possible: `&Script`, `&str`, `&Path`
- Mutable references for output: `&mut String` pattern for building formatted output
- Builder pattern for optional configuration: `SolverConfig::new().with_timeout().with_extra_args()`

**Return Values:**
- Explicit `Result<T, E>` for fallible operations
- `Option<T>` for queries that may not find values
- Tuple returns rare; struct wrapping preferred when multiple values needed
- Default trait implementation when sensible: `impl Default for Model { fn default() -> Self { Self::new() } }`

## Module Design

**Exports:**
- Re-exports at crate root (`lib.rs`) for primary types:

```rust
// From solver/src/lib.rs:
pub use config::SolverConfig;
pub use error::SolverError;
pub use model::Model;
pub use result::SolverResult;
pub use solver::Z3Solver;
```

- Private modules: `mod parser;` without pub keyword for internal-only modules
- Public submodules: `pub mod encode_sort;` for modules meant to be accessed

**Barrel Files:**
- Not used in this codebase
- Each module is either a file or a directory with `lib.rs` (workspace structure)
- Crates expose top-level modules, not intermediate barrels

## Type System & Safety

**Strong typing:**
- Enum types for domain concepts: `SolverResult` (Sat/Unsat/Unknown), `Statement`, `Terminator`
- Newtype patterns for semantic distinction: `BlockId = usize`
- Type-driven design: `Place` struct for l-values, `Operand` enum for rvalues
- No generic abuse; generics used sparingly and only for clear abstractions

**Traits:**
- Debug and Clone derived universally for testability
- PartialEq for test assertions
- Display for error messages and user output
- Default for sensible defaults (Model, contracts)
- Error trait for error handling integration

## Testing Helpers

**Test module structure:**
- Tests placed in `#[cfg(test)] mod tests { }` at end of file or in `tests/` directory
- Helper functions prefixed with context: `make_solver()`, `make_add_function()`, `script_to_smtlib()`
- Assertions use standard `assert!`, `assert_eq!`, `assert_ne!`

**Test naming:**
- Descriptive names showing intent: `test_overflow_verification_unconstrained_add`, `raw_simple_sat`
- Tests organized by behavior blocks with comments: `// ---- Helper ----`, `// ============ Test 1 ============`

---

*Convention analysis: 2026-02-10*
