# External Integrations

**Analysis Date:** 2026-02-10

## APIs & External Services

**SMT Solver:**
- Z3 Theorem Prover - Automated satisfiability checking for verification conditions
  - SDK/Client: Subprocess invocation via `std::process::Command`
  - Communication: SMT-LIB2 text protocol over stdin/stdout
  - Location: `crates/solver/src/solver.rs` (`Z3Solver` struct)
  - Configuration: `crates/solver/src/config.rs`

**Rustc Compiler (Private Internal API):**
- Integration point: `RUSTC` environment variable override
- Callback mechanism: `rustc_driver::Callbacks` trait implementation
- Hook point: `after_analysis` phase (post-MIR generation)
- Location: `crates/driver/src/callbacks.rs`

## Data Storage

**Databases:**
- None detected

**File Storage:**
- Local filesystem only - No cloud/remote storage integrations

**Caching:**
- None detected (Z3 results not persisted between invocations)

**Temporary Files:**
- Build artifacts in `target/` directory

## Authentication & Identity

**Auth Provider:**
- None detected - Tool operates without authentication/authorization

**Identity:**
- GitHub repository: https://github.com/o2alexanderfedin/rust-fv
- No auth required for local execution

## Monitoring & Observability

**Error Tracking:**
- None detected - Error handling via Rust `Result` types
- Errors propagated through `SolverError` enum in `crates/solver/src/error.rs`

**Logs:**
- `rustc_driver::init_rustc_env_logger()` - Standard rustc logging via `RUST_LOG` environment variable
- Solver stderr/stdout captured but not logged to external systems
- Location: `crates/driver/src/main.rs`

## CI/CD & Deployment

**Hosting:**
- GitHub repository (no specific hosting platform for binaries)

**CI Pipeline:**
- Not detected - No `.github/workflows/` or similar CI configuration
- Git hooks in place:
  - Pre-commit: `rustfmt`, `clippy`, `cargo check`, git flow enforcement
  - Pre-push: Full test suite (`cargo test`)

## Environment Configuration

**Required env vars:**
- `RUSTC` - Path to rust-fv-driver binary (for verification integration with cargo)
- Optional: `RUST_FV_VERIFY` - Enable verification mode (can use CLI flag `--rust-fv-verify` instead)
- Optional: `RUST_LOG` - Logger verbosity (standard rustc logging)

**Z3 Discovery:**
- Automatic detection via `which z3`
- Fallback paths checked:
  - `/opt/homebrew/bin/z3` (Homebrew macOS)
  - `/usr/local/bin/z3` (Unix standard)
  - `/usr/bin/z3` (Linux standard)
- Manual override via `SolverConfig::new(path)`

**Secrets location:**
- None - No API keys or credentials required

## Webhooks & Callbacks

**Incoming:**
- Rustc compilation callbacks via `rustc_driver::Callbacks` trait
- Callback method: `after_analysis(compiler)` - Invoked after type checking and MIR generation

**Outgoing:**
- Z3 subprocess communication:
  - SMT-LIB2 text written to Z3 stdin
  - Results read from Z3 stdout/stderr
  - Location: `crates/solver/src/solver.rs` lines 55-102

## Z3 Solver Integration Details

**Process Management:**
- Z3 spawned as subprocess for each verification task
- Communication: Pipe-based (stdin for commands, stdout/stderr for results)
- Process closure: Waits for Z3 completion via `wait_with_output()`

**Command Format:**
- Standard Z3 flags: `-in` (interactive mode), `-t:{timeout_ms}` (timeout), custom arguments
- Timeout mechanism: Configurable per `SolverConfig`, checked in stderr
- Error detection: Timeout responses checked in both stdout and stderr

**Result Parsing:**
- Parser: `crate::parser::parse_solver_output()` in `crates/solver/src/parser.rs`
- Result types: `SolverResult` enum (Sat with model, Unsat, Unknown)
- Model extraction: Text parsing of Z3's `(get-model)` output

**Test Coverage:**
- Integration tests: `crates/solver/tests/z3_integration.rs`
- Tests verify: SAT/UNSAT correctness, bitvector handling, model extraction
- Requirement: Z3 must be installed; tests skip gracefully if unavailable

---

*Integration audit: 2026-02-10*
