# Codebase Structure

**Analysis Date:** 2026-02-10

## Directory Layout

```
rust-fv/
├── crates/                          # Multi-crate workspace
│   ├── macros/                      # Procedural macros for specifications
│   │   ├── src/lib.rs              # Macro implementations
│   │   ├── tests/basic.rs          # Macro functionality tests
│   │   └── Cargo.toml
│   ├── smtlib/                      # SMT-LIB2 AST and formatting
│   │   ├── src/
│   │   │   ├── lib.rs              # Public API
│   │   │   ├── sort.rs             # Type representation
│   │   │   ├── term.rs             # Expression representation
│   │   │   ├── command.rs          # SMT-LIB command types
│   │   │   ├── script.rs           # Script composition
│   │   │   └── formatter.rs        # Text generation
│   │   └── Cargo.toml
│   ├── analysis/                    # MIR analysis and VC generation
│   │   ├── src/
│   │   │   ├── lib.rs              # Public API
│   │   │   ├── ir.rs               # Stable IR definition
│   │   │   ├── vcgen.rs            # Verification condition generator
│   │   │   ├── encode_sort.rs      # Type → SMT sort mapping
│   │   │   └── encode_term.rs      # Operation → SMT term encoding
│   │   ├── tests/e2e_verification.rs # Integration tests
│   │   └── Cargo.toml
│   ├── solver/                      # Z3 subprocess interface
│   │   ├── src/
│   │   │   ├── lib.rs              # Public API
│   │   │   ├── solver.rs           # Z3Solver implementation
│   │   │   ├── config.rs           # Solver configuration
│   │   │   ├── error.rs            # Error types
│   │   │   ├── result.rs           # Result type
│   │   │   ├── parser.rs           # Z3 output parsing
│   │   │   └── model.rs            # Model representation
│   │   ├── tests/z3_integration.rs # Z3 solver tests
│   │   └── Cargo.toml
│   └── driver/                      # Rustc driver binary
│       ├── src/
│       │   ├── main.rs             # Entry point
│       │   ├── callbacks.rs        # Rustc callbacks
│       │   └── mir_converter.rs    # MIR → IR conversion
│       └── Cargo.toml
├── docs/                            # Research and design documentation
│   ├── 00-SYNTHESIS.md             # Implementation roadmap
│   ├── formal_verification_research_summary.md
│   ├── compiler-integration-research.md
│   ├── specification-language-research.md
│   ├── proof-automation-strategies.md
│   ├── GIT-HOOKS.md                # Pre-commit/pre-push hook documentation
│   └── README.md                   # Docs index
├── .planning/                       # GSD planning artifacts
│   └── codebase/                   # Architecture and structure docs
├── Cargo.toml                       # Workspace definition
├── Cargo.lock                       # Dependency lock file
├── rust-toolchain.toml             # Rust version specification (1.85.0)
├── README.md                        # Project overview
├── CLAUDE.md                        # AI development guidelines
├── PROGRESS.md                      # Implementation tracker
└── .gitignore
```

## Directory Purposes

**crates/macros:**
- Purpose: Define procedural macros for formal specification attributes
- Contains: Macro implementations for `#[requires]`, `#[ensures]`, `#[pure]`, `#[invariant]`
- Key files: `src/lib.rs`, `tests/basic.rs`
- Responsibility: Parse specification expressions and embed as hidden doc comments without affecting compilation

**crates/smtlib:**
- Purpose: Provide SMT-LIB2 syntax as strongly-typed Rust enums
- Contains: Sorts (type definitions), Terms (expressions), Commands (SMT directives), Scripts (command sequences)
- Key files: `src/term.rs`, `src/sort.rs`, `src/command.rs`, `src/formatter.rs`
- Responsibility: Composable AST construction; display implementation converts to text

**crates/analysis:**
- Purpose: Transform Rust MIR into verification conditions encoded as SMT-LIB scripts
- Contains: Stable IR representation, VC generator, type/operation encoders
- Key files: `src/ir.rs`, `src/vcgen.rs`, `src/encode_sort.rs`, `src/encode_term.rs`
- Responsibility: Complete semantic translation; all output is testable on stable Rust

**crates/solver:**
- Purpose: Interface with Z3 SMT solver via subprocess communication
- Contains: Z3 process spawning, SMT-LIB submission, output parsing
- Key files: `src/solver.rs`, `src/config.rs`, `src/parser.rs`, `src/model.rs`
- Responsibility: Bidirectional communication with Z3; return parsed results

**crates/driver:**
- Purpose: Custom rustc driver that hooks into compilation for formal verification
- Contains: Compiler callback implementation, MIR-to-IR conversion
- Key files: `src/main.rs`, `src/callbacks.rs`, `src/mir_converter.rs`
- Responsibility: Integrate verification into standard `cargo` workflow

**docs/:**
- Purpose: Design documentation and research artifacts
- Contains: Formal verification approaches, compiler integration strategies, specification language research
- Key files: `00-SYNTHESIS.md` (implementation plan), research summaries
- Responsibility: Design rationale and phase planning

## Key File Locations

**Entry Points:**

- `crates/driver/src/main.rs`: Binary entrypoint; reads `RUST_FV_VERIFY` env var, instantiates callbacks, delegates to rustc
- `crates/macros/src/lib.rs`: Procedural macro entry; 4 macros (`requires`, `ensures`, `pure`, `invariant`)
- `crates/analysis/tests/e2e_verification.rs`: E2E test entrypoint; demonstrates complete IR → VC → solver flow

**Configuration:**

- `Cargo.toml`: Workspace manifest; defines 5 crate members and shared dependencies
- `rust-toolchain.toml`: Rust version constraint (1.85.0); ensures unstable API stability
- `docs/00-SYNTHESIS.md`: Implementation phases and feature roadmap
- `CLAUDE.md`: Development guidelines (Rust idioms, TDD, linting requirements)

**Core Logic:**

- `crates/analysis/src/ir.rs`: IR definition — `Function`, `BasicBlock`, `Statement`, `Terminator`, `Rvalue`, `Operand`
- `crates/analysis/src/vcgen.rs`: VC generation algorithm; walks CFG and generates SMT assertions
- `crates/analysis/src/encode_sort.rs`: Rust type → SMT sort mapping (e.g., `i32` → `(_ BitVec 32)`)
- `crates/analysis/src/encode_term.rs`: Operation → SMT term with exact semantics and overflow checks
- `crates/solver/src/solver.rs`: Z3 process management; spawns with `-in`, pipes SMT-LIB, parses results

**Testing:**

- `crates/macros/tests/basic.rs`: 16 tests verifying macro compilation and runtime behavior
- `crates/solver/tests/z3_integration.rs`: 10+ tests for Z3 interaction (SAT, UNSAT, model extraction)
- `crates/analysis/tests/e2e_verification.rs`: Full pipeline tests (IR → VC → Z3)

## Naming Conventions

**Files:**

- Rust source: `snake_case.rs` (e.g., `mir_converter.rs`, `encode_sort.rs`)
- Tests: `{module}_tests/` directory or `tests/{test_name}.rs` for integration tests
- Documentation: `SCREAMING_SNAKE_CASE.md` (e.g., `PROGRESS.md`, `GIT-HOOKS.md`)

**Modules:**

- Crate structure: `crates/{functionality}/src/{module}.rs`
- Visibility: Each crate exposes public API in `lib.rs` or `main.rs`
- Naming: Module names reflect responsibility (e.g., `vcgen` = VC generation, `encode_sort` = sort encoding)

**Types:**

- Structs: `PascalCase` (e.g., `Function`, `BasicBlock`, `Z3Solver`, `VerificationCondition`)
- Enums: `PascalCase` (e.g., `Statement`, `Terminator`, `Term`, `Sort`)
- Constants: `SCREAMING_SNAKE_CASE` (e.g., `Z3_NOT_AVAILABLE`)
- Type aliases: `camelCase` (e.g., `BlockId = usize`)

**Functions:**

- Regular functions: `snake_case` (e.g., `generate_vcs`, `encode_type`, `check_sat`)
- Constructor methods: `new()`, `with_default_config()`, `with_config()`
- Conversion methods: `convert_mir()`, `encode_operand()`
- Query methods: `is_sat()`, `get_model()`

**Variables:**

- Local variables: `snake_case` (e.g., `local_def_id`, `body`, `smtlib`)
- Loop counters: Single letter (e.g., `i`, `idx`) or descriptive (e.g., `block_idx`)
- Temporaries: Prefixed with underscore in IR representation (e.g., `_0`, `_1`, `_2` for rustc MIR locals)

## Where to Add New Code

**New Feature - Analysis Enhancement:**
- Primary code: `crates/analysis/src/{new_module}.rs` (e.g., `loop_invariants.rs`, `ghost_state.rs`)
- Tests: `crates/analysis/tests/e2e_verification.rs` (add test case for new IR constructs)
- Integration: Import and call from `crates/analysis/src/vcgen.rs` in relevant VC generation phase
- Encoding: Extend `crates/analysis/src/encode_term.rs` if new operations need SMT encoding

**New Macro - Specification Annotation:**
- Implementation: Add to `crates/macros/src/lib.rs` as new `#[proc_macro_attribute]` function
- Tests: Add test case to `crates/macros/tests/basic.rs`
- Documentation: Update `crates/macros/src/lib.rs` doc comment with usage example
- Integration: No compiler integration needed — macros attach specs as doc comments for driver to extract

**New Solver Feature:**
- Configuration: Extend `crates/solver/src/config.rs` (e.g., new solver option)
- Interaction: Modify `crates/solver/src/solver.rs` to use new configuration
- Result parsing: Update `crates/solver/src/parser.rs` if Z3 output format changes
- Error handling: Add error variant to `crates/solver/src/error.rs` if needed
- Tests: Add case to `crates/solver/tests/z3_integration.rs`

**New IR Construct:**
- Definition: Add variant to enum in `crates/analysis/src/ir.rs` (e.g., new `Statement` variant)
- MIR conversion: Implement conversion in `crates/driver/src/mir_converter.rs`
- VC generation: Handle in `crates/analysis/src/vcgen.rs`
- SMT encoding: Implement in `crates/analysis/src/encode_term.rs` if it's an operation
- Tests: Add IR construction in `crates/analysis/tests/e2e_verification.rs`

**Shared Utilities:**
- Helper functions: Place in same module as primary user, or create dedicated `utils.rs` if many modules need it
- Type conversions: Implement `From`/`Into` or named conversion functions (e.g., `to_smt_term()`)
- Location: `crates/analysis/src/utils.rs` or `crates/smtlib/src/utils.rs` depending on scope

## Special Directories

**crates/driver:**
- Purpose: Integrates with rustc unstable API
- Generated: `target/debug/rust-fv-driver` binary after `cargo build`
- Committed: Source code committed; binary generated at build time
- Coupling: Directly depends on `rustc_driver`, `rustc_middle`, `rustc_hir` (changes with Rust versions)

**target/:**
- Purpose: Build artifacts (compiled binaries, intermediate objects)
- Generated: Yes (automatically from `cargo build`)
- Committed: No (in `.gitignore`)
- Note: `target/debug/rust-fv-driver` is the produced driver binary to use as `RUSTC=/path/to/...`

**.planning/codebase/:**
- Purpose: GSD-managed codebase documentation (architecture, structure, conventions, testing, concerns)
- Generated: By GSD mapping tools
- Committed: Yes (part of planning artifacts)
- Note: Used by `/gsd:plan-phase` and `/gsd:execute-phase` to understand codebase patterns

**docs/:**
- Purpose: Research artifacts and design documentation
- Generated: Manual authorship (not generated)
- Committed: Yes (reference material)
- Organization: Prefixed with numbers (00-, 01-, etc.) for reading order; `README.md` as index

---

*Structure analysis: 2026-02-10*
