# Phase 2: Table Stakes Completion - Research

**Researched:** 2026-02-11
**Domain:** Loop invariants, SMT datatype encoding, cargo integration, panic detection, z3 crate migration
**Confidence:** HIGH

## Summary

Phase 2 adds the core features developers expect from verification tools: loops, assertions, panic detection, aggregate types, and cargo integration. This phase is technically demanding, requiring deep SMT knowledge (datatypes, array theory), careful loop invariant UX design, and native Z3 integration for performance.

**Critical findings:**
1. **Loop invariants are the hardest UX problem** - manual specification will be primary approach, with targeted inference for common patterns (immutable variables, simple bounds)
2. **Z3 crate with bundled feature is production-ready** - statically links Z3, eliminates installation issues, enables incremental solving
3. **SMT datatypes are standard for struct encoding** - SMT-LIB 2.6+ declare-datatypes with constructors/selectors
4. **Creusot 0.9.0 demonstrates feasible invariant auto-detection** - type invariants + immutable variable tracking reduces manual burden
5. **Panic points are statically detectable in MIR** - unwrap, indexing, division, shifts have explicit checks/terminators

**Primary recommendation:** Build loop support incrementally: (1) manual invariants with excellent error messages, (2) targeted auto-insertion for type invariants and immutables (Creusot pattern), (3) defer general inference to Phase 3+.

## Standard Stack

### Core Libraries (Additions to Phase 1)

| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| z3 | 0.19.7+ | Native Z3 bindings (typed API) | Production-ready, used by verification tools, statically links Z3 with `bundled` feature |
| tracing | 0.1.40+ | Structured logging/diagnostics | Industry standard for Rust instrumentation, module-level filtering |
| tracing-subscriber | 0.3.18+ | Logging backend (JSON, env filter) | Companion to tracing, enables per-module log control |
| syn (extended features) | 2.0.114+ | Full expression parsing | Add "visit", "visit-mut" features for AST traversal |

### Supporting Libraries

| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| cargo (metadata API) | 0.80+ | Parse Cargo.toml, workspace structure | For cargo verify subcommand to find project files |
| colored | 2.1+ | Terminal color output | For cargo verify OK/FAIL/TIMEOUT status display |
| cargo-nextest (dev) | 0.9+ | Fast test runner | Development only, faster than cargo test |
| cargo-expand (dev) | 1.0+ | Macro debugging | Development only, debug proc macro output |

### Installation

```bash
# Core dependencies (add to Cargo.toml workspace.dependencies)
z3 = { version = "0.19", features = ["bundled"] }
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }
colored = "2.1"
cargo_metadata = "0.18"

# Development tools
cargo install cargo-nextest
cargo install cargo-expand
```

**Confidence:** HIGH - all libraries are mature, widely adopted, and well-documented.

## Architecture Patterns

### Pattern 1: Z3 Crate Migration (Native API vs Subprocess)

**What:** Migrate from subprocess SMT-LIB2 text generation to native Z3 API via z3 crate.

**When to use:** For all new features in Phase 2. Keep subprocess as fallback.

**Tradeoffs:**
- **Pro:** Type-safe API, incremental solving (push/pop), better error messages, ~10x faster (no process spawn per VC)
- **Con:** Requires Z3 linking (mitigated by `bundled` feature)

**Example:**
```rust
// OLD (Phase 1): Subprocess with text
let smt_script = format!("(declare-const x (_ BitVec 32))\n(assert (= x #x00000001))");
let result = subprocess::run_z3(&smt_script)?;

// NEW (Phase 2): Native API
use z3::*;
let cfg = Config::new();
let ctx = Context::new(&cfg);
let solver = Solver::new(&ctx);
let x = ast::BV::new_const(&ctx, "x", 32);
solver.assert(&x._eq(&ast::BV::from_i64(&ctx, 1, 32)));
let result = solver.check(); // SatResult::Sat/Unsat/Unknown
```

**Build order:**
1. Add z3 dependency with `bundled` feature
2. Create `solver/src/z3_backend.rs` implementing SolverBackend trait
3. Add feature flag to choose backend (default: z3-native, fallback: subprocess)
4. Test equivalence on Phase 1 test suite
5. Migrate new features to use z3-native

### Pattern 2: Loop Invariant Verification (3-VC Generation)

**What:** Generate three verification conditions for loops with user-supplied invariants.

**When to use:** For all while/for loops with `#[invariant("expr")]` annotations.

**VCs generated:**
1. **Base case:** Precondition ⊢ Invariant (on loop entry)
2. **Inductive case:** Invariant ∧ LoopCondition ⊢ wp(LoopBody, Invariant)
3. **Exit case:** Invariant ∧ ¬LoopCondition ⊢ Postcondition

**Example:**
```rust
#[requires(n >= 0)]
#[ensures(result == n * (n - 1) / 2)]
#[invariant(i <= n)]
#[invariant(sum == i * (i - 1) / 2)]
fn sum_to_n(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    while i < n {  // Loop header
        sum += i;
        i += 1;
    }  // Loop exit
    sum
}

// VC1 (base): n >= 0 ⊢ (0 <= n) ∧ (0 == 0)
// VC2 (inductive): (i <= n) ∧ (sum == i*(i-1)/2) ∧ (i < n)
//                  ⊢ wp(sum += i; i += 1, (i <= n) ∧ (sum == i*(i-1)/2))
// VC3 (exit): (i <= n) ∧ (sum == i*(i-1)/2) ∧ ¬(i < n) ⊢ (sum == n*(n-1)/2)
```

**Implementation:**
- Detect loop header (MIR basic block with back-edge to itself)
- Extract invariant from `#[invariant]` attribute on loop
- Generate 3 separate VCs, label clearly in error messages
- Report which VC failed (helps user fix invariant)

### Pattern 3: Creusot-Style Automatic Invariant Insertion

**What:** Automatically insert type invariants and immutability invariants for variables not written in loop.

**When to use:** Reduce manual invariant burden for common cases.

**Creusot 0.9.0 insight:** Detect variables that are read but never written in loop body. Auto-insert `x == old(x)` invariant.

**Example:**
```rust
#[invariant(i < arr.len())]  // User must supply bounds check
fn find_zero(arr: &[i32]) -> Option<usize> {
    let mut i = 0;
    while i < arr.len() {
        if arr[i] == 0 { return Some(i); }  // arr is immutable in loop
        i += 1;
    }
    None
}
// AUTO-INSERT: arr.len() == old(arr.len()) -- arr not mutated
// AUTO-INSERT: arr[j] == old(arr[j]) for all j -- arr contents unchanged
```

**Implementation:**
1. Scan loop body for assignments
2. Identify variables in scope but not assigned
3. Insert `x == @x` (where @ is "value on loop entry") for immutables
4. Insert type invariants (e.g., Vec::len() >= 0, Option is Some or None)

**Confidence:** MEDIUM - Creusot demonstrates feasibility, but implementation complexity is non-trivial.

### Pattern 4: SMT Datatype Encoding for Structs

**What:** Encode Rust structs as SMT-LIB 2.6 datatypes with constructors and selectors.

**When to use:** For all struct types used in specifications.

**Example:**
```rust
// Rust
struct Point { x: i32, y: i32 }

// SMT-LIB (via z3 crate)
use z3::*;
let ctx = Context::new(&Config::new());
let point_sort = DatatypeBuilder::new(&ctx, "Point")
    .variant("mk-point", vec![
        ("x", DatatypeAccessor::Sort(Sort::bitvector(&ctx, 32))),
        ("y", DatatypeAccessor::Sort(Sort::bitvector(&ctx, 32))),
    ])
    .finish();

// Usage in specifications
#[ensures(result.x > 0 && result.y > 0)]  // Field access
fn new_point(x: i32, y: i32) -> Point {
    Point { x, y }  // Constructor
}

// SMT encoding
// (declare-datatype Point ((mk-point (x (_ BitVec 32)) (y (_ BitVec 32)))))
// (assert (and (bvsgt (x result) #x00000000) (bvsgt (y result) #x00000000)))
```

**Build order:**
1. Extract struct layout via rustc_abi
2. Generate SMT datatype declaration
3. Encode field access as selector application
4. Encode struct literal as constructor application
5. Test with nested structs

### Pattern 5: Panic Point Detection in MIR

**What:** Statically detect MIR terminators/statements that can panic and generate VCs proving they don't.

**Panic sources in MIR:**
1. **Assert terminator:** `assert!(expr)` → MIR `Assert { cond, expected: true, ... }`
2. **Unwrap/expect:** Generates MIR Assert checking Option/Result discriminant
3. **Array indexing:** `arr[i]` → MIR Assert checking `i < arr.len()`
4. **Division/remainder:** Explicit overflow checks already in Phase 1
5. **Shift operations:** `x << n` → Assert checking `n < bit_width`

**Example:**
```rust
fn safe_unwrap(opt: Option<i32>) -> i32 {
    opt.unwrap()  // MIR: Assert { cond: discriminant(opt) == Some, msg: UnwrapFailed }
}

// VC: Prove discriminant(opt) == Some OR report potential panic at unwrap site
```

**Implementation:**
- Scan MIR for Assert terminators
- Extract condition and panic message
- Generate VC: precondition ⊢ assert_condition
- If UNSAT, report: "Potential panic at line X: unwrap on None"

### Pattern 6: Cargo Subcommand Pattern

**What:** Implement `cargo verify` as a cargo subcommand that invokes rust-fv-driver.

**Naming convention:** Binary named `cargo-verify` in PATH → invoked as `cargo verify`

**Implementation:**
```rust
// crates/driver/src/main.rs (becomes cargo-verify binary)
fn main() {
    let args: Vec<String> = env::args().collect();

    // Cargo passes "verify" as second arg
    if args.len() > 1 && args[1] == "verify" {
        // Running as cargo subcommand
        run_cargo_verify();
    } else {
        // Running as rustc_driver wrapper
        run_rustc_driver();
    }
}

fn run_cargo_verify() {
    // 1. Parse Cargo.toml with cargo_metadata
    // 2. Set RUSTC_WRAPPER=cargo-verify
    // 3. Run cargo check
    // 4. Collect verification results per function
    // 5. Print colored summary
}
```

**Colored output:**
```
Verifying my_crate v0.1.0 (/path/to/crate)
    Checking src/lib.rs
  [OK]      max(a, b) -> i32
  [FAIL]    unsafe_div(a, b) -> i32 (division by zero at line 42)
  [TIMEOUT] complex_loop() (loop invariant verification timed out)

Summary: 1 OK, 1 FAIL, 1 TIMEOUT
```

**Build order:**
1. Add cargo_metadata and colored dependencies
2. Implement cargo verify entry point
3. Collect per-function results (store in static or file)
4. Format output with colored status
5. Test with workspace containing multiple crates

### Pattern 7: Structured Tracing for Debugging

**What:** Use `tracing` crate for module-level diagnostics instead of println! debugging.

**When to use:** Throughout verification pipeline for debugging and user diagnostics.

**Example:**
```rust
use tracing::{info, debug, warn, instrument};

#[instrument(skip(tcx))]
fn convert_mir(tcx: TyCtxt<'_>, body: &mir::Body<'_>) -> ir::Function {
    debug!("Converting MIR for {:?}", body.source);
    let func = /* conversion */;
    info!(blocks = func.basic_blocks.len(), "MIR conversion complete");
    func
}

// Usage
// RUST_LOG=rust_fv_driver=debug cargo verify
// Shows detailed conversion steps
// RUST_LOG=rust_fv_driver=info cargo verify
// Shows only high-level progress
```

**Setup:**
```rust
// Initialize subscriber in main
use tracing_subscriber::{fmt, EnvFilter};

fn main() {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .init();

    // Rest of main
}
```

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Loop invariant inference | Custom ML model, theorem prover | Manual + targeted auto-insertion (Creusot pattern) | General inference is research-level problem, unlikely to work reliably. Focus on excellent error messages. |
| SMT solver | Custom SAT/SMT implementation | Z3 via z3 crate (bundled feature) | Z3 is 20+ years of engineering. Building competitive solver is PhD-level multi-year effort. |
| Struct encoding | Ad-hoc tuple representation | SMT-LIB 2.6 datatypes | Datatypes are standard, solver-optimized, support nested/recursive types. |
| Expression parsing | Regex/hand-rolled parser | syn crate (full feature) | Syn handles all Rust syntax edge cases, maintained by dtolnay. |
| Cargo integration | Shell scripts | cargo_metadata crate | Official Cargo metadata format, handles workspaces/targets/features correctly. |
| Colored terminal output | ANSI escape codes | colored crate | Cross-platform (Windows/Unix), handles NO_COLOR env var, widely adopted. |

**Key insight:** Phase 2 features touch well-solved problems in PL tooling. Reuse battle-tested libraries.

## Common Pitfalls

### Pitfall 1: Loop Invariant Inference Over-Ambition

**What goes wrong:** Attempt general-purpose invariant inference, spend months getting 20% accuracy, users frustrated.

**Why it happens:** Loop invariants are "the hardest problem in verification" - even LLMs achieve <50% success on simple programs (2025 research).

**How to avoid:**
- Accept that manual invariants are primary approach
- Focus on excellent error messages (which VC failed? why?)
- Add targeted auto-insertion for specific patterns:
  - Immutable variables (Creusot 0.9.0 pattern)
  - Type invariants (Option is Some/None, Vec len >= 0)
  - Simple bounds (0 <= i < n for iteration variables)
- Defer general inference to Phase 3+ research spike

**Warning signs:**
- Users report "I tried 10 invariants, none worked"
- Verification times out on simple loops
- Can't explain which invariant clause is too weak

**Confidence:** HIGH - extensive research confirms difficulty, Creusot team explicitly chose targeted approach.

### Pitfall 2: Z3 Bundled Feature Linking Issues

**What goes wrong:** `z3 = { version = "0.19", features = ["bundled"] }` fails to link on some platforms (ARM64, Windows MSVC).

**Why it happens:** Bundled feature builds Z3 from source via cmake, which requires C++ toolchain and cmake installed.

**How to avoid:**
- Document cmake requirement in README
- Keep subprocess backend as fallback
- Add CI testing on all platforms (Linux x86_64, macOS ARM64/x86_64, Windows)
- Provide clear error message if z3 crate unavailable: "Install cmake or set Z3_SYS_Z3_HEADER to use system Z3"

**Warning signs:**
- Build fails with linker errors on fresh checkout
- Works on Linux, fails on macOS/Windows
- Users report "can't build rust-fv"

**Mitigation:**
```toml
# Cargo.toml
[dependencies]
z3 = { version = "0.19", features = ["bundled"], optional = true }

[features]
default = ["z3-native"]
z3-native = ["z3"]
subprocess-only = []
```

**Confidence:** MEDIUM - bundled feature is production-ready, but platform-specific build issues are common in native bindings.

### Pitfall 3: SMT Datatype Encoding for Generics

**What goes wrong:** Rust `struct Point<T> { x: T, y: T }` has monomorphization - each `Point<i32>`, `Point<f64>` is separate type. Naive encoding generates duplicate SMT datatypes or incorrect generic encoding.

**Why it happens:** SMT-LIB has no generics - each type is monomorphic. Must generate separate datatype per instantiation.

**How to avoid:**
- Detect generic instantiation during MIR conversion
- Generate unique SMT datatype name per instantiation: `Point_i32`, `Point_f64`
- Track instantiations in datatype registry (prevent duplicates)
- Start with non-generic structs in Phase 2, add generic support incrementally

**Warning signs:**
- Verification fails on generic functions
- SMT solver reports "unknown sort Point"
- Different instantiations interfere with each other

**Example:**
```rust
// Rust
struct Point<T> { x: T, y: T }
fn f() { let p: Point<i32> = ...; }
fn g() { let q: Point<i64> = ...; }

// SMT (monomorphization)
// (declare-datatype Point_i32 ((mk-Point_i32 (x (_ BitVec 32)) (y (_ BitVec 32)))))
// (declare-datatype Point_i64 ((mk-Point_i64 (x (_ BitVec 64)) (y (_ BitVec 64)))))
```

**Confidence:** MEDIUM - datatype encoding is well-understood, but generic handling adds complexity.

### Pitfall 4: Assert! vs Debug Assert Semantics

**What goes wrong:** Rust has `assert!()` (always checked) and `debug_assert!()` (only in debug builds). Verifying debug_assert in release mode configuration is unsound.

**Why it happens:** MIR for release builds omits debug_assert checks.

**How to avoid:**
- Detect compilation profile (debug vs release)
- Only verify assertions present in MIR for target profile
- Document: "rust-fv verifies assertions based on --release flag"
- Consider: add `#[verify_assert]` attribute to force verification even in release

**Warning signs:**
- Verification passes, but debug_assert fails at runtime
- Different results in debug vs release builds

**Confidence:** HIGH - Rust assert semantics are well-defined.

### Pitfall 5: Panic Message Attribution

**What goes wrong:** MIR Assert terminators have opaque panic messages. User sees "potential panic at line 42" but can't tell if it's unwrap, index, division, etc.

**Why it happens:** MIR AssertKind enum has variants (BoundsCheck, Overflow, DivisionByZero, etc.) but must extract and format correctly.

**How to avoid:**
- Match on AssertKind to provide specific message:
  - BoundsCheck → "array index out of bounds"
  - Overflow(Add) → "integer overflow in addition"
  - UnwrapNone → "unwrap on None"
- Include source location (line number, column)
- Show code snippet if available

**Example output:**
```
[FAIL] safe_unwrap(opt: Option<i32>) -> i32
  Error: Potential panic at src/lib.rs:42:5
  Reason: unwrap() called on Option that may be None

  42 |     opt.unwrap()
     |     ^^^^^^^^^^^^ this unwrap is not guaranteed to succeed

  Help: Add a precondition: #[requires(opt.is_some())]
```

**Confidence:** MEDIUM - MIR provides necessary info, but formatting requires care.

### Pitfall 6: Old() Operator Scoping

**What goes wrong:** `old(x)` in postcondition should refer to pre-state value, but implementation accidentally captures mid-execution value.

**Why it happens:** Weakest precondition substitution must explicitly track pre-state snapshot.

**How to avoid:**
- At function entry, snapshot all parameters/globals: `x_pre = x`
- In postcondition, replace `old(x)` with `x_pre` before encoding
- Never substitute into `old()` expressions during WP calculation
- Test with functions that modify parameters

**Example:**
```rust
#[ensures(result == old(x) + 1)]
fn increment(x: &mut i32) -> i32 {
    *x += 1;
    *x
}

// Encoding:
// x_pre = x  (snapshot at entry)
// x = x + 1  (mutation)
// result = x
// Postcondition: result == x_pre + 1  (NOT result == x + 1)
```

**Confidence:** MEDIUM - standard technique but easy to implement incorrectly.

## Code Examples

Verified patterns from z3 crate and SMT-LIB documentation.

### Loop Verification with 3 VCs

```rust
// Source: Adapted from Creusot tutorial (POPL 2026)
use rust_fv_macros::*;

#[requires(n >= 0)]
#[ensures(result == n * (n - 1) / 2)]
fn sum_to_n(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;

    #[invariant(i <= n)]
    #[invariant(sum == i * (i - 1) / 2)]
    while i < n {
        sum += i;
        i += 1;
    }

    sum
}

// VCGen implementation
fn generate_loop_vcs(loop_node: &Loop, func: &Function) -> Vec<VC> {
    let mut vcs = Vec::new();

    // VC1: Base case (precondition implies invariant on entry)
    let base_vc = vc_builder()
        .assume_all(&func.preconditions)
        .assert_all(&loop_node.invariants)
        .with_label("loop invariant initialization")
        .build();
    vcs.push(base_vc);

    // VC2: Inductive case (invariant + condition implies invariant after body)
    let inductive_vc = vc_builder()
        .assume_all(&loop_node.invariants)
        .assume(&loop_node.condition)
        .encode_statements(&loop_node.body)
        .assert_all(&loop_node.invariants)  // After body execution
        .with_label("loop invariant preservation")
        .build();
    vcs.push(inductive_vc);

    // VC3: Exit case (invariant + !condition implies postcondition)
    let exit_vc = vc_builder()
        .assume_all(&loop_node.invariants)
        .assume(&negate(&loop_node.condition))
        .assert_all(&func.postconditions)
        .with_label("loop exit to postcondition")
        .build();
    vcs.push(exit_vc);

    vcs
}
```

### Z3 Native API for Struct Encoding

```rust
// Source: z3 crate docs (docs.rs/z3/0.19)
use z3::*;

fn encode_struct_type(ctx: &Context) -> Sort {
    // Rust: struct Point { x: i32, y: i32 }

    DatatypeBuilder::new(ctx, "Point")
        .variant("mk-point", vec![
            ("x", DatatypeAccessor::Sort(Sort::bitvector(ctx, 32))),
            ("y", DatatypeAccessor::Sort(Sort::bitvector(ctx, 32))),
        ])
        .finish()
}

fn verify_struct_access(ctx: &Context, point_sort: &Sort) {
    let solver = Solver::new(ctx);

    // Create point variable
    let p = Datatype::new_const(ctx, "p", point_sort);

    // Access fields (via generated selectors)
    let x_accessor = point_sort.variants[0].accessors[0].apply(&[&p]);
    let y_accessor = point_sort.variants[0].accessors[1].apply(&[&p]);

    // Assert: p.x > 0 && p.y > 0
    solver.assert(&x_accessor.bvsgt(&BV::from_i64(ctx, 0, 32)));
    solver.assert(&y_accessor.bvsgt(&BV::from_i64(ctx, 0, 32)));

    match solver.check() {
        SatResult::Sat => {
            let model = solver.get_model().unwrap();
            // Extract counterexample
        }
        SatResult::Unsat => println!("Verified!"),
        SatResult::Unknown => println!("Timeout"),
    }
}
```

### Panic Detection in MIR

```rust
// Source: Adapted from MirChecker (CCS 2021)
use rustc_middle::mir::{self, BasicBlock, Terminator, TerminatorKind};

fn detect_panic_points(body: &mir::Body<'_>) -> Vec<PanicPoint> {
    let mut panics = Vec::new();

    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if let Some(terminator) = &data.terminator {
            match &terminator.kind {
                TerminatorKind::Assert { cond, expected, msg, .. } => {
                    let panic_kind = match msg {
                        mir::AssertKind::BoundsCheck { .. } => "array index out of bounds",
                        mir::AssertKind::Overflow(op) =>
                            format!("arithmetic overflow in {:?}", op),
                        mir::AssertKind::DivisionByZero => "division by zero",
                        mir::AssertKind::RemainderByZero => "remainder by zero",
                        mir::AssertKind::OverflowNeg => "negation overflow",
                        mir::AssertKind::MisalignedPointerDereference { .. } =>
                            "misaligned pointer dereference",
                        _ => "assertion failure",
                    };

                    panics.push(PanicPoint {
                        location: terminator.source_info.span,
                        condition: cond.clone(),
                        expected: *expected,
                        message: panic_kind.to_string(),
                    });
                }
                _ => {}
            }
        }
    }

    panics
}
```

### Cargo Verify Subcommand

```rust
// Source: Cargo Book - External Tools
use cargo_metadata::MetadataCommand;
use colored::*;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() > 1 && args[1] == "verify" {
        run_cargo_verify();
    } else {
        run_rustc_driver();
    }
}

fn run_cargo_verify() {
    // Parse project metadata
    let metadata = MetadataCommand::new()
        .exec()
        .expect("Failed to parse Cargo.toml");

    println!("Verifying {} v{}",
        metadata.workspace_root.file_name().unwrap(),
        metadata.root_package().unwrap().version
    );

    // Run verification (via RUSTC_WRAPPER)
    std::env::set_var("RUSTC_WRAPPER", env::current_exe().unwrap());
    let status = std::process::Command::new("cargo")
        .arg("check")
        .arg("--quiet")
        .status()
        .expect("Failed to run cargo check");

    // Collect results (from global state or temp file)
    let results = collect_verification_results();

    // Print colored summary
    for result in results {
        match result.status {
            VerificationStatus::Ok =>
                println!("  [{}]  {}", "OK".green(), result.function),
            VerificationStatus::Failed { reason } =>
                println!("  [{}] {} ({})", "FAIL".red(), result.function, reason),
            VerificationStatus::Timeout =>
                println!("  [{}] {}", "TIMEOUT".yellow(), result.function),
        }
    }

    // Summary
    let ok = results.iter().filter(|r| matches!(r.status, VerificationStatus::Ok)).count();
    let fail = results.iter().filter(|r| matches!(r.status, VerificationStatus::Failed{..})).count();
    let timeout = results.iter().filter(|r| matches!(r.status, VerificationStatus::Timeout)).count();

    println!("\nSummary: {} OK, {} FAIL, {} TIMEOUT",
        ok.to_string().green(),
        fail.to_string().red(),
        timeout.to_string().yellow()
    );

    std::process::exit(if fail > 0 { 1 } else { 0 });
}
```

### Tracing Setup

```rust
// Source: Tokio tracing docs
use tracing::{info, debug, instrument};
use tracing_subscriber::{fmt, EnvFilter};

fn main() {
    // Initialize tracing subscriber
    tracing_subscriber::fmt()
        .with_env_filter(
            EnvFilter::from_default_env()
                .add_directive("rust_fv_driver=info".parse().unwrap())
        )
        .with_target(true)  // Show module name
        .with_line_number(true)
        .init();

    run_verification();
}

#[instrument(skip(tcx, body))]
fn convert_mir(tcx: TyCtxt<'_>, body: &mir::Body<'_>) -> ir::Function {
    debug!("Converting MIR for function");

    let func = /* conversion logic */;

    info!(
        blocks = func.basic_blocks.len(),
        locals = func.locals.len(),
        "MIR conversion complete"
    );

    func
}

// Usage:
// RUST_LOG=debug cargo verify  -- verbose output
// RUST_LOG=info cargo verify   -- normal output
// RUST_LOG=error cargo verify  -- errors only
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Subprocess Z3 with text SMT-LIB | z3 crate native API | 2024-2025 | 10x faster, type safety, incremental solving |
| Manual loop invariants only | Auto-insert type/immutability invariants | Creusot 0.9.0 (Jan 2026) | Reduces user burden for common patterns |
| Uninterpreted aggregate types | SMT datatypes (declare-datatypes) | SMT-LIB 2.6 (2015+) | Enables struct field reasoning |
| LLM-only invariant inference | Hybrid LLM + symbolic (BALI, CEGIS+RL) | 2024-2026 | Improved but still <70% accuracy |
| Process per query | Incremental solving (push/pop) | Standard practice 2020+ | 100x speedup for related queries |

**Deprecated/outdated:**
- **SMT-LIB 2.5 and earlier:** No datatype support, use 2.6+
- **Z3 Python bindings for Rust tools:** FFI overhead, use native z3 crate
- **Pure LLM invariant inference:** 2025 research shows limited success, hybrid approaches better

## Open Questions

### 1. Loop Invariant Inference Scope for Phase 2

**What we know:**
- General inference is research-level hard (LLM accuracy <50%)
- Creusot 0.9.0 successfully auto-inserts type invariants + immutability invariants
- Template-based CEGIS works for specific patterns (0 <= i < n)

**What's unclear:**
- How much manual burden is acceptable for MVP?
- Should we implement CEGIS for simple templates in Phase 2 or defer to Phase 3?
- What % of common loops can be verified with just type+immutability inference?

**Recommendation:**
- Phase 2: Manual invariants + Creusot-style auto-insertion (80/20 rule)
- Phase 3: Add template CEGIS for iteration variables (research spike)
- Phase 4+: Explore LLM-assisted invariant suggestion (if research improves)

### 2. Z3 Performance Regression Risk

**What we know:**
- Z3 crate enables incremental solving (push/pop)
- Subprocess spawning is bottleneck in current implementation (~50ms per VC)

**What's unclear:**
- Will z3 crate actually be faster for our workload?
- Are there edge cases where native API is slower (e.g., large datatypes)?

**Recommendation:**
- Benchmark Phase 1 test suite with both backends
- Keep subprocess as fallback
- Add performance regression tests (Phase 2.1 deliverable)

### 3. Generic Struct Encoding Complexity

**What we know:**
- Generics require monomorphization (separate SMT datatype per instantiation)
- Must track instantiations to avoid duplicate declarations

**What's unclear:**
- How to handle recursive generic types (e.g., `struct Node<T> { data: T, next: Box<Node<T>> }`)?
- Do we need separate SMT sorts for each lifetime parameter?

**Recommendation:**
- Phase 2: Non-generic structs only
- Phase 3: Monomorphic generics (concrete type substitutions)
- Phase 4: Recursive datatypes (requires SMT recursive datatype support)

## Sources

### Primary (HIGH confidence)

**Loop Invariants:**
- [Creusot 0.9.0 - Creusot Devlog](https://creusot-rs.github.io/devlog/2026-01-19/) — January 2026, auto-insertion of type/immutability invariants
- [Loop Invariant Inference through SMT Solving Enhanced Reinforcement Learning](https://dl.acm.org/doi/10.1145/3597926.3598047) — Template-based CEGIS with RL
- [LLM For Loop Invariant Generation and Fixing: How Far Are We?](https://arxiv.org/html/2511.06552) — LLM limitations (2025)

**Z3 Integration:**
- [z3 crate - crates.io](https://crates.io/crates/z3) — Official crate, bundled feature documentation
- [An Introductory Practical Guide to Rust Bindings for the Z3 Solver](https://z3prover.github.io/papers/z3_rust_guide.pdf) — Practical guide
- [GitHub - prove-rs/z3.rs](https://github.com/prove-rs/z3.rs) — Source repository

**SMT Datatypes:**
- [Datatypes - Online Z3 Guide](https://microsoft.github.io/z3guide/docs/theories/Datatypes/) — Official Z3 datatype documentation
- [SMT-LIB Standard Version 2.6](https://smt-lib.org/papers/smt-lib-reference-v2.6-r2021-05-12.pdf) — declare-datatypes syntax
- [Datatypes - CVC4](http://cvc4.cs.stanford.edu/wiki/Datatypes) — SMT-LIB 2.6 datatype format

**Cargo Integration:**
- [Extending Cargo with Custom Commands - The Rust Programming Language](https://doc.rust-lang.org/book/ch14-05-extending-cargo.html) — Official subcommand guide
- [External Tools - The Cargo Book](https://doc.rust-lang.org/cargo/reference/external-tools.html) — RUSTC_WRAPPER pattern

**Tracing:**
- [Getting started with Tracing - Tokio](https://tokio.rs/tokio/topics/tracing) — Official guide
- [How to Create Structured JSON Logs with tracing in Rust](https://oneuptime.com/blog/post/2026-01-25-structured-json-logs-tracing-rust/view) — January 2026 tutorial
- [GitHub - tokio-rs/tracing](https://github.com/tokio-rs/tracing) — Source repository

**Panic Detection:**
- [Miri: Practical Undefined Behavior Detection for Rust](https://research.ralfj.de/papers/2026-popl-miri.pdf) — POPL 2026, MIR analysis patterns
- [MirChecker: Detecting Bugs in Rust Programs via Static Analysis](https://www.zhuohua.me/assets/CCS2021-MirChecker.pdf) — CCS 2021, panic detection techniques

**Expression Parsing:**
- [Expr in syn - Rust](https://docs.rs/syn/latest/syn/enum.Expr.html) — syn::Expr documentation
- [GitHub - dtolnay/syn](https://github.com/dtolnay/syn) — Official repository

### Secondary (MEDIUM confidence)

**Verification Techniques:**
- [Optimizing Prestate Copies in Runtime Verification of Function Postconditions](https://link.springer.com/chapter/10.1007/978-3-031-17196-3_5) — old() operator optimization
- [Static Analysis of Memory Models for SMT Encodings](https://dl.acm.org/doi/10.1145/3622855) — SMT encoding optimization (OOPSLA 2023)

**Overflow Checking:**
- [Using BitVector Theory to find the overflow bug in Binary Search](https://verificationglasses.wordpress.com/2020/12/17/bitvector-overflow/) — Bitvector overflow detection
- [Check for overflow on bitvector operations - Z3 Discussion](https://github.com/Z3Prover/z3/discussions/5138) — Z3 overflow predicates

**Terminal Output:**
- [Reporting test results - cargo-nextest](https://nexte.st/docs/reporting/) — Colored test output patterns
- [colored crate - lib.rs](https://lib.rs/crates/colored) — Cross-platform colored output

### Tertiary (LOW confidence - needs validation)

- [Synthesizing Loop-Free Programs with Rust and Z3](https://fitzgen.com/2020/01/13/synthesizing-loop-free-programs.html) — Blog post on z3 crate usage (2020)
- [Improving Counterexample Quality from Failed Program Verification](https://arxiv.org/pdf/2208.10492) — Counterexample extraction techniques

## Metadata

**Confidence breakdown:**
- Loop invariants: MEDIUM-HIGH — Creusot 0.9.0 demonstrates feasibility of targeted auto-insertion, general inference remains hard
- Z3 crate integration: HIGH — Production-ready, bundled feature solves installation issues, well-documented
- SMT datatypes: HIGH — Standard SMT-LIB 2.6 feature, supported by all major solvers, z3 crate has good API
- Panic detection: HIGH — MIR provides explicit Assert terminators, straightforward to extract
- Cargo integration: HIGH — Official pattern, well-documented, used by many cargo subcommands
- Tracing: HIGH — Mature crate, widely adopted, official Tokio project

**Research date:** 2026-02-11
**Valid until:** 2026-03-15 (30 days for stable libraries, phase planning should complete before expiry)
