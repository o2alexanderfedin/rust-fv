# Architecture Research

**Domain:** Formal verification tools for Rust
**Researched:** 2026-02-10
**Confidence:** HIGH

## Standard Architecture

### System Overview

```
┌─────────────────────────────────────────────────────────────┐
│                    Specification Layer                       │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐       │
│  │ Proc Macros  │  │  Pearlite    │  │  Attributes  │       │
│  │ (#[requires])│  │ Spec Lang    │  │  (metadata)  │       │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘       │
├─────────┴──────────────────┴──────────────────┴──────────────┤
│                    Compiler Integration Layer                 │
│  ┌──────────────────────────────────────────────────────┐    │
│  │         rustc_driver Callbacks (after_analysis)      │    │
│  │  ┌────────────┐  ┌──────────┐  ┌────────────────┐   │    │
│  │  │ HIR Access │→ │ Extract  │→ │ MIR Extraction │   │    │
│  │  │ (contracts)│  │ Metadata │  │   (semantics)  │   │    │
│  │  └────────────┘  └──────────┘  └────────────────┘   │    │
│  └──────────────────────────────────────────────────────┘    │
├───────────────────────────────────────────────────────────────┤
│                    Translation Layer                          │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐       │
│  │  MIR → IR    │→ │   IR (CFG)   │→ │  IR → VC     │       │
│  │  Converter   │  │  Validation  │  │  Generator   │       │
│  └──────────────┘  └──────────────┘  └──────────────┘       │
├───────────────────────────────────────────────────────────────┤
│                    Encoding Layer                             │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐       │
│  │ Type → Sort  │  │ Expr → Term  │  │ VC Builder   │       │
│  │  Encoding    │  │  Encoding    │  │ (SMT Script) │       │
│  └──────────────┘  └──────────────┘  └──────────────┘       │
├───────────────────────────────────────────────────────────────┤
│                    SMT Backend Layer                          │
│  ┌──────────────────────────────────────────────────────┐    │
│  │  SMT-LIB Generator → Z3/CVC5 → Model Parser          │    │
│  └──────────────────────────────────────────────────────┘    │
└───────────────────────────────────────────────────────────────┘
```

### Component Responsibilities

| Component | Responsibility | Typical Implementation |
|-----------|----------------|------------------------|
| **Specification Frontend** | Rust-native spec syntax via proc macros or embedded DSL | Proc macro attributes (rust-fv), embedded Pearlite language (Creusot) |
| **Compiler Integration** | Hook into rustc pipeline after type/borrow checking | rustc_driver::Callbacks::after_analysis, access HIR+MIR+TyCtxt |
| **Contract Extraction** | Parse specifications from attributes/syntax | Scan HIR attributes for doc-hidden markers or AST nodes |
| **MIR Converter** | Translate rustc MIR to stable IR | Thin translation layer isolating rustc internal changes |
| **Intermediate Representation** | Stable, testable program representation | Custom IR mirroring MIR structure (Function, BasicBlock, Statement) |
| **Verification Condition Generator** | Transform IR into logical VCs to prove | Weakest precondition calculus or SSA-based encoding |
| **Type/Expression Encoder** | Map Rust types/expressions to SMT sorts/terms | Bitvector encoding for integers, theory-specific mappings |
| **SMT-LIB Builder** | Construct well-formed SMT-LIB scripts | Builder pattern for commands, sorts, terms with validation |
| **Solver Interface** | Invoke SMT solver and parse results | Subprocess spawning with SMT-LIB stdin/stdout protocol |
| **Model Parser** | Extract counterexamples from solver models | Parse SMT-LIB get-model responses into structured data |

## Recommended Project Structure

### Monorepo Crate Organization (Proven Pattern)

```
crates/
├── macros/              # Specification syntax (proc macros)
│   ├── lib.rs          # #[requires], #[ensures], #[pure] macros
│   └── tests/          # Macro expansion tests
├── smtlib/             # SMT-LIB AST and formatting (solver-agnostic)
│   ├── command.rs      # SMT-LIB commands (declare-const, assert, etc.)
│   ├── sort.rs         # SMT-LIB sorts (Bool, BitVec, Array, etc.)
│   ├── term.rs         # SMT-LIB terms (expressions)
│   ├── script.rs       # Script builder (sequence of commands)
│   └── formatter.rs    # Pretty-printing to SMT-LIB text
├── solver/             # SMT solver interface
│   ├── config.rs       # Solver configuration (path, timeout, etc.)
│   ├── solver.rs       # Z3/CVC5 subprocess interface
│   ├── parser.rs       # Parse sat/unsat/model responses
│   ├── result.rs       # Solver result types
│   └── error.rs        # Solver error types
├── analysis/           # Core verification logic (stable Rust)
│   ├── ir.rs           # Intermediate representation (decoupled from rustc)
│   ├── vcgen.rs        # Verification condition generator
│   ├── encode_sort.rs  # Type → SMT sort encoding
│   ├── encode_term.rs  # Expression → SMT term encoding
│   └── tests/          # Unit tests for VCGen (no rustc dependency)
└── driver/             # Compiler integration (nightly-only)
    ├── main.rs         # rustc_driver wrapper entry point
    ├── callbacks.rs    # Callbacks::after_analysis implementation
    └── mir_converter.rs # rustc MIR → stable IR conversion
```

### Structure Rationale

- **macros/:** Separate crate for proc macros (required by Rust). Provides ergonomic Rust-native syntax.
- **smtlib/:** Solver-agnostic SMT-LIB builder. Enables testing encoding logic without solver invocation, supports multiple backends (Z3, CVC5, etc.).
- **solver/:** Isolates external process communication. Strategy pattern allows swapping solver implementations.
- **analysis/:** Pure verification logic with no rustc dependencies. Testable on stable Rust, enables unit testing without compiler overhead.
- **driver/:** Thin integration layer. Isolates nightly rustc API surface, minimizes code affected by compiler changes.

**Dependency Direction:** driver → analysis → smtlib, solver. Core logic (analysis) depends only on stable smtlib abstractions.

## Architectural Patterns

### Pattern 1: Stable IR Decoupling

**What:** Maintain a custom IR that mirrors rustc MIR but is fully owned and stable.

**When to use:** Always, for any rustc-integrated verification tool.

**Trade-offs:**
- **Pro:** Isolates core verification logic from rustc internal changes. Enables unit testing on stable Rust. Simplifies debugging.
- **Con:** Adds translation overhead (minimal). Requires maintaining mapping code.

**Example:**
```rust
// analysis/src/ir.rs (stable, no rustc dependency)
pub struct Function {
    pub name: String,
    pub params: Vec<Local>,
    pub basic_blocks: Vec<BasicBlock>,
    pub contracts: Contracts,
}

// driver/src/mir_converter.rs (nightly-only, thin layer)
pub fn convert_mir(tcx: TyCtxt<'_>, body: &mir::Body<'_>) -> ir::Function {
    // Translate rustc types to stable IR types
}
```

**Build order:** Define IR first, then build VCGen against IR, finally add MIR converter.

### Pattern 2: Layered Pipeline with Clear Phase Boundaries

**What:** Separate annotation extraction, IR conversion, VC generation, SMT encoding, and solving into distinct phases with well-defined interfaces.

**When to use:** For any multi-stage verification system.

**Trade-offs:**
- **Pro:** Each phase is independently testable. Clear responsibility boundaries. Enables parallel development. Easier debugging (can inspect intermediate stages).
- **Con:** More interfaces to maintain. Potential inefficiency from multiple passes (negligible in practice).

**Example:**
```rust
// Phase 1: Extract contracts from HIR
let contracts = extract_contracts(tcx, local_def_id);

// Phase 2: Convert rustc MIR → stable IR
let ir_func = convert_mir(tcx, mir, contracts);

// Phase 3: Generate verification conditions
let vcs = generate_vcs(&ir_func);

// Phase 4: Encode to SMT-LIB
for vc in vcs.conditions {
    let script = vc.script; // Already encoded in phase 3

    // Phase 5: Solve
    let result = solver.check_sat(&script);
}
```

**Build order:** Bottom-up (SMT layer → IR → VCGen → MIR converter → driver callbacks).

### Pattern 3: Weakest Precondition VC Generation

**What:** Generate verification conditions by computing weakest preconditions through backward symbolic execution.

**When to use:** For functional correctness properties (contracts, assertions). Standard in deductive verification tools (Dafny, Boogie, Why3, Prusti).

**Trade-offs:**
- **Pro:** Sound and complete for sequential code. Well-understood theory. Produces compact VCs. Works naturally with postconditions.
- **Con:** Requires SSA or careful handling of variable updates. Loop invariants must be supplied (cannot be inferred without additional techniques).

**Example (conceptual):**
```rust
// Given: { P } S { Q }  (Hoare triple)
// WP computes: P ⊢ wp(S, Q)

// For postcondition: ensures result >= a && result >= b
// WP of return: [result/return_var]postcondition
// WP of assignment _0 = _1: postcondition[_1/_0]
// WP of branch: ITE(cond, wp(then_branch, Q), wp(else_branch, Q))

fn generate_contract_vcs(func: &Function) -> Vec<VC> {
    for postcond in &func.contracts.ensures {
        let mut vc = Script::new();
        // Assume preconditions
        for pre in &func.contracts.requires {
            vc.assert(encode_spec(pre));
        }
        // Encode function semantics (simplified: all assignments as equalities)
        for assignment in collect_assignments(func) {
            vc.assert(assignment);
        }
        // Assert NOT postcondition (looking for counterexample)
        vc.assert(Not(encode_spec(postcond)));
        // UNSAT = postcondition always holds
    }
}
```

### Pattern 4: Bitvector-Precise Integer Encoding

**What:** Encode Rust integer types (i8, u32, etc.) as SMT bitvectors with exact bit widths, not mathematical integers.

**When to use:** For verification requiring overflow/underflow detection and exact Rust semantics.

**Trade-offs:**
- **Pro:** Precise Rust semantics. Catches overflow bugs. Enables verification of low-level code.
- **Con:** Larger SMT queries than Int theory. Solver may be slower (modern SMT solvers handle bitvectors well).

**Example:**
```rust
// Encode i32 as (_ BitVec 32), not Int
fn encode_type(ty: &Ty) -> Sort {
    match ty {
        Ty::Int(IntTy::I32) => Sort::BitVec(32),
        Ty::Uint(UintTy::U64) => Sort::BitVec(64),
        _ => // ...
    }
}

// Generate overflow check for a + b
fn overflow_check(op: BinOp, lhs: Term, rhs: Term, ty: &Ty) -> Term {
    let width = ty.bit_width();
    match (op, ty.is_signed()) {
        (Add, true) => {
            // No signed overflow: bvadd_overflow checks
            And(vec![
                Not(BvSAddOverflow(lhs, rhs)),
                Not(BvSAddUnderflow(lhs, rhs)),
            ])
        }
        // Similar for unsigned, other ops...
    }
}
```

### Pattern 5: Linear Block-Walking VCGen (Current Limitation)

**What:** Walk basic blocks sequentially, accumulating assignments as SMT assertions without proper SSA handling or control-flow merging.

**When to use:** Only for initial prototype. Must upgrade to true SSA for production.

**Trade-offs:**
- **Pro:** Simple to implement. Works for straight-line code.
- **Con:** Unsound for branches (missing phi nodes). Cannot handle loops. Limited to single-path functions.

**Example (current rust-fv approach):**
```rust
// Current: Linear walk, no SSA
fn collect_assignments_up_to(func: &Function, up_to_block: usize, up_to_stmt: usize) -> Vec<Command> {
    let mut assertions = Vec::new();
    for (block_idx, block) in func.basic_blocks.iter().enumerate() {
        if block_idx > up_to_block { break; }
        for (stmt_idx, stmt) in block.statements.iter().enumerate() {
            if block_idx == up_to_block && stmt_idx >= up_to_stmt { break; }
            if let Statement::Assign(place, rvalue) = stmt {
                // Encode as: place = rvalue (overwrites previous values)
                assertions.push(Assert(Eq(encode_place(place), encode_rvalue(rvalue))));
            }
        }
    }
    assertions
}
```

**Replacement:** True SSA encoding (Pattern 6).

### Pattern 6: SSA-Based VCGen (Recommended Upgrade)

**What:** Convert IR to Static Single Assignment form, where each variable is assigned exactly once. At control-flow merge points, insert phi nodes.

**When to use:** For sound verification of code with branches and loops.

**Trade-offs:**
- **Pro:** Sound handling of control flow. Standard compiler IR. Simplifies VC generation (each variable has unique value). Enables precise dataflow analysis.
- **Con:** More complex than linear walking. Requires phi node insertion at merge points.

**Example:**
```rust
// SSA transformation
// Before:
//   bb0: x = 1; if (cond) goto bb1 else bb2
//   bb1: x = 2; goto bb3
//   bb2: x = 3; goto bb3
//   bb3: y = x; return

// After SSA:
//   bb0: x_0 = 1; if (cond) goto bb1 else bb2
//   bb1: x_1 = 2; goto bb3
//   bb2: x_2 = 3; goto bb3
//   bb3: x_3 = phi(x_1, x_2); y = x_3; return

// VC encoding:
fn encode_ssa(func: &SSAFunction) -> Script {
    let mut script = Script::new();
    // Declare all SSA variables (each version is a distinct SMT constant)
    for ssa_var in func.ssa_vars {
        script.declare_const(ssa_var.name, encode_type(ssa_var.ty));
    }
    // Encode assignments (no overwrites, each is a fresh variable)
    for assign in func.assignments {
        script.assert(Eq(assign.lhs, encode_rvalue(assign.rhs)));
    }
    // Encode phi nodes as conditional assertions
    for phi in func.phi_nodes {
        // x_3 = phi(x_1 from bb1, x_2 from bb2)
        script.assert(Ite(
            came_from_bb1,
            Eq(phi.result, phi.input1),
            Eq(phi.result, phi.input2)
        ));
    }
    script
}
```

**Build order:** Add SSA conversion step between MIR→IR and VCGen. Replace linear walking with SSA-aware encoding.

### Pattern 7: Modular Inter-Procedural Verification with Function Summaries

**What:** Verify each function in isolation using its contract (requires/ensures) as a summary. When verifying a caller, assume callee's postcondition without re-verifying callee's body.

**When to use:** For scaling to large codebases. Standard in modular verification (Prusti, Dafny, Viper).

**Trade-offs:**
- **Pro:** Scales to large programs (linear in codebase size, not exponential). Enables separate compilation. Reduces VC size dramatically.
- **Con:** Requires user-supplied contracts for all callees. Cannot verify programs with missing specifications.

**Example:**
```rust
// Caller verification: assume callee contract, don't inline body
fn encode_function_call(call: &Call, func_contracts: &Contracts) -> Vec<Command> {
    let mut cmds = vec![];

    // Assert callee's precondition must hold
    for pre in &func_contracts.requires {
        cmds.push(Assert(encode_spec_with_args(pre, &call.args)));
    }

    // Havoc the return value (introduce fresh variable)
    let fresh_ret = fresh_var();
    cmds.push(DeclareConst(fresh_ret.clone(), encode_type(return_ty)));

    // Assume callee's postcondition
    for post in &func_contracts.ensures {
        cmds.push(Assert(encode_spec_with_result(post, &fresh_ret, &call.args)));
    }

    // Bind call destination to fresh return value
    cmds.push(Assert(Eq(call.destination, Const(fresh_ret))));

    cmds
}
```

**Build order:** After basic VCGen works, add contract lookup and modular encoding for Call terminators.

### Pattern 8: Loop Invariant Framework (Placeholder for Inference)

**What:** Require user-supplied loop invariants. Verify: (1) invariant holds on entry, (2) invariant preserved by iteration, (3) invariant + exit condition implies postcondition.

**When to use:** As foundation for loop support. Inference can be added later.

**Trade-offs:**
- **Pro:** Sound and complete with correct invariants. Standard approach (Dafny, Prusti, Frama-C).
- **Con:** User burden to write invariants. Manual effort.

**Future extension:** Loop invariant inference via LLMs, abstract interpretation, or Houdini-style guess-and-check.

**Example:**
```rust
// Encoding loop verification (manual invariants)
#[invariant("i <= n")]
#[invariant("sum == i * (i - 1) / 2")]
while i < n {
    sum += i;
    i += 1;
}

// VC generation (simplified):
// 1. Base case: precondition ⊢ invariant[0/i]
// 2. Inductive case: invariant ∧ i < n ⊢ wp(body, invariant)
// 3. Exit case: invariant ∧ ¬(i < n) ⊢ postcondition
```

## Data Flow

### Verification Pipeline Flow

```
User Code (Rust + Specifications)
    ↓
[Rustc Frontend: Parse → HIR → Type Check → Borrow Check]
    ↓
[Rustc MIR Generation] ──────────────┐
    ↓                                 │
[driver: after_analysis hook]        │
    ↓                                 │
┌────────────────────────────────────┴───────────────────┐
│ Extract Contracts from HIR Attributes                  │
│ (Scan for #[doc = "rust_fv::requires::..."])           │
└────────────────────────────────────┬───────────────────┘
    ↓                                 │
┌────────────────────────────────────┴───────────────────┐
│ Convert rustc MIR → Stable IR                          │
│ (Translate types, statements, terminators)             │
└────────────────────────────────────┬───────────────────┘
    ↓
┌────────────────────────────────────────────────────────┐
│ Generate Verification Conditions (VCGen)               │
│ - Walk basic blocks (currently linear, upgrade to SSA) │
│ - Encode assignments as SMT assertions                 │
│ - Generate overflow/div-by-zero checks                 │
│ - Generate contract verification queries               │
└────────────────────────────────────┬───────────────────┘
    ↓
┌────────────────────────────────────────────────────────┐
│ Encode to SMT-LIB (smtlib crate)                       │
│ - Map types → sorts (Ty::Int(i32) → BitVec(32))        │
│ - Map expressions → terms (Rvalue → Term)              │
│ - Build Script (sequence of commands)                  │
└────────────────────────────────────┬───────────────────┘
    ↓
┌────────────────────────────────────────────────────────┐
│ Format to SMT-LIB2 Text                                │
│ (declare-const x (_ BitVec 32))                        │
│ (assert (= x (bvadd y #x00000001)))                    │
└────────────────────────────────────┬───────────────────┘
    ↓
┌────────────────────────────────────────────────────────┐
│ Invoke Z3 Solver (subprocess)                          │
│ - Spawn: z3 -in -t:5000                                │
│ - Write SMT-LIB to stdin                               │
│ - Read stdout: sat/unsat/timeout/unknown               │
│ - Parse model if sat                                   │
└────────────────────────────────────┬───────────────────┘
    ↓
┌────────────────────────────────────────────────────────┐
│ Report Results                                         │
│ - UNSAT → Verified                                     │
│ - SAT → Failed (extract counterexample from model)     │
│ - Unknown → Timeout/solver limit                       │
└────────────────────────────────────────────────────────┘
```

### Key Data Transformations

1. **HIR Attributes → Contracts:** String matching on doc attributes to extract spec expressions.
2. **Rustc MIR → IR:** Type-preserving structural translation (isolates rustc changes).
3. **IR → VCs:** Symbolic execution or WP calculus to produce logical formulas.
4. **VCs → SMT-LIB:** Syntax translation (IR types/exprs to SMT sorts/terms).
5. **SMT-LIB → Z3 → Model:** Solver invocation and result parsing.

## Scaling Considerations

| Scale | Architecture Adjustments |
|-------|--------------------------|
| **Single-function verification (current)** | Current architecture sufficient. Linear VCGen works for straight-line code. |
| **Multi-function with contracts** | Add modular verification (Pattern 7). Verify functions independently using summaries. |
| **Loops and recursion** | Require SSA (Pattern 6) + invariants (Pattern 8). User-supplied invariants initially. |
| **Large codebase (1000+ functions)** | Add VC caching (reuse results for unchanged functions). Parallelize verification (independent VCs can run concurrently). Consider incremental verification. |
| **Complex types (structs, enums, arrays)** | Add SMT datatype encoding (structs → SMT records/datatypes). Use array theory for slices/arrays. May require quantifiers. |
| **Unsafe code / pointer reasoning** | Add separation logic encoding (Prusti/Creusot use Viper IDF logic). Model heap explicitly. Prophecy variables for mutable borrows (Pattern 9). |

### Scaling Priorities

1. **First bottleneck (current):** Lack of SSA encoding causes unsoundness for branches. **Fix:** Implement Pattern 6 (SSA VCGen) in Phase 2.
2. **Second bottleneck:** Missing loop invariants prevents loop verification. **Fix:** Add invariant syntax + verification (Pattern 8) in Phase 3.
3. **Third bottleneck:** Solver timeout on complex queries. **Fix:** Optimize VC generation (reduce assertions), add timeouts, use incremental solving (SMT push/pop).

## Anti-Patterns

### Anti-Pattern 1: Tight Coupling to Rustc Internals

**What people do:** Write verification logic directly against rustc types (TyCtxt, mir::Body, etc.) throughout the codebase.

**Why it's wrong:** Rustc internals are unstable and change frequently. Every compiler update breaks the tool. Impossible to unit test without full compiler. Debugging requires nightly toolchain.

**Do this instead:** Maintain a stable IR (Pattern 1). Isolate rustc coupling to a thin MIR converter layer. Write core verification logic (VCGen, encoding) against stable IR. This is how Prusti, Creusot, and Kani work.

### Anti-Pattern 2: Inline-All Inter-Procedural Verification

**What people do:** Inline function bodies at every call site to verify the entire program as one monolithic query.

**Why it's wrong:** Exponential blow-up in VC size. Even small programs become unsolvable. Doesn't scale past toy examples. Re-verifies library functions repeatedly.

**Do this instead:** Use modular verification (Pattern 7). Verify each function once against its contract. At call sites, assume callee postcondition. This is the standard approach in all production verifiers.

### Anti-Pattern 3: Mathematical Integers for Rust Integer Types

**What people do:** Encode i32 as SMT Int (mathematical integers, unbounded).

**Why it's wrong:** Misses overflow bugs (primary source of Rust verification interest). Unsound: SMT says verified, but code panics in production. Rust semantics use wrapping/checked arithmetic, not mathematical integers.

**Do this instead:** Use bitvector encoding (Pattern 4). i32 → BitVec(32). Generate overflow checks explicitly. Accept slightly larger SMT queries for correctness.

### Anti-Pattern 4: No Separation Between Encoding and Solving

**What people do:** Mix SMT encoding logic with Z3 API calls. Directly call solver.assert() during IR traversal.

**Why it's wrong:** Tightly couples to one solver (can't swap Z3 for CVC5/Vampire). Impossible to inspect/debug generated queries. Can't reuse encoding for different purposes (e.g., test generation). Hard to unit test encoding separately from solving.

**Do this instead:** Build SMT-LIB AST first (smtlib crate), then format and send to solver. Clear separation: IR → SMT-LIB AST → Text → Solver. Enables testing encoding logic without solver, supports multiple backends, allows query inspection/logging.

### Anti-Pattern 5: Ignoring Control Flow in VCGen

**What people do:** Encode all basic blocks as a flat sequence of assertions, ignoring branches and merges.

**Why it's wrong:** Unsound. Assumes all paths execute, even mutually exclusive branches. Generates contradictory assertions. May report spurious failures or false verification.

**Do this instead:** Use SSA with phi nodes (Pattern 6) or path-sensitive encoding. Track which path is taken. At merges, use ITE or phi nodes. Current rust-fv has this issue (linear walking) — must fix in Phase 2.

## Extension Points for Advanced Features

### 1. Loop Invariants (Phase 3)

**Current limitation:** No loop support (VCGen doesn't handle back edges).

**Extension architecture:**
- Add `#[invariant("...")]` attribute to proc macros.
- Parse invariants in contract extraction.
- Detect loops in IR (basic block with back edge).
- Generate three VCs per loop: base case, inductive case, exit case.
- Optional: Add invariant inference plugin (LLM-based, à la BALI system).

**Component changes:**
- `macros/`: Add `invariant!()` macro.
- `ir.rs`: Add `Loop { header, invariants, body }` node.
- `vcgen.rs`: Add `generate_loop_vcs()` function.

### 2. Mutable Borrow Reasoning with Prophecy Variables (Phase 4)

**Current limitation:** Borrows are treated transparently (borrow = value). Doesn't model borrow lifetime or "final value after borrow expires."

**Extension architecture (following Creusot pattern):**
- Introduce prophecy variables to represent "final value" of borrowed location.
- Current syntax: `*x` (current value). Final syntax: `^x` (final value after borrow).
- Generate prophesy declarations at borrow points.
- Connect prophecy to actual value when borrow expires.

**Component changes:**
- `ir.rs`: Add `Prophecy` operand variant.
- `encode_term.rs`: Add prophecy encoding (fresh uninterpreted constant).
- `vcgen.rs`: Add borrow/prophecy lifecycle tracking.

### 3. Aggregate Type Support (Phase 2-3)

**Current limitation:** Structs/tuples are uninterpreted. Cannot access fields in verification.

**Extension architecture:**
- Encode structs as SMT datatypes or records.
- Encode field access as SMT selector function.
- Encode struct construction as SMT constructor.

**Example:**
```rust
// Rust: struct Point { x: i32, y: i32 }
// SMT: (declare-datatype Point ((mk-Point (x (_ BitVec 32)) (y (_ BitVec 32)))))
// Rust: p.x
// SMT: (x p)
```

**Component changes:**
- `encode_sort.rs`: Add datatype generation for Ty::Struct.
- `encode_term.rs`: Add selector/constructor encoding for field access/construction.
- `ir.rs`: Preserve field metadata in Place projections.

### 4. Inter-Procedural Verification (Phase 4)

**Current limitation:** Only single-function verification. Calls are uninterpreted.

**Extension architecture:**
- Implement modular verification (Pattern 7).
- At call sites, encode as: assert precondition, havoc return, assume postcondition.
- Require contracts on all verified callees.

**Component changes:**
- `vcgen.rs`: Add `encode_call()` function implementing modular encoding.
- `callbacks.rs`: Build function signature → contract map.
- `ir.rs`: Include callee contract in Call terminator.

### 5. Enhanced Spec Parsing (Phase 2)

**Current limitation:** Simple hand-rolled parser (split on operators). No quantifiers, no complex expressions.

**Extension architecture:**
- Embed Rust expression parser (use syn crate).
- Extend with logical operators (forall, exists, ==>, old()).
- Type-check specs against function signature.

**Component changes:**
- `macros/`: Parse proc macro input as syn::Expr.
- `vcgen.rs`: Replace `parse_simple_spec()` with full expression evaluator.
- Add `spec_typeck.rs`: Type-check specs using Rust type rules.

## Integration Points

### External Dependencies

| Dependency | Integration Pattern | Notes |
|------------|---------------------|-------|
| **rustc_driver** | Callbacks::after_analysis hook | Nightly-only. Provides TyCtxt, HIR, MIR access. Update driver crate when rustc internals change. |
| **Z3 Solver** | Subprocess via stdin/stdout SMT-LIB protocol | Auto-detect z3 binary in PATH. Fallback to manual configuration. Timeout via `-t:N` flag. |
| **Proc Macros** | Attribute macros stored in doc attributes | Workaround: macros can't pass data to driver directly. Encode specs in `#[doc = "rust_fv::..."]`. |
| **Cargo** | Custom cargo command or RUSTC_WRAPPER | Invoke as `cargo rust-fv` (requires cargo plugin) or `RUSTC_WRAPPER=rust-fv-driver cargo check`. |

### Internal Boundaries

| Boundary | Communication | Notes |
|----------|---------------|-------|
| **driver ↔ analysis** | Stable IR types (ir::Function) | One-way: driver converts MIR → IR, passes to analysis. Analysis never touches rustc types. |
| **analysis ↔ smtlib** | SMT-LIB AST (Command, Term, Sort) | VCGen builds Scripts, solver formats to text. No reverse dependency. |
| **smtlib ↔ solver** | Text (SMT-LIB2 standard) | Process boundary. Solver is external binary. Parser handles responses. |
| **macros ↔ driver** | Hidden doc attributes | Macros write specs to HIR attributes. Driver scans attributes at analysis time. |

## Proven Patterns from Existing Tools

### Prusti Architecture (ETH Zurich)

- **Compiler integration:** rustc_driver callbacks, uses unoptimized MIR (borrow checker runs on it).
- **Backend:** Translates to Viper intermediate verification language (Implicit Dynamic Frames separation logic).
- **Modularity:** Encodes Rust's ownership as separation logic predicates.
- **Specification:** Procedural macros for contracts, reuses Rust syntax for specs.
- **Key insight:** Leverage Rust's type system for modular verification. Ownership = separation logic permissions.

**Lessons for rust-fv:**
- SSA encoding is critical (Prusti generates SSA from MIR).
- Modular verification scales (Prusti verifies functions independently).
- Separation logic needed for heap reasoning (consider Viper-like encoding for unsafe code).

### Creusot Architecture (Inria)

- **Compiler integration:** rustc_driver, MIR → Coma (Why3 IR).
- **Specification language:** Pearlite (embedded pure functional DSL, Rust-like syntax).
- **Prophecy variables:** Used for mutable borrows (^x = final value syntax).
- **Backend:** Why3 platform (supports multiple provers: Z3, CVC5, Alt-Ergo).
- **Key insight:** Functional translation (Rust → pure functions) simplifies reasoning. Prophecies handle mutable borrows compositionally.

**Lessons for rust-fv:**
- Prophecy variables essential for sound borrow reasoning (add in Phase 4).
- Pearlite's Rust-like spec syntax is ergonomic (consider for enhanced parser).
- Why3 backend enables prover diversity (smtlib abstraction supports this).

### Kani Architecture (AWS)

- **Compiler integration:** rustc_driver, MIR → CBMC IR.
- **Approach:** Bounded model checking (unroll loops N times, bit-precise).
- **Backend:** CBMC (C Bounded Model Checker), SAT solver.
- **Key insight:** Bounded verification is complementary to deductive (finds bugs fast, doesn't prove correctness).

**Lessons for rust-fv:**
- Bitvector encoding is standard (Kani uses bit-precise CBMC).
- Bounded model checking useful for bug-finding mode (consider adding BMC backend option).

## Build Order for Extensions

**Phase 2: Core Soundness**
1. Implement SSA conversion (Pattern 6) — foundational for all control flow.
2. Add aggregate type encoding (structs/tuples via SMT datatypes).
3. Enhance spec parser (support quantifiers, implications).

**Phase 3: Loop Support**
1. Add loop invariant syntax to macros.
2. Implement loop VC generation (base, inductive, exit).
3. (Optional) Add basic invariant inference (e.g., LLM-based suggestion).

**Phase 4: Inter-Procedural Verification**
1. Implement modular call encoding (assume/assert contracts).
2. Build function contract database.
3. Add call graph analysis (detect cycles, require termination measures).

**Phase 5: Advanced Borrow Reasoning**
1. Add prophecy variables to IR.
2. Implement prophecy lifecycle tracking in VCGen.
3. Extend spec language with Current/Final operators (*x, ^x).

**Phase 6: Optimizations**
1. Add VC caching (skip unchanged functions).
2. Implement incremental solving (SMT push/pop for related queries).
3. Parallelize verification (independent VCs in separate solver instances).

## Sources

### Academic Publications
- [The Prusti Project: Formal Verification for Rust](https://pm.inf.ethz.ch/publications/AstrauskasBilyFialaGrannanMathejaMuellerPoliSummers22.pdf) (NFM 2022) — Architecture of Prusti verifier
- [Leveraging Rust Types for Modular Specification and Verification](https://www.cs.ubc.ca/~alexsumm/papers/AstrauskasMuellerPoliSummers19.pdf) (OOPSLA 2019) — Modular verification approach
- [Creusot: A Foundry for Deductive Verification of Rust Programs](https://inria.hal.science/hal-03737878/document) (ICFEM 2022) — Creusot architecture and Why3 translation
- [The Future is Ours: Prophecy Variables in Separation Logic](https://dl.acm.org/doi/10.1145/3371113) (POPL 2020) — Prophecy variables for mutable borrows
- [BALI: Branch-Aware Loop Invariant Inference with LLMs](https://arxiv.org/pdf/2601.00882) (2026) — LLM-based loop invariant inference

### Tools and Documentation
- [Rust Formal Methods Interest Group](https://rust-formal-methods.github.io/) — Overview of Rust verification ecosystem
- [KMIR: Formal Semantics of Rust MIR](https://runtimeverification.com/blog/introducing-kmir) — K Framework semantics for MIR
- [Kani Rust Verifier](https://github.com/model-checking/kani) — AWS's bounded model checker for Rust
- [Creusot Architecture Documentation](https://github.com/creusot-rs/creusot) — Creusot component structure
- [Why3 Platform](https://why3.lri.fr/) — Multi-prover verification platform
- [SMT-LIB Standard](https://smt-lib.org/) — SMT-LIB language specification
- [Z3 Theorem Prover](https://github.com/Z3Prover/z3) — Microsoft Research SMT solver

### Verification Theory
- [Weakest Precondition Semantics](https://softwarefoundations.cis.upenn.edu/slf-current/WPsem.html) (Software Foundations) — WP calculus theory
- [Static Single Assignment Form](https://www.cs.cornell.edu/courses/cs6120/2022sp/lesson/6/) (Cornell CS 6120) — SSA principles
- [Boogie: An Intermediate Verification Language](https://www.microsoft.com/en-us/research/publication/boogie-an-intermediate-verification-language/) — IVL design patterns
- [SMT Solving for Program Verification](https://ocamlpro.github.io/verification_for_dummies/smt/) (OCamlPro) — SMT solver usage patterns

---
*Architecture research for: Rust formal verification tools*
*Researched: 2026-02-10*
*Confidence: HIGH (based on production tools Prusti/Creusot/Kani + SMT verification literature)*
