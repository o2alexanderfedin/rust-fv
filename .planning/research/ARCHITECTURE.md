# Architecture Patterns: Advanced Verification Features Integration

**Domain:** Formal verification tool enhancement
**Researched:** 2026-02-11
**Focus:** Integration of recursive functions, closures, traits, unsafe code, lifetimes, floating-point, and concurrency into existing 5-crate architecture

## Executive Summary

The existing rust-fv architecture is well-positioned for advanced feature integration. The 5-crate separation (macros, smtlib, solver, analysis, driver) provides clean boundaries for extending verification capabilities. Key architectural patterns from existing tools (Creusot, Prusti, Verus) inform integration strategies:

- **Recursive functions**: Uninterpreted function encoding in smtlib/, termination analysis in analysis/
- **Closures**: Defunctionalization in analysis/, first-order encoding in smtlib/
- **Trait objects**: V-table modeling in IR, dynamic dispatch resolution in analysis/
- **Unsafe code**: Memory model in analysis/, separation logic encoding in smtlib/
- **Lifetimes**: Borrow graph analysis in analysis/, region encoding in IR
- **Floating-point**: IEEE 754 FPA theory in smtlib/, rounding mode tracking in analysis/
- **Concurrency**: Thread interleaving in analysis/, happens-before relations in smtlib/

## Existing Architecture Foundation

### Current Component Structure

| Crate | Current Responsibility | Lines of Code | Key Types |
|-------|----------------------|---------------|-----------|
| **macros/** | Proc macros for annotations | ~500 | `#[requires]`, `#[ensures]`, `#[invariant]` |
| **smtlib/** | SMT-LIB AST and formatting | ~2000 | `Term`, `Sort`, `Command`, `Script` |
| **solver/** | Z3 backend abstraction | ~1500 | `SolverBackend` trait, `Z3Solver`, `Z3NativeSolver` |
| **analysis/** | IR, VCGen, encoding | ~15000 | `Function`, `VcGen`, `ContractDatabase`, `CallGraph` |
| **driver/** | Rustc integration, orchestration | ~4000 | `MirConverter`, diagnostics, caching |

### Current Data Flow

```
Source code with annotations
    ↓
[macros/] Parse annotations → HIR attributes
    ↓
[driver/] Extract MIR → Convert to IR
    ↓
[analysis/] Generate VCs → Encode to SMT
    ↓
[solver/] Check SAT → Parse results
    ↓
[driver/] Format diagnostics → Output
```

### Existing Extension Points

1. **IR types** (`analysis/src/ir.rs`): `Ty`, `Rvalue`, `Terminator` enums support new constructs
2. **Encoding modules** (`analysis/src/encode_*.rs`): Modular encoding for types, terms, quantifiers
3. **VCGen hooks** (`analysis/src/vcgen.rs`): Path traversal, terminator handling, VC generation
4. **SMT theories** (`smtlib/src/*.rs`): Theory-specific term constructors
5. **Contract database** (`analysis/src/contract_db.rs`): Function summaries for modular verification

## Integration Architecture by Feature

### 1. Recursive Functions

#### Components to Add

**New in analysis/:**
- `termination.rs`: Termination analysis and well-foundedness checking
- `recursion_encoding.rs`: Uninterpreted function declaration and axiomatization

**Modified:**
- `ir.rs`: Add `RecursiveInfo` to `Function` (base cases, recursive calls, decreases clause)
- `vcgen.rs`: Detect recursive calls, generate termination VCs
- `contract_db.rs`: Store recursion contracts (decreases clauses)

**New in smtlib/:**
- `uninterpreted.rs`: Uninterpreted function declarations and fuel-based unrolling
- Extend `Command` enum: `DeclareFun`, `DefineFunRec` (Z3-specific)

#### Data Flow

```
Recursive function with #[decreases(measure)]
    ↓
[analysis/termination.rs] Extract decreases clause, identify recursive calls
    ↓
[analysis/recursion_encoding.rs] Encode as uninterpreted function + axioms
    ↓
[smtlib/uninterpreted.rs] Generate (declare-fun f ...) + (assert (forall ...))
    ↓
[solver/] Z3 with recursive function theory
```

#### Integration Points

| Component | Integration | Dependencies |
|-----------|-------------|--------------|
| `ir.rs` | Add `recursive_info: Option<RecursionInfo>` | None |
| `vcgen.rs` | Check `termination_vc()` before `postcondition_vc()` | `termination.rs` |
| `contract_db.rs` | Store `decreases` clause | `ir.rs` |
| `smtlib/command.rs` | Add `DeclareFun(name, params, ret)` | None |

#### Encoding Strategy

**Approach: Uninterpreted functions with axiomatization** (HIGH confidence)

```rust
// For: fn factorial(n: u32) -> u32 #[decreases(n)]
// Generate:
(declare-fun factorial ((_ BitVec 32)) (_ BitVec 32))
(assert (forall ((n (_ BitVec 32)))
  (=> (= n #x00000000) (= (factorial n) #x00000001))))
(assert (forall ((n (_ BitVec 32)))
  (=> (bvugt n #x00000000)
      (= (factorial n)
         (bvmul n (factorial (bvsub n #x00000001)))))))
// Termination VC:
(assert (forall ((n (_ BitVec 32)))
  (=> (bvugt n #x00000000)
      (bvult (bvsub n #x00000001) n))))
```

**Alternative: Bounded unrolling** (for non-terminating cases)
- Fuel parameter limits recursion depth
- Used by F* and Dafny
- Lower confidence for deep recursion

---

### 2. Closures and Higher-Order Functions

#### Components to Add

**New in analysis/:**
- `closure_conversion.rs`: Defunctionalization and closure environment capture
- `higher_order.rs`: Higher-order function encoding

**Modified:**
- `ir.rs`: Add `Ty::Closure(env_fields, params, ret)`, `Rvalue::ClosureCall`
- `vcgen.rs`: Handle closure calls, environment encoding
- `mir_converter.rs` (driver): Extract closure MIR, capture analysis

**New in smtlib/:**
- `datatype.rs`: Closure sum types (one variant per closure)

#### Data Flow

```
Closure with captured environment
    ↓
[driver/mir_converter.rs] Extract closure MIR + upvars
    ↓
[analysis/closure_conversion.rs] Defunctionalize to first-order
    ↓
[analysis/encode_sort.rs] Encode closure type as datatype
    ↓
[smtlib/] Generate sum type + function per closure
```

#### Integration Points

| Component | Integration | Dependencies |
|-----------|-------------|--------------|
| `ir.rs` | Add `Closure` variant to `Ty`, `Terminator::ClosureCall` | None |
| `closure_conversion.rs` | Transform closures to datatypes + functions | `ir.rs` |
| `smtlib/datatype.rs` | Generate `(declare-datatypes ...)` for closures | `command.rs` |
| `vcgen.rs` | Encode closure calls via datatype matching | `encode_term.rs` |

#### Encoding Strategy

**Approach: Defunctionalization** (HIGH confidence, based on Creusot/Verus research)

```rust
// For: let f = |x| x + captured; f(5)
// Transform to:
(declare-datatype Closure
  ((Closure_1 (captured Int))))
(define-fun apply_Closure_1 ((closure Closure) (x Int)) Int
  (+ x (captured (as closure Closure_1))))
// At call site:
(apply_Closure_1 (Closure_1 captured_val) 5)
```

**Alternative: Direct encoding** (for simple cases)
- Inline closure body at call sites
- No datatype overhead
- Only works for non-escaping closures

---

### 3. Trait Objects and Dynamic Dispatch

#### Components to Add

**New in analysis/:**
- `vtable.rs`: V-table modeling and dispatch resolution
- `trait_encoding.rs`: Trait constraint encoding

**Modified:**
- `ir.rs`: Add `Ty::DynTrait(trait_name)`, `Rvalue::DynDispatch(vtable, method_index)`
- `vcgen.rs`: Resolve dynamic dispatch to concrete types
- `contract_db.rs`: Store trait method contracts

**New in smtlib/:**
- Extend datatypes for trait objects (fat pointer: data + vtable)

#### Data Flow

```
Trait object call
    ↓
[driver/] Extract dyn trait type + available implementations
    ↓
[analysis/vtable.rs] Build v-table mapping, enumerate concrete types
    ↓
[analysis/trait_encoding.rs] Encode as sum type over implementors
    ↓
[vcgen.rs] Generate VC for each possible concrete type
    ↓
[smtlib/] Encode as ITE chain or quantified formula
```

#### Integration Points

| Component | Integration | Dependencies |
|-----------|-------------|--------------|
| `ir.rs` | Add `DynTrait(name)` to `Ty`, `vtable_index` metadata | None |
| `vtable.rs` | Map trait methods to implementor functions | `contract_db.rs` |
| `trait_encoding.rs` | Generate sum type for `dyn Trait` | `encode_sort.rs` |
| `vcgen.rs` | Split VCs per concrete type | `vtable.rs` |

#### Encoding Strategy

**Approach: Sum type over concrete implementations** (MEDIUM confidence)

```rust
// For: fn process(x: &dyn Display)
// If Display is implemented by String, u32:
(declare-datatype DynDisplay
  ((DynDisplay_String (data String))
   (DynDisplay_u32 (data (_ BitVec 32)))))
// At call site:
(assert (or
  (and (is DynDisplay_String x) (display_String (data x)))
  (and (is DynDisplay_u32 x) (display_u32 (data x)))))
```

**Challenges:**
- Scalability: sum type grows with implementors
- Open-world assumption: may need to assume unknown implementors
- Research gap: No established SMT encoding for open trait objects (LOW confidence for open-world)

---

### 4. Unsafe Code

#### Components to Add

**New in analysis/:**
- `memory_model.rs`: Heap model, pointer validity, aliasing
- `unsafe_analysis.rs`: Safety obligations for unsafe blocks
- `separation_logic.rs`: Optional: separation logic encoding

**Modified:**
- `ir.rs`: Add `Ty::RawPtr` handling, `Rvalue::PtrOffset`, `is_unsafe: bool` to blocks
- `vcgen.rs`: Generate memory safety VCs (null checks, bounds, aliasing)
- `ownership.rs`: Extend for raw pointer reasoning

**New in smtlib/:**
- `memory.rs`: Heap theory (array theory + validity predicates)

#### Data Flow

```
Unsafe block with raw pointers
    ↓
[driver/] Mark unsafe regions in IR
    ↓
[analysis/unsafe_analysis.rs] Extract safety obligations
    ↓
[analysis/memory_model.rs] Model heap, generate validity VCs
    ↓
[smtlib/memory.rs] Encode heap as SMT array + validity predicates
    ↓
[solver/] Check memory safety VCs
```

#### Integration Points

| Component | Integration | Dependencies |
|-----------|-------------|--------------|
| `ir.rs` | Add `is_unsafe: bool` to `BasicBlock`, pointer operations | None |
| `memory_model.rs` | Heap representation, validity tracking | `encode_sort.rs` |
| `vcgen.rs` | Generate `null_check_vc()`, `bounds_check_vc()`, `aliasing_vc()` | `memory_model.rs` |
| `smtlib/memory.rs` | `(declare-const heap (Array Addr Val))` | `term.rs` |

#### Encoding Strategy

**Approach: Heap-as-array with validity predicates** (MEDIUM confidence, based on Verus)

```rust
// For: unsafe { *ptr = 42; }
// Generate:
(declare-const heap (Array (_ BitVec 64) (_ BitVec 32)))
(declare-fun valid ((_ BitVec 64)) Bool)
// VCs:
(assert (not (= ptr #x0000000000000000))) ; null check
(assert (valid ptr))                      ; validity check
(assert (= (select heap ptr) old_value))  ; read VC
(define heap_new (store heap ptr #x0000002a)) ; write
```

**Alternative: Separation logic** (HIGH complexity, HIGH confidence for correctness)
- Used by Prusti/RustBelt
- Requires significant SMT encoding machinery
- Recommend Phase 2+ (defer for initial implementation)

---

### 5. Lifetime and Borrow Reasoning

#### Components to Add

**New in analysis/:**
- `lifetime_analysis.rs`: Lifetime inference, borrow graph
- `region_encoding.rs`: Lifetime regions in SMT

**Modified:**
- `ir.rs`: Add `Lifetime` metadata to `Ty::Ref`, `borrows: Vec<BorrowInfo>` to `Function`
- `ownership.rs`: Extend with lifetime constraints
- `encode_prophecy.rs`: Already handles mutable borrows; extend for lifetimes

**New in smtlib/:**
- Lifetime ordering relations (`(declare-fun outlives (Region Region) Bool)`)

#### Data Flow

```
Function with lifetime annotations
    ↓
[driver/] Extract MIR lifetime regions
    ↓
[analysis/lifetime_analysis.rs] Build borrow graph, region constraints
    ↓
[analysis/region_encoding.rs] Encode region ordering as SMT
    ↓
[smtlib/] Generate outlives constraints
    ↓
[vcgen.rs] Verify borrow validity using lifetime constraints
```

#### Integration Points

| Component | Integration | Dependencies |
|-----------|-------------|--------------|
| `ir.rs` | Add `lifetime: Option<Lifetime>` to `Ty::Ref` | None |
| `lifetime_analysis.rs` | Extract borrow graph from MIR | `driver/mir_converter.rs` |
| `ownership.rs` | Add `lifetime_constraint_vc()` | `lifetime_analysis.rs` |
| `smtlib/term.rs` | Add `Outlives(lhs, rhs)` predicate | None |

#### Encoding Strategy

**Approach: Prophecy-based (existing) + region ordering** (HIGH confidence, extends existing)

```rust
// Existing prophecy encoding handles mutable borrows.
// Add:
(declare-sort Region)
(declare-const 'a Region)
(declare-const 'b Region)
(declare-fun outlives (Region Region) Bool)
(assert (outlives 'a 'b)) ; 'a: 'b constraint
// Borrow validity:
(assert (=> (valid_borrow x 'a) (alive_at 'a use_point)))
```

**Key insight:** Existing `encode_prophecy.rs` already handles final value reasoning. Lifetimes add temporal validity constraints on top.

---

### 6. Floating-Point Arithmetic

#### Components to Add

**New in smtlib/:**
- `fpa_theory.rs`: IEEE 754 floating-point theory terms
- Extend `Sort`: `Float32`, `Float64`
- Extend `Term`: `FpLit`, `FpAdd`, `FpMul`, rounding modes

**Modified:**
- `analysis/encode_sort.rs`: Map `Ty::Float(FloatTy)` to FPA sorts
- `analysis/encode_term.rs`: Encode FP operations with rounding modes
- `analysis/vcgen.rs`: Generate FP overflow/underflow VCs

**New in solver/:**
- Verify Z3/CVC5 support for FPA theory

#### Data Flow

```
Function with floating-point operations
    ↓
[driver/] Extract FP operations from MIR
    ↓
[analysis/encode_term.rs] Encode with rounding mode
    ↓
[smtlib/fpa_theory.rs] Generate FPA theory terms
    ↓
[solver/] Z3 with FPA theory
```

#### Integration Points

| Component | Integration | Dependencies |
|-----------|-------------|--------------|
| `smtlib/sort.rs` | Add `Float32`, `Float64` to `Sort` enum | None |
| `smtlib/term.rs` | Add `FpAdd`, `FpMul`, `RoundingMode` variants | None |
| `encode_term.rs` | Encode `BinOp` for floats using FPA ops | `fpa_theory.rs` |
| `vcgen.rs` | Generate NaN/Inf VCs | `encode_term.rs` |

#### Encoding Strategy

**Approach: SMT-LIB FPA theory** (HIGH confidence, standardized)

```rust
// For: let z = x + y; (f32)
// Generate:
(declare-const x Float32)
(declare-const y Float32)
(declare-const z Float32)
(assert (= z (fp.add RNE x y))) ; RNE = round-to-nearest-even
// VCs:
(assert (not (fp.isNaN z)))
(assert (not (fp.isInfinite z)))
```

**Challenges:**
- Bit-blasting overhead: FPA theory is expensive in SMT solvers
- Rounding mode tracking: requires flow-sensitive analysis
- Z3 FPA support: Mature (MEDIUM confidence for performance)

---

### 7. Concurrency (Thread Safety & Data Races)

#### Components to Add

**New in analysis/:**
- `concurrency.rs`: Thread interleaving, happens-before analysis
- `sync_encoding.rs`: Mutex, RwLock, atomic operations encoding

**Modified:**
- `ir.rs`: Add `Terminator::Spawn(thread_id, closure)`, `Rvalue::AtomicOp`
- `vcgen.rs`: Generate data race VCs, mutex invariant VCs

**New in smtlib/:**
- `concurrency.rs`: Happens-before relations, thread-local state

#### Data Flow

```
Function with threads/atomics
    ↓
[driver/] Extract thread spawn, atomic operations
    ↓
[analysis/concurrency.rs] Build happens-before graph
    ↓
[analysis/sync_encoding.rs] Encode synchronization primitives
    ↓
[smtlib/concurrency.rs] Generate ordering constraints
    ↓
[vcgen.rs] Check data race freedom
```

#### Integration Points

| Component | Integration | Dependencies |
|-----------|-------------|--------------|
| `ir.rs` | Add `Spawn`, `Join`, `AtomicLoad/Store` terminators/rvalues | None |
| `concurrency.rs` | Happens-before analysis, thread interleaving | `ir.rs` |
| `vcgen.rs` | Generate `data_race_vc()`, `lock_order_vc()` | `concurrency.rs` |
| `smtlib/term.rs` | Add `HappensBefore(event1, event2)` | None |

#### Encoding Strategy

**Approach: Bounded thread interleaving** (MEDIUM confidence)

```rust
// For: spawn(|| { x = 1; }); spawn(|| { y = x; });
// Generate:
(declare-const x_thread1 Int)
(declare-const x_thread2 Int)
(declare-fun happens_before (Event Event) Bool)
(assert (=> (happens_before write_x_thread1 read_x_thread2)
            (= x_thread2 1)))
// Data race VC:
(assert (not (and (not (happens_before write_x_thread1 read_x_thread2))
                  (not (happens_before read_x_thread2 write_x_thread1)))))
```

**Alternative: Rely-guarantee reasoning** (HIGH complexity, research-level)
- Used by RustHornBelt for concurrency
- Requires separation logic + thread-local invariants
- Recommend Phase 3+ (advanced concurrency)

**Pragmatic subset: `Send`/`Sync` verification only**
- Verify trait bounds statically (existing type system)
- Defer happens-before reasoning to later phase

---

## Cross-Cutting Architecture Patterns

### 1. Modular Encoding Pattern

**Applied to:** All features

```
ir.rs (new IR construct)
    ↓
encode_<feature>.rs (feature-specific encoding)
    ↓
smtlib/<theory>.rs (SMT theory terms)
    ↓
vcgen.rs (VC generation hooks)
```

**Example structure for closures:**
```
analysis/
  closure_conversion.rs  -- Defunctionalization
  encode_closure.rs      -- SMT encoding
smtlib/
  datatype.rs            -- Closure datatypes (extends existing)
```

### 2. Incremental VC Generation

**Existing:** `vcgen.rs` generates VCs per-path
**Extension:** Feature-specific VCs added to `VcKind` enum

```rust
pub enum VcKind {
    // Existing
    Precondition, Postcondition, Overflow, ...
    // New
    Termination,        // Recursive functions
    ClosureWellFormed,  // Closures
    DynamicDispatch,    // Trait objects
    MemorySafety,       // Unsafe code
    BorrowValidity,     // Lifetimes
    FloatingPointNaN,   // Floating-point
    DataRaceFreedom,    // Concurrency
}
```

### 3. Progressive Enhancement

**Strategy:** Each feature adds:
1. New IR variants (opt-in via `Option<T>`)
2. New encoding modules (separate files)
3. New VCs (extend `VcKind`)
4. New SMT theories (separate theory modules)

**Backward compatibility:** Features with `None` metadata use existing codepaths.

### 4. Contract Database Extension

**Existing:** `FunctionSummary` stores requires/ensures
**Extension:** Feature-specific metadata

```rust
pub struct FunctionSummary {
    pub contracts: Contracts,
    pub param_names: Vec<String>,
    pub param_types: Vec<Ty>,
    pub return_ty: Ty,
    // NEW:
    pub recursion_info: Option<RecursionInfo>,   // Recursive functions
    pub closure_env: Option<ClosureEnv>,         // Closures
    pub trait_bounds: Vec<TraitBound>,           // Trait constraints
    pub unsafe_preconditions: Vec<SafetyObligation>, // Unsafe
    pub lifetime_bounds: Vec<LifetimeBound>,     // Lifetimes
}
```

---

## Recommended Component Build Order

Based on dependency analysis and incremental integration:

### Phase 1: Foundations (Minimal Dependencies)
1. **Floating-point** (smtlib/fpa_theory.rs → encode_term.rs)
   - Self-contained, well-defined SMT theory
   - No new IR constructs, only encoding changes
   - Risk: Low, SMT-LIB FPA is standardized

2. **Recursive functions** (analysis/termination.rs → recursion_encoding.rs)
   - Extends existing IR minimally (`recursive_info`)
   - Uninterpreted functions well-supported in Z3
   - Risk: Medium (termination proving hard, but encoding simple)

### Phase 2: Higher-Order Features (Depends on IR extensions)
3. **Closures** (analysis/closure_conversion.rs → encode_closure.rs)
   - Requires datatype support (extend existing)
   - Defunctionalization well-understood
   - Risk: Medium (capture analysis complexity)

4. **Trait objects** (analysis/vtable.rs → trait_encoding.rs)
   - Depends on closure encoding (similar sum type pattern)
   - Closed-world assumption simplifies encoding
   - Risk: Medium (scalability with many implementors)

### Phase 3: Memory Reasoning (Depends on Phases 1-2)
5. **Lifetimes** (analysis/lifetime_analysis.rs → region_encoding.rs)
   - Extends existing prophecy encoding
   - Adds ordering constraints to SMT
   - Risk: Medium (borrow graph complexity)

6. **Unsafe code** (analysis/memory_model.rs → unsafe_analysis.rs)
   - Requires heap model (array theory)
   - Depends on lifetime reasoning for pointer validity
   - Risk: High (memory model soundness critical)

### Phase 4: Concurrency (Depends on all previous)
7. **Concurrency** (analysis/concurrency.rs → sync_encoding.rs)
   - Requires memory model + happens-before
   - Most complex feature, highest research risk
   - Risk: High (thread interleaving explosion)

---

## Suggested Build Order (Summary)

| Order | Feature | Rationale | Complexity | Risk |
|-------|---------|-----------|------------|------|
| 1 | Floating-point | Self-contained, standardized theory | Low | Low |
| 2 | Recursive functions | Foundational, uninterpreted functions simple | Medium | Medium |
| 3 | Closures | Enables higher-order verification | Medium | Medium |
| 4 | Trait objects | Builds on closure patterns | Medium | Medium |
| 5 | Lifetimes | Extends existing prophecy encoding | Medium | Medium |
| 6 | Unsafe code | Critical for soundness, needs lifetime support | High | High |
| 7 | Concurrency | Most complex, depends on memory model | High | High |

---

## Data Flow Changes (Integrated View)

```
[EXISTING]
Source → macros/ → driver/MIR → analysis/IR → vcgen → smtlib/ → solver/

[WITH ADVANCED FEATURES]
Source with #[decreases], closures, dyn Trait, unsafe, 'a lifetimes, f32, spawn
    ↓
[macros/] Parse all annotations (termination, safety obligations)
    ↓
[driver/mir_converter.rs] Extract:
  - Recursive call sites + decreases clauses
  - Closure upvars + capture modes
  - Trait object vtables + implementors
  - Unsafe blocks + pointer operations
  - Lifetime regions + borrow graph
  - Floating-point rounding modes
  - Thread spawns + atomic operations
    ↓
[analysis/] Feature-specific analysis:
  - termination.rs: Check well-foundedness
  - closure_conversion.rs: Defunctionalize
  - vtable.rs: Build dispatch table
  - unsafe_analysis.rs: Extract safety obligations
  - lifetime_analysis.rs: Borrow graph + outlives
  - (FP: direct encoding, no analysis)
  - concurrency.rs: Happens-before graph
    ↓
[analysis/encode_*.rs] Feature-specific encodings:
  - recursion_encoding.rs → uninterpreted functions
  - encode_closure.rs → datatypes
  - trait_encoding.rs → sum types
  - memory_model.rs → heap arrays
  - region_encoding.rs → outlives constraints
  - encode_term.rs (FP) → FPA theory terms
  - sync_encoding.rs → happens-before predicates
    ↓
[vcgen.rs] Generate VCs (extended VcKind):
  - Termination VCs
  - Closure well-formedness VCs
  - Dynamic dispatch VCs
  - Memory safety VCs
  - Borrow validity VCs
  - FP NaN/Inf VCs
  - Data race VCs
    ↓
[smtlib/] Extended theories:
  - uninterpreted.rs (recursive)
  - datatype.rs (closures, traits)
  - memory.rs (heap)
  - (lifetime ordering inline)
  - fpa_theory.rs (floats)
  - concurrency.rs (threads)
    ↓
[solver/] Z3 with theories: BV + Arrays + Datatypes + UF + FPA + (partial: Concurrency)
    ↓
[driver/] Extended diagnostics per VcKind
```

---

## New Components Summary

| Crate | New Modules | Estimated LOC | Dependencies |
|-------|-------------|---------------|--------------|
| **analysis/** | `termination.rs`, `recursion_encoding.rs`, `closure_conversion.rs`, `higher_order.rs`, `vtable.rs`, `trait_encoding.rs`, `memory_model.rs`, `unsafe_analysis.rs`, `separation_logic.rs` (opt), `lifetime_analysis.rs`, `region_encoding.rs`, `concurrency.rs`, `sync_encoding.rs` | +8000 | `ir.rs`, `encode_*.rs` |
| **smtlib/** | `uninterpreted.rs`, `datatype.rs` (extend), `memory.rs`, `fpa_theory.rs`, `concurrency.rs` | +2000 | `term.rs`, `command.rs` |
| **driver/** | (Minimal) MIR extraction extensions in `mir_converter.rs` | +500 | `rustc` internals |
| **macros/** | (Minimal) `#[decreases]`, `#[trusted]` macros | +200 | `syn`, `quote` |
| **solver/** | (Minimal) Z3 FPA feature flags | +100 | `z3` crate |
| **Total** | | **~10800 LOC** | |

---

## Modified Components Summary

| File | Modifications | Estimated LOC | Reason |
|------|---------------|---------------|--------|
| `analysis/ir.rs` | Add `Ty::Closure`, `Ty::DynTrait`, `Lifetime`, `RecursiveInfo`, `is_unsafe`, `Terminator::Spawn`, `Rvalue::AtomicOp` | +500 | Support new constructs |
| `analysis/vcgen.rs` | Add feature-specific VC generation hooks | +800 | VC generation entry points |
| `analysis/contract_db.rs` | Extend `FunctionSummary` with feature metadata | +200 | Modular verification metadata |
| `analysis/ownership.rs` | Add lifetime constraint generation | +300 | Lifetime reasoning |
| `analysis/encode_term.rs` | Add FP encoding, closure encoding | +400 | SMT encoding |
| `driver/mir_converter.rs` | Extract closure upvars, lifetimes, unsafe blocks | +600 | MIR extraction |
| `smtlib/term.rs` | Add FPA terms, happens-before, outlives | +300 | SMT theory support |
| `smtlib/command.rs` | Add `DeclareFun`, `DefineFunRec` | +100 | Recursive functions |
| `driver/diagnostics.rs` | Add error messages for new VcKinds | +200 | User experience |
| **Total** | | **~3400 LOC** | |

---

## Architectural Principles (From Existing Codebase)

The existing codebase demonstrates these principles, which guide integration:

1. **Separation of Concerns**: IR decoupled from rustc MIR (enables testability)
   - **Apply to:** All features use internal IR, not rustc types

2. **Modular Encoding**: `encode_term.rs`, `encode_sort.rs`, `encode_quantifier.rs`
   - **Apply to:** Each feature gets its own `encode_<feature>.rs`

3. **Extensible Enums**: `Ty`, `Rvalue`, `Terminator` designed for extension
   - **Apply to:** Add variants, not wrapper types

4. **Testability**: Every encoding module has unit tests
   - **Apply to:** Each new module includes:
     - Unit tests (encoding correctness)
     - Integration tests (VCGen end-to-end)
     - SMT-level tests (solver behavior)

5. **Contract-Based Modularity**: `ContractDatabase` + `CallGraph` for interprocedural
   - **Apply to:** Extend `FunctionSummary` for feature metadata

6. **Path-Condition Encoding**: VCGen uses path conditions, not SSA phi-nodes
   - **Apply to:** Closures, trait objects use path-based encoding

---

## Confidence Assessment

| Feature | Architecture Confidence | SMT Encoding Confidence | Integration Risk |
|---------|------------------------|------------------------|------------------|
| Recursive functions | HIGH (uninterpreted functions standard) | MEDIUM (termination proving hard) | LOW |
| Closures | HIGH (defunctionalization well-known) | HIGH (datatype encoding proven) | MEDIUM |
| Trait objects | MEDIUM (sum type scalability unclear) | MEDIUM (open-world assumption hard) | MEDIUM |
| Unsafe code | MEDIUM (heap models researched) | LOW (separation logic complex) | HIGH |
| Lifetimes | HIGH (extends existing prophecy) | MEDIUM (borrow graph extraction) | MEDIUM |
| Floating-point | HIGH (SMT-LIB FPA standardized) | HIGH (Z3 support mature) | LOW |
| Concurrency | LOW (thread interleaving explosion) | LOW (SMT scalability unclear) | HIGH |

---

## Open Questions & Research Gaps

1. **Trait objects: Open-world assumption**
   - How to soundly verify `dyn Trait` when new implementors may exist?
   - Resolution: Require closed-world annotation or assume bounded implementors

2. **Unsafe code: Separation logic integration**
   - Full separation logic (Prusti-style) vs. simpler heap model (Verus-style)?
   - Resolution: Start with heap-as-array, defer separation logic to Phase 2

3. **Concurrency: Thread interleaving bounds**
   - How many interleavings to explore before giving up?
   - Resolution: Bounded model checking with configurable bound

4. **Recursive functions: Fuel vs. uninterpreted functions**
   - When to use bounded unrolling (fuel) vs. full axiomatization?
   - Resolution: Uninterpreted by default, fuel as fallback for non-terminating

5. **Closures: Higher-order contracts**
   - How to specify contracts on closure parameters?
   - Resolution: Require explicit closure contracts at call sites

---

## Sources

### High Confidence (Official Documentation + Tools)
- [SMT-LIB FPA Theory](https://smt-lib.org/theories-FloatingPoint.shtml) — Floating-point standard
- [Programming Z3](https://theory.stanford.edu/~nikolaj/programmingz3.html) — Uninterpreted functions, datatypes
- [Understanding how F* uses Z3](https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html) — Recursive function encoding
- [Z3 Online Guide - Uninterpreted Functions](https://microsoft.github.io/z3guide/docs/logic/Uninterpreted-functions-and-constants/) — Z3 UF support
- [Z3 Online Guide - Datatypes](https://microsoft.github.io/z3guide/docs/theories/Datatypes/) — Datatype encoding

### Medium Confidence (Academic Research)
- [Creusot: A Foundry for the Deductive Verification of Rust Programs](https://www.researchgate.net/publication/364287862_Creusot_A_Foundry_for_the_Deductive_Verification_of_Rust_Programs) — Prophecy encoding
- [Using a Prophecy-Based Encoding of Rust Borrows](https://inria.hal.science/hal-05244847v1/document) — Mutable borrow encoding in Creusot
- [RustHornBelt: A Semantic Foundation for Functional Verification](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf) — Prophecy + lifetimes
- [Verus: Verifying Rust Programs using Linear Ghost Types](https://users.ece.cmu.edu/~chanheec/verus-ghost.pdf) — SMT-based Rust verification
- [The Prusti Project: Formal Verification for Rust](https://www.researchgate.net/publication/360716882_The_Prusti_Project_Formal_Verification_for_Rust) — Separation logic approach
- [Verifying Dynamic Trait Objects in Rust](https://cs.wellesley.edu/~avh/dyn-trait-icse-seip-2022-preprint.pdf) — Trait object verification
- [Model Finding for Recursive Functions in SMT](https://www.cs.vu.nl/~jbe248/frf_conf.pdf) — Recursive function encoding
- [Modular Specification and Verification of Closures in Rust](https://pm.inf.ethz.ch/publications/WolffBilyMathejaMuellerSummers21.pdf) — Closure encoding
- [A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust](https://dl.acm.org/doi/fullHtml/10.1145/3443420) — Lifetime formalization

### Low Confidence (Emerging Research)
- [A hybrid approach to semi-automated Rust verification](https://arxiv.org/html/2403.15122v1) — Gillian-Rust separation logic
- [Defunctionalization](https://en.wikipedia.org/wiki/Defunctionalization) — Closure conversion background
- [Interprocedural Analysis](https://www.cs.cmu.edu/~aldrich/courses/15-819O-13sp/resources/interprocedural.pdf) — Call graph analysis
- [Towards Practical Formal Verification for a General-Purpose OS in Rust](https://asterinas.github.io/2025/02/13/towards-practical-formal-verification-for-a-general-purpose-os-in-rust.html) — Concurrency verification challenges

---

## Conclusion

The existing 5-crate architecture provides strong foundations for advanced feature integration. Key recommendations:

1. **Leverage existing patterns**: Prophecy encoding (lifetimes), modular encoding (all features), contract database (interprocedural)
2. **Incremental integration**: Each feature adds IR variants + encoding modules + VC kinds
3. **Build order**: Start with floating-point and recursion (low risk), defer concurrency (high risk)
4. **SMT theories**: Prioritize standardized theories (FPA, datatypes, UF) over custom encodings
5. **Testing**: Maintain existing test discipline (unit + integration + SMT-level tests per feature)

**Total estimated effort:** ~14,200 LOC across all features (10,800 new + 3,400 modified)

**Risk mitigation:** Phased approach (7 milestones) allows early validation of architectural patterns before tackling high-risk features (unsafe, concurrency).
