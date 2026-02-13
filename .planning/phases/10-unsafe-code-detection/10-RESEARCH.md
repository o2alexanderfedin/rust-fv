# Phase 10: Unsafe Code Detection - Research

**Researched:** 2026-02-12
**Domain:** Unsafe Rust verification, raw pointer safety, memory safety verification, trust boundaries
**Confidence:** HIGH

## Summary

Unsafe code verification in Rust is a critical frontier combining static analysis, contract-based reasoning, and SMT-based memory safety checks. The core challenge is verifying memory safety properties (null-safety, bounds-safety, use-after-free) that Rust's type system cannot guarantee in `unsafe` blocks, while providing explicit trust boundaries via annotations. This phase builds on existing lifetime reasoning (Phase 9) and extends the verifier with unsafe-specific VCs, contract attributes for unsafe functions, and basic heap reasoning.

**Primary recommendation:** Use a three-tier approach: (1) Detection and flagging of all unsafe blocks with source locations, (2) Basic memory safety VCs for pointer operations (null-check, bounds-check) using heap-as-array encoding, (3) Contract-based trust boundaries via `#[unsafe_requires]`/`#[unsafe_ensures]` and `#[verifier::trusted]` annotations. Defer full separation logic and advanced aliasing analysis to v0.3+.

**Key insight:** Most unsafe code verification tools (Prusti, Creusot, Verus) do NOT verify unsafe block internals—they assume unsafe blocks are correct if they satisfy their contracts. This phase follows that proven pattern: verify contracts at call sites, provide escape hatch via `#[verifier::trusted]`, and focus on basic memory safety properties where automatic verification is tractable.

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| Z3 | 4.13+ | SMT solver for memory safety VCs | Already in use, array theory for heap-as-array model |
| rustc MIR | nightly | Detect unsafe blocks, extract raw pointer ops | Official compiler IR, provides all unsafe operation metadata |
| Existing IR (ir.rs) | current | Already has Ty::RawPtr, can extend with unsafe metadata | No new dependencies needed |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| Miri | latest | Runtime UB detection (testing/validation) | Validate VCs against ground truth, find test cases |
| rustc_hir | nightly | Extract unsafe block source locations | For diagnostic source spans |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| Heap-as-array (Z3 array theory) | Separation logic (full SMT encoding) | Separation logic more precise but requires frame inference, heap footprint tracking—major complexity for v0.2 |
| Basic null/bounds checks | Full aliasing analysis | Aliasing analysis catches more bugs but requires points-to analysis, shape analysis—defer to v0.3+ |
| Contract-based trust | Inline unsafe verification | Inline verification of arbitrary unsafe code is undecidable; contracts provide sound modular boundary |

**Installation:**
```bash
# Already available in project
# Z3 in dependencies
# rustc nightly already required
```

## Architecture Patterns

### Recommended Module Structure
```
crates/analysis/src/
├── vcgen.rs                # EXTEND: Add VcKind::MemorySafety
├── unsafe_analysis.rs      # NEW: Detect unsafe blocks, extract pointer ops
├── heap_model.rs           # NEW: Heap-as-array encoding in Z3
├── ir.rs                   # EXTEND: Add unsafe block metadata
└── encode_term.rs          # EXTEND: Encode pointer null/bounds checks

crates/driver/src/
├── mir_converter.rs        # EXTEND: Extract unsafe block locations
├── unsafe_extractor.rs     # NEW: Extract raw pointer operations from MIR
└── diagnostics.rs          # EXTEND: Add VcKind::MemorySafety formatting

crates/macros/src/
└── lib.rs                  # EXTEND: Add #[unsafe_requires], #[unsafe_ensures], #[verifier::trusted]
```

### Pattern 1: Unsafe Block Detection and Flagging
**What:** Traverse MIR to find all unsafe blocks and emit warnings with source locations
**When to use:** Every function containing unsafe code
**Example:**
```rust
// Source: Rustc MIR representation - UnsafetyViolation
// https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_build/check_unsafety/struct.UnsafetyViolation.html

use rustc_middle::mir::{Body, BasicBlock, Statement, Terminator};
use rustc_hir::Unsafety;

/// Detect all unsafe blocks in a function's MIR.
pub fn detect_unsafe_blocks(body: &Body<'_>) -> Vec<UnsafeBlockInfo> {
    let mut unsafe_blocks = Vec::new();

    // Check function-level unsafety
    if body.unsafety == Unsafety::Unsafe {
        unsafe_blocks.push(UnsafeBlockInfo {
            location: UnsafeLocation::FunctionLevel,
            source_span: body.span,
            reason: "function marked unsafe".to_string(),
        });
    }

    // Scan for unsafe blocks in MIR
    for (bb_idx, bb_data) in body.basic_blocks.iter_enumerated() {
        // Check if this basic block is inside an unsafe block
        if let Some(scope_data) = body.source_scopes.get(bb_data.source_scope) {
            if scope_data.local_data.as_ref().map_or(false, |d| d.unsafety.is_unsafe()) {
                unsafe_blocks.push(UnsafeBlockInfo {
                    location: UnsafeLocation::Block(bb_idx),
                    source_span: bb_data.terminator().source_info.span,
                    reason: "unsafe block".to_string(),
                });
            }
        }
    }

    unsafe_blocks
}

pub struct UnsafeBlockInfo {
    pub location: UnsafeLocation,
    pub source_span: Span,
    pub reason: String,
}

pub enum UnsafeLocation {
    FunctionLevel,
    Block(BasicBlock),
}
```

### Pattern 2: Raw Pointer Null-Check VC Generation
**What:** Generate SMT constraint that pointer is non-null before dereference
**When to use:** Every raw pointer dereference operation
**Example:**
```rust
// For MIR: _2 = *_1 where _1: *const T
// Generate VC: (assert (not (= _1 null)))

use rust_fv_smtlib::term::Term;

/// Generate null-check VC for raw pointer dereference.
pub fn generate_null_check_vc(
    ptr_local: &str,
    ptr_ty: &Ty,
    location: &VcLocation,
) -> VerificationCondition {
    // Declare null constant for this pointer type
    let null_term = Term::Const(format!("null_{}", type_size(ptr_ty)));
    let ptr_term = Term::Const(ptr_local.to_string());

    // VC: ptr != null
    let null_check = Term::Not(Box::new(
        Term::Eq(Box::new(ptr_term), Box::new(null_term))
    ));

    VerificationCondition {
        description: format!(
            "raw pointer dereference requires non-null pointer: {}",
            ptr_local
        ),
        script: build_script_with_check(null_check),
        location: location.clone(),
    }
}

fn type_size(ty: &Ty) -> usize {
    match ty {
        Ty::RawPtr(inner, _) => match **inner {
            Ty::Int(IntTy::I8) | Ty::Uint(UintTy::U8) => 1,
            Ty::Int(IntTy::I32) | Ty::Uint(UintTy::U32) => 4,
            _ => 8, // default pointer size
        },
        _ => 8,
    }
}
```

### Pattern 3: Heap-as-Array Model with Bounds Checking
**What:** Encode heap as Z3 array theory, generate bounds-check VCs for pointer arithmetic
**When to use:** Pointer offset operations, indexed access
**Example:**
```rust
// Source: Z3 Array Theory
// https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-arrays

// Heap model: (Array (_ BitVec 64) (_ BitVec 8))
// Allocation metadata: (Array (_ BitVec 64) AllocationInfo)
//
// For ptr.offset(n):
//   - base_addr = allocation_base(ptr)
//   - alloc_size = allocation_size(ptr)
//   - offset = ptr - base_addr + n
//   - VC: offset < alloc_size

use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::term::Term;
use rust_fv_smtlib::sort::Sort;

/// Declare heap and allocation tracking arrays.
pub fn declare_heap_model() -> Vec<Command> {
    vec![
        // Heap: byte array indexed by 64-bit addresses
        Command::DeclareFun(
            "heap".to_string(),
            vec![Sort::BitVec(64)],
            Sort::BitVec(8),
        ),

        // Allocation base address map
        Command::DeclareFun(
            "alloc_base".to_string(),
            vec![Sort::BitVec(64)], // ptr -> base
            Sort::BitVec(64),
        ),

        // Allocation size map
        Command::DeclareFun(
            "alloc_size".to_string(),
            vec![Sort::BitVec(64)], // ptr -> size
            Sort::BitVec(64),
        ),
    ]
}

/// Generate bounds-check VC for pointer arithmetic.
pub fn generate_bounds_check_vc(
    ptr_operand: &Operand,
    offset_operand: &Operand,
    location: &VcLocation,
) -> VerificationCondition {
    let ptr_term = encode_operand(ptr_operand);
    let offset_term = encode_operand(offset_operand);

    // Calculate effective offset from allocation base
    // effective_offset = (ptr - base) + offset
    let base = Term::App(
        "alloc_base".to_string(),
        vec![ptr_term.clone()],
    );
    let ptr_offset = Term::BvSub(
        Box::new(ptr_term.clone()),
        Box::new(base),
    );
    let effective_offset = Term::BvAdd(
        Box::new(ptr_offset),
        Box::new(offset_term),
    );

    // Get allocation size
    let size = Term::App(
        "alloc_size".to_string(),
        vec![ptr_term.clone()],
    );

    // VC: effective_offset < alloc_size
    let bounds_check = Term::BvUlt(
        Box::new(effective_offset),
        Box::new(size),
    );

    VerificationCondition {
        description: format!(
            "pointer arithmetic must stay within allocation bounds"
        ),
        script: build_script_with_check(bounds_check),
        location: location.clone(),
    }
}
```

### Pattern 4: Contract-Based Trust Boundaries
**What:** Annotate unsafe functions with contracts, verify at call sites
**When to use:** Unsafe functions with well-defined safety requirements
**Example:**
```rust
// User code:
#[unsafe_requires(ptr != null)]
#[unsafe_requires(len > 0)]
#[unsafe_ensures(*result == old(*ptr))]
unsafe fn read_ptr(ptr: *const i32, len: usize) -> i32 {
    *ptr // verifier assumes preconditions, checks postconditions
}

// Caller verification:
fn caller() {
    let x = 42;
    let ptr = &x as *const i32;

    // Verifier generates VC:
    // - Check: ptr != null (precondition)
    // - Check: len > 0 (precondition)
    // - Assume: result == old(*ptr) (postcondition)
    unsafe {
        let result = read_ptr(ptr, 1);
    }
}

// In IR:
pub struct UnsafeContracts {
    /// Safety preconditions (#[unsafe_requires])
    pub requires: Vec<SpecExpr>,
    /// Safety postconditions (#[unsafe_ensures])
    pub ensures: Vec<SpecExpr>,
    /// Whether this function is trusted (skip verification)
    pub is_trusted: bool,
}

// Extend Function IR:
impl Function {
    pub unsafe_contracts: Option<UnsafeContracts>,
}
```

### Pattern 5: Trusted Function Escape Hatch
**What:** Mark unsafe function as axiomatically correct, skip body verification
**When to use:** Complex unsafe code with manual verification, FFI wrappers
**Example:**
```rust
// Source: Prusti trusted functions
// https://viperproject.github.io/prusti-dev/user-guide/verify/trusted.html

// User code:
#[verifier::trusted]
#[unsafe_requires(buf.len() >= size)]
#[unsafe_ensures(result.len() == size)]
unsafe fn complex_ffi_call(buf: &[u8], size: usize) -> Vec<u8> {
    // Complex unsafe code that verifier cannot handle
    // Developer attests this is correct
    external_c_function(buf.as_ptr(), size)
}

// Verifier behavior:
// 1. Does NOT verify function body
// 2. DOES verify preconditions at call sites
// 3. ASSUMES postconditions hold after call

// In diagnostics:
pub fn format_trusted_warning(func_name: &str) -> String {
    format!(
        "warning: function '{}' is marked #[verifier::trusted]\n\
         The verifier assumes this function's contracts are correct.\n\
         Incorrect contracts may lead to unsound verification results.",
        func_name
    )
}
```

### Anti-Patterns to Avoid
- **Don't try to verify arbitrary unsafe code automatically:** Most unsafe operations involve semantic properties (aliasing, initialization) that require programmer insight. Use contracts instead.
- **Don't encode full heap graph in SMT:** Separation logic with full heap encoding causes SMT timeouts. Heap-as-array with basic allocation tracking is sufficient for v0.2.
- **Don't skip unsafe block detection:** Even if body can't be verified, flagging unsafe code location helps developers understand verification limitations.
- **Don't make `#[trusted]` implicit:** Require explicit annotation. Silent trust defeats the purpose of verification.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Pointer null-ness tracking | Custom null-flow analysis | Simple null != ptr check at dereference | Null-flow analysis requires data-flow framework and alias analysis. Basic check at dereference point is sound and tractable. |
| Heap aliasing analysis | Points-to analysis, shape analysis | Heap-as-array with no aliasing assumptions | Precise aliasing analysis is undecidable for unsafe code. Conservative heap model sufficient for basic safety. |
| UB detection | Custom undefined behavior detector | Miri for testing, contracts for verification | Miri already handles all UB cases comprehensively. Use it for validation, not reimplementation. |
| Unsafe block AST parsing | Custom HIR/AST traversal | rustc's MIR with source scope metadata | MIR already has unsafe block information in source scopes. Extract from compiler's analysis. |
| Allocation tracking | Custom malloc/free tracker | Z3 uninterpreted functions (alloc_base, alloc_size) | Full tracking requires heap state machine. Uninterpreted functions provide axioms without execution semantics. |

**Key insight:** Unsafe code verification hits undecidability quickly (aliasing, initialization, temporal safety). The only practical approach is contracts + basic checks, not full automatic verification.

## Common Pitfalls

### Pitfall 1: Assuming Raw Pointers Have Allocation Metadata
**What goes wrong:** Generating bounds-check VCs for raw pointers created from arbitrary integers, which have no allocation context.
**Why it happens:** Confusion between safe references (always point to valid allocations) and raw pointers (can be arbitrary bit patterns).
**How to avoid:**
- Raw pointers can be created from arbitrary integers: `0xdeadbeef as *const i32`
- Only generate bounds VCs when pointer provenance is known (cast from reference, explicit allocation)
- For unknown provenance, require explicit contract: `#[unsafe_requires(ptr_valid(ptr, size))]`
- Consider adding `ptr_valid(ptr, size)` builtin predicate for contracts
**Warning signs:** VCs failing on valid unsafe code that casts integers to pointers.

### Pitfall 2: Verifying Unsafe Block Bodies Without Contracts
**What goes wrong:** Attempting automatic verification of unsafe operations that require semantic reasoning (e.g., "this pointer is initialized").
**Why it happens:** Desire for completeness—want to verify everything, not just contracts.
**How to avoid:**
- Unsafe blocks often rely on invariants not expressible in type system
- Without contracts, verifier must conservatively reject (or unsoundly accept)
- Phase 10 focuses on *detection* and *contract checking*, not full unsafe verification
- Full unsafe verification requires separation logic, frame inference (v0.3+ scope)
**Warning signs:** Complex unsafe operations passing verification without any annotations.

### Pitfall 3: Missing Mutable Aliasing in Unsafe Code
**What goes wrong:** Unsafe code creates multiple mutable pointers to same location, verifier doesn't detect conflict.
**Why it happens:** Safe Rust's aliasing rules don't apply in unsafe blocks—raw pointers bypass borrow checker.
**How to avoid:**
- Phase 10's basic heap model does NOT track aliasing precisely
- Generate warning: "Unsafe code with raw pointers—aliasing not verified"
- Require manual contracts: `#[unsafe_requires(ptr1 != ptr2)]` for non-aliasing
- Full aliasing verification (points-to analysis) deferred to v0.3+
**Warning signs:** Unsafe code with multiple `*mut` pointers passing without aliasing contracts.

### Pitfall 4: Null-Check False Positives on Non-Null Types
**What goes wrong:** Generating null-check VCs for pointers derived from safe references, which are guaranteed non-null by construction.
**Why it happens:** Not tracking pointer provenance through safe-to-unsafe conversions.
**How to avoid:**
- When converting `&T` to `*const T`, provenance is "from safe reference"
- Safe references are never null (guaranteed by type system)
- Skip null-check VC if provenance is safe reference
- Track provenance in IR: `RawPtrProvenance::FromRef | FromInt | Unknown`
**Warning signs:** Trivially true null-check VCs for pointers from `&x as *const _`.

### Pitfall 5: Trusted Functions Without Contracts
**What goes wrong:** Developer marks function `#[verifier::trusted]` without providing contracts, making it a black hole for verification.
**Why it happens:** Wanting to skip complex unsafe code verification without understanding contract requirements.
**How to avoid:**
- Require `#[unsafe_requires]`/`#[unsafe_ensures]` when `#[trusted]` is used
- Emit error if `#[trusted]` has no contracts (exception: `#[trusted]` + safe function = no-op)
- Trusted contracts are verified at call sites, so they must be specified
- Better: generate warning suggesting developer add contracts
**Warning signs:** Many `#[trusted]` annotations with no contract annotations.

### Pitfall 6: Ignoring Offset Signedness in Pointer Arithmetic
**What goes wrong:** Treating pointer offset as unsigned, missing negative offset overflow bugs.
**Why it happens:** Rust's `.offset(n)` takes `isize`, but address arithmetic in SMT often uses unsigned bitvectors.
**How to avoid:**
- `ptr.offset(n)` where `n: isize` can be negative
- Encode offset as signed bitvector: `((_ sign_extend 0) n_i64)`
- Check both underflow (offset < -base) and overflow (offset > size)
- Distinguish `.offset()` (signed) from `.add()` (unsigned) in MIR
**Warning signs:** Bounds-check VCs failing on valid negative offsets.

## Code Examples

Verified patterns from official sources and existing codebase:

### Detecting Unsafe Operations in MIR
```rust
// Source: Existing codebase pattern from vcgen.rs

use rustc_middle::mir::{Rvalue, Place, Operand};
use crate::ir::{Ty, Mutability};

/// Detect raw pointer operations in MIR that require safety VCs.
pub fn extract_unsafe_operations(
    body: &rustc_middle::mir::Body<'_>,
) -> Vec<UnsafeOperation> {
    let mut ops = Vec::new();

    for (bb_idx, bb_data) in body.basic_blocks.iter_enumerated() {
        for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                match rvalue {
                    // Raw pointer dereference: *ptr
                    Rvalue::Use(Operand::Copy(p)) | Rvalue::Use(Operand::Move(p)) => {
                        if has_deref_of_raw_ptr(p) {
                            ops.push(UnsafeOperation::RawDeref {
                                ptr_place: convert_place(p),
                                location: (bb_idx, stmt_idx),
                            });
                        }
                    }

                    // Cast to raw pointer: x as *const T
                    Rvalue::Cast(CastKind::Pointer(_), operand, target_ty) => {
                        if is_raw_ptr_ty(target_ty) {
                            ops.push(UnsafeOperation::PtrCast {
                                source: convert_operand(operand),
                                target_ty: convert_ty(target_ty),
                                location: (bb_idx, stmt_idx),
                            });
                        }
                    }

                    _ => {}
                }
            }
        }
    }

    ops
}

pub enum UnsafeOperation {
    /// Dereference of raw pointer
    RawDeref {
        ptr_place: Place,
        location: (BasicBlock, usize),
    },
    /// Cast to raw pointer
    PtrCast {
        source: Operand,
        target_ty: Ty,
        location: (BasicBlock, usize),
    },
    /// Pointer arithmetic (offset, add)
    PtrArithmetic {
        ptr: Operand,
        offset: Operand,
        location: (BasicBlock, usize),
    },
}
```

### Extending VcKind for Memory Safety
```rust
// Source: Existing codebase crates/analysis/src/vcgen.rs
// Pattern: Add new variant to existing enum

// In vcgen.rs:
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VcKind {
    // ... existing variants ...
    BorrowValidity,

    // NEW for Phase 10:
    /// Memory safety check (null-check, bounds-check, use-after-free)
    MemorySafety,
}

// In diagnostics.rs:
fn vc_kind_description(vc_kind: &VcKind) -> &'static str {
    match vc_kind {
        // ... existing cases ...
        VcKind::BorrowValidity => "borrow validity violation",

        // NEW:
        VcKind::MemorySafety => "memory safety violation (null/bounds/validity)",
    }
}

pub fn suggest_fix(vc_kind: &VcKind) -> Option<String> {
    match vc_kind {
        // ... existing cases ...

        VcKind::MemorySafety => Some(
            "Memory safety violation in unsafe code. Add safety contracts:\n\
             #[unsafe_requires(ptr != null)] for null-safety\n\
             #[unsafe_requires(offset < size)] for bounds-safety\n\
             Or mark function #[verifier::trusted] if manually verified."
                .to_string(),
        ),
        _ => None,
    }
}
```

### Proc Macro for Unsafe Contracts
```rust
// Source: Existing codebase pattern from crates/macros/src/lib.rs
// Pattern: Similar to #[requires], #[ensures]

// In crates/macros/src/lib.rs:

/// Safety precondition for unsafe function.
///
/// # Example
/// ```
/// #[unsafe_requires(ptr != null)]
/// #[unsafe_requires(len > 0)]
/// unsafe fn read_buffer(ptr: *const u8, len: usize) -> u8 {
///     *ptr
/// }
/// ```
#[proc_macro_attribute]
pub fn unsafe_requires(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse attribute into contract string
    // Attach to function metadata
    // Similar to existing #[requires] implementation
    item
}

/// Safety postcondition for unsafe function.
///
/// # Example
/// ```
/// #[unsafe_ensures(*result != null)]
/// unsafe fn allocate() -> *mut u8 {
///     libc::malloc(1024)
/// }
/// ```
#[proc_macro_attribute]
pub fn unsafe_ensures(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
```

### Heap Model Encoding
```rust
// Adapted from: Z3 Array Theory documentation
// https://theory.stanford.edu/~nikolaj/programmingz3.html

use rust_fv_smtlib::{command::Command, term::Term, sort::Sort};

/// Encode heap-as-array memory model in SMT.
pub fn encode_heap_model() -> Vec<Command> {
    vec![
        // Heap: maps addresses (bitvectors) to bytes
        Command::DeclareFun(
            "heap".to_string(),
            vec![Sort::BitVec(64)],
            Sort::BitVec(8),
        ),

        // Allocation validity: is this address allocated?
        Command::DeclareFun(
            "allocated".to_string(),
            vec![Sort::BitVec(64)],
            Sort::Bool,
        ),

        // Allocation base: what's the base address of this allocation?
        Command::DeclareFun(
            "alloc_base".to_string(),
            vec![Sort::BitVec(64)],
            Sort::BitVec(64),
        ),

        // Allocation size: how many bytes in this allocation?
        Command::DeclareFun(
            "alloc_size".to_string(),
            vec![Sort::BitVec(64)],
            Sort::BitVec(64),
        ),

        // Axiom: all addresses in allocation have same base
        // (forall ((p BitVec 64) (offset BitVec 64))
        //   (=> (and (allocated p)
        //            (bvult offset (alloc_size p)))
        //       (= (alloc_base (bvadd p offset))
        //          (alloc_base p))))
        Command::Assert(Term::Forall(
            vec![
                ("p".to_string(), Sort::BitVec(64)),
                ("offset".to_string(), Sort::BitVec(64)),
            ],
            Box::new(Term::Implies(
                Box::new(Term::And(vec![
                    Term::App("allocated".to_string(), vec![Term::Const("p".to_string())]),
                    Term::BvUlt(
                        Box::new(Term::Const("offset".to_string())),
                        Box::new(Term::App(
                            "alloc_size".to_string(),
                            vec![Term::Const("p".to_string())],
                        )),
                    ),
                ])),
                Box::new(Term::Eq(
                    Box::new(Term::App(
                        "alloc_base".to_string(),
                        vec![Term::BvAdd(
                            Box::new(Term::Const("p".to_string())),
                            Box::new(Term::Const("offset".to_string())),
                        )],
                    )),
                    Box::new(Term::App(
                        "alloc_base".to_string(),
                        vec![Term::Const("p".to_string())],
                    )),
                )),
            )),
        )),
    ]
}
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Manual unsafe auditing | Contract-based verification (Prusti, Creusot) | 2020-2022 | Contracts enable modular verification of unsafe code without full automation. Standard practice in Rust verification tools. |
| Inline UB checks (Miri) | Static verification with SMT | Ongoing (2024+) | Miri finds bugs via concrete execution; SMT proves absence of bugs across all inputs. Complementary, not replacement. |
| Ignoring unsafe code | Flagging all unsafe blocks | Safety-critical Rust (2023+) | Even without full verification, knowing where unsafe code exists helps security audits. |
| Implicit trust in stdlib | Verification of stdlib unsafe code | Ongoing (2025-2026) | Rust project goal to add safety contracts to std library. Sets standard for unsafe contract style. |
| Lexical pointer lifetimes | Stacked borrows / Tree borrows | 2018 (NLL), refined 2020+ | Aliasing model evolved. Verification must align with Miri's operational semantics. |

**Deprecated/outdated:**
- **Verifying unsafe code without contracts:** Early verification attempts tried to prove unsafe code correct automatically. Current consensus: contracts are required for soundness.
- **Full heap shape analysis in SMT:** Research tools attempted encoding full separation logic in SMT. Performance unworkable; heap-as-array with axioms is practical baseline.
- **Assuming raw pointers follow borrow rules:** Raw pointers explicitly bypass aliasing rules. Can't assume XOR mutability property.

## Open Questions

1. **Interaction Between #[trusted] and Unsafe Contracts**
   - What we know: `#[trusted]` skips body verification, contracts verified at call sites
   - What's unclear: Should trusted functions with unsafe contracts generate different warnings than safe trusted functions?
   - Recommendation: Emit warning for `#[trusted]` unsafe functions mentioning manual verification responsibility. Keep same VC generation for contracts.

2. **Heap Model Granularity: Byte-Level vs. Type-Level**
   - What we know: Heap-as-array can index by byte (fine-grained) or by object (coarse-grained)
   - What's unclear: Does byte-level precision improve verification or just slow SMT solver?
   - Recommendation: Start with type-level (heap maps `*T` to `T`). If bounds VCs need finer precision, add byte-level encoding later.

3. **Raw Pointer Provenance Tracking**
   - What we know: Rust's memory model is formalizing pointer provenance (where pointer "came from")
   - What's unclear: How much provenance information is available in MIR for verification?
   - Recommendation: Track simple provenance (from-reference vs. from-int vs. unknown). Full provenance model may require additional rustc support.

4. **Unsafe Block vs. Unsafe Function Contracts**
   - What we know: Unsafe functions can have contracts, but unsafe blocks are inline in safe functions
   - What's unclear: Should inline unsafe blocks support local contracts (e.g., `#[block_requires]`)?
   - Recommendation: Phase 10 focuses on unsafe *functions* with contracts. Inline block contracts deferred to v0.3+ (requires syntax design).

5. **Integration with Miri for VC Validation**
   - What we know: Miri can execute unsafe code and detect UB concretely
   - What's unclear: Can we automatically generate Miri test cases from VCs to validate correctness?
   - Recommendation: Manual workflow for v0.2: developer writes tests, verifier generates VCs, Miri validates test coverage. Automatic test generation deferred.

## Sources

### Primary (HIGH confidence)
- [Miri: Practical Undefined Behavior Detection for Rust (POPL 2026)](https://research.ralfj.de/papers/2026-popl-miri.pdf) - Operational semantics for unsafe Rust, UB detection
- [Prusti Trusted Functions Documentation](https://viperproject.github.io/prusti-dev/user-guide/verify/trusted.html) - `#[trusted]` attribute semantics
- [Rust Standard Library Safety Contracts (2025 Project Goal)](https://rust-lang.github.io/rust-project-goals/2025h1/std-contracts.html) - Contract annotation standards
- [Programming Z3](https://theory.stanford.edu/~nikolaj/programmingz3.html) - Z3 array theory for heap encoding
- [Efficient Evaluation of Pointer Predicates with Z3 SMT Solver](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/axioms.submitted.pdf) - Pointer encoding in SMT
- Existing codebase: `crates/analysis/src/vcgen.rs` (VcKind pattern), `crates/analysis/src/ir.rs` (Ty::RawPtr already exists)

### Secondary (MEDIUM confidence)
- [The Prusti Project: Formal Verification for Rust](https://pm.inf.ethz.ch/publications/AstrauskasBilyFialaGrannanMathejaMuellerPoliSummers22.pdf) - Contract-based verification approach
- [Creusot: Deductive Verification of Rust Programs](https://inria.hal.science/hal-03737878v1/document) - Unsafe abstraction verification
- [RefinedRust: High-Assurance Verification of Rust Programs](https://plv.mpi-sws.org/refinedrust/paper-refinedrust.pdf) - Type-based approach to unsafe code
- [Annotating and Auditing Safety Properties of Unsafe Rust](https://arxiv.org/pdf/2504.21312) - Safety property specification research
- [Automating Separation Logic Using SMT](https://www.cs.yale.edu/homes/piskac/papers/2013PiskacWiesZuffreySepLog.pdf) - Separation logic in SMT solvers

### Tertiary (LOW confidence, needs validation)
- [Review of Heap Specification and Verification](https://arxiv.org/pdf/1910.10176) - Survey of heap models (general, not Rust-specific)
- [Unsafe Pointers in Rust: Common Pitfalls](https://medium.com/@vjgaur/unsafe-pointers-in-rust-common-pitfalls-and-how-to-avoid-them-efa6573397bc) - Practical guidance (blog, not peer-reviewed)
- [Rust Raw Pointers Guide](https://www.compilenrun.com/docs/language/rust/rust-advanced-features/rust-raw-pointers/) - Tutorial material (needs verification against official docs)

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH - Z3 array theory well-documented, rustc MIR is official IR
- Architecture: HIGH - patterns from existing phases, proven in Prusti/Creusot
- Pitfalls: HIGH - based on known verification challenges, Miri's UB categories
- Heap model: MEDIUM - simplified model (full separation logic deferred), but sufficient for basic checks
- Contract syntax: MEDIUM - follows Rust project goals, but exact syntax may evolve
- Provenance tracking: LOW - Rust memory model still evolving, MIR support uncertain

**Research date:** 2026-02-12
**Valid until:** 30 days (stable techniques), 7 days for Rust memory model developments
