# Phase 29: Fix Identified Gaps — Research

**Researched:** 2026-02-24
**Domain:** Rust MIR → IR → SMT-LIB2 VCGen pipeline completeness and soundness
**Confidence:** HIGH — all findings from direct codebase inspection post-Phase-28

---

## Summary

Phase 29 addresses all gaps identified by the comprehensive gap analysis in
`.planning/debug/rust-smt-feature-coverage-gaps.md`. The gaps fall into four
layers: MIR Converter (upstream bottleneck), IR Representation (missing variants),
VCGen/Encoding (soundness holes), and Missing Rvalue Coverage (silently dropped).

The highest-priority items are two soundness holes: (1) `Rvalue::Cast` in
`mir_converter.rs` always emits `CastKind::IntToInt` regardless of the actual
Rustc cast kind — meaning float-to-int casts are encoded as integer truncation
which is type-incorrect in SMT-LIB2 FPA theory, and (2) `encode_float_to_int_cast`
in `encode_term.rs` uses `Term::Extract` on a `Float` sort term which violates
SMT-LIB2 type rules (Extract operates on BitVec, not Float). After these two
soundness fixes, the coverage breadth items can be addressed: aggregate
struct/enum conversion, missing IR statement variants (SetDiscriminant, Assume),
missing Rvalue variants (Repeat, AddressOf, CopyForDeref, NullaryOp), projected
LHS mutation, and Downcast type narrowing.

**Primary recommendation:** Fix soundness holes first (C3.1 + C1.1), then
expand coverage breadth in dependency order (IR variants before VCGen consumers).

---

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| MIRCONV-01 | Cast kind preservation in mir_converter.rs — map rustc CastKind variants to ir::CastKind correctly | Rustc `mir::CastKind` enum documented below; ir::CastKind already has all needed variants |
| MIRCONV-02 | Aggregate struct/enum/closure conversion in mir_converter.rs — ir::AggregateKind already has Struct/Enum/Closure variants, just need to wire them | ir.rs:662-668 shows all three variants exist |
| VCGEN-05 | Float-to-int SMT encoding soundness — replace `Term::Extract` on Float sort with `Term::App("(_ fp.to_sbv N)", [RTZ, src])` | SMT-LIB2 standard; Term::App supports arbitrary indexed identifiers |
| VCGEN-06 | Projected LHS + non-Use rvalue encoding — struct field mutation must produce a "functional update" SMT assertion | Functional record update pattern documented below |
</phase_requirements>

---

## Standard Stack

### Core (unchanged from Phase 28)
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| `rustc_middle::mir` | nightly-2026-02-11 | MIR source types | Project toolchain |
| `rust_fv_analysis::ir` | internal | Stable IR decoupled from rustc | Project convention |
| `rust_fv_smtlib::term::Term` | internal | SMT-LIB2 AST | Project convention |
| Z3 | system | SMT solver for testing | Project convention |

### Rustc CastKind Variants (mir::CastKind — HIGH confidence, direct source inspection)

The actual `mir::CastKind` enum (from `rustc_middle/src/mir/syntax.rs`) is:
```rust
pub enum CastKind {
    PointerExposeProvenance,       // ptr as usize (exposes provenance)
    PointerWithExposedProvenance,  // usize as *const T (reconstructs ptr)
    PointerCoercion(PointerCoercion, CoercionSource), // fat ptr coercions
    IntToInt,                      // integer widening/narrowing/sign change
    FloatToInt,                    // f64 as i32, f64 as u32, etc.
    FloatToFloat,                  // f32 as f64, f64 as f32
    IntToFloat,                    // i32 as f64, u8 as f32, etc.
    PtrToPtr,                      // *const T as *const U
    FnPtrToPtr,                    // fn() as *const ()
    Transmute,                     // mem::transmute
    Subtype,                       // no-op subtype coercion (safe to treat as identity)
}
```

### IR CastKind Variants (ir::CastKind — already exists in ir.rs:778-789)
```rust
pub enum CastKind {
    IntToInt,      // maps from mir::CastKind::IntToInt
    IntToFloat,    // maps from mir::CastKind::IntToFloat
    FloatToInt,    // maps from mir::CastKind::FloatToInt
    FloatToFloat,  // maps from mir::CastKind::FloatToFloat
    Pointer,       // maps from PointerExposeProvenance, PointerWithExposedProvenance,
                   //           PointerCoercion, PtrToPtr, FnPtrToPtr
}
```

Note: `Transmute` and `Subtype` are not in `ir::CastKind`. Transmute should map to
`IntToInt` (bitwise identity at the BV layer is what Transmute means for same-size
types). Subtype should also map to `IntToInt` (identity).

### IR AggregateKind (ir::AggregateKind — already complete in ir.rs:662-668)
```rust
pub enum AggregateKind {
    Tuple,
    Struct(String),        // struct name
    Enum(String, usize),   // enum name + variant index
    Closure(String),       // closure name
}
```

All four variants already exist in IR. The mir_converter just needs to wire them.

---

## Architecture Patterns

### Pattern 1: CastKind Mapping in convert_rvalue (mir_converter.rs:288-295)

**What:** Replace `_ =>` wildcard with explicit match on `mir::CastKind` variants.
**Current code (BUG):**
```rust
mir::Rvalue::Cast(_, op, ty) => {           // BUG: ignores cast kind
    Some(ir::Rvalue::Cast(
        ir::CastKind::IntToInt,              // hardcoded — all casts treated as integer
        convert_operand(op),
        ir_ty,
    ))
}
```
**Fixed pattern:**
```rust
mir::Rvalue::Cast(kind, op, ty) => {
    let ir_ty = convert_ty(*ty);
    let ir_kind = match kind {
        mir::CastKind::IntToInt   => ir::CastKind::IntToInt,
        mir::CastKind::FloatToInt => ir::CastKind::FloatToInt,
        mir::CastKind::IntToFloat => ir::CastKind::IntToFloat,
        mir::CastKind::FloatToFloat => ir::CastKind::FloatToFloat,
        mir::CastKind::PtrToPtr
        | mir::CastKind::FnPtrToPtr
        | mir::CastKind::PointerCoercion(..)
        | mir::CastKind::PointerExposeProvenance
        | mir::CastKind::PointerWithExposedProvenance => ir::CastKind::Pointer,
        mir::CastKind::Transmute  => ir::CastKind::IntToInt, // same-size BV reinterpret
        mir::CastKind::Subtype    => ir::CastKind::IntToInt, // identity coercion
    };
    Some(ir::Rvalue::Cast(ir_kind, convert_operand(op), ir_ty))
}
```

### Pattern 2: Aggregate Struct/Enum/Closure Conversion (mir_converter.rs:300-307)

**What:** Extend the `Aggregate` arm to handle Struct, Enum, Closure.
**Key question:** How to get struct/enum names from `mir::AggregateKind`?
- `mir::AggregateKind::Struct(def_id, _)` → use `tcx.def_path_str(def_id)` for name
- `mir::AggregateKind::Adt(def_id, variant_idx, _, _, _)` → use `tcx.def_path_str(def_id)` + `variant_idx.as_usize()`
- `mir::AggregateKind::Closure(def_id, _)` → use `tcx.def_path_str(def_id)`

**Problem:** `convert_rvalue` does not have access to `TyCtxt`. It is a standalone function.
**Solution options:**
1. Pass `tcx` down to `convert_rvalue` (breaking change — requires thread through call chain)
2. Use debug formatting (`format!("{:?}", kind)`) to extract the name as a string — matches existing `Named` pattern
3. Use `mir::AggregateKind::Adt` with `variant.as_usize()` and `fields.len()` from operands

**Recommended approach (KISS):** Use debug format for names in struct/enum/closure aggregates. The VCGen already handles `Ty::Named` fallback. The fix provides the correct shape without requiring TyCtxt threading.

```rust
mir::Rvalue::Aggregate(box kind, operands) => {
    let ir_ops: Vec<ir::Operand> = operands.iter().map(|op| convert_operand(op)).collect();
    let ir_kind = match kind {
        mir::AggregateKind::Tuple => ir::AggregateKind::Tuple,
        mir::AggregateKind::Adt(def_id, variant_idx, _, _, _) => {
            // Use debug format for name — adequate for VCGen constructor matching
            let name = format!("{def_id:?}");
            ir::AggregateKind::Enum(name, variant_idx.as_usize())
        }
        mir::AggregateKind::Closure(def_id, _) => {
            ir::AggregateKind::Closure(format!("{def_id:?}"))
        }
        mir::AggregateKind::Coroutine(..) | mir::AggregateKind::CoroutineClosure(..) => {
            return None; // coroutine aggregates handled by async_vcgen
        }
        mir::AggregateKind::RawPtr(..) => return None, // raw ptr aggregate — skip
    };
    Some(ir::Rvalue::Aggregate(ir_kind, ir_ops))
}
```

Note: `mir::AggregateKind::Struct` may not exist as a separate variant in the current nightly — Rust MIR uses `Adt` for both struct and enum. Check at compile time.

### Pattern 3: Float-to-Int SMT Encoding Fix (encode_term.rs:755-756)

**What:** Replace type-incorrect `Term::Extract` on Float sort with proper SMT-LIB2 FPA-to-BV conversion.

**SMT-LIB2 standard:** The correct operation is `((_ fp.to_sbv N) RTZ src)` for signed truncation toward zero (matching Rust's `as` cast semantics), or `((_ fp.to_ubv N) RTZ src)` for unsigned.

**Current code (SOUNDNESS HOLE):**
```rust
fn encode_float_to_int_cast(src: Term, _from_bits: u32, to_bits: u32) -> Term {
    Term::Extract(to_bits - 1, 0, Box::new(src))  // TYPE ERROR: Extract on Float sort
}
```

**Fixed pattern using Term::App:**
```rust
fn encode_float_to_int_cast(src: Term, _from_bits: u32, to_bits: u32, to_signed: bool) -> Term {
    // SMT-LIB2: ((_ fp.to_sbv N) RTZ src) for signed, ((_ fp.to_ubv N) RTZ src) for unsigned
    // RTZ = Round Toward Zero, which is Rust's float-to-int cast semantics
    let op_name = if to_signed {
        format!("(_ fp.to_sbv {to_bits})")
    } else {
        format!("(_ fp.to_ubv {to_bits})")
    };
    Term::App(op_name, vec![Term::RoundingMode("RTZ".to_string()), src])
}
```

The function signature needs a `to_signed: bool` parameter. The caller in `encode_cast` needs to pass it. Since `encode_cast` receives `from_signed` (source type), we need `to_signed` from the target type. The call site in `vcgen.rs:1572-1578` has access to both `source_ty` and `target_ty` (target is `rvalue.Cast(_, _, ty)`). The `ty_is_signed()` helper already exists in `encode_term.rs`.

### Pattern 4: SetDiscriminant Statement in IR (ir.rs + mir_converter.rs)

**What:** Add `Statement::SetDiscriminant(Place, usize)` to ir.rs and wire it in mir_converter.rs.
**Why needed:** Optimized MIR uses `SetDiscriminant` to set the enum tag separately from field construction. Without it, some enum constructions are invisible to VCGen.

**IR addition:**
```rust
// In ir.rs Statement enum:
pub enum Statement {
    Assign(Place, Rvalue),
    Nop,
    SetDiscriminant(Place, usize),  // NEW: set enum variant tag
    Assume(Operand),                // NEW: inject assumption premise
}
```

**MIR converter wiring:**
```rust
// In convert_statement():
mir::StatementKind::SetDiscriminant { place, variant_index } => {
    Some(ir::Statement::SetDiscriminant(
        convert_place(place),
        variant_index.as_usize(),
    ))
}
mir::StatementKind::Intrinsic(
    mir::NonDivergingIntrinsic::Assume(op)
) => {
    Some(ir::Statement::Assume(convert_operand(op)))
}
```

**VCGen handling:** SetDiscriminant becomes an equality assertion on the discriminant term. Assume becomes an `Assert(op_term)` premise injected as an assumption.

### Pattern 5: Projected LHS Mutation Fix (vcgen.rs:1522-1529)

**What:** Support `s.x = expr` by producing a functional update: `(mk-Struct new_x old_y old_z)`.
**Why needed:** Currently `_ => return None` silently drops struct field mutations.

**Pattern (functional record update):**
```rust
// For: s.field_idx = new_val
// Produce: s = (mk-StructName new_field_0 ... new_val_at_idx ... old_field_n)
// Where old_field_k = (field_k-selector s) for k != idx
```

This requires knowing:
1. The struct type (to get field names and constructor name)
2. The field index from `Projection::Field(idx)`
3. All other field values via selectors

The existing `encode_place_with_type` and `encode_field_access` helpers in `encode_term.rs` provide field selector encoding. The `find_local_type` function in `vcgen.rs` provides type lookup.

**Approach:**
```rust
if !place.projections.is_empty() {
    // Check if this is a single-level field projection (most common case)
    if place.projections.len() == 1 {
        if let Projection::Field(field_idx) = &place.projections[0] {
            // Get the base local's type to build functional update
            if let Some(base_ty) = find_local_type(func, &place.local) {
                if let Ty::Struct(name, fields) = base_ty {
                    let new_val = encode_rvalue_as_term(rvalue, func)?;
                    // Build: (mk-Name f0 f1 ... new_val ... fn)
                    let base_term = Term::Const(place.local.clone());
                    let field_terms: Vec<Term> = fields.iter().enumerate().map(|(i, (fname, _))| {
                        if i == *field_idx {
                            new_val.clone()
                        } else {
                            Term::App(format!("{name}-{fname}"), vec![base_term.clone()])
                        }
                    }).collect();
                    let updated = Term::App(format!("mk-{name}"), field_terms);
                    let lhs = Term::Const(place.local.clone());
                    return Some(Command::Assert(Term::Eq(Box::new(lhs), Box::new(updated))));
                }
            }
        }
    }
    // Fallback: encode via place_with_type for Use rvalues
    let lhs = encode_place_with_type(place, func)?;
    let rhs = match rvalue {
        Rvalue::Use(op) => encode_operand_for_vcgen(op, func),
        _ => return None,
    };
    return Some(Command::Assert(Term::Eq(Box::new(lhs), Box::new(rhs))));
}
```

### Pattern 6: TyKind::Param → Ty::Generic Fix (mir_converter.rs:415)

**What:** Map `TyKind::Param(t)` to `ir::Ty::Generic(t.name.as_str().to_string())` before the catch-all `Named`.
**Current code:**
```rust
_ => ir::Ty::Named(format!("{ty:?}")),  // BUG: Param(T) becomes Named("T") not Generic("T")
```
**Fixed code:**
```rust
ty::TyKind::Param(t) => ir::Ty::Generic(t.name.as_str().to_string()),
// ... then fall through to:
_ => ir::Ty::Named(format!("{ty:?}")),
```
Phase 28 decisions confirm: `Ty::Generic(name)` encodes as `Sort::Uninterpreted(name)` in `encode_sort.rs`.

### Pattern 7: Missing Rvalue Variants

**Rvalue::CopyForDeref** — identity: same as `Rvalue::Use(Operand::Copy(place))`
```rust
mir::Rvalue::CopyForDeref(place) => {
    Some(ir::Rvalue::Use(ir::Operand::Copy(convert_place(place))))
}
```

**Rvalue::AddressOf** — raw pointer creation: encode as BitVec64 identity
```rust
mir::Rvalue::AddressOf(_, place) => {
    // AddressOf is a reference to a place as raw pointer
    // Model: same as Ref (transparent pointer identity in SMT)
    let mutability = match mutability_from_mir_mutability(mutability) { ... };
    Some(ir::Rvalue::Ref(mutability, convert_place(place)))
}
```
Or add a new `ir::Rvalue::AddressOf(ir::Mutability, ir::Place)` — both approaches are valid. Reusing `Rvalue::Ref` is simpler (KISS).

**Rvalue::Repeat([x; N])** — array fill
```rust
// Add to ir::Rvalue:
Repeat(Operand, usize),   // [x; N]
```
VCGen encoding: for small N, expand to Store chain. For large/variable N, emit a universally quantified axiom: `(forall ((i (_ BitVec 64))) (=> (bvult i (bv N 64)) (= (select arr i) x)))`.

**Rvalue::NullaryOp(SizeOf, ty)** — emit uninterpreted constant or known value
```rust
mir::Rvalue::NullaryOp(mir::NullaryOp::SizeOf, ty) => {
    // Known sizes: bool=1, u8=1, u16=2, u32=4, u64=8, i32=4, f64=8
    let size_bytes = known_size_bytes(convert_ty(*ty)).unwrap_or(0);
    Some(ir::Rvalue::Use(ir::Operand::Constant(ir::Constant::Uint(size_bytes as u128, ir::UintTy::Usize))))
}
```

---

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Float-to-int SMT encoding | Custom bitvector extraction | `Term::App("(_ fp.to_sbv N)", [RTZ, src])` | SMT-LIB2 standard FPA operation; Extract is wrong sort |
| Struct type lookup for functional update | Custom IR traversal | `find_local_type(func, local)` (already exists in vcgen.rs) | Existing infrastructure |
| Field selector naming | Custom format string | Follow `encode_field_access` naming convention | Consistency with existing selector names |
| CastKind matching | Exhaustive manual checking | Rust exhaustive match (compiler enforces) | Compiler catches missing variants |

---

## Common Pitfalls

### Pitfall 1: mir::AggregateKind::Struct Does Not Exist
**What goes wrong:** Trying to match `mir::AggregateKind::Struct` causes a compile error because in rustc's current MIR, struct construction uses `AggregateKind::Adt` (the same variant used for both struct and enum Adt types). The `AggregateKind::Struct` variant exists only in older rustc versions or in the SMIR (stable MIR) API.
**Why it happens:** Rustc unified struct and enum construction under `Adt` with `variant_idx = 0` for struct-like bodies.
**How to avoid:** Match on `mir::AggregateKind::Adt` and inspect the DefId/variant index to distinguish struct vs enum.
**Warning signs:** Compile error "no variant named `Struct` in `AggregateKind`".

### Pitfall 2: Term::Extract on Float Sort is Type-Incorrect
**What goes wrong:** Z3 rejects `((_ extract 31 0) fp_term)` with a type error because `Extract` expects BitVec, not Float sort.
**Why it happens:** Float and BitVec are distinct sorts in SMT-LIB2. FPA theory uses `fp.to_sbv/fp.to_ubv` for conversion.
**How to avoid:** Use `Term::App("(_ fp.to_sbv N)", ...)` for signed, `Term::App("(_ fp.to_ubv N)", ...)` for unsigned.
**Warning signs:** Z3 solver output contains "type mismatch" or "expected BitVec, got Float".

### Pitfall 3: Functional Record Update Requires Complete Field List
**What goes wrong:** `mk-Struct(new_field)` with only one argument fails if the struct has multiple fields — the constructor arity must match the declared datatype exactly.
**Why it happens:** SMT-LIB2 datatype constructors take all fields positionally.
**How to avoid:** When building a functional update, iterate over ALL fields and use selector terms `(struct-field_k base)` for unchanged fields.
**Warning signs:** Z3 reports "wrong number of arguments for constructor".

### Pitfall 4: encode_float_to_int_cast Signature Change Propagates
**What goes wrong:** Adding `to_signed: bool` to `encode_float_to_int_cast` requires updating the `encode_cast` call site. The call site in `vcgen.rs` must pass the target type's signedness.
**Why it happens:** The current `encode_cast` API only passes `from_signed` (source type). The fix requires `to_signed` for the float-to-int conversion.
**How to avoid:** Update `encode_cast` signature to include `to_signed: bool` OR determine signedness from target_ty inside `encode_float_to_int_cast` by passing the target `Ty`.
**Recommended:** Add `to_signed: bool` parameter to `encode_cast` — cleaner and propagates up to the already-known target type.

### Pitfall 5: SetDiscriminant VCGen Must Not Conflict with Discriminant Rvalue
**What goes wrong:** Emitting two contradictory SMT assertions for the same enum's discriminant — one from `SetDiscriminant` and one from `Rvalue::Discriminant` read.
**Why it happens:** In MIR, enum construction can involve: (1) `Aggregate` rvalue writing fields, then (2) `SetDiscriminant` writing the tag. Both can produce discriminant-related VCs.
**How to avoid:** `SetDiscriminant` should produce `(assert (= (discriminant-{local} {local}) {variant_idx}))`. This is consistent with how `Rvalue::Discriminant` reads produce `discriminant-{local}` terms.

### Pitfall 6: TyKind::Param Must Be Added BEFORE the Catch-All
**What goes wrong:** If `TyKind::Param` case is added after the `_ =>` catch-all, it is unreachable and the bug persists.
**How to avoid:** Insert the `TyKind::Param(t) => ir::Ty::Generic(...)` arm before `_ => ir::Ty::Named(...)`.

---

## Code Examples

### Float-to-Int Correct SMT-LIB2 Encoding
```
; Rust: let x: i32 = f as i32;  where f: f64
; SMT-LIB2 correct encoding (FPA theory):
(assert (= x ((_ fp.to_sbv 32) RTZ f)))

; Rust: let x: u64 = f as u64;  where f: f64
(assert (= x ((_ fp.to_ubv 64) RTZ f)))
```
Source: SMT-LIB2 standard, Section 4.4 (Floating-Point theory)

### Term::App Encoding for fp.to_sbv
```rust
// Source: Term::App is the generic SMT function application
// Used for indexed operators like (_ fp.to_sbv N)
Term::App(
    format!("(_ fp.to_sbv {to_bits})"),
    vec![Term::RoundingMode("RTZ".to_string()), src],
)
```
This matches the pattern already used by `encode_int_to_float_cast` for `(_ to_fp eb sb)`.

### Functional Record Update Pattern
```
; Rust: s.x = new_x;   where s: Point { x: i32, y: i32 }
; SMT-LIB2 functional update:
(assert (= s (mk-Point new_x (Point-y s))))
; where mk-Point is the constructor, Point-y is the y field selector
```

### SetDiscriminant Encoding
```
; Rust MIR: SetDiscriminant(_1, variant_index=0)
; SMT-LIB2:
(assert (= (discriminant-_1 _1) 0))
; Consistent with how Rvalue::Discriminant is encoded
```

---

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| `Term::Extract` on Float | `Term::App("(_ fp.to_sbv N)", ...)` | Phase 29 (this phase) | Soundness fix |
| All casts → `IntToInt` | Correct cast kind mapping | Phase 29 (this phase) | Soundness fix for float casts |
| `_ => return None` for non-Tuple aggregates | Wire Struct/Enum/Closure | Phase 29 (this phase) | Coverage breadth |
| No `SetDiscriminant` in IR | Add as IR Statement variant | Phase 29 (this phase) | Correctness for optimized MIR |

---

## Recommended Phase 29 Plan Decomposition

Based on the gap analysis priorities and dependencies:

**Plan 1 — Soundness: Cast Kind Preservation (C1.1 + MIRCONV-01)**
- Fix `mir_converter.rs:288-295` to map all `mir::CastKind` variants to `ir::CastKind`
- Tests: add test verifying `FloatToInt`, `IntToFloat`, `FloatToFloat` cast kinds are preserved

**Plan 2 — Soundness: Float-to-Int SMT Encoding (C3.1 + VCGEN-05)**
- Fix `encode_term.rs:755-756` to use `Term::App("(_ fp.to_sbv/ubv N)", [RTZ, src])`
- Add `to_signed: bool` parameter to `encode_cast` and `encode_float_to_int_cast`
- Update call site in `vcgen.rs:1578`
- Tests: verify `f64 as i32` produces `fp.to_sbv 32` not `extract`

**Plan 3 — Coverage: Aggregate Struct/Enum Conversion (C1.2 + MIRCONV-02)**
- Fix `mir_converter.rs:300-307` to handle `Adt` and `Closure` aggregate kinds
- Add IR Statement variants `SetDiscriminant` and `Assume` (C2.2a + C1.4b)
- Wire `StatementKind::SetDiscriminant` and `Intrinsic::Assume` in `convert_statement`
- Tests: verify struct/enum aggregates produce IR `Aggregate(Struct(...), ...)` rvalues

**Plan 4 — Coverage: TyKind::Param + Missing Rvalue Variants (C1.6a + C1.3)**
- Fix `convert_ty` to map `TyKind::Param` to `Ty::Generic`
- Add `ir::Rvalue::Repeat`, `ir::Rvalue::NullaryOp` variants to IR
- Wire `Rvalue::CopyForDeref` (→ identity), `Rvalue::AddressOf` (→ Ref), `Rvalue::Repeat` (→ IR), `Rvalue::NullaryOp` SizeOf/AlignOf (→ constant) in `convert_rvalue`
- Tests: verify CopyForDeref, AddressOf, Repeat, NullaryOp produce correct IR

**Plan 5 — VCGen Soundness: Projected LHS Mutation + Downcast Narrowing (C3.2 + C3.7 + VCGEN-06)**
- Fix `vcgen.rs:1522-1529` projected LHS handling to produce functional record updates for struct field mutation
- Fix `encode_term.rs:86-89` Downcast projection to narrow the type for field access
- Tests: verify `s.field = expr` produces a correct SMT functional update assertion

---

## Open Questions

1. **mir::AggregateKind variants for current nightly**
   - What we know: In rustc stable MIR API (`rustc_public`), `AggregateKind` has `Adt`, `Closure`, `Coroutine`, `CoroutineClosure`, `RawPtr`. In `rustc_middle::mir`, likely the same.
   - What's unclear: Whether `Adt` is used for both struct and enum (likely yes, distinguished by `variant_index`)
   - Recommendation: Check at compile time. The `mir_converter.rs` uses `rustc_middle::mir` directly.

2. **NullaryOp variants in current nightly**
   - What we know: `NullaryOp::SizeOf`, `NullaryOp::AlignOf` are standard. `NullaryOp::OffsetOf` and `NullaryOp::UbChecks` may also exist.
   - Recommendation: Use exhaustive match with explicit fallback `_ => None` to avoid surprises.

3. **Functional update for nested projections (depth > 1)**
   - What we know: `s.x = val` is depth-1 (one Field projection). `s.inner.x = val` is depth-2.
   - What's unclear: How common are depth-2+ projected LHS mutations in typical MIR.
   - Recommendation: Handle depth-1 in Plan 5. Document depth-2+ as out of scope for Phase 29 (NICE-TO-HAVE).

---

## Sources

### Primary (HIGH confidence)
- Direct codebase inspection — `crates/driver/src/mir_converter.rs` (lines 257-311, 386-417)
- Direct codebase inspection — `crates/analysis/src/ir.rs` (lines 565-834)
- Direct codebase inspection — `crates/analysis/src/encode_term.rs` (lines 691-757)
- Direct codebase inspection — `crates/smtlib/src/term.rs` (full Term enum)
- Direct codebase inspection — `.planning/debug/rust-smt-feature-coverage-gaps.md` (comprehensive gap analysis)
- Direct source inspection — `rustc_middle/src/mir/syntax.rs` (CastKind enum, current nightly)

### Secondary (MEDIUM confidence)
- SMT-LIB2 standard FPA theory: `fp.to_sbv`, `fp.to_ubv` with RTZ rounding mode for Rust `as` cast semantics
- Pattern from existing `encode_int_to_float_cast`: `Term::App("(_ to_fp eb sb)", [RNE, src])` — same indexed operator pattern applies to `fp.to_sbv/ubv`

---

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH — all from direct codebase inspection of actual source files
- Architecture: HIGH — fixing documented bugs with clear before/after patterns
- Pitfalls: HIGH — identified from real compile-time and runtime failure modes

**Research date:** 2026-02-24
**Valid until:** 2026-03-24 (stable area, rustc nightly changes slowly for MIR layer)
