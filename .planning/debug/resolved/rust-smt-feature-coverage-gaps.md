---
status: resolved
trigger: "Identify all Rust language features not yet covered (or only partially covered) by SMT-LIB/SMT-LIB2 inference in the rust-fv formal verification tool"
created: 2026-02-24T00:00:00Z
updated: 2026-02-24T00:00:00Z
goal: analysis_only
---

## Current Focus

hypothesis: comprehensive gap analysis completed
test: direct codebase inspection of vcgen.rs, encode_term.rs, encode_sort.rs, ir.rs, mir_converter.rs, REQUIREMENTS.md, ROADMAP.md, Phase 28 research
expecting: actionable gap document organized by category, priority, complexity
next_action: document complete

## Symptoms

expected: Every idiomatic Rust language construct can be verified — VCGen produces correct SMT-LIB2 constraints for all major Rust expression/statement/type categories.
actual: Unknown — need to systematically map what IS currently implemented vs. what major Rust features are still missing or incomplete.
errors: None (this is a coverage gap analysis, not a crash)
reproduction: Write a Rust function using feature X → run cargo verify → see if VCs are generated or silently skipped
timeline: Project has shipped v0.1–v0.4 (phases 1-27), v0.5 just completed Phase 28 (SMT VCGen Completeness for casts, discriminants, array bounds, generics). What remains for full coverage?

## Eliminated

- hypothesis: Phase 28 was not completed
  evidence: ROADMAP.md shows Phase 28 plans 01-05 completed (plan 04 checked, others in progress per state); vcgen.rs at line 1572 shows Rvalue::Cast with encode_cast wired, line 1588 shows Rvalue::Discriminant with App encoding, line 1566 shows Rvalue::Len wired
  timestamp: 2026-02-24

- hypothesis: Cast encoding is still a stub
  evidence: encode_term.rs contains encode_cast(), encode_int_to_int_cast(), encode_int_to_float_cast(), encode_float_to_int_cast(), encode_float_to_float_cast() — all wired from vcgen.rs:1572-1578
  timestamp: 2026-02-24

## Evidence

- timestamp: 2026-02-24
  checked: crates/driver/src/mir_converter.rs convert_rvalue()
  found: Line 288-295: Rvalue::Cast always emits ir::CastKind::IntToInt regardless of actual Rustc CastKind. All float casts, pointer-to-int, and FnDef casts are mapped to the same IntToInt. Line 303: Aggregate only converts Tuple kind — Struct, Enum, Closure all return None. Line 309: `_ => None` silently drops Rvalue::AddressOf, Rvalue::ThreadLocalRef, Rvalue::NullaryOp (SizeOf/AlignOf), Rvalue::ShallowInitBox, Rvalue::CopyForDeref, Rvalue::Repeat.
  implication: Even if VCGen encodes correctly, the MIR converter is the upstream bottleneck — the IR never receives these constructs

- timestamp: 2026-02-24
  checked: crates/driver/src/mir_converter.rs convert_terminator()
  found: Line 251: Drop → Goto (stub). Line 253: All other terminators (InlineAsm, UnwindResume, DropAndReplace, TailCall, CoroutineYield) → Unreachable. This means Drop cleanup, inline assembly, and coroutine Yield terminators are not converted.
  implication: Unsafe code with Drop semantics, InlineAsm, and coroutine Yield are silently dropped

- timestamp: 2026-02-24
  checked: crates/driver/src/mir_converter.rs convert_ty()
  found: Line 415: `_ => ir::Ty::Named(format!("{ty:?}"))` — all unhandled types (FnDef, FnPtr, Dynamic/trait objects, Str, CoroutineWitness, Alias, Param, Bound, etc.) fall through to Named() with debug formatting. FnPtr types come out as Named("fn(...)") strings rather than a structured FnPtr IR node. Struct, Enum not handled — they go to Named too.
  implication: Rich struct/enum/FnPtr type information is lost at MIR conversion; only recovered if Aggregate rvalue carries the shape inline

- timestamp: 2026-02-24
  checked: crates/analysis/src/encode_sort.rs
  found: All Ty variants are encoded. Struct → Sort::Datatype. Enum → Sort::Datatype. Tuple → Sort::Datatype. TraitObject → Sort::Uninterpreted. Closure → Sort::Datatype. RawPtr → Sort::BitVec(64). F16/F128 are NOT in FloatTy (only F32/F64). FnPtr type is absent from Ty enum (no Ty::FnPtr variant). ConstGeneric is absent. Never → Sort::Bool (acceptable stub).
  implication: F16/F128 are silently rounded to F32/F64 in mir_converter.rs. FnPtr has no dedicated sort. Const generics are entirely absent.

- timestamp: 2026-02-24
  checked: crates/analysis/src/vcgen.rs encode_assignment() line 1514-1598
  found: Rvalue::Cast (line 1572): wired to encode_cast — DONE. Rvalue::Discriminant (line 1588): wired to Term::App discriminant encoding — DONE. Rvalue::Len (line 1566): wired to len_constant_name — DONE. Rvalue::Ref (line 1562): transparent identity — partial (no aliasing constraints). Rvalue::Aggregate (line 1580): delegates to encode_aggregate_with_type — Enum variant uses mk-{variant_name} but fallback is mk-variant-{idx} which will not match declared datatype constructors. Projected LHS (line 1522-1529): only Rvalue::Use is handled — complex rvalue on projected place returns None.
  implication: Enum aggregate construction has a fragile fallback path. Struct/Enum field mutation (projected LHS + non-Use rvalue) is silently skipped.

- timestamp: 2026-02-24
  checked: crates/analysis/src/vcgen.rs Terminator handling
  found: SwitchInt: handled with path conditions. Call: handled with contract summaries. Assert: handled. Return: handled. Goto: handled. Unreachable: handled. Drop: mapped to Goto — no drop semantics or Drop trait contract generated. InlineAsm: mapped to Unreachable — silently aborts path traversal. There is no Terminator variant for Drop in IR (ir.rs line 574) — Drop is converted to Goto at MIR layer.
  implication: Drop/destructor contracts cannot be expressed or verified. Code after inline assembly is not reachable.

- timestamp: 2026-02-24
  checked: crates/analysis/src/encode_term.rs encode_float_to_int_cast()
  found: Line 754-756: `TODO Phase 29: proper round-to-zero conversion` comment. Current encoding uses Extract(to_bits-1, 0, src) — this is unsound for floats since Float sort and BV sort have different memory representations. Extract on a Float term may not produce correct bits.
  implication: f64 as i32 and similar float-to-int casts have incorrect SMT encoding — a known soundness hole

- timestamp: 2026-02-24
  checked: crates/analysis/src/ir.rs Rvalue enum
  found: Missing vs. Rustc MIR Rvalue: AddressOf (raw pointer creation from place), ThreadLocalRef (thread-local access), NullaryOp::SizeOf / NullaryOp::AlignOf (compile-time sizes), ShallowInitBox (Box allocation), CopyForDeref (copy through deref coercion), Repeat (array fill: [x; N]). Present: Use, BinaryOp, CheckedBinaryOp, UnaryOp, Cast, Ref, Aggregate, Len, Discriminant.
  implication: 6 Rustc MIR Rvalue variants are entirely absent from IR — any code using them is silently dropped at MIR conversion

- timestamp: 2026-02-24
  checked: crates/analysis/src/ir.rs Statement enum
  found: Only two variants: Assign and Nop. Missing Rustc MIR Statement variants: FakeRead (pattern binding reads), SetDiscriminant (enum variant tag assignment), StorageLive/StorageDead (scope markers — OK to drop), Retag (borrow revalidation — OK to drop), Intrinsic (non-diverging intrinsics like assume, copy_nonoverlapping).
  implication: SetDiscriminant (used by enum construction in MIR) is not representable. Intrinsics like core::intrinsics::assume() cannot be modeled as SMT assert premises.

- timestamp: 2026-02-24
  checked: REQUIREMENTS.md v0.5 Out of Scope section
  found: Explicitly deferred: Async closures (Rust 2024), Const generics (to v0.6), Full pattern matching on nested ADTs beyond depth-2. ROADMAP.md: Phase 28 plan 05 (generic where-clause premises as SMT Assert) shown as unchecked [ ].
  implication: VCGEN-04 generic trait bound assertion injection may not be fully complete despite plan 04 being checked; plan 05 is the actual implementation step

- timestamp: 2026-02-24
  checked: crates/analysis/src/monomorphize.rs (via Phase 28 research document)
  found: trait_bound_constraints() returns Vec<String> — human-readable strings, not SMT Terms. The research document says trait_bounds_as_smt_assumptions() companion needs to be added. ROADMAP plan 28-05 is unchecked.
  implication: Generic where-clause premises are NOT yet injected as SMT Assert commands (VCGEN-04 gap still open)

- timestamp: 2026-02-24
  checked: crates/analysis/src/spec_parser.rs and spec language
  found: Supported in spec expressions: arithmetic, comparison, old(), forall/exists with triggers, ghost predicates, fn_spec, state_invariant, SpecInt/SpecNat. Not found: support for spec-level pattern matching (match in ensures), type coercions in spec, str literal comparison (Constant::Str encoded as STR_{s} opaque constant), specification of Drop behavior, format string specs.
  implication: Specs cannot reason about string values semantically (only identity). No way to specify what a destructor should do.

- timestamp: 2026-02-24
  checked: crates/analysis/src/hof_vcgen.rs and closure_analysis.rs
  found: Fn/FnOnce/FnMut closures covered. fn_spec entailment under AUFLIA logic covered. Captured variable environment via defunctionalization covered. Missing: async closures (deferred per REQUIREMENTS.md). Multi-argument closures may be limited (fn_spec bound arg is singular in current encoding). Closure as return value is not handled in HOF contracts.
  implication: Closures used as return values from functions or stored in structs cannot be verified with fn_spec

- timestamp: 2026-02-24
  checked: crates/analysis/src/async_vcgen.rs
  found: Covered: AsyncPostcondition (at Poll::Ready), AsyncStateInvariantSuspend/Resume (at .await points), select! branch variables, join! as consecutive states. Missing: async closures (Rust 2024 edition deferred), nested async fn calls (inner await points in called async fns), async Drop (futures dropped before Poll::Ready), Pin semantics, waker/context verification.
  implication: Complex async patterns (nested .await, cancellation via drop, Pin) are not verified

- timestamp: 2026-02-24
  checked: crates/analysis/src/sep_logic.rs and heap_model.rs
  found: pts_to, separating conjunction, frame rule, ghost_predicate with depth-3 unfolding covered. Missing: nested struct heap predicates beyond depth-3, fractional permissions, linear capabilities (vs. boolean separation), permission transfer across thread boundaries (concurrent separation logic).
  implication: Deep recursive data structures and concurrent ownership transfer cannot be specified

- timestamp: 2026-02-24
  checked: crates/analysis/src/encode_sort.rs collect_datatype_declarations()
  found: Collects from return type, params, locals. Does NOT collect from: Rvalue types that appear only in assignments (e.g., intermediate aggregate construction results), types inside Constant::Str values, types from CallSiteInfo callee contracts. If a struct type only appears in a callee return value and not in declared locals, it may be missing from datatype declarations.
  implication: Edge case: datatype sort may be missing if type only appears in callee return positions not captured in local types

## Resolution

root_cause: N/A — this is a gap analysis, not a bug investigation
fix: N/A — analysis only
verification: N/A
files_changed: []

---

# COMPREHENSIVE GAP ANALYSIS: SMT-LIB Feature Coverage in rust-fv

**Analyzed:** 2026-02-24
**Against:** codebase state post-Phase-28 (v0.5 in progress)
**Confidence:** HIGH — all findings from direct codebase inspection

---

## Executive Summary

The rust-fv codebase has a rich and mature VCGen infrastructure covering the majority of idiomatic Rust. The main coverage gaps fall into four distinct layers:

1. **MIR Converter Layer** (upstream bottleneck): 6 Rvalue variants silently dropped, cast kind not preserved, Aggregate partially converted
2. **IR Representation Layer**: No FnPtr type, no const generic type, no SetDiscriminant statement, no NullaryOp
3. **VCGen/Encoding Layer**: Float-to-int cast encoding unsound, projected LHS + non-Use rvalue skipped, enum aggregate fallback fragile
4. **Spec Language Layer**: No destructor specs, no string value reasoning, no permission types for concurrent separation logic

---

## Category 1: MIR Converter Gaps (mir_converter.rs)

These gaps cause constructs to be **silently dropped before VCGen even sees them**. This is the most critical layer because no downstream improvement can recover from upstream information loss.

### 1.1 Rvalue::Cast — Cast Kind Not Preserved

**File:** `crates/driver/src/mir_converter.rs:288-295`
**Current code:**
```rust
mir::Rvalue::Cast(_, op, ty) => {
    let ir_ty = convert_ty(*ty);
    Some(ir::Rvalue::Cast(
        ir::CastKind::IntToInt,  // BUG: hardcoded regardless of actual Rustc CastKind
        convert_operand(op),
        ir_ty,
    ))
}
```
**Impact:** Float-to-int casts (`f64 as i32`) are encoded as integer truncation rather than float-to-integer conversion. Pointer-to-integer casts (`ptr as usize`) are encoded identically to integer widening. All cast kinds collapse to `IntToInt`.

**Rustc cast kinds that are not preserved:**
- `CastKind::FloatToInt` — should encode as float-to-int conversion with rounding
- `CastKind::IntToFloat` — should encode as int-to-float with to_fp
- `CastKind::FloatToFloat` — should encode as float precision conversion
- `CastKind::PointerCoercion` — should preserve pointer semantics
- `CastKind::FnPtrToPtr` / `CastKind::PtrToPtr` — pointer reinterpretation
- `CastKind::Transmute` — unsafe bit reinterpretation

**Priority:** MUST-HAVE (soundness hole for float code)
**Complexity:** Medium — need to map Rustc's `CastKind` enum to `ir::CastKind` in convert_rvalue

### 1.2 Rvalue::Aggregate — Only Tuple Converted

**File:** `crates/driver/src/mir_converter.rs:300-307`
**Current code:**
```rust
mir::Rvalue::Aggregate(box kind, operands) => {
    let ir_kind = match kind {
        mir::AggregateKind::Tuple => ir::AggregateKind::Tuple,
        _ => return None, // Skip complex aggregates for Phase 1
    };
```
**Impact:** Struct construction, enum variant construction, and closure creation are all silently dropped. This means:
- `let s = Struct { x: 1, y: 2 }` produces no assignment VC
- `let v = MyEnum::Variant(x)` produces no VCs
- Closure creation is dropped (closure analysis uses a separate path, but the Aggregate construction that packages captured vars is lost)

**Priority:** MUST-HAVE (struct/enum construction is core Rust)
**Complexity:** Medium — mapping `mir::AggregateKind::{Struct, Enum, Closure, Coroutine}` to `ir::AggregateKind`

### 1.3 Missing Rvalue Variants (6 total)

**File:** `crates/driver/src/mir_converter.rs:309` — `_ => None`

| Rustc Rvalue Variant | Impact | Priority | Complexity |
|----------------------|--------|----------|------------|
| `Rvalue::AddressOf(mutability, place)` | Raw pointer creation (`&raw const x`) not modeled | SHOULD-HAVE | Small — encode as BitVec 64 identity on place address |
| `Rvalue::ThreadLocalRef(def_id)` | Thread-local access (`thread_local!` variables) not modeled | NICE-TO-HAVE | Large — requires thread model |
| `Rvalue::NullaryOp(SizeOf, ty)` | `std::mem::size_of::<T>()` returns uninterpreted constant | SHOULD-HAVE | Small — emit a constant for known types |
| `Rvalue::NullaryOp(AlignOf, ty)` | `std::mem::align_of::<T>()` returns uninterpreted constant | NICE-TO-HAVE | Small — emit a constant |
| `Rvalue::ShallowInitBox(op, ty)` | Box allocation not modeled | NICE-TO-HAVE | Medium — tie to heap model |
| `Rvalue::CopyForDeref(place)` | Deref coercion copy not modeled | SHOULD-HAVE | Small — encode as identity copy |
| `Rvalue::Repeat(op, count)` | `[x; N]` array fill not modeled | SHOULD-HAVE | Medium — needs Array theory Store loop or SMT lambda |

### 1.4 MIR Statement Variants Not Converted

**File:** `crates/driver/src/mir_converter.rs:177-188` — only Assign converted

| Rustc Statement Variant | Impact | Priority | Complexity |
|-------------------------|--------|----------|------------|
| `StatementKind::SetDiscriminant(place, variant_idx)` | Enum tag mutation after construction not modeled — used in optimized MIR for in-place enum updates | MUST-HAVE | Small — convert to IR SetDiscriminant (needs new IR Statement variant) |
| `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op))` | `core::intrinsics::assume(cond)` cannot be propagated as SMT premise | SHOULD-HAVE | Small — convert to IR Assign(_, Use(op)) or new Assume IR statement |
| `StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping { src, dst, count })` | Unsafe memcpy not modeled | NICE-TO-HAVE | Large — requires heap model integration |
| `StatementKind::FakeRead` | Pattern binding reads — OK to skip (no semantic content) | N/A | None needed |
| `StatementKind::StorageLive/Dead` | Scope markers — OK to skip | N/A | None needed |
| `StatementKind::Retag` | Stacked borrows validation — OK to skip for sound-but-incomplete model | NICE-TO-HAVE | Large — requires borrow model extension |

### 1.5 MIR Terminator Variants Not Converted

**File:** `crates/driver/src/mir_converter.rs:253` — `_ => Unreachable`

| Rustc Terminator Variant | Impact | Priority | Complexity |
|--------------------------|--------|----------|------------|
| `TerminatorKind::InlineAsm` | Any function with `asm!` block is truncated at that point — path ends as Unreachable | SHOULD-HAVE (unsafe code) | Large — model as havoc of destination registers |
| `TerminatorKind::UnwindResume` | Panic paths always seen as Unreachable — OK for sound-but-incomplete model | NICE-TO-HAVE | Medium — needs unwind tracking |
| `TerminatorKind::TailCall` | Tail call optimization not modeled | NICE-TO-HAVE | Medium — treat same as Call |
| `TerminatorKind::CoroutineYield` | Post-transform coroutines don't use this (handled via async_vcgen) | N/A | N/A |

### 1.6 Type Conversion Gaps

**File:** `crates/driver/src/mir_converter.rs:386-417` — `_ => Named(format!("{ty:?}"))`

| Rustc Type | IR Representation | Impact | Priority | Complexity |
|------------|-------------------|--------|----------|------------|
| `TyKind::Adt(def, substs)` for structs/enums | `Named("{ty:?}")` — debug string | Struct/enum types not recognized as structured | MUST-HAVE | Medium — inspect `def.adt_kind()` and reconstruct Struct/Enum IR type |
| `TyKind::FnPtr(sig)` | `Named("fn(...)")` — opaque | Cannot reason about function pointer equality or spec | SHOULD-HAVE | Medium — need `Ty::FnPtr` IR variant |
| `TyKind::FnDef(def_id, _)` | `Named("...")` — opaque | Function items used as closures lose type info | SHOULD-HAVE | Medium — map to closure encoding |
| `TyKind::Str` | `Named("str")` — opaque | String slice content unverifiable | NICE-TO-HAVE | Large — SMT Seq theory |
| `TyKind::Param(t)` | `Named("{t:?}")` — loses Generic marker | Generic parameters not recognized as `Ty::Generic` | MUST-HAVE | Small — map to `ir::Ty::Generic(t.name.as_str().to_string())` |
| `TyKind::Alias` (opaque/projection) | `Named(...)` — opaque | Associated types not resolved | NICE-TO-HAVE | Large — requires trait resolution |
| `TyKind::Float(F16)` / `Float(F128)` | Rounded to F32/F64 | Incorrect bit widths for f16/f128 | NICE-TO-HAVE | Medium — need F16/F128 in ir::FloatTy |

---

## Category 2: IR Representation Gaps (ir.rs)

These gaps prevent certain constructs from being expressed even if converted.

### 2.1 Missing IR Rvalue Variants

| Missing Variant | Description | Priority | Complexity |
|-----------------|-------------|----------|------------|
| `Rvalue::AddressOf(Mutability, Place)` | Raw reference to place (for `ptr::addr_of!`) | SHOULD-HAVE | Small |
| `Rvalue::Repeat(Operand, usize)` | Array fill `[x; N]` | SHOULD-HAVE | Small |
| `Rvalue::NullaryOp(NullaryOp, Ty)` | SizeOf/AlignOf/OffsetOf/UbChecks queries | SHOULD-HAVE | Small |
| `Rvalue::CopyForDeref(Place)` | Deref coercion copy | SHOULD-HAVE | Small |
| `Rvalue::ShallowInitBox(Operand, Ty)` | Box heap allocation | NICE-TO-HAVE | Medium |
| `Rvalue::ThreadLocalRef(String)` | Thread-local variable reference | NICE-TO-HAVE | Large |

### 2.2 Missing IR Statement Variants

| Missing Variant | Description | Priority | Complexity |
|-----------------|-------------|----------|------------|
| `Statement::SetDiscriminant(Place, usize)` | Enum tag assignment separate from data | MUST-HAVE | Small |
| `Statement::Assume(Operand)` | Inject assume premise from intrinsics | SHOULD-HAVE | Small |

### 2.3 Missing IR Type Variants

| Missing Type | Description | Priority | Complexity |
|--------------|-------------|----------|------------|
| `Ty::FnPtr(Vec<Ty>, Ty)` | Function pointer type `fn(A, B) -> C` | SHOULD-HAVE | Medium |
| `Ty::ConstGeneric(Box<Ty>, String)` | Const generic parameter `N: usize` | NICE-TO-HAVE (deferred v0.6) | Large |
| `Ty::Str` | String slice type `str` | NICE-TO-HAVE | Medium |
| `Ty::Float(F16)` / `Ty::Float(F128)` | 16-bit / 128-bit IEEE floats | NICE-TO-HAVE | Medium |

---

## Category 3: VCGen / Encoding Gaps (vcgen.rs, encode_term.rs, encode_sort.rs)

These gaps are in the translation layer — IR constructs that exist but are not encoded correctly.

### 3.1 Float-to-Int Cast Encoding Unsound

**File:** `crates/analysis/src/encode_term.rs:755-756`
```rust
// TODO Phase 29: proper round-to-zero conversion.
fn encode_float_to_int_cast(src: Term, _from_bits: u32, to_bits: u32) -> Term {
    Term::Extract(to_bits - 1, 0, Box::new(src))
}
```
**Impact:** `f64 as i32` is encoded by extracting bits from a Float sort term. However, Float sort and BitVec sort have different SMT-LIB2 representations — `Extract` on a Float is type-incorrect in standard SMT-LIB2. The correct encoding is `((_ fp.to_sbv 32) RTZ src)` for signed truncation or the unsigned variant.

**Priority:** MUST-HAVE (soundness — current encoding may produce type errors in Z3 or unsound results)
**Complexity:** Small — replace Extract with `Term::App("(_ fp.to_sbv to_bits)", [rtz_mode, src])`

### 3.2 Projected LHS + Non-Use Rvalue Returns None

**File:** `crates/analysis/src/vcgen.rs:1522-1529`
```rust
if !place.projections.is_empty() {
    let lhs = encode_place_with_type(place, func)?;
    let rhs = match rvalue {
        Rvalue::Use(op) => encode_operand_for_vcgen(op, func),
        _ => return None, // Complex rvalues on projected places are rare
    };
```
**Impact:** Field mutation assignments like `s.x = s.x + 1` (which in MIR is: `Assign(*(_1.0), BinaryOp(Add, Copy(_1.0), Const(1)))`) silently produce no VC. This means mutations of struct fields do not create SMT assertions — postconditions about field values after mutation may trivially pass without verification.

**Priority:** MUST-HAVE (soundness hole for struct mutation)
**Complexity:** Medium — need to create a struct update term: `mk-Struct(new_field_val, original_other_fields...)`

### 3.3 Enum Aggregate Fallback Produces Invalid Constructor Names

**File:** `crates/analysis/src/encode_term.rs:173-183`
```rust
AggregateKind::Enum(_name, variant_idx) => {
    if let Ty::Enum(_enum_name, variants) = result_ty
        && let Some((variant_name, _)) = variants.get(*variant_idx)
    {
        let constructor = format!("mk-{variant_name}");
        return Some(Term::App(constructor, encoded_ops));
    }
    // Fallback: use variant index
    let constructor = format!("mk-variant-{variant_idx}");
    Some(Term::App(constructor, encoded_ops))
```
**Impact:** When the result type is not `Ty::Enum` (e.g., it was converted to `Ty::Named` at MIR conversion), the fallback `mk-variant-{idx}` constructor is emitted, but the datatype declaration uses `mk-{variant_name}` constructors. The SMT solver will report an undeclared function symbol, causing a solver error rather than a verification result.

**Priority:** SHOULD-HAVE
**Complexity:** Small — propagate enum type information from MIR conversion (Category 1.6 fix enables this)

### 3.4 Generic Trait Bound Premises Not Injected (VCGEN-04 — Plan 28-05 Incomplete)

**File:** `crates/analysis/src/monomorphize.rs` — `trait_bound_constraints()` returns `Vec<String>`
**File:** `crates/analysis/src/vcgen.rs` — `generate_vcs_monomorphized()` does not inject trait bounds

**Impact:** Generic functions with `where T: Ord` or `where T: Add<Output=T>` bounds do not have those constraints as SMT premises. The VCGen proves postconditions assuming nothing about `T` — which is sound (conservative) but means verification may be incomplete: valid generic functions may fail to verify because the bound's implications are not available.

**ROADMAP status:** Phase 28 Plan 05 (`28-05-PLAN.md`) shown as unchecked `[ ]` in ROADMAP.md line 305.

**Priority:** MUST-HAVE (completing v0.5 commitment)
**Complexity:** Small — add `trait_bounds_as_smt_assumptions()` returning `Vec<Term>` and wire into `generate_vcs_with_db`

### 3.5 Rvalue::Ref — No Aliasing or Separation Logic Integration

**File:** `crates/analysis/src/vcgen.rs:1562-1565`
```rust
Rvalue::Ref(_, ref_place) => {
    // Reference is transparent -- same as the value
    Term::Const(ref_place.local.clone())
}
```
**Impact:** Mutable references create no ownership constraints in the VCGen path. The separation logic reasoning (SEP phases 20-24) runs separately. If a function takes two `&mut` parameters aliasing the same location, VCGen encodes them as two separate variables without any aliasing constraint — potentially proving unsound postconditions.

**Priority:** SHOULD-HAVE (borrow checker prevents most cases in safe Rust; only matters for unsafe code or raw pointers)
**Complexity:** Large — requires integration between VCGen and the ownership/separation logic module

### 3.6 String Constants — Semantic Content Opaque

**File:** `crates/analysis/src/encode_term.rs:295`
```rust
Constant::Str(s) => Term::Const(format!("STR_{s}")),
```
**Impact:** String constants are encoded as uninterpreted SMT constants. Comparison of `s == "hello"` produces a term that Z3 treats as a boolean over two opaque uninterpreted constants — the equality can be asserted but string content cannot be reasoned about. Pattern matching on string values in specs is not possible.

**Priority:** NICE-TO-HAVE
**Complexity:** Large — SMT Seq theory with char/byte element type; requires new IR Constant::Str variant handling

### 3.7 Projection::Downcast — No Type Narrowing in encode_place_with_type

**File:** `crates/analysis/src/encode_term.rs:86-89`
```rust
Projection::Downcast(_variant_idx) => {
    // Enum downcast is handled during pattern matching
    // The type doesn't change here
}
```
**Impact:** When accessing a field of a specific enum variant (`if let MyEnum::Variant(x) = e { ... }`), the downcast projection does not narrow the type to the variant's inner type. This means `encode_place_with_type` may return the wrong selector application when the subsequent `Field` projection tries to access a variant-specific field.

**Priority:** SHOULD-HAVE (needed for correct if-let/match pattern variable extraction)
**Complexity:** Medium — need to thread variant type information through Downcast → Field projection chain

### 3.8 Array Repeat `[x; N]` — No VCGen Support

**Impact:** `let a = [0u32; 10]` cannot be verified. The array is not even converted (Category 1.3 gap). No `Term::Lambda` or constant array encoding exists for initializing all elements.

**Priority:** SHOULD-HAVE
**Complexity:** Medium — encode as `Store(Store(... Store(default_arr, 0, x) ..., N-1, x))` for small N, or uninterpreted constant with `forall i. arr[i] == x` for large N

### 3.9 SizeOf / AlignOf — No Constant Encoding

**Impact:** `std::mem::size_of::<T>()` and `std::mem::align_of::<T>()` return uninterpreted values (dropped at MIR conversion). Unsafe code relying on layout properties cannot be verified.

**Priority:** SHOULD-HAVE (important for unsafe code)
**Complexity:** Small — maintain a table of known sizes and emit as BV constant; emit uninterpreted constant for generic types

---

## Category 4: Spec Language Gaps

These gaps prevent users from writing certain kinds of specifications.

### 4.1 No Destructor/Drop Contracts

**Impact:** Cannot specify what a `Drop` impl should ensure. Rust programs that rely on RAII invariants (invariants established in `new()` and maintained through `drop()`) cannot be end-to-end verified.

**Priority:** SHOULD-HAVE
**Complexity:** Large — need `#[on_drop(ensures)]` spec form; requires Drop trait method detection in call graph

### 4.2 No Const Generic Specs

**Impact:** Functions like `fn zeros<const N: usize>() -> [u32; N]` cannot have specs that reference `N`. Const generic parameters are entirely absent from the IR.

**Priority:** MUST-HAVE for array-oriented code (deferred to v0.6 per REQUIREMENTS.md)
**Complexity:** Large — `Ty::ConstGeneric`, const evaluation pipeline, SMT Int sort for N

### 4.3 No Pattern Match in Spec Expressions

**Impact:** Cannot write `#[ensures(match result { Ok(v) => v > 0, Err(_) => true })]` — specs must be expressed as boolean combinations of projections. Complex discriminant-based specs require manual projection encoding.

**Priority:** SHOULD-HAVE
**Complexity:** Large — requires spec parser extension and discriminant-aware spec encoding

### 4.4 No Fractional Permissions in Separation Logic

**Impact:** Cannot express partial ownership (e.g., `1/2 * pts_to(p, v)` for shared read permission). The current separation logic uses full ownership only. Read-sharing between concurrent readers requires fractional permissions.

**Priority:** NICE-TO-HAVE (advanced concurrent verification)
**Complexity:** Large — requires fractional heap model extension

### 4.5 No Async Closure Specs (Rust 2024)

**Impact:** `async |x| { ... }` closures (Rust 2024 feature) cannot be specified with fn_spec or verified. Explicitly deferred to v0.6.

**Priority:** MUST-HAVE for v0.6
**Complexity:** Large — needs async closure IR, fn_spec extension with async postconditions

### 4.6 No Pin / Unpin Reasoning

**Impact:** Cannot verify that `Pin<P>` invariants are maintained. Async code using custom futures requires Pin-safe memory movement reasoning.

**Priority:** NICE-TO-HAVE
**Complexity:** Large — requires type-level Pin tracking in IR

### 4.7 No Trait Method Specs Inheritance Checking

**Impact:** When a trait method has a contract (`#[requires]`/`#[ensures]`) and an impl overrides it, the tool verifies the impl but does not check that the impl's behavior is consistent with the trait's contract. The behavioral subtyping check (Phase 8) covers LSP-style subtype checking but does not verify that ALL implementors satisfy ALL callers' assumptions.

**Priority:** SHOULD-HAVE
**Complexity:** Medium — extend behavioral_subtyping.rs to check every impl against the trait contract

---

## Category 5: IDE / Driver Gaps

### 5.1 Source Locations for Aggregate-Derived VCs

**Impact:** VCs generated from aggregate construction (struct/enum) will have `source_line: None` because the statement-level location tracking only populates locations for terminators and overflow checks. Fixing aggregate VCGen (Category 1.2) without also propagating source locations will yield confusing diagnostics.

**Priority:** SHOULD-HAVE (usability)
**Complexity:** Small — piggyback on existing location propagation pattern

### 5.2 Counterexample Rendering for Enum Variants

**File:** `crates/driver/src/cex_render.rs`
**Impact:** Enum variant counterexamples need to show which variant was selected and its field values. The current rendering handles bitvectors, structs, arrays, and raw pointers. Enum discriminant + variant payload rendering may be incomplete.

**Priority:** SHOULD-HAVE
**Complexity:** Medium — inspect the cex_render enum path; may already be partially handled via datatype model values

---

## Prioritized Gap Summary

### P0: MUST-HAVE (Correctness / Soundness Holes)

| Gap ID | Description | File | Complexity |
|--------|-------------|------|------------|
| C1.1 | Cast kind not preserved in mir_converter (float-to-int unsound) | mir_converter.rs:288 | Medium |
| C1.2 | Aggregate only converts Tuple (struct/enum construction silently dropped) | mir_converter.rs:303 | Medium |
| C1.6a | Generic Param type not mapped to `Ty::Generic` in convert_ty | mir_converter.rs:415 | Small |
| C3.1 | Float-to-int cast SMT encoding is type-incorrect (Extract on Float sort) | encode_term.rs:755 | Small |
| C3.2 | Projected LHS + non-Use rvalue returns None (struct mutation not verified) | vcgen.rs:1527 | Medium |
| C3.4 | VCGEN-04 generic trait bound premises not injected (Plan 28-05 incomplete) | monomorphize.rs + vcgen.rs | Small |
| C2.2a | SetDiscriminant statement not representable in IR | ir.rs + mir_converter.rs | Small |

### P1: SHOULD-HAVE (Practical Coverage)

| Gap ID | Description | File | Complexity |
|--------|-------------|------|------------|
| C1.3a | Rvalue::CopyForDeref not converted | mir_converter.rs | Small |
| C1.3d | Rvalue::Repeat (`[x; N]`) not converted | mir_converter.rs | Medium |
| C1.3c | Rvalue::NullaryOp (SizeOf/AlignOf) not converted | mir_converter.rs | Small |
| C1.3a | Rvalue::AddressOf not converted | mir_converter.rs | Small |
| C1.4b | StatementKind::Intrinsic::Assume not converted | mir_converter.rs | Small |
| C1.6b | ADT struct/enum types go to Named() instead of Ty::Struct/Enum | mir_converter.rs:415 | Medium |
| C2.1d | Rvalue::Repeat missing from IR | ir.rs | Small |
| C2.3a | Ty::FnPtr missing from IR | ir.rs | Medium |
| C3.3 | Enum aggregate fallback constructor name mismatch | encode_term.rs:183 | Small (blocked by C1.6b) |
| C3.5 | Mutable reference aliasing not modeled in VCGen | vcgen.rs:1562 | Large |
| C3.7 | Projection::Downcast no type narrowing | encode_term.rs:86 | Medium |
| C3.8 | Array repeat `[x; N]` — no VCGen support | vcgen.rs + encode_term.rs | Medium |
| C3.9 | SizeOf/AlignOf — no constant encoding | vcgen.rs | Small |
| C4.1 | No destructor/Drop contracts | spec parser + vcgen | Large |
| C4.3 | No pattern match in spec expressions | spec_parser.rs | Large |
| C4.7 | Trait method spec inheritance not checked for all impls | behavioral_subtyping.rs | Medium |
| C5.2 | Counterexample rendering for enum variants incomplete | cex_render.rs | Medium |

### P2: NICE-TO-HAVE (Advanced / Deferred)

| Gap ID | Description | Complexity |
|--------|-------------|------------|
| C1.3b | Rvalue::ThreadLocalRef not converted | Large |
| C1.3e | Rvalue::ShallowInitBox (Box allocation) not converted | Medium |
| C1.5a | InlineAsm terminator not converted | Large |
| C1.5b | UnwindResume terminator not converted | Medium |
| C1.6c | TyKind::Str not mapped to structured type | Large |
| C1.6d | F16/F128 not in FloatTy | Medium |
| C2.3b | Ty::ConstGeneric (deferred to v0.6 per REQUIREMENTS.md) | Large |
| C2.3c | Ty::Str | Medium |
| C3.6 | String constant semantic reasoning | Large |
| C4.2 | Const generic specs (deferred v0.6) | Large |
| C4.4 | Fractional permissions in separation logic | Large |
| C4.5 | Async closure specs (deferred v0.6) | Large |
| C4.6 | Pin/Unpin reasoning | Large |
| C5.1 | Source locations for aggregate-derived VCs | Small |

---

## Recommended Next Milestone (v0.6) Sequencing

Based on dependencies and impact, the recommended order for the next phase batch:

**Phase 29: MIR Converter Completeness** (prerequisite for most VCGen work)
- Fix cast kind preservation (C1.1)
- Fix ADT struct/enum type conversion (C1.6b)
- Fix TyKind::Param → Ty::Generic mapping (C1.6a)
- Add Aggregate struct/enum/closure conversion (C1.2)
- Add SetDiscriminant Statement (C2.2a, C1.4a)

**Phase 30: VCGen Soundness Fixes** (can start after Phase 29)
- Fix float-to-int cast encoding (C3.1)
- Fix projected LHS + non-Use rvalue (C3.2)
- Fix Projection::Downcast type narrowing (C3.7)
- Fix enum aggregate constructor fallback (C3.3)

**Phase 31: Missing Rvalue Coverage**
- Rvalue::Repeat / array fill (C3.8)
- Rvalue::AddressOf / raw pointer creation (C1.3a)
- Rvalue::CopyForDeref (C1.3a)
- Rvalue::NullaryOp SizeOf/AlignOf (C3.9)

**Phase 32: VCGEN-04 Completion + Spec Extensions**
- Generic trait bound premises injection — Plan 28-05 (C3.4)
- Assume intrinsic as SMT premise (C1.4b)
- FnPtr type + spec (C2.3a)

**Deferred to v0.6:**
- Const generics (C4.2, C2.3b)
- Async closures (C4.5)
- Pattern match in spec expressions (C4.3)
- Drop contracts (C4.1)
- String reasoning (C3.6, C1.6c)

---

## Appendix: What IS Working Well (Do Not Regress)

The following areas are confirmed correct and should not be disturbed:

| Feature | Implementation | Status |
|---------|----------------|--------|
| BinaryOp (all 16 ops, signed/unsigned/float) | encode_binop() | Complete |
| UnaryOp (Not, Neg for all types) | encode_unop() | Complete |
| SwitchInt path-condition traversal | traverse_block() | Complete |
| Loop invariant VCGen (init/preserve/exit) | generate_loop_vcs() | Complete |
| Overflow/division/shift checks | overflow_check() | Complete |
| Contract pre/postconditions | generate_contract_vcs() | Complete |
| Struct field access via selector | encode_field_access() | Complete |
| Array index via Select + bounds VC | generate_index_bounds_vcs() | Complete |
| Slice Len as constant | Rvalue::Len encoding | Complete |
| Discriminant binding for match | Rvalue::Discriminant encoding | Complete |
| Numeric as-cast encoding | encode_cast() | Complete |
| FPA theory for f32/f64 | encode_fp_binop() | Complete |
| Monomorphization | generate_vcs_monomorphized() | Complete |
| fn_spec closures (Fn/FnMut/FnOnce) | hof_vcgen.rs | Complete |
| Separation logic (pts_to, ghost predicates) | sep_logic.rs | Complete |
| Async state invariants | async_vcgen.rs | Complete |
| Data race freedom (happens-before) | concurrency/happens_before.rs | Complete |
| RC11 weak memory coherence | concurrency/rc11.rs | Complete |
| Deadlock detection | concurrency/deadlock_detection.rs | Complete |
| Quantifiers with trigger inference | encode_quantifier.rs | Complete |
| Prophecy variables | encode_prophecy.rs | Complete |
| SpecInt/SpecNat unbounded arithmetic | bv2int.rs + encode_sort.rs | Complete |
| Behavioral subtyping (LSP) | behavioral_subtyping.rs | Complete |
| Counterexample typed rendering | cex_render.rs | Complete |
| Incremental caching | cache.rs | Complete |
