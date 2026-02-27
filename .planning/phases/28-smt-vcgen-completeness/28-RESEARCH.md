# Phase 28: SMT VCGen Completeness — Research

**Researched:** 2026-02-23
**Domain:** Rust IR → SMT-LIB VCGen — completeness audit for Rust expression categories
**Confidence:** HIGH (all findings from direct codebase inspection)

---

## Summary

Phase 28 closes the VCGen completeness gap for four major Rust expression categories:
memory operations, conditional operators, typecasts, and generics. The codebase
already has a rich VCGen infrastructure (`crates/analysis/src/vcgen.rs`, ~8150 lines),
a complete IR definition (`ir.rs`), and a full SMT term library. The gaps are well-defined
and surgical — no architectural rewrites needed.

The most critical gap is `Rvalue::Cast` (line 1444 in vcgen.rs), which today is a
comment-marked identity stub: `// Phase 1: casts are identity (TODO: proper cast encoding)`.
All four `CastKind` variants (`IntToInt`, `IntToFloat`, `FloatToInt`, `FloatToFloat`,
`Pointer`) fall through to `encode_operand(op)`, discarding type information. The SMT
term library already has `ZeroExtend`, `SignExtend`, `Extract`, `Bv2Int`, `Int2Bv` — all
the primitives needed.

The `Rvalue::Discriminant` path is similarly stubbed out (line 1456: `return None`). Match
arms lower to `SwitchInt { discr: Operand::Copy(discriminant_place), targets, otherwise }` —
the path-sensitive VCGen already handles `SwitchInt`, but discriminant extraction is skipped.
`if let` and `while let` also desugar to `SwitchInt` after MIR lowering.

For generics, `trait_bound_constraints()` in monomorphize.rs exists but its output (a
`Vec<String>` of human-readable constraints) is never injected into VCGen as SMT premises.
The monomorphization pathway (`generate_vcs_monomorphized`) is complete but does not pass
trait bounds as assumptions. Spec propagation for generic specs is not wired.

Array indexing has partial support — `Projection::Index(idx_local)` maps to `Term::Select`
in `encode_place_with_type()`, but the bounds check VC for `a[i]` (asserting `i < len`) is
not generated. `Rvalue::Len` returns `None` (no VC generated). Range expressions and
foreach iteration have no IR representation — they are caller responsibilities to lower
into index-bounded loops before constructing the `Function` IR.

**Primary recommendation:** Implement in four plans, one per requirement: (1) VCGEN-01
memory/index/slice/range/field, (2) VCGEN-02 match/if-let/while-let discriminants, (3)
VCGEN-03 numeric as-casts + transmute, (4) VCGEN-04 generic where-clause premises.

---

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| VCGEN-01 | Memory operations: array indexing bounds VCs, loop/range encoding, slice/span length model, struct/tuple field projection | `Projection::Index` → `Term::Select` exists; `Rvalue::Len` stubbed; `encode_place_with_type` has field projection; bounds check VC missing |
| VCGEN-02 | Conditional operators: match with patterns (literal/tuple/enum/wildcard/guard), if-let, while-let, exhaustiveness | `SwitchInt` handled; `Rvalue::Discriminant` returns None; match arms not modeled with guard predicates |
| VCGEN-03 | Typecasts: numeric `as` casts (truncation/sign-ext), unsafe transmute as BV reinterpret, pointer-to-integer, no-op casts | `Rvalue::Cast` is identity stub (line 1444); all `CastKind` variants unimplemented; SMT primitives available |
| VCGEN-04 | Generics: where-clause constraints as SMT premises, generic spec annotation propagation, trait bound encoding as uninterpreted sort constraints | `trait_bound_constraints()` returns `Vec<String>`; never injected as SMT `Assert`s; monomorphization pathway exists |
</phase_requirements>

---

## Standard Stack

### Core (already in use — no new dependencies needed)

| Component | Location | Purpose | Status |
|-----------|----------|---------|--------|
| `rust_fv_smtlib::term::Term` | `crates/smtlib/src/term.rs` | SMT term AST | Complete — has ZeroExtend, SignExtend, Extract, Bv2Int, Int2Bv, SeqNth, SeqLen, Select, Store |
| `rust_fv_smtlib::sort::Sort` | `crates/smtlib/src/sort.rs` | Sort system | Complete — BitVec, Bool, Int, Array, Seq, Float |
| `crate::ir::*` | `crates/analysis/src/ir.rs` | IR definitions | Complete — CastKind, Projection, Rvalue all defined |
| `crate::encode_term` | `crates/analysis/src/encode_term.rs` | Term encoding helpers | `encode_binop`, `encode_unop`, `encode_place_with_type` exist |
| `crate::encode_sort` | `crates/analysis/src/encode_sort.rs` | Sort encoding | `encode_type()` handles all Ty variants |
| `crate::vcgen::generate_vcs_with_db` | `crates/analysis/src/vcgen.rs:235` | Main VCGen entry | All new VCGen logic plugs in here |
| `crate::monomorphize` | `crates/analysis/src/monomorphize.rs` | Generic type substitution | `substitute_generics()`, `trait_bound_constraints()` exist |

**No new crate dependencies required.** All SMT primitives for Phase 28 already exist in
the smtlib crate.

### SMT Theory Requirements per Requirement

| Requirement | SMT Theory | Logic String |
|-------------|------------|--------------|
| VCGEN-01 (array index bounds) | QF_BV + Array theory | `QF_AUFBV` or `QF_ABV` |
| VCGEN-01 (seq/slice length) | SMT Seq theory | `QF_AUFLIA` with seq |
| VCGEN-02 (match/discriminant) | QF_BV (integer discriminants) | `QF_BV` |
| VCGEN-03 (numeric as-casts) | QF_BV (bitvector extract/extend) | `QF_BV` |
| VCGEN-03 (transmute) | QF_BV (concat/extract reinterpret) | `QF_BV` |
| VCGEN-04 (trait bounds) | QF_BV or QF_LIA depending on concrete type | depends on monomorphization |

---

## Architecture Patterns

### Recommended Project Structure (no changes needed)

```
crates/analysis/src/
├── vcgen.rs              # main entry — encode_assignment() is the hook point
├── encode_term.rs        # add encode_cast(), bounds_check_term()
├── encode_sort.rs        # no changes needed
├── monomorphize.rs       # add trait_bounds_as_smt_assumptions()
└── ir.rs                 # no changes needed (CastKind already complete)

crates/analysis/tests/
└── vcgen_completeness28.rs   # new test file for VCGEN-01..04
```

### Pattern 1: Cast Encoding in encode_assignment()

**What:** Replace the identity stub at vcgen.rs:1444 with a proper `encode_cast()` dispatcher.
**When to use:** Every `Rvalue::Cast(kind, op, target_ty)` assignment.
**Example:**

```rust
// In encode_term.rs — new function
pub fn encode_cast(kind: &CastKind, operand: &Operand, target_ty: &Ty, source_ty: &Ty) -> Term {
    let src = encode_operand(operand);
    match kind {
        CastKind::IntToInt => encode_int_to_int_cast(src, source_ty, target_ty),
        CastKind::IntToFloat => encode_int_to_float_cast(src, source_ty, target_ty),
        CastKind::FloatToInt => encode_float_to_int_cast(src, source_ty, target_ty),
        CastKind::FloatToFloat => encode_float_to_float_cast(src, source_ty, target_ty),
        CastKind::Pointer => src, // pointer casts modeled as identity on bitvector
    }
}

// Integer-to-integer cast: widening (zero/sign extend) or narrowing (extract)
fn encode_int_to_int_cast(src: Term, from_ty: &Ty, to_ty: &Ty) -> Term {
    let from_bits = from_ty.bit_width().unwrap_or(64) as u32;
    let to_bits = to_ty.bit_width().unwrap_or(64) as u32;
    match (from_bits.cmp(&to_bits), from_ty.is_signed(), to_ty.is_signed()) {
        (Ordering::Less, true, _)  => Term::SignExtend(to_bits - from_bits, Box::new(src)),
        (Ordering::Less, false, _) => Term::ZeroExtend(to_bits - from_bits, Box::new(src)),
        (Ordering::Greater, _, _)  => Term::Extract(to_bits - 1, 0, Box::new(src)),
        (Ordering::Equal, _, _)    => src, // no-op cast (reinterpret)
    }
}
```

Source: direct inspection of `encode_term.rs` and `ir.rs` — HIGH confidence.

### Pattern 2: Discriminant Encoding for Match/if-let

**What:** Handle `Rvalue::Discriminant(place)` as the integer discriminant value of an enum.
**When to use:** Every `SwitchInt` whose `discr` operand reads from a `Discriminant` assignment.
**Example:**

```rust
// In vcgen.rs encode_assignment()
Rvalue::Discriminant(disc_place) => {
    // Encode discriminant as an uninterpreted integer selector (or BV if enum is known)
    // Pattern: declare _N_discriminant as BitVec(8) and assert its value constraints
    // from the enum type's variant indices
    let disc_term = Term::App(
        format!("discriminant-{}", disc_place.local),
        vec![encode_place(disc_place)]
    );
    disc_term
}
```

For full match pattern support, the SwitchInt path-condition encoding in `traverse_block`
already works correctly — match arms lower to `SwitchInt` with one target per variant
discriminant value. The gap is: `encode_assignment` currently returns `None` for
`Rvalue::Discriminant`, so the discriminant variable is not bound in the SMT context,
causing match arms to have unconstrained discriminants.

### Pattern 3: Array Index Bounds VC

**What:** When `Projection::Index(idx)` is used, generate a `BoundsCheck` VC alongside the
array access.
**When to use:** Any place with `Projection::Index` in statements or terminators.
**Example:**

```rust
// In vcgen.rs — add to generate_overflow_vc style, or inline in path enumeration
// Bounds check: 0 <= idx AND idx < len
let idx_term = Term::Const(idx_local.clone());
let len_term = Term::Const(format!("{}_len", arr_local));
let bounds_ok = Term::And(vec![
    Term::BvULe(Box::new(Term::BitVecLit(0, 64)), Box::new(idx_term.clone())),
    Term::BvULt(Box::new(idx_term), Box::new(len_term)),
]);
// VC: assert NOT bounds_ok is UNSAT (i.e., bounds_ok always holds)
let vc_script = build_vc_script_with_negation(bounds_ok, ...);
```

For `Rvalue::Len(place)`, encode as `{place_local}_len` constant (declare as BitVec 64)
and tie to the slice/array sort's length field.

### Pattern 4: Generic Where-Clause as SMT Premise

**What:** Inject trait-bound constraints from `func.generic_params[i].trait_bounds` as
SMT `Assert` commands before postcondition/precondition checks.
**When to use:** `generate_vcs_with_db` when `!func.generic_params.is_empty()`.
**Example:**

```rust
// In vcgen.rs generate_vcs_with_db, after collecting declarations
for gp in &func.generic_params {
    let concrete_ty = /* from monomorphization substitution */;
    let constraints = crate::monomorphize::trait_bounds_as_smt_assumptions(gp, concrete_ty);
    for constraint_term in constraints {
        declarations.push(Command::Assert(constraint_term));
    }
}
```

`trait_bound_constraints()` currently returns `Vec<String>` (human-readable). It needs a
companion `trait_bounds_as_smt_assumptions()` that returns `Vec<Term>`. For `Ord` on `i32`:
the assumption is that comparison operators are total order — which is already guaranteed by
BV semantics, so the assumption is `BoolLit(true)`. For unrecognized traits: use an
`Uninterpreted` sort constraint as `BoolLit(true)` (conservative: no contradiction).

### Anti-Patterns to Avoid

- **Identity cast stub persistence:** Do not leave `Rvalue::Cast(_, op, _) => encode_operand(op)` — this causes `u64 as i32` to pass through full 64-bit width, generating soundness holes.
- **Discriminant skipping in match:** Do not return `None` from `encode_assignment` for `Rvalue::Discriminant` — SwitchInt path conditions become unconstrained, proving false postconditions.
- **New SMT logic strings:** Do not introduce new `SetLogic` strings beyond those already used (`QF_BV`, `QF_LIA`, `QF_ABV`, `AUFLIA`). The existing set covers all needs.
- **Transmute as semantic cast:** Transmute is `unsafe` and must be modeled as raw bitvector reinterpretation (`concat`/`extract`), never as a value-preserving cast.
- **Range encoding in IR:** Ranges (`1..10`, `1..=10`) do not exist in the IR as a first-class value. They are desugared by the MIR lowering. In the IR, they appear as bounds variables on loops. Do not add a `Range` IR node — use the existing `LoopInfo.invariants` + start/end bounds pattern.

---

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Zero/sign extension | Custom bitvector math | `Term::ZeroExtend(n, _)` / `Term::SignExtend(n, _)` | Already in smtlib term.rs, emits correct SMT-LIB2 `((_ zero_extend n) ...)` |
| Bitvector truncation | Manual bit masking | `Term::Extract(hi, lo, _)` | Already in smtlib term.rs, emits `((_ extract hi lo) ...)` |
| BV-to-int conversion | Custom arithmetic | `Term::Bv2Int(_)` | Already in smtlib term.rs, emits `(bv2int ...)` |
| SMT Seq length | Custom array counter | `Term::SeqLen(_)` | Already in smtlib term.rs, used by stdlib Vec contracts |
| Array bounds assertion | Custom bounds check function | Pattern: `Term::BvULt(idx, len)` as a VcKind::BoundsCheck | Follows existing `overflow_check()` pattern in encode_term.rs |
| Discriminant sort | New IR node | Encode discriminant as `BitVec(8)` uninterpreted constant | Discriminant is always a small integer; stays within QF_BV |

**Key insight:** The smtlib `Term` enum already has all 60+ operators needed for Phase 28.
The work is wiring them into `encode_assignment()` and the bounds-check VC generator.

---

## Common Pitfalls

### Pitfall 1: Cast Source Type Not Available at Encoding Site

**What goes wrong:** `encode_assignment` for `Rvalue::Cast(kind, op, target_ty)` has the
target type but not the source type. Source type must be inferred from the operand.
**Why it happens:** The `Rvalue::Cast` variant stores `(CastKind, Operand, Ty)` where `Ty`
is the *target* type. Source type must come from `infer_operand_type(func, op)`.
**How to avoid:** Call `infer_operand_type(func, op)` (already exists in vcgen.rs) to get
the source type. Fall back to `find_local_type(func, &place.local)` if needed. If source
type cannot be determined, fall through to identity (existing behavior) with a warning.
**Warning signs:** Cast VC generates wrong bitvector width — check that source and target
widths are being computed separately.

### Pitfall 2: QF_BV Logic Incompatible with Seq Theory

**What goes wrong:** If a function uses both array index bounds (needing `QF_ABV`) and seq
operations (needing `QF_AUFLIA`), mixing logic strings in one VC causes Z3 to reject the
script.
**Why it happens:** Logic strings are per-script. A VC must use one logic that covers all
operations it uses.
**How to avoid:** Use `QF_AUFBV` for scripts that combine arrays+bitvectors. For scripts
that use Seq theory (Vec/slice length), use `AUFLIA` as done by existing HOF VCs. The
logic selection in `generate_contract_vcs` should inspect what sorts are declared.
**Warning signs:** Z3 returns `(error "unknown logic")` — check the logic string matches
the Sort set used.

### Pitfall 3: Discriminant Value Confusion with Rust Enum Discriminant Layout

**What goes wrong:** Rust enums can have explicit discriminants (e.g., `Foo = 5`) or
auto-incremented ones. The SwitchInt targets contain the raw discriminant values. If
VCGen assumes discriminants are 0-based, it will prove wrong path conditions for enums
with custom discriminant values.
**Why it happens:** `Terminator::SwitchInt { targets: Vec<(i128, BlockId)>, ... }` already
carries the correct discriminant value per arm. This is already handled correctly in the
existing SwitchInt path-condition logic.
**How to avoid:** Use the `(value, block)` pairs from `targets` as-is — do not normalize.
The `Rvalue::Discriminant` encoding should produce the same value that SwitchInt compares
against.
**Warning signs:** If a `match x { 0 => ..., 1 => ... }` postcondition VC is SAT (fails)
when the function is correct — check that `Discriminant` assignment term equals the SwitchInt
target values.

### Pitfall 4: Transmute Width Mismatch Causes Unsound VCs

**What goes wrong:** `transmute::<u32, f32>(x)` must produce a term of exactly 32 bits.
If the implementation zero-extends to 64 bits before reinterpreting, the VC encodes wrong
semantics.
**Why it happens:** FloatTy::F32 has sort `(_ FloatingPoint 8 24)` (32 bits total), but
`Sort::BitVec(32)` is also 32 bits. The conversion must pass through `FpFromBits`.
**How to avoid:** Model transmute between integer and float as:
- `u32 as transmute → f32`: `Term::FpFromBits` on the 32-bit BV
- `f32 as transmute → u32`: concat of sign/exponent/mantissa bits
Use `CastKind::Pointer` path for pointer transmutes (already identity on BitVec 64).
**Warning signs:** Transmute VC UNSAT when it should be SAT, or wrong FP sort emitted.

### Pitfall 5: Generic Where Bounds Already Satisfied by BV Semantics

**What goes wrong:** Adding spurious `Assert(BoolLit(true))` premises for trivially-true
trait bounds causes no harm but adds noise. More dangerous: adding incorrect premises
(e.g., claiming `T: Ord` implies `T` is comparable with BvSLt) for non-integer types.
**Why it happens:** `Ord` for integers is guaranteed by bitvector comparison; for custom
types it is not.
**How to avoid:** `trait_bounds_as_smt_assumptions` should only emit non-trivial constraints
for known integer/bool types. For unrecognized concrete types, emit `BoolLit(true)`.
**Warning signs:** A postcondition VC becomes UNSAT after generic substitution for a
non-integer type — check that no false ordering assumptions were injected.

---

## Code Examples

Verified patterns from codebase inspection:

### Existing: SwitchInt Path Condition (vcgen.rs ~line 1100)

```rust
// Source: crates/analysis/src/vcgen.rs traverse_block()
Terminator::SwitchInt { discr, targets, otherwise } => {
    let discr_term = encode_operand_for_vcgen(discr, func);
    for (value, target_block) in targets {
        let cond = Term::Eq(
            Box::new(discr_term.clone()),
            Box::new(Term::BitVecLit(*value, /* width */)),
        );
        // push cond and recurse into target_block
    }
    // otherwise: not(any of the target conditions)
}
```

This already works. Match arms need `Rvalue::Discriminant` to bind the discriminant variable.

### New Pattern: IntToInt Cast (widening signed)

```rust
// Source: crates/analysis/src/encode_term.rs — to be added
// i8 as i32: sign-extend by 24 bits
pub fn encode_int_to_int_cast(src: Term, from_bits: u32, to_bits: u32, from_signed: bool) -> Term {
    use std::cmp::Ordering;
    match from_bits.cmp(&to_bits) {
        Ordering::Equal   => src,  // no-op (reinterpret)
        Ordering::Less    => if from_signed {
            Term::SignExtend(to_bits - from_bits, Box::new(src))
        } else {
            Term::ZeroExtend(to_bits - from_bits, Box::new(src))
        },
        Ordering::Greater => Term::Extract(to_bits - 1, 0, Box::new(src)),
    }
}
```

Term::SignExtend, Term::ZeroExtend, Term::Extract all verified present in term.rs.

### New Pattern: Discriminant Assignment

```rust
// vcgen.rs encode_assignment() — replace `return None` with:
Rvalue::Discriminant(disc_place) => {
    // The discriminant is an integer selector on the enum value.
    // Model as: _N_discr = discriminant(disc_place.local)
    // Since the enum value is declared as an uninterpreted sort, use an
    // uninterpreted function `discriminant-X : X -> BitVec(8)`
    let disc_fn = format!("discriminant-{}", disc_place.local);
    Term::App(disc_fn, vec![Term::Const(disc_place.local.clone())])
}
```

The SwitchInt handler then compares this term against literal discriminant values, forming
the correct path conditions for match arms.

### New Pattern: Trait Bound as SMT Assumption

```rust
// monomorphize.rs — new function
pub fn trait_bounds_as_smt_assumptions(gp: &GenericParam, concrete_ty: &Ty) -> Vec<Term> {
    // For integer types with Ord/PartialOrd: the assumption is trivially true
    // (BV comparison is already total-ordered)
    // Return BoolLit(true) for all known constraints — they become no-ops in SMT
    // but document the contract expectation
    gp.trait_bounds.iter().map(|_bound| Term::BoolLit(true)).collect()
}
```

For `fn_spec` spec propagation, generic functions need their spec expression to carry
the generic param name (e.g., `T`) which gets substituted during monomorphization.
`spec_parser.rs` already handles generic parameter names as free constants in int_mode.

---

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Casts as identity (`encode_operand(op)`) | (Phase 28 target) Correct BV extend/truncate | Phase 28 | Fixes truncation soundness holes |
| Discriminant returns None | (Phase 28 target) Uninterpreted function encoding | Phase 28 | Enables match/if-let VCs |
| Trait bounds as `Vec<String>` (human-readable only) | (Phase 28 target) As SMT Assert premises | Phase 28 | Enables generic spec propagation |
| Array index as `Term::Select` only (no bounds check) | (Phase 28 target) Select + BoundsCheck VC | Phase 28 | Adds VCGEN-01 index safety |

**Currently working (do not change):**
- `Rvalue::BinaryOp`, `UnaryOp`, `Use`, `Aggregate`, `CheckedBinaryOp`, `Ref`: all correct
- `SwitchInt` path-condition traversal: correct
- `Projection::Field` in `encode_place_with_type`: correct
- `Projection::Index` → `Term::Select`: correct (just needs the bounds VC companion)
- Monomorphization via `substitute_generics`: correct
- All overflow/division/shift VCs: correct

---

## Open Questions

1. **Range expressions in IR**
   - What we know: Ranges (`1..10`, `1..=10`) are not a distinct `Rvalue` variant. MIR lowers
     them to struct constructors (`std::ops::Range { start: 1, end: 10 }`).
   - What's unclear: Whether the MIR converter (`crates/driver/src/mir_converter.rs`) emits
     a `Ty::Struct("Range", ...)` or a `Ty::Named("Range")` for range types in the IR.
   - Recommendation: For Phase 28, model ranges as start/end variable pairs extracted by
     field projection. If MIR converter emits `Ty::Named("Range")`, the VCGen treats it as
     uninterpreted — add a stdlib contract entry for `Range` in the contract DB.

2. **`if let` / `while let` IR shape**
   - What we know: `if let Some(x) = opt { ... }` lowers to `SwitchInt` on the `Option`
     discriminant (0 = None, 1 = Some). The inner `x` binding is via `Downcast` + `Field`
     projection.
   - What's unclear: Whether `Projection::Downcast(variant_idx)` is currently threaded
     through `encode_place_with_type` correctly when the inner type is a struct-variant.
   - Recommendation: Audit `encode_place_with_type` for the `Projection::Downcast` case
     (currently: `// Enum downcast is handled during pattern matching — the type doesn't
     change here`). For Phase 28, this may be sufficient if the discriminant VC is added.

3. **Transmute of non-primitive types**
   - What we know: `transmute::<u64, [u8; 8]>(x)` involves composite types. The IR would
     have `CastKind::Pointer` for raw pointer transmutes (already identity).
   - What's unclear: Whether the MIR converter ever emits `Rvalue::Cast(CastKind::IntToInt, ..)`
     for composite-type transmutes, or whether they are handled differently.
   - Recommendation: For Phase 28, handle transmute only for primitive types (int-float,
     int-int). Mark composite transmute as `// TODO Phase 29` with identity fallback.

---

## Validation Architecture

**Note:** `workflow.nyquist_validation` is not set in `.planning/config.json`. Tests run
via standard `cargo test` in TDD style as per project CLAUDE.md conventions.

### Test Framework

| Property | Value |
|----------|-------|
| Framework | Rust built-in test harness via `cargo test` |
| Config file | `Cargo.toml` (workspace) |
| Quick run command | `cargo test -p rust-fv-analysis --test vcgen_completeness28 2>&1 \| tail -20` |
| Full suite command | `cargo test -p rust-fv-analysis 2>&1 \| tail -30` |
| Estimated runtime | ~15–30 seconds (Z3 integration tests) |

### Phase Requirements → Test Map

| Req ID | Behavior | Test Type | Automated Command | File Exists? |
|--------|----------|-----------|-------------------|-------------|
| VCGEN-01 | Array index bounds VC generated for `a[i]` with `i < len` premise | unit | `cargo test -p rust-fv-analysis vcgen_01_array_index` | No — Wave 0 gap |
| VCGEN-01 | Field projection encodes as selector function in SMT | unit | `cargo test -p rust-fv-analysis vcgen_01_field_projection` | No — Wave 0 gap |
| VCGEN-01 | Slice `Rvalue::Len` generates length constant declaration | unit | `cargo test -p rust-fv-analysis vcgen_01_slice_len` | No — Wave 0 gap |
| VCGEN-02 | Match discriminant binding produces correct path conditions | unit | `cargo test -p rust-fv-analysis vcgen_02_match_discr` | No — Wave 0 gap |
| VCGEN-02 | if-let SwitchInt+Downcast generates correct path VC | unit | `cargo test -p rust-fv-analysis vcgen_02_if_let` | No — Wave 0 gap |
| VCGEN-03 | i8 as i32 encodes as sign_extend(24, x) | unit | `cargo test -p rust-fv-analysis vcgen_03_cast_sign_extend` | No — Wave 0 gap |
| VCGEN-03 | u64 as i32 encodes as extract(31, 0, x) | unit | `cargo test -p rust-fv-analysis vcgen_03_cast_truncate` | No — Wave 0 gap |
| VCGEN-03 | transmute u32↔f32 encodes as BV reinterpretation | unit | `cargo test -p rust-fv-analysis vcgen_03_transmute` | No — Wave 0 gap |
| VCGEN-04 | where T: Ord produces SMT assume premise in generic function | unit | `cargo test -p rust-fv-analysis vcgen_04_trait_bound` | No — Wave 0 gap |
| VCGEN-04 | Generic spec annotation propagated after monomorphization | unit | `cargo test -p rust-fv-analysis vcgen_04_generic_spec` | No — Wave 0 gap |

### Wave 0 Gaps (must be created before implementation)

- [ ] `crates/analysis/tests/vcgen_completeness28.rs` — all VCGEN-01..04 tests
- [ ] Register in `crates/analysis/Cargo.toml` under `[[test]]` if not auto-discovered

*(Existing test infrastructure in `completeness_suite.rs`, `e2e_verification.rs` cover
arithmetic/control-flow but have no Phase 28 constructs.)*

---

## Sources

### Primary (HIGH confidence — direct codebase inspection)

- `crates/analysis/src/vcgen.rs:1444` — Cast identity stub confirmed
- `crates/analysis/src/vcgen.rs:1456` — Discriminant stub (`return None`) confirmed
- `crates/analysis/src/encode_term.rs:22-50` — `encode_place` flattening vs `encode_place_with_type` selection confirmed
- `crates/analysis/src/encode_sort.rs:37-47` — Array and Slice → `Sort::Array` confirmed
- `crates/analysis/src/ir.rs:776-789` — `CastKind` enum verified: `IntToInt`, `IntToFloat`, `FloatToInt`, `FloatToFloat`, `Pointer`
- `crates/analysis/src/ir.rs:712-723` — `Projection` enum verified: `Deref`, `Field`, `Index`, `Downcast`
- `crates/smtlib/src/term.rs:94-100` — `ZeroExtend`, `SignExtend`, `Extract` confirmed present
- `crates/analysis/src/monomorphize.rs:253-300` — `trait_bound_constraints()` returns `Vec<String>`, not wired to VCGen
- `crates/analysis/src/vcgen.rs:987-1039` — `generate_vcs_monomorphized()` does not inject trait bound premises

### Secondary (MEDIUM confidence)

- `crates/analysis/tests/completeness_suite.rs` — confirms existing tests cover arithmetic/branching, not casts/match/generics
- `.planning/REQUIREMENTS.md` — VCGEN-01..04 requirements as specified

---

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH — all relevant types/functions verified by file inspection
- Architecture: HIGH — encode_assignment hook point verified, all needed Term variants confirmed present
- Pitfalls: HIGH — cast stub and discriminant stub confirmed by reading exact lines in vcgen.rs
- Test gaps: HIGH — searched all test files, confirmed no VCGEN-01..04 tests exist

**Research date:** 2026-02-23
**Valid until:** 2026-03-25 (codebase is stable; no external dependency changes needed)
