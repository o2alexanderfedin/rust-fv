# Phase 46: SMT Datatype Foundations - Context

**Gathered:** 2026-03-04
**Status:** Ready for planning

<domain>
## Phase Boundary

Structs and enums are encoded as first-class SMT datatypes with constructors, selectors, and testers. Rvalue::Repeat is encoded as universally quantified array equality or const-array. Functional update is hardened for all rvalue types, nested projections, and enum variant fields. Z3 native backend supports Int, Datatype, and Array sorts with full arithmetic.

Requirements: COMPL-01 (struct/enum datatypes), COMPL-05 (functional update hardening), COMPL-07 (Z3 Int sort), COMPL-11 (Rvalue::Repeat encoding).

</domain>

<decisions>
## Implementation Decisions

### Repeat Array Encoding ([expr; N])
- Hybrid approach: Z3 const-array for literal/known N, forall quantifier for symbolic N
- Forall quantifier uses auto-trigger with `(select arr i)` to prevent matching loops
- Bounds-checked access reuses `VcKind::MemorySafety` (consistent with Phase 28 BoundsCheck VCs)
- Array length emitted as named SMT constant (like `Rvalue::Len`) — enables postconditions referencing length

### Datatype Wiring
- Full replacement of all `Sort::Uninterpreted` fallbacks for struct/enum types with `Sort::Datatype`
- Enum testers use Z3 built-in `((_ is mk-VariantName) expr)` from declare-datatype — no explicit discriminant assertions
- Struct field access uses SMT selectors `(StructName-fieldName expr)` — Z3 evaluates natively
- Aggregate initialization (`Rvalue::Aggregate`) emits full constructor terms `(mk-StructName val1 val2 ...)` instead of per-field assertions

### Z3 Native Backend Sort Support
- Full Int arithmetic: declare-const, add/sub/mul/div/mod, all comparisons
- Int-to-BitVec and BitVec-to-Int conversions for bv2int paths
- Sort::Datatype support in native backend: constructor/selector/tester operations
- Sort::Array support in native backend: const-array, select, store operations

### Functional Update Hardening
- All rvalue types supported on projected places: Use, BinaryOp, CheckedBinaryOp, UnaryOp, Cast, Ref, Len, Discriminant
- Nested field projections supported via chained mk-Inner inside mk-Outer constructors
- Enum variant field mutation via Downcast projection supported (mk-Variant constructor with updated field)
- All functional updates unified with new datatype constructor terms (mk-StructName)

### Claude's Discretion
- Internal refactoring approach for wiring datatype declarations into VCGen pipeline
- Test organization for the four feature areas
- Error handling when MIR types lack field information for datatype encoding
- SMT logic selection when datatypes are used (QF_DT, AUFDTLIA, etc.)

</decisions>

<code_context>
## Existing Code Insights

### Reusable Assets
- `encode_sort.rs:collect_datatype_declarations()`: Already generates `DeclareDatatype` commands from IR types — struct, tuple, enum, closure all supported
- `encode_sort.rs:encode_type()`: Maps `Ty::Struct/Enum` to `Sort::Datatype(name)` — encoding layer complete
- `smtlib/command.rs:DeclareDatatype`: AST variant with `DatatypeVariant { constructor, fields }` — fully defined
- `smtlib/formatter.rs`: DeclareDatatype formatting tested and working for structs, enums, tuples
- `smtlib/sort.rs:Sort::Datatype`: Sort variant exists; `Sort::Int` also exists

### Established Patterns
- Phase 29: Functional update uses `mk-StructName` constructor with ALL fields in order — changed field gets new_val, others get selector(base)
- Phase 28: `Rvalue::Discriminant` encoded as `Term::App` uninterpreted selector — will be replaced with native tester
- Phase 28: `BoundsCheck VCs` use `VcKind::MemorySafety` — Repeat array access should follow same pattern
- Phase 28: `Rvalue::Len` emits named constant — Repeat array length should match

### Integration Points
- `vcgen.rs:1792`: `Rvalue::Repeat(..) => return None` — the exact line that needs encoding
- `vcgen.rs:1667`: `_ => None` in `encode_rvalue_for_assignment` — needs all rvalue branches
- `vcgen.rs:1684-1714`: Single-level Field projection functional update — needs nesting + Downcast
- `z3_native.rs:137`: `Sort::Int => Err(...)` — needs full implementation
- `z3_native.rs:140`: Catch-all `_ => Err(...)` — needs Datatype and Array handling

</code_context>

<specifics>
## Specific Ideas

No specific requirements — open to standard approaches. All decisions follow "recommended" patterns consistent with existing codebase conventions and Z3 datatype theory best practices.

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 46-smt-datatype-foundations*
*Context gathered: 2026-03-04*
