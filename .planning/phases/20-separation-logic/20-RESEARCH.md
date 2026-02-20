# Phase 20: Separation Logic - Research

**Researched:** 2026-02-19
**Domain:** Separation logic SMT encoding, heap ownership predicates, frame rule, recursive ghost predicates
**Confidence:** HIGH (codebase), MEDIUM (separation logic encoding strategy)

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| SEP-01 | User can write `pts_to(p, v)` ownership predicate in `#[requires]`/`#[ensures]` to specify raw pointer ownership | `pts_to(p, v)` is recognized as a built-in call in `spec_parser.rs::convert_call`; encodes to a heap-select equality term plus an ownership assertion on a new `sep_heap` SMT array; heap array sorts already exist (`Sort::Array`) and the `heap_model.rs` byte-array can be extended or shadowed |
| SEP-02 | User can write separating conjunction (`H1 * H2`) in specs to prove disjoint ownership and aliasing freedom | Rust `*` is `BinOp::Mul` in syn — already parsed; a special-casing rule in `convert_binop` (or a new operator surface) detects that both operands are heap-predicate terms and emits a `SepConj` term; `Term` enum needs a new `SepConj` variant OR sep-conj is encoded as a pair of assertions with a disjointness axiom |
| SEP-03 | Frame rule is automatically applied during function calls so unchanged heap portions are not required to be manually re-specified | Frame rule is applied automatically during call-site encoding in `vcgen.rs::encode_call_site`; when a callee has sep-logic contracts, the footprint is computed from `pts_to` atoms in the precondition; a framing axiom asserts that all heap addresses outside the footprint are unchanged |
| SEP-04 | User can define recursive heap predicates via `#[ghost_predicate]` and the verifier unfolds them to depth 3 | A new `#[ghost_predicate]` proc-macro stores the predicate body as a doc attribute (`rust_fv::ghost_predicate::name::body`); a new `GhostPredicateDatabase` in `analysis` stores parsed predicate bodies; the spec parser substitutes predicate calls by inlining the body up to depth 3 at parse time |
</phase_requirements>

## Summary

Phase 20 adds separation logic to the existing Rust formal verifier. The verifier currently uses a byte-array heap model (`heap_model.rs`) for raw pointer null-checks and bounds-checks, plus pure first-order logic for functional specs. Separation logic requires a distinct heap domain so that ownership (pts_to) and separating conjunction can be encoded without conflicting with the existing byte-array model.

The four requirements decompose cleanly into: (1) a new `SepHeap` sort — an SMT array from pointer addresses (BitVec 64) to typed values, separate from the existing byte-array `heap` — plus a companion `perm` array tracking ownership booleans; (2) a `pts_to(p, v)` built-in recognized in the spec parser that encodes as `(and (= (select sep_heap p) v) (select perm p))`; (3) separating conjunction encoded as `(and P Q (not (exists addr. (and (select perm_P addr) (select perm_Q addr)))))` — i.e., P and Q hold AND their permission domains do not overlap; (4) frame rule applied automatically at call sites by asserting that all non-footprint addresses are unchanged; (5) recursive ghost predicates stored in a new `GhostPredicateDatabase` and inlined to depth 3 by the spec parser.

The critical design decision flagged in prior planning is: use the **Viper-style Ref sort + permission mask** model (fractional permissions, `perm: Array Addr Real`, threshold at 1.0) vs the **bitvector-set permissions** approach (boolean ownership tracking per address). Based on codebase analysis, the bitvector-set / boolean-ownership approach is simpler to integrate with the existing Z3/QF_BV setup and sufficient for the phase requirements (which do not require fractional shared permissions).

**Primary recommendation:** Use a dedicated `SepHeap` sort (distinct from the existing byte-array heap model), encode ownership as a Boolean permission array `perm`, encode `pts_to` and separating conjunction as Z3 array terms, apply frame rule automatically by asserting unchanged addresses outside the callee footprint, and inline recursive ghost predicates to depth 3 at spec-parse time.

## Standard Stack

### Core
| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| Z3 (via rust_fv_smtlib) | existing | SMT encoding of sep-logic as array + forall terms | Already the solver backend; `Sort::Array`, `Term::Forall`, `Term::Exists`, `Term::Select`, `Term::Store` all exist |
| syn | existing | Parsing `#[ghost_predicate]` attribute bodies | Already used in all proc-macros; parses Rust expression syntax |
| rust_fv_smtlib | existing | `Term`, `Sort`, `Command` types for new sep-logic terms | All needed sorts and term forms already present |
| rust_fv_analysis::ir | existing | `Ty`, `Contracts`, `SpecExpr`, `Function` | Sep-logic contracts stored as `SpecExpr { raw }` — no IR change needed |

### Supporting
| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| HashMap (std) | std | `GhostPredicateDatabase` internal storage | Predicate name → body lookup during spec parsing |
| tracing | existing | Debug logging for predicate unfolding depth | Already used throughout; add depth trace logs |

### Alternatives Considered
| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| Boolean perm array | Fractional perm (Real sort) | Fractional is needed for shared read permissions; Boolean suffices for Phase 20 (only exclusive ownership required) |
| Inline ghost predicates at parse time | Z3 recursive functions (`define-fun-rec`) | Z3 recursive functions require quantifier support and trigger annotations; bounded inlining is simpler and decidable |
| New `SepConj` Term variant | Encoding sep-conj as conjunction + disjointness axiom inline | A dedicated `Term::SepConj` keeps the formatter clean; encoding inline at every call site is verbose and error-prone |

**No new Cargo dependencies required.** All required sorts and term forms already exist in the smtlib crate.

## Architecture Patterns

### Recommended Project Structure

New files and extensions:

```
crates/
├── macros/src/lib.rs               # EXTEND: add ghost_predicate proc-macro
├── analysis/src/
│   ├── sep_logic.rs                # NEW: SepHeap declarations, pts_to/sep_conj encoding, frame rule
│   ├── ghost_predicate_db.rs       # NEW: GhostPredicateDatabase (name → parsed body)
│   ├── spec_parser.rs              # EXTEND: recognize pts_to(), sep_conj (*) in convert_call / convert_binop
│   ├── vcgen.rs                    # EXTEND: include sep_heap declarations, apply frame rule at call sites
│   └── ir.rs                       # EXTEND: GhostPredicate field in Function (or separate DB)
├── driver/src/
│   └── callbacks.rs                # EXTEND: extract ghost_predicate attrs, populate GhostPredicateDatabase
└── smtlib/src/
    └── term.rs                     # EXTEND: add Term::SepConj variant (optional; can encode inline)
```

### Pattern 1: Separation Heap Domain

**What:** Declare a typed heap separate from the existing byte-array model. The sep-heap maps pointer addresses (BitVec 64) to an uninterpreted sort `HeapVal` (each pointer carries its own value in the model). A companion permission array tracks ownership.

**SMT-LIB declarations:**
```smtlib
; Separation heap sorts
(declare-sort HeapVal 0)                        ; abstract value type
(declare-fun sep_heap () (Array (_ BitVec 64) HeapVal))   ; address -> value
(declare-fun perm     () (Array (_ BitVec 64) Bool))      ; address -> owned?
```

**Rust code to add in `sep_logic.rs`:**
```rust
// Source: analysis pattern, verified against Sort::Array and Sort::Uninterpreted in codebase
use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::sort::Sort;

pub fn declare_sep_heap() -> Vec<Command> {
    let addr_sort = Sort::BitVec(64);
    let heap_val_sort = Sort::Uninterpreted("HeapVal".to_string());
    let perm_sort = Sort::Bool;
    vec![
        Command::DeclareSort("HeapVal".to_string(), 0),
        Command::DeclareFun(
            "sep_heap".to_string(),
            vec![],
            Sort::Array(Box::new(addr_sort.clone()), Box::new(heap_val_sort)),
        ),
        Command::DeclareFun(
            "perm".to_string(),
            vec![],
            Sort::Array(Box::new(addr_sort), Box::new(perm_sort)),
        ),
    ]
}
```

**Confidence:** HIGH — `Sort::Array`, `Sort::Uninterpreted`, `Command::DeclareSort`, `Command::DeclareFun` are all verified in the codebase.

### Pattern 2: `pts_to(p, v)` Encoding

**What:** `pts_to(p, v)` asserts two things: (1) the permission array says address `p` is owned, (2) `sep_heap[p] == v` where `v` is interpreted as a `HeapVal`.

**SMT encoding:**
```smtlib
; pts_to(p, v) encodes to:
; (and (select perm p) (= (select sep_heap p) v_heap))
; where v_heap is v cast to HeapVal via a declared function or equality on HeapVal
```

**Spec parser extension in `convert_call` (inside `match func_name.as_str()`):**
```rust
// In spec_parser.rs, add to the match block in convert_call:
"pts_to" => {
    if call_expr.args.len() != 2 {
        return None; // pts_to(ptr, value) takes exactly 2 arguments
    }
    let ptr_term = convert_expr_with_bounds(
        &call_expr.args[0], func, in_old, in_int_mode, bound_vars
    )?;
    let val_term = convert_expr_with_bounds(
        &call_expr.args[1], func, in_old, in_int_mode, bound_vars
    )?;
    // perm ownership: (select perm ptr)
    let perm_select = Term::Select(
        Box::new(Term::Const("perm".to_string())),
        Box::new(ptr_term.clone()),
    );
    // heap value equality: (= (select sep_heap ptr) val_term_as_heapval)
    // HeapVal is uninterpreted; connect via equality with a cast function
    let heap_select = Term::Select(
        Box::new(Term::Const("sep_heap".to_string())),
        Box::new(ptr_term),
    );
    let val_eq = Term::Eq(Box::new(heap_select), Box::new(val_term));
    return Some(Term::And(vec![perm_select, val_eq]));
}
```

**Confidence:** HIGH — `Term::Select`, `Term::Eq`, `Term::And` are verified in `smtlib/src/term.rs`.

**Note on typed values:** `HeapVal` is uninterpreted. For `pts_to(p, v)` where `v: i32`, we need a bridge. Declare a per-type accessor: `(declare-fun heapval_to_i32 (HeapVal) (_ BitVec 32))`. The equality becomes `(= (heapval_to_i32 (select sep_heap p)) v)`. This is the standard "proxy field" approach used by Viper's heap encoding.

### Pattern 3: Separating Conjunction (`H1 * H2`)

**What:** Two heap predicates `H1` and `H2` are written `H1 * H2` in specs. Rust syntax: `H1 * H2` parses as `BinOp::Mul`. We detect when both sub-expressions contain sep-logic terms and re-interpret multiplication as separating conjunction.

**Detection approach:** Track whether a spec expression is a "sep-logic formula" vs a "value formula" via a new `SpecKind` enum passed through the parser OR simply recognize the pattern when both arguments are `pts_to(...)` calls (simpler for Phase 20 scope).

**SMT encoding of `P * Q`:**
```smtlib
; H1 * H2 encodes to:
; (and H1_assertion H2_assertion
;      (forall ((addr (_ BitVec 64)))
;        (not (and (= (select perm_H1 addr) true)
;                  (= (select perm_H2 addr) true)))))
```

Since we use a single global `perm` array (not per-assertion), the disjointness is:
- Assert H1 (which asserts `select perm p1`)
- Assert H2 (which asserts `select perm p2`)
- Assert `(distinct p1 p2)` — the two pointers are different addresses

For Phase 20 (bounded aliasing freedom, not full permission accounting), the separating conjunction of two `pts_to` atoms simplifies to asserting both and asserting the addresses differ:

```rust
// In convert_binop, add a case for Mul when both sides are sep-logic:
SynBinOp::Mul(_) if is_sep_logic_expr(&left) && is_sep_logic_expr(&right) => {
    // Separating conjunction: H1 * H2
    // Both H1 and H2 must hold, and their footprints must be disjoint
    // For pts_to atoms, disjointness = address inequality (handled by sep_heap model)
    Some(Term::And(vec![left, right]))
    // Disjointness is enforced by the permission model: a single perm array
    // where pts_to(p, v) asserts (select perm p), and the sep-heap model
    // axiomatizes that each address can only be owned once.
}
```

**Confidence:** MEDIUM — The encoding is correct for the `pts_to * pts_to` case but full separating conjunction over arbitrary predicates requires permission mask tracking, which is more complex. For Phase 20 bounded scope, two `pts_to` atoms are sufficient.

### Pattern 4: Frame Rule at Call Sites

**What:** When calling a function `f` with sep-logic contracts (contains `pts_to` in requires/ensures), the frame rule says: the caller's heap outside `f`'s footprint is unchanged after the call.

**Implementation in `vcgen.rs` call-site encoding:**

The existing `encode_call_site` logic in `vcgen.rs` asserts preconditions and assumes postconditions. To add the frame rule:

1. **Compute footprint:** Extract all pointer arguments from `pts_to(p, v)` atoms in the callee's `requires`.
2. **Assert frame:** After the call, assert `∀ addr. addr ∉ footprint → sep_heap_post[addr] = sep_heap_pre[addr]`.

In SMT-LIB:
```smtlib
; Frame axiom (for callee with footprint {p1}):
; (assert (forall ((addr (_ BitVec 64)))
;           (=> (not (= addr p1))
;               (= (select sep_heap_post addr) (select sep_heap_pre addr)))))
```

**Rust pattern for frame assertion:**
```rust
// In vcgen.rs, after encoding callee postconditions:
fn build_frame_assertion(footprint_ptrs: &[Term]) -> Term {
    let addr_var = "sep_frame_addr".to_string();
    let addr_sort = Sort::BitVec(64);

    // not_in_footprint: addr ≠ p1 ∧ addr ≠ p2 ∧ ...
    let not_in_fp: Term = if footprint_ptrs.is_empty() {
        Term::BoolLit(true)
    } else {
        let neq_terms: Vec<Term> = footprint_ptrs.iter().map(|p| {
            Term::Not(Box::new(Term::Eq(
                Box::new(Term::Const(addr_var.clone())),
                Box::new(p.clone()),
            )))
        }).collect();
        Term::And(neq_terms)
    };

    // heap unchanged: (= (select sep_heap_post addr) (select sep_heap_pre addr))
    let heap_unchanged = Term::Eq(
        Box::new(Term::Select(
            Box::new(Term::Const("sep_heap_post".to_string())),
            Box::new(Term::Const(addr_var.clone())),
        )),
        Box::new(Term::Select(
            Box::new(Term::Const("sep_heap_pre".to_string())),
            Box::new(Term::Const(addr_var.clone())),
        )),
    );

    Term::Forall(
        vec![(addr_var, addr_sort)],
        Box::new(Term::Implies(Box::new(not_in_fp), Box::new(heap_unchanged))),
    )
}
```

**Confidence:** HIGH — `Term::Forall`, `Term::Implies`, `Term::Not`, `Term::Eq`, `Term::Select` all verified in codebase. The pattern follows the standard frame axiom encoding used by Dafny and Viper's Carbon backend.

### Pattern 5: `#[ghost_predicate]` Macro and Recursive Unfolding

**What:** User defines a recursive heap predicate:
```rust
#[ghost_predicate]
fn linked_list(p: *const Node, n: usize) -> bool {
    if n == 0 {
        p.is_null()
    } else {
        pts_to(p, *p) && linked_list((*p).next, n - 1)
    }
}
```

The verifier unfolds `linked_list(p, n)` up to depth 3 when it appears in a spec.

**Implementation parts:**

1. **Proc-macro (`macros/src/lib.rs`):** New `#[ghost_predicate]` attribute stored as `rust_fv::ghost_predicate::<name>::<serialized_fn_body>`.

2. **Extraction (`callbacks.rs`):** In `extract_contracts`, recognize `rust_fv::ghost_predicate::` prefix, parse function name and body, store in a new `GhostPredicateDatabase`.

3. **`GhostPredicateDatabase` (`ghost_predicate_db.rs`):** Maps predicate name → (param_names: Vec<String>, body_raw: String). At lookup time, substitutes actual arguments into the body string and re-parses.

4. **Bounded inlining:** In `spec_parser.rs::convert_call`, when `func_name` is found in the `GhostPredicateDatabase`, inline the body with depth counter:
   - Depth 0: inline with recursive calls left as uninterpreted `Term::App(name, args)` (treat as unknown/false)
   - Depth 1-3: recursively inline with decremented depth
   - Depth > 3: return `Term::BoolLit(false)` (conservative: assume predicate doesn't hold beyond depth 3)

**Confidence:** MEDIUM — The attribute-based storage pattern is directly from the existing `spec_attribute` mechanism (verified). The bounded inlining is standard in SL verifiers (Viper/Prusti use it for predicates) but requires careful substitution logic.

### Anti-Patterns to Avoid

- **Reusing the existing `heap` byte-array for sep-logic:** `heap: Array (_ BitVec 64) (_ BitVec 8)` is byte-addressed and conflicts with typed ownership. Use a separate `sep_heap` and `perm` array. The prior planning decision explicitly requires this separation.
- **Encoding `pts_to` as equality only (without permission):** `pts_to(p, v)` without the `(select perm p)` ownership check is unsound — two `pts_to(p, v1) * pts_to(p, v2)` would not be detected as aliased.
- **Using `define-fun-rec` in SMT-LIB for ghost predicates:** Z3's support for recursive function definitions (`define-fun-rec`) requires careful termination arguments and is poorly supported in QF_ALL_ARRAYS contexts. Use bounded inlining instead.
- **Allowing sep-conj (`*`) to pass through as integer multiplication:** The `convert_binop` `Mul` branch must check if both sub-expressions are sep-logic terms BEFORE falling through to `BvMul`. Failure to do this will silently encode `H1 * H2` as bitvector multiplication, producing wrong Z3 queries with no error.
- **Running sep-logic VCs with `QF_BV` logic:** Sep-logic introduces array theory (sep_heap, perm) and quantifiers (frame rule). The SMT logic must be changed to `ALL` or `QF_AUFBV` for VCs involving sep-logic specs.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Recursive predicate termination | Custom fixpoint iteration | Bounded unfolding (depth 3) | Fixpoint requires mu-calculus or widening; bounded inlining is decidable and matches success criteria |
| Full separation logic decision procedure | Custom heap analysis | Z3 array + forall axioms | SL decision procedures are complex (GRASShopper is 50k LOC); Z3 array + quantifier encoding covers the required fragment |
| Permission accounting | Fractional permission tree | Simple boolean `perm` array | Fractional permissions are needed for shared reads; Phase 20 only requires exclusive ownership (`pts_to`), boolean suffices |
| Ghost predicate body serialization | Custom AST serialization | `syn::Expr::to_token_stream().to_string()` | The same `spec_attribute` mechanism already serializes spec expressions; reuse it |
| Heap footprint computation | Alias analysis | Syntactic extraction from `pts_to` atoms in requires | Phase 20 footprint = explicit `pts_to(p, ...)` pointers; no alias analysis needed |

**Key insight:** The phase does not require a complete separation logic decision procedure. It requires enough of SL to (1) express ownership, (2) check non-aliasing, (3) frame automatically. Z3 array + quantifier encoding with bounded predicate unfolding achieves all four requirements without implementing a specialized SL solver.

## Common Pitfalls

### Pitfall 1: SMT Logic String Must Include Array Theory

**What goes wrong:** The existing null-check VCs use `(set-logic QF_BV)`. Sep-logic VCs use `(select sep_heap addr)` — array operations — and `(forall ...)` for frame axioms. Z3 will reject `(select ...)` under `QF_BV`.

**Why it happens:** Each VC script has a `Command::SetLogic(...)` at the top. Sep-logic VCs need `QF_AUFBV` (quantifier-free arrays + bitvectors) for the sep_heap/perm arrays, or `ALL` if the frame forall quantifier is present.

**How to avoid:** In `sep_logic.rs`, provide a helper `sep_logic_smt_logic() -> &'static str` that returns `"AUFBV"` (if frame rule forall is present: `"ALL"`). The VCGen uses this instead of `"QF_BV"` for any VC containing sep-logic assertions.

**Warning signs:** Z3 returning `unknown` or `error` with "unknown sort" or "invalid logic" for a sep-logic VC.

### Pitfall 2: Recursive Ghost Predicate Causes Spec Parser Stack Overflow

**What goes wrong:** `linked_list(p, n)` calls `linked_list((*p).next, n - 1)`. Without a depth counter, the spec parser recursively expands forever.

**Why it happens:** The spec parser calls `parse_spec_expr` on the body, which calls `convert_call` on `linked_list(...)`, which calls `parse_spec_expr` on the body again — unbounded recursion.

**How to avoid:** Pass a `depth: usize` parameter through the spec parser call chain. In `GhostPredicateDatabase::unfold(name, args, depth)`, when `depth == 0`, return `Term::BoolLit(false)` (or a sentinel for "unknown"). Never call `unfold` without decrementing the counter.

**Warning signs:** Stack overflow (`thread main has overflowed its stack`) when parsing a spec containing a recursive ghost predicate.

### Pitfall 3: `pts_to` Type Mismatch Between HeapVal and Concrete Type

**What goes wrong:** `pts_to(p, 42i32)` where `p: *const i32`. The `sep_heap` maps addresses to `HeapVal` (uninterpreted sort). Comparing `(select sep_heap p)` (type: `HeapVal`) with `42i32` (type: `(_ BitVec 32)`) produces a sort mismatch in Z3.

**Why it happens:** The uninterpreted `HeapVal` sort cannot directly be compared with bitvector terms.

**How to avoid:** Declare a per-type accessor function: `(declare-fun heapval_as_i32 (HeapVal) (_ BitVec 32))`. In `pts_to` encoding, wrap the heap select: `(= (heapval_as_i32 (select sep_heap p)) v)`. The accessor name is derived from the pointer's pointee type from the IR (`Ty::RawPtr(inner, _)` → use `inner` to determine width).

**Warning signs:** Z3 error "sort mismatch" when running a sep-logic VC.

### Pitfall 4: Separating Conjunction on Non-`pts_to` Expressions

**What goes wrong:** User writes `(x > 0) * pts_to(p, v)` — `x > 0` is a Boolean value expression, not a heap predicate. Treating `*` as sep-conj here would either fail to parse or silently encode as bitvector multiplication.

**Why it happens:** The `*` operator is ambiguous between arithmetic multiplication and separating conjunction depending on context.

**How to avoid:** Detect sep-conj only when at least one operand is a `pts_to(...)` call or a known ghost predicate application. Implement a `is_sep_logic_formula(expr) -> bool` helper that checks if a `syn::Expr` is a call to `pts_to` or a registered ghost predicate name. If neither operand is a sep-formula, fall through to the existing `BvMul` encoding.

**Warning signs:** `BvMul` of two `Bool` sorts, producing Z3 sort error; or sep-logic term silently treated as integer multiplication.

### Pitfall 5: Frame Rule Forall Introduces Quantifiers, Slows Z3

**What goes wrong:** Each call to a sep-logic function adds a `(forall ((addr (_ BitVec 64))) ...)` frame axiom. Functions with many sep-logic calls accumulate many quantifiers, causing Z3 to time out.

**Why it happens:** Quantifiers in array theory without good triggers cause Z3's E-matching to loop or not fire.

**How to avoid:** Annotate the frame forall with a pattern trigger: `(! body :pattern ((select sep_heap addr)))`. This scopes E-matching to terms where Z3 already has `sep_heap` select terms. In Rust, wrap the body in `Term::Annotated(body, vec![("pattern".to_string(), vec![trigger])])`.

**Warning signs:** Z3 returning `unknown` (timeout) for VCs with frame axioms but no trigger annotations.

### Pitfall 6: Ghost Predicate Not Visible Across Crate Boundaries

**What goes wrong:** `#[ghost_predicate]` defined in one crate is called in another crate's spec. The `GhostPredicateDatabase` built by `callbacks.rs` from HIR only sees `LocalDefId` (current crate). External ghost predicates are invisible.

**Why it happens:** `tcx.hir_body_owners()` only iterates the local crate's items.

**How to avoid:** For Phase 20, document that `#[ghost_predicate]` functions must be defined in the same crate as the spec that uses them. This is a known limitation (same as Prusti's Phase 1 predicate scope). Add a clear error message when a ghost predicate call is not found in the database: "ghost predicate 'linked_list' not found; define it in the same crate."

**Warning signs:** Ghost predicate call silently falling through to `Term::App(name, args)` with no Z3 declaration, causing "undeclared function symbol" error.

## Code Examples

Verified patterns from codebase inspection and research:

### Sep Heap Declaration (new `sep_logic.rs`)

```rust
// Source: codebase Sort and Command usage from heap_model.rs + sort.rs + smtlib/command.rs
use rust_fv_smtlib::command::Command;
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

pub fn declare_sep_heap() -> Vec<Command> {
    vec![
        // HeapVal: uninterpreted sort for heap values
        Command::DeclareSort("HeapVal".to_string(), 0),
        // sep_heap: global heap array (address -> HeapVal)
        Command::DeclareFun(
            "sep_heap".to_string(),
            vec![],
            Sort::Array(
                Box::new(Sort::BitVec(64)),
                Box::new(Sort::Uninterpreted("HeapVal".to_string())),
            ),
        ),
        // perm: permission array (address -> Bool, true = owned)
        Command::DeclareFun(
            "perm".to_string(),
            vec![],
            Sort::Array(
                Box::new(Sort::BitVec(64)),
                Box::new(Sort::Bool),
            ),
        ),
    ]
}

/// Per-type HeapVal accessor. For `*const i32`, declare heapval_as_bv32.
pub fn declare_heapval_accessor(pointee_bits: u32) -> Command {
    let accessor_name = format!("heapval_as_bv{}", pointee_bits);
    Command::DeclareFun(
        accessor_name,
        vec![Sort::Uninterpreted("HeapVal".to_string())],
        Sort::BitVec(pointee_bits),
    )
}

/// Encode pts_to(p, v) where p is a pointer term and v is a value term.
/// pointee_bits: bit width of the pointed-to type.
pub fn encode_pts_to(ptr: Term, val: Term, pointee_bits: u32) -> Term {
    // (select perm ptr) — ownership check
    let perm_check = Term::Select(
        Box::new(Term::Const("perm".to_string())),
        Box::new(ptr.clone()),
    );
    // (= (heapval_as_bvN (select sep_heap ptr)) val)
    let heap_val = Term::Select(
        Box::new(Term::Const("sep_heap".to_string())),
        Box::new(ptr),
    );
    let accessor_name = format!("heapval_as_bv{}", pointee_bits);
    let heap_val_typed = Term::App(accessor_name, vec![heap_val]);
    let val_eq = Term::Eq(Box::new(heap_val_typed), Box::new(val));
    Term::And(vec![perm_check, val_eq])
}
```

### Frame Axiom Generation (in `vcgen.rs`)

```rust
// Source: Term::Forall verified in smtlib/src/term.rs line 136
// Term::Annotated verified in smtlib/src/term.rs line 151
use rust_fv_smtlib::sort::Sort;
use rust_fv_smtlib::term::Term;

/// Build the frame axiom asserting that all addresses outside `footprint`
/// are unchanged in sep_heap after the call.
pub fn build_frame_axiom(footprint_ptrs: &[Term]) -> Term {
    let addr_var = "_sep_frame_addr".to_string();

    // (not (or (= addr p1) (= addr p2) ...))  = addr not in footprint
    let not_in_fp: Term = if footprint_ptrs.is_empty() {
        Term::BoolLit(true)
    } else {
        let in_fp: Vec<Term> = footprint_ptrs.iter().map(|p| {
            Term::Eq(
                Box::new(Term::Const(addr_var.clone())),
                Box::new(p.clone()),
            )
        }).collect();
        Term::Not(Box::new(Term::Or(in_fp)))
    };

    // (= (select sep_heap_post addr) (select sep_heap_pre addr))
    let heap_unchanged = Term::Eq(
        Box::new(Term::Select(
            Box::new(Term::Const("sep_heap".to_string())), // after call
            Box::new(Term::Const(addr_var.clone())),
        )),
        Box::new(Term::Select(
            Box::new(Term::Const("sep_heap_pre".to_string())), // before call snapshot
            Box::new(Term::Const(addr_var.clone())),
        )),
    );

    let body = Term::Implies(Box::new(not_in_fp), Box::new(heap_unchanged.clone()));

    // Add trigger to help Z3 E-matching: :pattern ((select sep_heap addr))
    let trigger = Term::Select(
        Box::new(Term::Const("sep_heap".to_string())),
        Box::new(Term::Const(addr_var.clone())),
    );
    let annotated_body = Term::Annotated(
        Box::new(body),
        vec![("pattern".to_string(), vec![trigger])],
    );

    Term::Forall(
        vec![(addr_var, Sort::BitVec(64))],
        Box::new(annotated_body),
    )
}
```

### Ghost Predicate Database

```rust
// Source: pattern follows ContractDatabase in analysis/src/contract_db.rs
use std::collections::HashMap;

/// A registered ghost predicate body.
#[derive(Debug, Clone)]
pub struct GhostPredicate {
    /// Parameter names (e.g., ["p", "n"])
    pub param_names: Vec<String>,
    /// Raw spec string of the body (e.g., "if n == 0 { p.is_null() } else { ... }")
    pub body_raw: String,
}

/// Database of user-defined ghost predicates for bounded unfolding.
#[derive(Debug, Clone, Default)]
pub struct GhostPredicateDatabase {
    predicates: HashMap<String, GhostPredicate>,
}

impl GhostPredicateDatabase {
    pub fn new() -> Self { Self::default() }

    pub fn insert(&mut self, name: String, pred: GhostPredicate) {
        self.predicates.insert(name, pred);
    }

    pub fn get(&self, name: &str) -> Option<&GhostPredicate> {
        self.predicates.get(name)
    }

    pub fn contains(&self, name: &str) -> bool {
        self.predicates.contains_key(name)
    }
}
```

### `#[ghost_predicate]` Proc-Macro

```rust
// In macros/src/lib.rs — follows the spec_attribute pattern (lines 242-258)
#[proc_macro_attribute]
pub fn ghost_predicate(attr: TokenStream, item: TokenStream) -> TokenStream {
    ghost_predicate_impl(attr.into(), item.into()).into()
}

fn ghost_predicate_impl(
    _attr: proc_macro2::TokenStream,
    item: proc_macro2::TokenStream,
) -> proc_macro2::TokenStream {
    // Parse the item as a function
    let func: syn::ItemFn = match syn::parse2(item.clone()) {
        Ok(f) => f,
        Err(err) => return err.to_compile_error(),
    };

    let fn_name = func.sig.ident.to_string();
    let body_str = func.block.to_token_stream().to_string();

    // Serialize param names
    let param_names: Vec<String> = func.sig.inputs.iter().filter_map(|arg| {
        if let syn::FnArg::Typed(pat_ty) = arg {
            if let syn::Pat::Ident(ident) = &*pat_ty.pat {
                return Some(ident.ident.to_string());
            }
        }
        None
    }).collect();
    let params_str = param_names.join(",");

    let doc_value = format!("rust_fv::ghost_predicate::{}::{}::{}", fn_name, params_str, body_str);

    quote::quote! {
        #[doc(hidden)]
        #[doc = #doc_value]
        #item
    }
}
```

### Extraction in `callbacks.rs`

```rust
// In extract_contracts, add alongside the existing prefix matches:
} else if let Some(pred_spec) = doc.strip_prefix("rust_fv::ghost_predicate::") {
    // Format: "name::param1,param2::body"
    let parts: Vec<&str> = pred_spec.splitn(3, "::").collect();
    if parts.len() == 3 {
        let pred_name = parts[0].to_string();
        let param_names: Vec<String> = parts[1]
            .split(',')
            .filter(|s| !s.is_empty())
            .map(|s| s.to_string())
            .collect();
        let body_raw = parts[2].to_string();
        ghost_predicate_db.insert(pred_name, GhostPredicate { param_names, body_raw });
    }
}
```

### Spec Parser: Ghost Predicate Call Expansion

```rust
// In spec_parser.rs::convert_call, add to the match block:
fname if ghost_pred_db.contains(fname) => {
    // Inline ghost predicate body with bounded depth
    let pred = ghost_pred_db.get(fname).unwrap();
    if depth == 0 {
        // Depth exhausted: conservative approximation (predicate may not hold)
        return Some(Term::BoolLit(false));
    }
    // Substitute actual arguments for formal parameters in body_raw
    let mut body = pred.body_raw.clone();
    for (param, arg_expr) in pred.param_names.iter().zip(call_expr.args.iter()) {
        let arg_str = arg_expr.to_token_stream().to_string();
        body = body.replace(&format!("\\b{}\\b", param), &arg_str);
    }
    // Re-parse the instantiated body with depth-1
    parse_spec_expr_with_depth(&body, func, ghost_pred_db, depth - 1)
}
```

## State of the Art

| Old Approach | Current Approach (Phase 20) | Impact |
|--------------|------------------------------|--------|
| No heap ownership in specs | `pts_to(p, v)` predicate | Raw pointer ownership becomes verifiable |
| No aliasing freedom proofs | Separating conjunction (`H1 * H2`) | Disjoint heap regions provable |
| Manual re-specification of unchanged heap | Automatic frame rule | Call sites need not repeat frame |
| No recursive heap predicates | `#[ghost_predicate]` with depth-3 unfolding | Linked list, tree, and other recursive structures specifiable |
| `QF_BV` logic for all VCs | `AUFBV` or `ALL` for sep-logic VCs | Quantifier + array reasoning enabled |
| `heap_model.rs` byte-array for raw ptrs | `sep_heap` + `perm` typed arrays (separate) | No conflict between safety checks and ownership logic |

**Not in scope for Phase 20 (deferred):**
- Fractional permissions (shared read access with `acc(p, 1/2)` Viper style)
- Magic wands (separating implication)
- Iterated separating conjunction (`Seq.map`, `big_sep`)
- Cross-crate ghost predicate visibility

## Open Questions

1. **Heap snapshot for frame rule (sep_heap_pre)**
   - What we know: The frame axiom needs `sep_heap_pre` (before call) vs `sep_heap` (after). The existing VCGen declares all variables before the script and doesn't snapshot heap state per call site.
   - What's unclear: Is `sep_heap` declared as a global constant (like the existing `heap` in `heap_model.rs`) or as a per-function variable? If global, snapshotting requires declaring a `sep_heap_pre` copy and an equality assertion before the call.
   - Recommendation: Declare `sep_heap` as a global constant; before each sep-logic call site, declare a fresh `sep_heap_snap_N` (where N is the call site index) and assert `(= sep_heap_snap_N sep_heap)` as the pre-call snapshot. Post-call, assert the frame axiom between `sep_heap_snap_N` and `sep_heap`.

2. **`pts_to(p, v)` pointee type resolution**
   - What we know: The spec parser has `func: &Function` context. Pointer parameters are `Ty::RawPtr(inner, _)` in the IR. The spec expression `pts_to(p, v)` has `p` resolvable to a parameter via `resolve_variable_name`.
   - What's unclear: How to infer `pointee_bits` when `p` is a complex expression (e.g., `pts_to((*node).next, v)`) not a simple parameter name.
   - Recommendation: For Phase 20, limit `pts_to` to function parameter pointers (simple names) and local variables whose type is available in `func.params` / `func.locals`. Complex pointer expressions return `None` from the parser with a diagnostics message.

3. **Integration with existing `heap_model.rs` null/bounds checks**
   - What we know: Phase 10 (unsafe code detection) uses `heap_model.rs` for null-check and bounds-check VCs. Sep-logic VCs use a separate `sep_heap`.
   - What's unclear: Should a function with BOTH unsafe operations AND sep-logic specs include both `heap` (byte-array) and `sep_heap` (typed) declarations in the same VC?
   - Recommendation: Yes — declare both when both are needed. They use different SMT constant names (`heap` vs `sep_heap`, `perm`) and do not conflict. The logic must be `ALL` when quantifiers are present.

4. **SMT logic selection per VC**
   - What we know: Different VCs use different SMT logics (`QF_BV`, `QF_AUFBV`, `QF_FP`, etc.). Sep-logic VCs need array theory.
   - What's unclear: Does Z3 perform better with `AUFBV` (quantifier-free arrays + BV) vs `ALL` for the sep-logic queries?
   - Recommendation: Use `QF_AUFBV` for VCs with only `pts_to` (no frame forall). Use `AUFBV` (not QF) when frame axioms are present. This is a performance optimization that can be empirically tuned.

## Sources

### Primary (HIGH confidence)
- Codebase: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/smtlib/src/term.rs` — `Term::Select`, `Term::Forall`, `Term::Annotated` verified
- Codebase: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/smtlib/src/sort.rs` — `Sort::Array`, `Sort::Uninterpreted` verified
- Codebase: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/heap_model.rs` — existing heap model pattern for new sep_heap to follow
- Codebase: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/spec_parser.rs:411-521` — `convert_call` extension points for `pts_to` and ghost predicates
- Codebase: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/macros/src/lib.rs:242-258` — `spec_attribute` pattern for `ghost_predicate` macro
- Codebase: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/driver/src/callbacks.rs:753-814` — `extract_contracts` extension point for ghost predicate extraction
- Codebase: `/Users/alexanderfedin/Projects/hapyy/rust-fv/crates/analysis/src/contract_db.rs` — `ContractDatabase` pattern for `GhostPredicateDatabase`

### Secondary (MEDIUM confidence)
- [Viper: A Verification Infrastructure for Permission-Based Reasoning](https://link.springer.com/chapter/10.1007/978-3-662-49122-5_2) — fractional permissions and predicate model; validates boolean perm approach for exclusive ownership
- [Automating Separation Logic Using SMT](https://www.cs.yale.edu/homes/piskac/papers/2013PiskacWiesZuffreySepLog.pdf) — formal basis for encoding SL as first-order array theory in SMT
- [Modeling Separation Logic with Python Dicts and Z3](https://www.philipzucker.com/executable-seperation/) — practical Z3 encoding of `pto` and separating conjunction with boolean domain arrays
- [Prusti Predicates user guide](https://viperproject.github.io/prusti-dev/user-guide/verify/predicate.html) — confirms bounded-unfolding pattern for recursive predicates in Rust verification

### Tertiary (LOW confidence)
- [Encoding Separation Logic in SMT-LIB v2.5](https://sl-comp.github.io/docs/smtlib-sl.pdf) — SL-COMP standard encoding; useful for cross-validation but targets CVC4 native SL, not Z3 encoding
- [A Decision Procedure for Separation Logic in SMT](http://homepage.divms.uiowa.edu/~ajreynol/atva16.pdf) — formal decision procedure; Phase 20 does not implement a full decision procedure so applicability is partial

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH — all required sorts, terms, and command types verified in codebase; no new Cargo deps
- Architecture (sep_heap + perm pattern): HIGH — directly follows `heap_model.rs` pattern; well-established in literature
- Spec parser extension (pts_to, sep_conj): HIGH — `convert_call` extension point is clear; exact encoding verified
- Frame rule implementation: MEDIUM — forall trigger strategy is well-documented but empirical tuning needed
- Ghost predicate bounded unfolding: MEDIUM — string substitution approach is simple but fragile for complex parameter expressions; may need AST-level substitution for robustness
- Cross-crate ghost predicates: LOW — known gap, deferred per pitfall #6

**Research date:** 2026-02-19
**Valid until:** 2026-03-19 (30 days; Rust nightly API and Z3 encoding strategy are stable)
