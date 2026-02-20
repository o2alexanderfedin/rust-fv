# Phase 22: Higher-Order Closures - Research

**Researched:** 2026-02-20
**Domain:** Higher-order function closure verification, fn_spec annotation, FnMut SSA environment mutation, Z3 MBQI quantifier encoding
**Confidence:** HIGH (codebase gap analysis), HIGH (existing closure infrastructure), MEDIUM (FnMut SSA env encoding strategy)

<user_constraints>
## User Constraints (from CONTEXT.md)

### Locked Decisions

- Closure argument referenced by name: `fn_spec(f, |x| pre => post)`
- Multiple closures: `fn_spec(f => |x| ..., g => |y| ...)`
- Pre/postcondition delimiter: `|x| pre => post` (roadmap reference form)
- Placement of `fn_spec`: follow existing spec annotation convention (read codebase — proc macro via `#[doc(hidden)]` doc attribute encoding)
- SSA environment snapshots named: `env_before` / `env_after` (not numeric indices)
- All captured variables included in the environment snapshot
- Loop calls: inference-based loop invariant inference preferred over manual annotation
- Unprovable FnMut postconditions: follow existing pattern for unproven obligations
- Error primary location: call site (where closure is passed to HOF)
- Secondary note: points to specific fn_spec clause that failed
- Counterexamples: always show when available (extract concrete values from Z3 model)
- FnMut errors: show full `env_before` and `env_after` side-by-side
- All three traits in scope: `Fn`, `FnMut`, `FnOnce`
- Generic closure bounds: monomorphize at each call site (each concrete closure generates its own VC)
- FnOnce encoding: single-call VC with no repeated env tracking (preferred for soundness)
- Trait coercion (FnMut passed where Fn expected): follow Rust semantics and soundness requirements

### Claude's Discretion

- Exact `fn_spec` syntax form (name vs positional, delimiter style)
- FnOnce encoding details
- Trait coercion handling
- Loop invariant inference depth/strategy
- Exact `fn_spec` placement convention (determined by reading existing codebase)

### Deferred Ideas (OUT OF SCOPE)

None — discussion stayed within phase scope.
</user_constraints>

<phase_requirements>
## Phase Requirements

| ID | Description | Research Support |
|----|-------------|-----------------|
| HOF-01 | User can write `fn_spec(f, \|x\| pre => post)` specification entailments to verify that a closure `f` satisfies given pre/postconditions | New `#[fn_spec(...)]` proc macro in `macros/src/lib.rs` encoding as `rust_fv::fn_spec::PARAM::PRE::POST` doc attribute; driver `extract_contracts` extended to parse it; IR `Contracts` extended with `fn_specs: Vec<FnSpec>`; VCGen generates `ClosureContract` VCs using MBQI quantifiers in `AUFLIA` logic |
| HOF-02 | Stateful closures (`FnMut`) track environment mutation across calls via SSA-versioned environment (`env_v0 → env_v1`) | `ClosureInfo.env_fields` already captures env; FnMut path in VCGen must declare `env_before`/`env_after` SMT constants, assert mutation axiom (`env_after = update(env_before, delta)`), then check fn_spec postcondition referencing `env_after`; counterexample renderer shows both snapshots side-by-side |
</phase_requirements>

## Summary

Phase 22 implements higher-order function verification: the ability to write `#[fn_spec(f, |x| pre => post)]` on a function that takes a closure `f`, and have the verifier prove that `f` satisfies the stated entailment at every call site. The infrastructure required spans four layers: (1) a new `fn_spec` proc macro, (2) driver extraction of the annotation, (3) IR representation of closure specs in `Contracts`, and (4) VCGen logic that generates `ClosureContract` VCs.

The codebase already has substantial closure infrastructure: `ClosureInfo`, `ClosureTrait`, `defunctionalize.rs`, `closure_analysis.rs`, and the `ClosureContract` `VcKind` variant. What is missing is the `fn_spec` annotation itself, the IR field to hold it, and the VCGen path that encodes the entailment query as an SMT assertion. The annotation is an entailment `∀x. pre(x) => post(f(x))` checked by Z3 using MBQI (Model-Based Quantifier Instantiation) for the quantified form — consistent with the STATE.md decision "Z3 MBQI preferred for HOF spec entailment queries (heavy universal quantification)".

For `FnMut` closures (HOF-02), each call mutates the captured environment. The encoding uses two SMT constants `env_before` and `env_after` per captured variable, linked by an update axiom derived from the closure's body semantics (or left as an uninterpreted axiom when the body is not visible). The postcondition then references `env_after` values. This is the semantic `env_v0 → env_v1` pattern from the roadmap, renamed to the user-decision names `env_before`/`env_after`.

**Primary recommendation:** Add `fn_spec` proc macro encoding as `rust_fv::fn_spec::PARAM::PRE::POST`; add `FnSpec` struct and `fn_specs: Vec<FnSpec>` to `Contracts` in `ir.rs`; extend `extract_contracts` in `callbacks.rs`; extend `spec_parser.rs` with `parse_fn_spec_clause`; add VCGen function `generate_fn_spec_vcs()` that emits `ClosureContract` VCs using `Term::Forall` with MBQI; add FnMut env mutation path with `env_before`/`env_after` constants.

## Standard Stack

### Core

| Library | Version | Purpose | Why Standard |
|---------|---------|---------|--------------|
| rust_fv_smtlib | existing | `Term::Forall`, `Term::Implies`, `Sort::Int`/`Bool`/`BitVec` for entailment VC encoding | Already the SMT backend; `Term::Forall` with bound vars already exists (used in quantifier encoding) |
| rust_fv_analysis::ir | existing | `ClosureInfo`, `ClosureTrait`, `Contracts`, `Function` | `ClosureInfo` captures env_fields/params/return_ty/trait_kind — all needed for fn_spec VC |
| rust_fv_analysis::vcgen | existing | `VcKind::ClosureContract`, `generate_vcs()`, `FunctionVCs` | `ClosureContract` variant already declared; `generate_vcs()` is the extension point |
| rust_fv_analysis::defunctionalize | existing | `defunctionalize_closure_call()`, `encode_closure_as_uninterpreted()` | Uninterpreted function declaration for closure parameter already implemented |
| rust_fv_analysis::spec_parser | existing | `parse_spec_expr()`, `parse_spec_expr_with_db()` | Used to parse `pre` and `post` expressions from `fn_spec` annotation |
| rust_fv_macros | existing | proc macro infrastructure for `#[doc(hidden)]` encoding | All other spec attributes use this pattern; `fn_spec` follows same encoding |

### Supporting

| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| `Sort::Int` (smtlib) | existing | Environment snapshot version numbering for FnMut | Declare `env_before_x: Sort` and `env_after_x: Sort` per captured variable x |
| `Term::App` (smtlib) | existing | Encode closure application `f_impl(env, arg)` in VC body | Defunctionalized closure call encoding |
| `encode_quantifier::infer_triggers` | existing | Auto-infer Z3 MBQI triggers for fn_spec VC | Reuse existing trigger inference on closure application term |
| Z3 MBQI / `AUFLIA` logic | existing (Z3 capability) | Handles universally-quantified entailment VCs | MBQI mode handles `(forall (x Sort) ...)` with function application triggers |

### Alternatives Considered

| Instead of | Could Use | Tradeoff |
|------------|-----------|----------|
| `Term::Forall` with MBQI triggers | Concrete instantiation at each literal call | Universal quantifier is required for the entailment to hold for all inputs, not just observed ones; MBQI handles this without manual instantiation |
| `env_before`/`env_after` SMT constants per var | A single SMT datatype `ClosureEnv` with version | Per-variable constants are simpler to encode and easier to extract counterexample values from; avoid new datatype machinery |
| Uninterpreted closure body | Full body encoding from IR | HOF spec checking is about the interface spec, not body — uninterpreted body with axiom from fn_spec is both simpler and more general |

**No new Cargo dependencies required.** All SMT encoding primitives already exist in the smtlib crate. Z3's MBQI is invoked automatically when `(set-logic AUFLIA)` or `(set-option :smt.mbqi true)` is used.

## Architecture Patterns

### Recommended File Structure

```
crates/
├── macros/src/lib.rs            # Add fn_spec proc macro and fn_spec_impl()
├── analysis/src/
│   ├── ir.rs                    # Add FnSpec struct, fn_specs field to Contracts
│   ├── spec_parser.rs           # Add parse_fn_spec_clause() for |x| pre => post
│   ├── hof_vcgen.rs             # NEW: generate_fn_spec_vcs(), FnMut env encoding
│   └── vcgen.rs                 # Call generate_fn_spec_vcs() from generate_vcs()
└── driver/src/
    └── callbacks.rs             # Extend extract_contracts() to parse fn_spec attrs
```

### Pattern 1: fn_spec Proc Macro Encoding

**What:** `#[fn_spec(f, |x| pre => post)]` encodes as a hidden doc attribute following the exact pattern of `borrow_ensures` (multi-argument attribute with syn parser).
**When to use:** Whenever a function takes a closure parameter and the developer wants to specify what pre/postconditions that closure must satisfy.
**Example:**

```rust
// In macros/src/lib.rs — mirrors borrow_ensures_impl pattern

// User writes:
#[fn_spec(f, |x: i32| x > 0 => result > 0)]
fn apply(f: impl Fn(i32) -> i32, val: i32) -> i32 { f(val) }

// Macro emits:
// #[doc(hidden)]
// #[doc = "rust_fv::fn_spec::f::|x : i32| x > 0 => result > 0"]
// fn apply(f: impl Fn(i32) -> i32, val: i32) -> i32 { f(val) }

// Encoding format: "rust_fv::fn_spec::PARAM_NAME::CLAUSE"
// where CLAUSE is the full "|x| pre => post" token stream as string
```

### Pattern 2: IR Representation of fn_spec

**What:** A new `FnSpec` struct and `fn_specs: Vec<FnSpec>` field in `Contracts` represent parsed fn_spec clauses after extraction from HIR.
**Example:**

```rust
// In ir.rs

/// A higher-order function specification clause.
/// Represents: `fn_spec(f, |x| pre => post)`
#[derive(Debug, Clone)]
pub struct FnSpec {
    /// The closure parameter name (e.g., "f")
    pub closure_param: String,
    /// Bound variable names for the entailment (e.g., ["x"])
    pub bound_vars: Vec<(String, Ty)>,  // (name, type) pairs
    /// Pre-condition expression string (e.g., "x > 0")
    pub pre: SpecExpr,
    /// Post-condition expression string (e.g., "result > 0")
    pub post: SpecExpr,
}

// Contracts extended:
pub struct Contracts {
    pub requires: Vec<SpecExpr>,
    pub ensures: Vec<SpecExpr>,
    pub invariants: Vec<SpecExpr>,
    pub is_pure: bool,
    pub decreases: Option<SpecExpr>,
    /// HOF closure specification entailments (fn_spec clauses)
    pub fn_specs: Vec<FnSpec>,  // NEW
}
```

### Pattern 3: VCGen — fn_spec Entailment VC

**What:** For each `FnSpec` in `Contracts`, generate a `ClosureContract` VC that asserts `∀x. pre(x) => post(f_impl(env, x))`. This uses `Term::Forall` with the closure's uninterpreted function.
**When to use:** At the HOF function itself, not at call sites — the entailment is a property of the function's contract, proved once.
**Example:**

```rust
// In hof_vcgen.rs

// For fn_spec(f, |x: i32| x > 0 => result > 0) on apply(f, val):
//
// SMT encoding (logic AUFLIA):
// (declare-sort ClosureEnv_f 0)
// (declare-fun f_impl (ClosureEnv_f Int) Int)   ; uninterpreted body
// (declare-const env_f ClosureEnv_f)
//
// Entailment VC:
// (assert (not (forall ((x Int))
//   (=> (> x 0)
//       (> (f_impl env_f x) 0)))))
// (check-sat)  ; UNSAT = entailment holds (verified)

// For FnMut: additionally declare env_before/env_after:
// (declare-const f_env_before_count Int)
// (declare-const f_env_after_count Int)
// ; env mutation axiom (uninterpreted unless body visible):
// (declare-fun f_mut_impl (Int Int) Int)  ; (env_before, arg) -> env_after
```

### Pattern 4: FnMut Environment Mutation Encoding

**What:** For `FnMut` closures, each call transitions `env_before → env_after`. Captured variables appear as `env_before_VARNAME` and `env_after_VARNAME` SMT constants. The postcondition may reference `env_after_VARNAME`.
**When to use:** When `ClosureTrait::FnMut` is detected for a fn_spec closure.
**Example:**

```rust
// FnMut closure: let mut count = 0; let inc = |x: i32| { count += x; count };
//
// fn_spec(inc, |x: i32| x > 0 => result == env_before_count + x)
//
// SMT encoding:
// (declare-const env_before_count Int)
// (declare-const env_after_count Int)
// (declare-fun inc_impl (Int Int) Int)  ; (env_before_count, x) -> result
// ; Mutation constraint from postcondition:
// (assert (forall ((x Int))
//   (=> (> x 0)
//       (= (inc_impl env_before_count x) (+ env_before_count x)))))
// ; Counterexample on failure shows env_before_count and env_after_count
```

### Pattern 5: Call Site Monomorphization

**What:** For generic HOF parameters (`impl Fn(i32) -> i32` or `F: Fn(i32) -> i32`), each concrete closure passed at a call site generates its own VC. This is the monomorphization-at-call-site decision.
**When to use:** When the HOF is called with a concrete closure argument.

### Pattern 6: FnOnce Single-Call VC

**What:** FnOnce closures generate a single-call entailment VC (no `env_before`/`env_after` looping). The existing `validate_fnonce_single_call` already detects double-calls. The fn_spec VC simply checks the one call satisfies pre=>post.

### Pattern 7: doc attribute extraction in callbacks.rs

**What:** Extend `extract_contracts` to parse `rust_fv::fn_spec::PARAM::CLAUSE` doc attributes. Parse the clause `|x| pre => post` using syn to split at `=>` delimiter.
**Example:**

```rust
// In callbacks.rs extract_contracts():
} else if let Some(spec) = doc.strip_prefix("rust_fv::fn_spec::") {
    // Format: "PARAM_NAME::CLAUSE"
    if let Some((param, clause)) = spec.split_once("::") {
        contracts.fn_specs.push((param.to_string(), clause.to_string()));
    }
}
```

### Anti-Patterns to Avoid

- **Quantifying over closure bodies:** Do not attempt to quantify over all possible closure implementations. The fn_spec only constrains the specific closure passed — use uninterpreted functions, not universally quantified functions.
- **Encoding fn_spec at call sites only:** The entailment VC belongs on the HOF function. Call-site checking is separate (verify the concrete closure satisfies the spec at the call).
- **Using QF_BV logic for fn_spec VCs:** MBQI universally quantified VCs require `AUFLIA` or `ALL` logic. QF_BV is quantifier-free — would silently fail or reject the quantifier.
- **Eager env snapshot materialization:** For FnMut loops, do not materialize `env_before_0`, `env_before_1`, etc. for each iteration. Use loop invariant inference (bounded unrolling depth like ghost_predicate depth-3 pattern).
- **Numeric indexing for env snapshots:** User decision locks names to `env_before_VARNAME`/`env_after_VARNAME`. Never emit `env_v0`, `env_v1` in output.

## Don't Hand-Roll

| Problem | Don't Build | Use Instead | Why |
|---------|-------------|-------------|-----|
| Closure uninterpreted function | Custom closure encoding | `encode_closure_as_uninterpreted()` in `defunctionalize.rs` | Already implemented and tested; generates `(declare-fun f_impl ...)` correctly |
| Clause parsing `\|x\| pre => post` | Custom string split | `syn::parse_str` + split at `=>` between two `Expr` groups | The `=>` operator parses as `syn::BinOp::Ge` composed — use token-level split at `=>` fat arrow |
| MBQI trigger construction | Ad-hoc trigger strings | `encode_quantifier::infer_triggers()` | Already implemented trigger inference; reuse with closure application term as trigger |
| Multiple fn_spec in one annotation | Separate annotation per closure | `fn_spec(f => |x| ..., g => |y| ...)` via vec of clauses | Multiple closures are common in HOFs like `map_reduce`; single macro call is ergonomic |
| FnMut mutation axioms | Manual state machine encoding | Uninterpreted update function + postcondition axiom | Avoids needing to symbolically execute the closure body; unsoundness risk is minimized |

**Key insight:** The defunctionalization infrastructure in `defunctionalize.rs` is the right foundation. Do not re-implement closure-to-SMT encoding — extend it with fn_spec postcondition axioms.

## Common Pitfalls

### Pitfall 1: Wrong SMT Logic for Quantified fn_spec VCs

**What goes wrong:** Using `QF_BV` (set via existing `vcgen.rs` default) for fn_spec VCs causes Z3 to reject or silently ignore the `(forall ...)` quantifier.
**Why it happens:** `QF_` prefix means "quantifier-free". The fn_spec entailment is inherently universal (`∀x. pre(x) => post(f(x))`).
**How to avoid:** fn_spec VCs must use `(set-logic AUFLIA)` (arrays + uninterpreted functions + linear integer arithmetic) or `(set-logic ALL)`. This is consistent with the STATE.md note: "Z3 MBQI preferred for HOF spec entailment queries (heavy universal quantification)".
**Warning signs:** Z3 returns UNKNOWN instead of UNSAT/SAT for fn_spec VCs.

### Pitfall 2: Parsing `|x| pre => post` — `=>` Ambiguity

**What goes wrong:** `=>` is not a Rust operator. If you try `syn::parse_str::<Expr>("|x| pre => post")`, syn will fail or mis-parse because `=>` is the fat arrow used only in match arms.
**Why it happens:** `=>` in spec expressions is a domain-specific extension, not standard Rust syntax.
**How to avoid:** Parse the clause as a token stream and split at the `=>` token (`proc_macro2::TokenTree::Punct` with `=` followed by `>`), then parse left side and right side separately as expressions. Alternatively, accept a tuple form: `(pre, post)` and document `pre => post` as sugar. The existing `borrow_ensures` parser (splitting `param, expr` at comma) is the model.
**Warning signs:** Compile error or None return when parsing fn_spec clause string.

### Pitfall 3: FnMut env_after Not Constrained

**What goes wrong:** Declaring `env_before` and `env_after` but not asserting any relationship between them allows Z3 to assign arbitrary values to `env_after`, making the postcondition trivially satisfiable.
**Why it happens:** Without an axiom relating `env_before` and `env_after`, the VC is underconstrained.
**How to avoid:** For FnMut, the fn_spec postcondition itself provides the constraint: `∀x. pre(x) => post_involving_env_after(f_impl(env_before, x), env_after)`. Additionally, assert that `f_impl` is deterministic w.r.t. env (use a function return that includes env update: `f_impl(env_before, x) = (result, env_after)`). If the VC is purely contractual (no body), leave env_after unconstrained and flag the VC as MEDIUM confidence.
**Warning signs:** fn_spec postconditions referencing `env_after` always verify even when obviously wrong.

### Pitfall 4: FnOnce spec checked multiple times

**What goes wrong:** If FnOnce fn_spec VC is generated per-call rather than per-spec, and the closure is somehow referenced twice, you get duplicate VCs and confusing errors.
**Why it happens:** Existing VCGen traverses all call sites; if fn_spec logic hooks into call site traversal, it fires per call.
**How to avoid:** Generate fn_spec VCs once per `FnSpec` entry in `contracts.fn_specs`, not per call site. Separate the "spec entailment" VC from the "FnOnce double-call" diagnostic VC (which already exists in vcgen.rs).
**Warning signs:** Duplicate VC descriptions in output for the same fn_spec.

### Pitfall 5: Trait Coercion — FnMut as Fn

**What goes wrong:** A closure implementing `FnMut` can be passed where `Fn` is expected (Rust coerces automatically). If fn_spec declares `Fn` semantics but the closure mutates env, the spec may be unsound.
**Why it happens:** Rust's trait hierarchy: `Fn: FnMut: FnOnce`. A `FnMut` closure satisfies `Fn` bounds but also mutates.
**How to avoid:** When trait coercion is detected (FnMut closure passed to Fn HOF), still use `FnMut` encoding in the VC (soundness requirement). The fn_spec at the HOF level says "Fn" but the concrete closure's capability is FnMut — generate the VC using FnMut env tracking to remain sound.
**Warning signs:** fn_spec postconditions that reference `env_after` are not checked when closure is coerced to `Fn`.

### Pitfall 6: Counterexample Extraction for fn_spec Failures

**What goes wrong:** Quantified VCs (`∀x. ...`) are UNSAT when verified. When verification fails (SAT), Z3's model gives a witness `x` satisfying `pre(x) ∧ ¬post(...)`. Extracting this witness requires reading the model's `x` value, not a named Rust variable.
**Why it happens:** The bound variable `x` in the fn_spec is synthetic, not a Rust source variable. Existing counterexample extraction looks up `source_names` HashMap.
**How to avoid:** For fn_spec counterexamples, extract the Z3 model value for the bound variable name(s) (e.g., `x`) and report them as "witness values" in the error message. Add a new path in `cex_render.rs` for `VcKind::ClosureContract` that handles bound-variable witnesses vs. regular variables. FnMut failures additionally show `env_before_*` and `env_after_*` model values side-by-side as required by user decision.
**Warning signs:** Counterexample output shows raw SMT constant names instead of user-readable values.

## Code Examples

Verified patterns from the codebase:

### Existing: borrow_ensures doc format (model for fn_spec)

```rust
// Source: crates/macros/src/lib.rs borrow_ensures_impl()
// Encoding format: "rust_fv::borrow_ensures::PARAM::EXPR"
// fn_spec follows the same pattern:
// Encoding format: "rust_fv::fn_spec::PARAM::CLAUSE"

let doc_value = format!("rust_fv::fn_spec::{}::{}", param_str, clause_str);
quote::quote! {
    #[doc(hidden)]
    #[doc = #doc_value]
    #item
}
```

### Existing: ClosureContract VC generation (extension point)

```rust
// Source: crates/analysis/src/vcgen.rs ~line 395
// Current use: FnOnce double-call diagnostic
// New use: fn_spec entailment VC uses same VcKind
conditions.push(VerificationCondition {
    description: format!("fn_spec({}, |{}| {} => {})", closure_param, bound_var, pre, post),
    script,
    location: VcLocation {
        function: func.name.clone(),
        block: 0,
        statement: 0,
        source_file: None,
        source_line: None,
        source_column: None,
        contract_text: Some(format!("|{}| {} => {}", bound_var, pre, post)),
        vc_kind: VcKind::ClosureContract,
    },
});
```

### Existing: Uninterpreted closure function declaration (reuse)

```rust
// Source: crates/analysis/src/defunctionalize.rs encode_closure_as_uninterpreted()
// Generates: (declare-fun predicate_impl (ClosureEnv Int) Int)
pub fn encode_closure_as_uninterpreted(info: &ClosureInfo) -> Vec<Command> {
    let encoding = defunctionalize_closure_call(info, &[]);
    vec![Command::DeclareFun(
        encoding.defunctionalized_name,
        encoding.param_sorts,
        encoding.return_sort,
    )]
}
```

### New: fn_spec entailment VC (AUFLIA + Forall)

```rust
// In hof_vcgen.rs: generate_fn_spec_vcs()
// For: fn_spec(f, |x: i32| x > 0 => result > 0)
// Emits UNSAT = verified VC:

let mut script = Script::new();
script.push(Command::SetLogic("AUFLIA".to_string()));

// Declare uninterpreted closure function: f_impl(env, x) -> result
script.push(Command::DeclareFun(
    "f_impl".to_string(),
    vec![Sort::Datatype("ClosureEnv_f".to_string()), Sort::Int],
    Sort::Int,
));
script.push(Command::DeclareFun(
    "env_f".to_string(),
    vec![],
    Sort::Datatype("ClosureEnv_f".to_string()),
));

// Assert: NOT (forall x. x > 0 => f_impl(env_f, x) > 0)
// UNSAT = entailment holds
let pre_term = Term::IntGt(Box::new(Term::Const("x".to_string())), Box::new(Term::IntLit(0)));
let post_term = Term::IntGt(
    Box::new(Term::App("f_impl".to_string(), vec![
        Term::Const("env_f".to_string()),
        Term::Const("x".to_string()),
    ])),
    Box::new(Term::IntLit(0)),
);
let entailment = Term::Forall(
    vec![("x".to_string(), Sort::Int)],
    Box::new(Term::Implies(Box::new(pre_term), Box::new(post_term))),
    vec![],  // triggers inferred by infer_triggers()
);
script.push(Command::Assert(Term::Not(Box::new(entailment))));
script.push(Command::CheckSat);
```

### New: FnMut env encoding pattern

```rust
// For FnMut closure with captured `count: i32`:
// fn_spec(inc, |x: i32| x > 0 => result == env_before_count + x)

// Declare env snapshots:
script.push(Command::DeclareFun("env_before_count".to_string(), vec![], Sort::Int));
script.push(Command::DeclareFun("env_after_count".to_string(), vec![], Sort::Int));

// Declare FnMut impl: (env_before_count, x) -> result
script.push(Command::DeclareFun(
    "inc_impl".to_string(),
    vec![Sort::Int, Sort::Int],  // env_before_count, x
    Sort::Int,                   // result
));

// Assert: NOT (forall x. x > 0 => inc_impl(env_before_count, x) == env_before_count + x)
// The postcondition references env_before_count (the state at call time)
```

### Existing: extract_contracts pattern (model for fn_spec extraction)

```rust
// Source: crates/driver/src/callbacks.rs extract_contracts() ~line 775
// Pattern for all existing spec attributes:
for attr in attrs {
    if let Some(doc) = extract_doc_value(attr) {
        if let Some(spec) = doc.strip_prefix("rust_fv::requires::") {
            contracts.requires.push(spec.to_string());
        } else if let Some(spec) = doc.strip_prefix("rust_fv::ensures::") {
            contracts.ensures.push(spec.to_string());
        }
        // NEW: add fn_spec parsing here
        // } else if let Some(spec) = doc.strip_prefix("rust_fv::fn_spec::") {
        //     if let Some((param, clause)) = spec.split_once("::") {
        //         contracts.fn_specs.push((param.to_string(), clause.to_string()));
        //     }
        // }
    }
}
```

## State of the Art

| Old Approach | Current Approach | When Changed | Impact |
|--------------|------------------|--------------|--------|
| Manual closure argument contracts | Specification entailments (`fn_spec`-style) per Prusti/Wolff et al. 2021 | 2021 (OOPSLA) | First-order encoding of higher-order specs; automation via SMT |
| Numeric SSA indices (env_v0, env_v1) | Semantic names (env_before, env_after) | Phase 22 design decision | More readable counterexamples; matches Rust developer expectations |
| Existential quantification for closure choice | Uninterpreted functions + MBQI universal quantification | Z3 best practice circa 2020+ | Uninterpreted functions are efficient for Z3 MBQI; existential quantification over functions is undecidable in general |
| Per-call-site closure checking | Per-spec entailment checking (prove once, use at all call sites) | Prusti approach | Modular: proves the contract holds for the HOF's interface, not each specific call |

**Current approach in the codebase:**
- `defunctionalize.rs`: Defunctionalization already implemented — the HOF VC infrastructure exists
- `VcKind::ClosureContract`: Already declared — fn_spec VCs slot in here
- `ClosureInfo`, `ClosureTrait`: Already fully modeled in `ir.rs`
- `extract_closure_info()`, `detect_closure_calls()`: Already implemented in `closure_analysis.rs`
- **Missing:** `FnSpec` IR struct, fn_spec macro, driver extraction, and VCGen entailment logic

**Deprecated/outdated:**
- Numeric env snapshot naming (`env_v0`, `env_v1`): Never used in codebase; design decision replaced with semantic names before implementation.

## Open Questions

1. **fn_spec clause `=>` parsing in spec_parser.rs**
   - What we know: `=>` is not valid Rust binary operator; syn will reject `|x| pre => post` as a standard Rust expression
   - What's unclear: Best approach to split at `=>` — token-level scan vs. accepting comma syntax vs. separate `#[fn_pre]` and `#[fn_post]` attributes
   - Recommendation: In the proc macro, parse the clause as a raw `TokenStream`, scan for `FatArrow` (`=>`) token to split into pre and post halves, then call `syn::parse2::<Expr>` on each half. Store as `"PRE_STR%%POST_STR"` (double-percent separator) in the doc attribute to allow split in `extract_contracts`. This avoids `::` collisions in the clause content.

2. **Loop invariant inference depth for FnMut in loops**
   - What we know: User wants inference-based approach, not manual annotation; depth-3 ghost predicate pattern is the precedent
   - What's unclear: Whether bounded unrolling (depth 3) is sufficient for common FnMut loop patterns like `Vec::iter().map()` or `for_each`
   - Recommendation: Start with depth-3 unrolling for FnMut-in-loop patterns (consistent with ghost predicate depth). Flag remaining cases as `LOW` confidence VCs requiring manual invariant annotation if inference fails. Document the fallback.

3. **Trait coercion detection**
   - What we know: Rust's closure trait hierarchy means FnMut coerces to Fn; the IR's `ClosureTrait` reflects the declared bound, not the concrete closure capability
   - What's unclear: Whether the MIR converter in `mir_converter.rs` correctly identifies the concrete closure's actual trait vs. the HOF's parameter bound
   - Recommendation: In VCGen, always use the closure's concrete `ClosureTrait` from `ClosureInfo.trait_kind` (not the HOF's parameter bound) to determine which encoding to apply. If `trait_kind == FnMut` but the HOF bound says `Fn`, use FnMut encoding (soundness).

4. **env_after encoding when closure body is opaque**
   - What we know: When the closure is passed as a parameter (body not visible), `env_after` cannot be derived from a body encoding
   - What's unclear: Whether the fn_spec postcondition alone is sufficient to constrain `env_after`, or if we need an axiom saying `f_impl(env_before, x) = (result, env_after)`
   - Recommendation: Use a two-return-value encoding: declare `f_impl` to return only `result`, and separately declare `f_env_update(env_before, x)` returning the env after. The fn_spec postcondition then references `f_env_update(env_before, x)` as the `env_after` value. This keeps env tracking compositional.

## Sources

### Primary (HIGH confidence)

- Codebase analysis: `crates/analysis/src/defunctionalize.rs` — existing defunctionalization infrastructure
- Codebase analysis: `crates/analysis/src/closure_analysis.rs` — existing closure detection
- Codebase analysis: `crates/analysis/src/ir.rs` — `ClosureInfo`, `ClosureTrait`, `Contracts`
- Codebase analysis: `crates/macros/src/lib.rs` — `borrow_ensures_impl` pattern (model for fn_spec macro)
- Codebase analysis: `crates/driver/src/callbacks.rs` — `extract_contracts` doc attribute pattern
- Codebase analysis: `crates/analysis/src/vcgen.rs` — `VcKind::ClosureContract` extension point
- `.planning/STATE.md` — "Z3 MBQI preferred for HOF spec entailment queries"

### Secondary (MEDIUM confidence)

- [Wolff et al. 2021, OOPSLA — "Modular Specification and Verification of Closures in Rust"](https://dl.acm.org/doi/10.1145/3485522) — specification entailment encoding; FnMut first-order reduction
- [Prusti closure user guide](https://viperproject.github.io/prusti-dev/user-guide/verify/closure.html) — closure! macro syntax reference (MEDIUM: prototype status noted in docs)
- [Prusti specification syntax](https://viperproject.github.io/prusti-dev/user-guide/syntax.html) — specification entailment approach (MEDIUM: Viper-based, not identical to this codebase's SMT approach)

### Tertiary (LOW confidence)

- [WebSearch: "Compiling Higher-Order Specifications to SMT Solvers"](https://bentnib.org/hospec-smt.pdf) — general HOF→SMT compilation (LOW: PDF inaccessible, citation only)

## Metadata

**Confidence breakdown:**
- Standard stack: HIGH — all tools identified are already in the codebase; no new dependencies needed
- Architecture: HIGH — macro encoding pattern, IR extension, and VCGen extension all follow established codebase patterns; defunctionalize.rs provides the foundation
- FnMut env encoding: MEDIUM — the env_before/env_after pattern is well-understood but the exact shape of env_after when the body is opaque is an open question (resolved with recommendation above)
- Pitfalls: HIGH — `QF_BV` vs `AUFLIA` logic issue is confirmed by Z3 semantics; `=>` parsing issue is confirmed by syn behavior; others derived from codebase patterns
- fn_spec clause parsing: MEDIUM — the `%%` separator recommendation is a new design choice not yet validated against real macro output; confirm in implementation

**Research date:** 2026-02-20
**Valid until:** 2026-03-22 (30 days; stack is stable Rust + existing codebase)
