# Phase 34: Cross-Function Pointer Aliasing - Context

**Gathered:** 2026-02-28
**Status:** Ready for planning

<domain>
## Phase Boundary

Users annotate unsafe functions with `#[unsafe_requires(!ptr_a.alias(ptr_b))]` and `cargo verify` enforces that callers do not pass aliasing raw pointer arguments across function call boundaries. The system tracks aliased pointer pairs through call-graph edges so that a callee's non-aliasing precondition is checked at every call site. Creating posts, intra-procedural aliasing, and automatic alias inference are separate phases.

</domain>

<decisions>
## Implementation Decisions

### alias() predicate semantics
- `alias(p, q)` encodes as SMT address equality: `(= p q)` on BitVec 64
- Pointers are already BitVec 64 in encode_sort.rs — no new sort needed
- Catches the canonical aliasing case: same pointer passed in two argument positions
- Allocation-overlap semantics (range checking) is explicitly deferred — too heavyweight for this phase

### Counterexample format
- When an aliasing violation is detected, the counterexample names the specific parameter pair (e.g., "ptr_a and ptr_b alias at call site to `swap_unsafe`")
- Reuse existing solver `model.rs` variable extraction; add a new diagnostic formatter that maps SMT variable names back to source parameter names
- Output format: consistent with existing null-check/bounds-check counterexample style (description string + optional Z3 model assignment)

### Call-graph propagation mechanism
- At each call site where the callee has a `!alias(p, q)` precondition in `#[unsafe_requires]`, inject SMT assertions substituting actual caller argument addresses
- Extend `contract_db.rs` to carry alias preconditions per parameter-pair index (not by name — parameter names may differ at call site)
- The existing call_graph.rs topological ordering is reused; no new graph structure needed
- Alias constraints from `unsafe_contracts.requires` are extracted by `unsafe_analysis.rs` and passed through the existing contract propagation path

### Annotation scope and enforcement
- Alias checking applies ONLY to callees with an explicit `!ptr_a.alias(ptr_b)` in `#[unsafe_requires]`
- Unannotated callees: no alias check generated (consistent with existing contract-only enforcement philosophy)
- Transitive aliasing (A→B→C where aliasing originates 2 hops away): NOT inferred in this phase — that is Phase 36 territory (summary contract inference)
- Intra-procedural alias checking: explicitly out of scope; existing null/bounds VCs are unchanged

### Claude's Discretion
- Exact SMT variable naming convention for alias constraint terms
- Whether alias constraints are a new `VcKind` variant or annotated within `VcKind::MemorySafety`
- Internal representation of alias preconditions in `SpecExpr` (new variant vs. reuse of existing function-call expression node)
- Test file organization within `unsafe_verification.rs` (new section vs. new test module)

</decisions>

<specifics>
## Specific Ideas

- Success criterion 3 says `unsafe_verification.rs` tracks aliasing via call-graph edges — this is the test file (`crates/analysis/tests/unsafe_verification.rs`), not a source module; the implementation lives in `vcgen.rs` + `contract_db.rs`
- Existing intra-procedural null/bounds checks at the referenced lines in vcgen.rs must remain GREEN — regression guard is a hard requirement
- The `sep_logic.rs` footprint pointer tracking exists but is NOT the right anchor for this feature (footprints are about heap ownership regions; aliasing is about address identity)

</specifics>

<code_context>
## Existing Code Insights

### Reusable Assets
- `spec_parser.rs`: Already parses `pts_to(ptr, val)` as a function-call SpecExpr — `alias(p, q)` follows the same pattern; add a new parse arm
- `unsafe_analysis.rs`: `get_unsafe_requires()` already extracts `#[unsafe_requires]` preconditions — alias preconditions come through this path unchanged
- `call_graph.rs`: `CallGraph` + topological ordering already built — reuse for ordering alias VC injection
- `contract_db.rs`: `ContractDb` maps function names to contracts — extend to include alias precondition parameter-index pairs
- `heap_model.rs`: `null_check_assertion()` and `bounds_check_assertion()` are the pattern to follow for a new `alias_check_assertion(p_term, q_term)` helper
- `encode_sort.rs`: `ptr_addr_sort()` returns BitVec 64 — use directly for both pointer terms in the equality assertion
- `model.rs` + `solver.rs`: Existing model extraction for counterexample variable values — reuse without modification

### Established Patterns
- VcKind enum distinguishes verification condition types (MemorySafety, Overflow, etc.) — alias VCs should follow same enum pattern
- Unsafe operation VCs are collected into `Vec<VcInfo>` and filtered by `VcKind` in tests — alias VCs should be filterable the same way
- Integration tests in `unsafe_verification.rs` construct Function IR directly (no rustc needed) — new alias tests follow same pattern

### Integration Points
- `vcgen.rs`: Call-site handling (the `call_sites` field in `CfgPath`/`PathState`) is where alias VC injection happens
- `spec_parser.rs`: New `alias` parse arm connects annotation parsing to alias VC generation
- `contract_db.rs`: Alias precondition storage so call-site VC injection can look up callee requirements

</code_context>

<deferred>
## Deferred Ideas

- Allocation-overlap aliasing semantics (range-based) — too heavyweight; defer to dedicated alias analysis milestone
- `#[alias_group(N)]` annotation for intentional aliasing (ALIAS-03) — explicitly deferred per REQUIREMENTS.md
- Full unsafe block region-based alias analysis (ALIAS-04) — deferred per REQUIREMENTS.md
- Transitive alias propagation (A→B→C) — belongs in Phase 36 (summary contract inference)
- Concurrency + aliasing interaction — covered by v0.4; alias+concurrency deferred

</deferred>

---

*Phase: 34-cross-function-pointer-aliasing*
*Context gathered: 2026-02-28*
