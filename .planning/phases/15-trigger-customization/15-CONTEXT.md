# Phase 15: Trigger Customization - Context

**Gathered:** 2026-02-15
**Status:** Ready for planning

<domain>
## Phase Boundary

Developer can manually hint quantifier instantiation triggers with `#[trigger]` when automatic inference needs guidance, with diagnostics preventing common mistakes. Annotations are **optional hints** to guide the existing auto-inference engine — not a replacement for it. The tool does the heavy lifting; triggers are an escape hatch when auto-inference needs a nudge in the right direction.

</domain>

<decisions>
## Implementation Decisions

### Annotation Syntax
- Multiple trigger hints per quantifier supported (multi-trigger sets)
- Verbose mode (`--verbose`) shows which triggers were auto-inferred per quantifier, so developers can see when hinting might help
- Annotations do NOT modify source code — they influence SMT-LIB generation only

### Diagnostic UX
- Rustc-style error formatting: `error[E0xxx]` with spans, suggestions, and `--explain` codes — consistent with Rust ecosystem
- Self-instantiation detection shows the concrete instantiation loop: `"Trigger f(g(x)) self-instantiates: f(g(x)) -> f(g(g(x))) -> ..."`
- Error messages include what auto-inference would have chosen as a suggested fix: `"Error: trigger x+1 invalid. Auto-inference suggests: f(x) instead"`

### Override Behavior
- Valid developer hints **fully replace** auto-inferred triggers (not merged)
- **All validation failures are errors, not warnings** — developer must fix before verification proceeds
- Contradicting hints (incompatible with quantifier body/inference) are errors
- Suboptimal hints (interpreted symbols like arithmetic) are also errors — strict validation

### Validation Rules
- Validation runs at **SMT generation time** (late stage) — has full type info for accurate checking
- Self-instantiation detection: balanced toward safety and precision (not overly conservative, not overly permissive)
- Reasonable limit on trigger hints per quantifier (prevents misuse/spec problems)
- Interpreted symbol detection: arithmetic, equality in triggers are rejected as errors

### Claude's Discretion
- Exact annotation syntax style (Rust-native attributes vs macro-style — pick what fits Rust idioms)
- Whether to annotate the quantifier itself or sub-expressions in the body
- Whether to suggest trigger candidates when auto-inference fails (in error messages)
- Whether to support `#[no_trigger]` suppression (depends on Z3 MBQI fallback feasibility)
- Whether validation checks trigger relevance to quantifier body terms
- Exact self-instantiation detection algorithm (conservative-precise balance)
- Exact trigger set limit per quantifier (practical Z3 usage guides the number)
- Severity levels for interpreted symbols (warn vs error — user chose error for all)

</decisions>

<specifics>
## Specific Ideas

- "Annotations are optional — our big goal is to replace developer's work with our analysis and SMT inference. The annotations are for the developer to hint our inference in the better direction."
- Philosophy: tool-first, hints-second. The developer should rarely need to write trigger annotations.
- If a developer puts annotations that completely contradict inference, that's an error — developer must correct the code.
- Verbose mode is the window into inference decisions — developers use it to understand when hinting is needed.

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope.

</deferred>

---

*Phase: 15-trigger-customization*
*Context gathered: 2026-02-15*
