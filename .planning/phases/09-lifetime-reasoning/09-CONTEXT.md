# Phase 9: Lifetime Reasoning - Context

**Gathered:** 2026-02-12
**Status:** Ready for planning

<domain>
## Phase Boundary

Verify programs with explicit lifetime annotations and non-lexical lifetime (NLL) patterns. Developer can reason about borrow expiry using prophecy variables and get borrow validity VCs automatically. Pin/self-referential patterns are deferred to v0.3+.

</domain>

<decisions>
## Implementation Decisions

### Annotation requirements
- Dual approach: leverage existing Rust lifetime syntax AND support optional new annotations
- Existing Rust syntax (`'a`, `'b`, `where T: 'a`) automatically participates in verification
- New `#[borrow_ensures(x, expr)]` attribute on functions for specifying mutable borrow final values
- `final(*x)` syntax inline within `#[ensures]` for reasoning about mutable reference final state
- Functions with lifetime parameters automatically get borrow validity VCs — no opt-in needed
- Elided lifetimes are resolved (same as rustc) and verified — developer doesn't need to write explicit lifetimes

### Supported lifetime patterns
- Higher-ranked trait bounds (`for<'a>` syntax) included in v0.2
- Full generic lifetime bounds: `T: 'a`, `T: 'static`, and multi-lifetime bounds `T: 'a + 'b`
- Full `'static` lifetime verification — verify that values claimed as `'static` truly have no non-static references
- Pin/self-referential structs deferred to v0.3+ (depends on Phase 10 unsafe maturity)

### Borrow expiry semantics
- Automatic prophecy variable insertion for each mutable reference parameter — developer uses `final(*x)` in specs
- Layer-by-layer tracking for nested borrows (`&mut &mut T`): each indirection level gets its own prophecy variable (`final(*x)` for outer, `final(**x)` for inner)
- Generate explicit conflict VCs when shared (`&T`) and mutable (`&mut T`) borrows have overlapping lifetimes
- Full temporary borrow support — track borrows created in expressions (e.g., `&vec[0]`) with their precise scope

### Failure diagnostics
- Source-level borrow timeline showing full lifecycle: creation, usage, expiry, and conflict point
- Default to concise violation message; `--verbose` or `#[verifier::verbose]` for full lifetime explanation chain (`'a outlives 'b because...`)
- Include actionable fix suggestions (e.g., "consider cloning x before the borrow" or "move this usage before line N")
- Severity levels at Claude's discretion, leaning toward safety and precision (prefer errors over warnings when ambiguous)

### Claude's Discretion
- Specific prophecy variable encoding strategy in Z3
- NLL analysis implementation approach (MIR-based vs custom)
- Exact fix suggestion heuristics
- Severity classification for edge-case lifetime issues
- Temporary borrow tracking implementation details

</decisions>

<specifics>
## Specific Ideas

- Both `#[borrow_ensures]` attribute and `final()` inline syntax — maximum expressiveness for developers
- Layer-by-layer prophecy tracking mirrors Rust's actual reference nesting model
- Conflict VCs go beyond rustc's borrow checker — catch issues through unsafe or complex control flow
- Diagnostic verbosity flag matches existing tooling conventions (brief by default, detailed on request)

</specifics>

<deferred>
## Deferred Ideas

- Pin/self-referential structs — v0.3+ (depends on unsafe code verification maturity from Phase 10)

</deferred>

---

*Phase: 09-lifetime-reasoning*
*Context gathered: 2026-02-12*
