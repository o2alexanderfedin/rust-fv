# Phase 17: rust-analyzer Integration - Context

**Gathered:** 2026-02-16
**Status:** Ready for planning

<domain>
## Phase Boundary

rust-analyzer displays rust-fv diagnostics inline via custom diagnostic source and runs cargo verify on save. This phase extends the existing Phase 16 VSCode extension (single extension) to integrate with rust-analyzer's diagnostic system. No new verification capabilities — just a new delivery channel for existing results.

</domain>

<decisions>
## Implementation Decisions

### Diagnostic presentation
- Distinct visual style from rustc diagnostics — different color/style so users immediately distinguish rust-fv from rustc
- All diagnostics in the same Problems panel, tagged with a distinct diagnostic source (e.g., `rust-fv`)
- Green gutter checkmarks for verified functions (always active, part of the single extension)
- Counterexample details: Claude's discretion on inline tooltip vs output panel link, based on rust-analyzer's diagnostic model

### Verification trigger
- Auto-verify on save by default, with option to switch to manual-only mode
- End-to-end 2-second target from file save to diagnostics appearing (includes Z3 time, relies on Phase 14 incremental cache)
- Verification coordination between standalone and RA modes: Claude's discretion on shared vs independent runs
- Integration point (flycheck vs separate process): Claude's discretion based on rust-analyzer architecture

### Configuration UX
- Settings nested under `rust-analyzer.*` namespace (e.g., `rust-analyzer.rustfv.enable`) — feels native to RA users
- Enabled by default when extension installed — works out of the box
- Per-workspace overrides supported via `.vscode/settings.json` — useful for projects without contracts
- When cargo verify not installed: status bar hint showing "rust-fv: not installed" (non-intrusive but discoverable)

### Coexistence model
- Single extension handles both standalone and rust-analyzer integration (not two separate extensions)
- Both diagnostic channels active when rust-analyzer present, with deduplication to avoid duplicate squiggles
- Output panel (SMT-LIB viewer, structured failures) always available regardless of diagnostic mode
- Gutter checkmarks always work — part of the single extension, not tied to a specific diagnostic channel

### Claude's Discretion
- Integration architecture (flycheck hook vs separate process)
- Counterexample display in RA diagnostics (inline vs linked)
- Verification run coordination when both channels active
- Deduplication strategy for avoiding double diagnostics

</decisions>

<specifics>
## Specific Ideas

- Settings should feel native to rust-analyzer users — same namespace, same patterns
- Status bar hint for missing cargo-verify is non-intrusive, just shows state without prompting
- The 2-second end-to-end target is ambitious — relies heavily on Phase 14 incremental cache being effective

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 17-rust-analyzer-integration*
*Context gathered: 2026-02-16*
