# Phase 16: VSCode Extension - Context

**Gathered:** 2026-02-16
**Status:** Ready for planning

<domain>
## Phase Boundary

Developer receives real-time verification feedback in VSCode with inline diagnostics, status indicators, and detailed error reporting. Runs cargo verify on save and presents results as native VSCode diagnostics. rust-analyzer integration is a separate phase (17).

</domain>

<decisions>
## Implementation Decisions

### Diagnostic Presentation
- Verification failures appear as **Error severity** (red squiggles) — same level as rustc errors
- Hover tooltip shows **failure message + counterexample values** inline (e.g., "Postcondition may not hold: ensures(result > 0), counterexample: x = 42, y = -1")
- Primary diagnostic on the **contract annotation** (#[ensures], #[requires]), with **related information** pointing to the specific code path causing the violation
- **Verified functions get green checkmark** gutter indicators — positive reinforcement that specs hold

### Verification Triggering
- Runs **on save** — consistent with rust-analyzer's check-on-save pattern
- If verification is running and user saves again: **cancel current run and restart** with latest changes
- Background vs fresh spawn: Claude's discretion
- Whole crate vs changed file: Claude's discretion (incremental cache should make whole-crate fast)

### Output & Detail Levels
- Output panel shows **structured failure report** by default (function name, failed condition, counterexample, source location), with **toggle to see raw cargo verify output**
- **SMT-LIB access** via "Show SMT-LIB" command in palette — opens in a new editor tab for advanced debugging
- Per-function timing shown **only when slow** (>1s) — highlight performance issues without noise
- Counterexamples formatted as **symbolic + concrete**: e.g., "x = 42 (where x: i32 from line 5)" — adds source context for debugging

### Extension Packaging
- **Bundle Z3** with the extension VSIX — zero-config for users, no separate Z3 install needed
- First launch without cargo-verify: **auto-install prompt** notification with "Install" button
- Published to **both VSCode Marketplace AND .vsix download** — marketplace for discoverability, .vsix for offline/enterprise
- Configuration settings: **standard set** — enable/disable toggle, verification timeout, Z3 path override, verbose mode, auto-verify on save toggle

### Claude's Discretion
- Background process vs fresh spawn per save (pick what works best with incremental cache)
- Whole crate vs changed-file-only verification scope
- Green checkmark gutter icon design and implementation
- Exact structured output format in the panel
- Extension activation events and language server protocol details

</decisions>

<specifics>
## Specific Ideas

- Diagnostic UX should feel like rustc errors — familiar to Rust developers
- Related information pattern (primary on contract, secondary on code path) mirrors how rustc shows "note: required because of..." chains
- Counterexample format inspired by Verus and Dafny debugger output
- Bundled Z3 follows the rust-analyzer pattern of bundling its server binary

</specifics>

<deferred>
## Deferred Ideas

None — discussion stayed within phase scope

</deferred>

---

*Phase: 16-vscode-extension*
*Context gathered: 2026-02-16*
