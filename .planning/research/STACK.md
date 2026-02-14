# Stack Research

**Domain:** Formal Verification Tooling for Rust
**Researched:** 2026-02-14
**Confidence:** HIGH

## Recommended Stack

### Standard Library Contracts

| Technology | Version | Purpose | Why Recommended |
|------------|---------|---------|-----------------|
| External crate pattern | N/A | Distribute stdlib specifications separately | Proven by Prusti (`prusti-std`) and Verus (`vstd`). Allows versioning specs independently from rust-fv core, users opt-in with `extern crate rust_fv_std;` |
| `serde` for metadata | 1.0 | Serialize contract metadata for distribution | Industry standard for Rust serialization, already in workspace deps. Enables JSON-based contract storage/loading |

**Distribution Strategy:**
- Create `rust-fv-std` crate with `#[extern_spec]`-style contracts for stdlib functions
- Ship as separate optional dependency (follows Prusti model from external specs research)
- Store contracts as combination of proc macro annotations + JSON metadata (serde-serialized)
- Users add `extern crate rust_fv_std;` to import stdlib contracts
- Future: Consider upstream integration via rust-lang compiler-team MCP (see issue #942 for primitive ownership assertions precedent)

### Trigger Customization (Proc Macro)

| Technology | Version | Purpose | Why Recommended |
|------------|---------|---------|-----------------|
| `syn` | 2.x | Parse `#[trigger]` attribute syntax | Already workspace dep (macros/Cargo.toml), handles "full" feature for all Rust syntax |
| `quote` | 1.x | Code generation for trigger metadata | Already workspace dep, standard for proc macro codegen |
| `proc-macro2` | 1.x | Stable proc macro API | Already workspace dep, provides stable interface over unstable rustc APIs |

**Implementation Approach:**
- Add `#[trigger]` attribute macro to `rust-fv-macros` crate (alongside existing `#[requires]`, `#[ensures]`, etc.)
- Parse trigger patterns from attribute: `#[trigger(pattern = "f(x)")]` or `#[trigger(auto)]`
- Emit metadata struct alongside function (similar to existing contract metadata)
- rust-analyzer supports attribute proc macro expansion (enabled by default since v0.2.768)
- Verus/Dafny precedent: surface-language trigger selection with manual override annotations

**What NOT to do:**
- Don't implement trigger inference in proc macro (too complex, wrong layer) — do it in analysis crate during VCGen
- Don't use unstable proc macro features (stick to stable `syn`/`quote` patterns)

### VSCode Extension + Real-Time Verification

| Technology | Version | Purpose | Why Recommended |
|------------|---------|---------|-----------------|
| `tower-lsp` | 0.20+ | Rust LSP server implementation | De facto standard for Rust LSP servers (used by rust-analyzer, multiple verified tooling projects). Built on Tokio, provides `LanguageServer` trait |
| `lsp-types` | 0.97+ | LSP protocol type definitions | Official LSP 3.17 types, diagnostic structures, message types. 18M+ downloads, maintained by LSP working group |
| `tokio` | 1.47.x LTS | Async runtime for LSP server | tower-lsp requires Tokio. Use 1.47.x LTS (supported until Sept 2026) for stability. Provides async I/O for file watching + verification tasks |
| `notify` | 7.x+ | Cross-platform file system watching | Used by rust-analyzer, cargo-watch, watchexec. Provides debounced events + raw API. Cross-platform (inotify/FSEvents/ReadDirectoryChangesW) |
| `vscode-languageclient` (npm) | 9.x | VSCode extension LSP client | Official Microsoft LSP client for VSCode extensions. TypeScript/JavaScript, handles server lifecycle |
| `@vscode/vsce` (npm) | 3.6+ | VSCode extension packaging | Official packaging tool (renamed from `vsce`). Requires Node.js 20.x+, supports multi-platform targets |

**Architecture:**
```
VSCode Extension (TypeScript)
  └─ vscode-languageclient (spawns LSP server process)
       └─ rust-fv-lsp (Rust binary, tower-lsp)
            ├─ tower-lsp: LSP protocol handling
            ├─ notify: Watch .rs files for changes
            ├─ tokio: Async runtime (spawn verification tasks)
            └─ rust-fv-driver: Invoke verification on demand
```

**New Workspace Crate:**
- `crates/lsp/` - LSP server binary
  - Dependencies: `tower-lsp`, `lsp-types`, `tokio`, `notify`, `rust-fv-driver`, `rust-fv-analysis`
  - Implements: `textDocument/didOpen`, `didChange`, `didSave` → trigger verification
  - Implements: `textDocument/publishDiagnostics` → map `ariadne` output to LSP diagnostics
  - File watching: Use `notify` to detect changes outside VSCode (git switches, external edits)

**VSCode Extension Structure:**
```
extensions/vscode-rust-fv/
├── package.json          # Extension manifest, activationEvents, contributes
├── src/extension.ts      # Extension entry point (activates LSP client)
├── tsconfig.json
└── README.md
```

**Incremental Verification Strategy:**
- Use `notify` debounced events (default API) to avoid verification spam on rapid edits
- On file change: parse MIR only for changed function + dependents (inspired by Salsa incremental model from ty/Pyrefly LSP research)
- Cache verification results keyed by function body hash (use existing `sha2` workspace dep)
- Run verification on background Tokio task, stream diagnostics via `publishDiagnostics`

**What NOT to do:**
- Don't use WebAssembly for LSP server (adds complexity, harder debugging, no perf benefit for CPU-bound SMT solving)
- Don't use `napi-rs` for Node.js native addon (wrong abstraction — use LSP protocol boundary instead)
- Don't re-verify entire crate on every keystroke (implement file-level + function-level caching)

### Z3 bv2int Native Integration

| Technology | Version | Purpose | Why Recommended |
|------------|---------|---------|-----------------|
| `z3` (Rust bindings) | 0.19+ | High-level Z3 API | Already workspace dep. Provides `Config`, `Params`, `Solver` types for native solver configuration |
| `z3-sys` | (transitive) | Low-level Z3 C API | Used when high-level bindings don't expose specific features. Direct access to Z3 C API functions |

**Implementation Approach:**
- Use `z3::Params` to configure solver tactics programmatically (replaces subprocess CLI flags)
- Apply `bv2int` tactic via `Solver::set_params()` or tactic combinators
- Z3 Python precedent: `With('simplify', mul2concat=True)` → Rust: `Params::set_bool("mul2concat", true)`
- Tactic sequence: `simplify` (with bv2int-friendly options) → `solve-eqs` → `bit-blast` → `sat`

**Z3 Configuration API:**
```rust
use z3::{Config, Context, Params, Solver, Tactic};

let cfg = Config::new();
let ctx = Context::new(&cfg);

// Option 1: Configure via Params
let mut params = Params::new(&ctx);
params.set_bool("solver.bv.enable_int2bv", true);  // Enable bv2int rewrites
let solver = Solver::new(&ctx);
solver.set_params(&params);

// Option 2: Use tactics (more control)
let simplify = Tactic::new(&ctx, "simplify");
let solve_eqs = Tactic::new(&ctx, "solve-eqs");
let combined = simplify.and_then(&solve_eqs);
let solver = combined.solver(&ctx);
```

**Research Note:**
- Z3 C API exposes `Z3_OP_BV2INT` (unsigned) and `Z3_OP_SBV2INT` (signed) operations
- SMTLIB2 API: `ubv_to_int`, `sbv_to_int`, `int_to_bv` (recent additions per GitHub issues #1252, #1481)
- z3 crate 0.19 provides high-level bindings; if missing, drop to `z3_sys` for direct C API calls
- Configuration: 200+ parameters available via `set_global_param()` or solver-specific `Params`

**Integration into solver crate:**
- Extend `rust-fv-solver` enum to include `Z3Native { config: Z3Config }`
- Parse CLI flags `--z3-tactic`, `--z3-param` to populate `Z3Config`
- Route to native API instead of subprocess when `z3-native` feature enabled (already exists)
- Benchmark: native should be faster (no subprocess overhead, direct memory access)

**What NOT to do:**
- Don't use `bv2int` indiscriminately (can cause performance regression on bitwise-heavy code)
- Don't configure globally via `set_global_param()` (breaks isolation if multiple solvers in parallel)
- Don't assume all Z3 features are exposed in high-level bindings (use `z3_sys` when needed)

## Supporting Libraries

| Library | Version | Purpose | When to Use |
|---------|---------|---------|-------------|
| `dashmap` | 6.x+ | Concurrent hash map for caching | If implementing parallel verification with shared cache. Better than `RwLock<HashMap>` for high contention. Already have `rayon` for parallelism |
| `salsa` | 0.17+ | Incremental computation framework | If building sophisticated incremental verification (tracks dependencies, auto-invalidates). Large dep (consider later) — start with manual caching |
| `async-lsp` | 3.x+ | Alternative to tower-lsp | If need more control over LSP loop lifecycle (tower-lsp is opinionated). Consider only if tower-lsp limitations appear |
| `wasm-bindgen` | 0.2+ | WebAssembly TypeScript bindings | If shipping browser-based verification (future: Rust Playground integration). Not needed for VSCode extension |

## Development Tools

| Tool | Purpose | Notes |
|------|---------|-------|
| `@vscode/vsce` | Package VSCode extension | Install globally: `npm install -g @vscode/vsce`. Use `vsce package --target <platform>` for multi-platform |
| `tsc` (TypeScript) | Compile extension TypeScript | VSCode extension written in TS. Use `tsc --watch` during development |
| `cargo watch` | Auto-rebuild LSP server on change | Development workflow: `cargo watch -x 'build --bin rust-fv-lsp'` |
| `rust-analyzer` | VSCode Rust language server | Test LSP server alongside rust-analyzer (different language servers can coexist) |

## Installation

### Rust Dependencies (Cargo.toml additions)

```toml
# Workspace-level additions
[workspace.dependencies]
tower-lsp = "0.20"
lsp-types = "0.97"
tokio = { version = "1.47", features = ["full"] }  # LTS until Sept 2026
notify = "7"

# For lsp crate
[dependencies]
tower-lsp = { workspace = true }
lsp-types = { workspace = true }
tokio = { workspace = true }
notify = { workspace = true }
rust-fv-driver = { workspace = true }
rust-fv-analysis = { workspace = true }

# For std crate
[dependencies]
serde = { workspace = true }
serde_json = { workspace = true }
```

### VSCode Extension Dependencies (package.json)

```json
{
  "devDependencies": {
    "@types/node": "^20.x",
    "@types/vscode": "^1.85.0",
    "@vscode/vsce": "^3.6.0",
    "typescript": "^5.3.0"
  },
  "dependencies": {
    "vscode-languageclient": "^9.0.1"
  }
}
```

## Alternatives Considered

| Category | Recommended | Alternative | Why Not Alternative |
|----------|-------------|-------------|---------------------|
| LSP Server | `tower-lsp` | `async-lsp` | tower-lsp more popular, better docs, specialized for servers (not clients). async-lsp adds client support we don't need |
| LSP Server | `tower-lsp` | Custom LSP impl | Reinventing wheel. tower-lsp handles protocol details, lets us focus on verification logic |
| Async Runtime | `tokio` | `async-std` | tower-lsp requires tokio. Ecosystem momentum behind tokio (1.49+ active development) |
| File Watching | `notify` | Manual polling | notify provides platform-native watchers (inotify/FSEvents). Used by rust-analyzer (proven reliability) |
| VSCode Client | `vscode-languageclient` | Manual LSP client | Official Microsoft library, handles edge cases, lifecycle management. No reason to reimplement |
| Stdlib Contracts | Separate crate | Inline in core | Versioning independence (stdlib evolves slower than tool). Opt-in model (users choose to add dep) |
| Z3 API | Native bindings | Subprocess only | Native faster (no IPC), more control (tactics, params), same safety (z3 crate is safe wrapper) |

## What NOT to Use

| Avoid | Why | Use Instead |
|-------|-----|-------------|
| `async-std` for LSP | tower-lsp requires tokio, mixing runtimes causes issues | `tokio` 1.47 LTS |
| `vsce` (old package) | Deprecated, renamed to `@vscode/vsce` | `@vscode/vsce` 3.6+ |
| `languageserver-types` | Unmaintained, superseded by `lsp-types` | `lsp-types` 0.97+ |
| WebAssembly for LSP | Adds build complexity, no perf benefit for SMT solving, harder FFI to Z3 | Native Rust binary via LSP protocol |
| `napi-rs` | Wrong abstraction — we need LSP protocol boundary, not Node.js addon API | VSCode extension spawns Rust LSP binary |
| Global Z3 params | Breaks parallel solver isolation | Per-solver `Params` configuration |
| Polling for file changes | Inefficient, higher latency than OS-native watchers | `notify` crate with platform-specific backends |

## Stack Patterns by Feature

**Standard Library Contracts:**
- Create `crates/rust-fv-std/` with external specs
- Pattern: `#[extern_spec(std::vec::Vec)]` attribute (define in macros crate)
- Serialization: `serde` for metadata, proc macros for parsing
- Distribution: Separate crate users opt into

**Trigger Customization:**
- Extend `rust-fv-macros` with `#[trigger]` attribute
- Parse in proc macro, emit metadata, consume in `rust-fv-analysis` during VCGen
- Pattern matching: Verus-style surface syntax `#[trigger(f(x), g(y))]`
- Auto mode: `#[trigger(auto)]` delegates to analysis phase

**VSCode Extension + LSP:**
- New crate: `crates/lsp/` implements `tower_lsp::LanguageServer`
- VSCode extension (TypeScript): `extensions/vscode-rust-fv/`
- Communication: JSON-RPC over stdio (vscode-languageclient handles protocol)
- File watching: `notify` for external changes + LSP `didChange` for editor changes
- Incremental: Cache by function hash, re-verify only changed functions + dependents

**Z3 bv2int Native:**
- Use existing `z3` workspace dep (0.19+)
- Configure via `Params` API: `solver.set_params(&params)`
- Tactic combinators: `simplify.and_then(&solve_eqs).solver(&ctx)`
- Fallback to `z3_sys` if high-level API missing features

## Version Compatibility

| Package A | Compatible With | Notes |
|-----------|-----------------|-------|
| `tower-lsp` 0.20 | `tokio` 1.17+ | Requires Tokio runtime, tested with 1.47 LTS |
| `lsp-types` 0.97 | LSP 3.17 | Proposed 3.17 features via `proposed` feature flag |
| `vscode-languageclient` 9.x | Node.js 20+ | VSCode extension API, requires modern Node |
| `z3` 0.19 | Z3 solver 4.13+ | Bindings track Z3 releases, update together |
| `notify` 7.x | Tokio 1.x | Async file watcher, integrates with tokio runtime |
| `tokio` 1.47 LTS | Rust 1.70+ | LTS supported until Sept 2026, backported bugfixes |

**Critical Compatibility:**
- tower-lsp + tokio: MUST use tokio (not async-std), version 1.17+ required
- VSCode extension + Node.js: Requires Node.js 20.x+ (per @vscode/vsce docs)
- z3 crate + Z3 solver: Keep versions aligned (z3 0.19 → Z3 4.13.x)

## Sources

### High Confidence (Official Docs + Context7)
- [z3 crate documentation](https://docs.rs/z3/latest/z3/) — Version 0.19.8, API features
- [tower-lsp documentation](https://docs.rs/tower-lsp/latest/tower_lsp/) — Version 0.20.0, LanguageServer trait
- [lsp-types documentation](https://docs.rs/lsp-types/latest/lsp_types/) — Version 0.97.0, diagnostic types
- [Tokio releases](https://github.com/tokio-rs/tokio/releases) — LTS versions 1.43.x, 1.47.x
- [Prusti external specifications](https://viperproject.github.io/prusti-dev/user-guide/verify/external.html) — prusti-std pattern
- [Z3 API reference](https://z3prover.github.io/api/html/group__capi.html) — C API documentation

### Medium Confidence (Official GitHub/npm)
- [vscode-languageserver-node](https://github.com/microsoft/vscode-languageserver-node) — LSP implementation
- [notify-rs](https://github.com/notify-rs/notify) — Cross-platform file watching
- [VSCode Extension Guide](https://code.visualstudio.com/api/language-extensions/language-server-extension-guide) — Official LSP guide
- [rust-analyzer proc macro support](https://rust-analyzer.github.io/thisweek/2026/01/26/changelog-312.html) — Attribute macro expansion
- [Z3 tactics summary](https://microsoft.github.io/z3guide/docs/strategies/summary/) — Tactic configuration

### Low Confidence (WebSearch, Community)
- [Verus trigger patterns](https://www.cs.utexas.edu/~hleblanc/pdfs/verus.pdf) — Surface-level trigger selection (academic paper)
- [Pyrefly incremental verification](https://pyrefly.org/blog/2026/02/06/performance-improvements/) — Incremental type checking strategies

---
*Stack research for: Rust Formal Verification Tooling (v0.3 milestone)*
*Researched: 2026-02-14*
*Confidence: HIGH (official docs verified for all core dependencies)*
