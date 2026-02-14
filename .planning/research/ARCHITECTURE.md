# Architecture Integration: v0.3 Production Features

**Domain:** Compiler-integrated formal verification tool for Rust
**Researched:** 2026-02-14
**Confidence:** HIGH

## Executive Summary

This document analyzes how v0.3 production features integrate with rust-fv's existing 5-crate architecture. The features divide into four integration categories:

1. **Stdlib Contracts** - New data layer (contract database extension)
2. **Trigger Customization** - Macro + VCGen modification
3. **IDE Integration** - New project + LSP bridge
4. **bv2int Optimization** - Solver backend enhancement

All features integrate cleanly without requiring architectural changes to the core verification pipeline.

## Existing Architecture (v0.2)

### System Overview

```
┌─────────────────────────────────────────────────────────────┐
│                    User Code Layer                          │
│  #[requires], #[ensures] → hidden doc attributes            │
└────────────────┬────────────────────────────────────────────┘
                 │
┌────────────────▼────────────────────────────────────────────┐
│                   Driver Crate                              │
│  ┌─────────┐  ┌──────────┐  ┌─────────┐  ┌──────────┐      │
│  │ rustc   │→ │ Extract  │→ │  MIR    │→ │ Parallel │      │
│  │Callbacks│  │Contracts │  │Converter│  │Executor  │      │
│  └─────────┘  └──────────┘  └─────────┘  └──────────┘      │
└────────────────┬────────────────────────────────────────────┘
                 │
┌────────────────▼────────────────────────────────────────────┐
│                  Analysis Crate                             │
│  ┌─────────┐  ┌──────────┐  ┌─────────┐  ┌──────────┐      │
│  │   IR    │→ │  VCGen   │→ │ Encode  │→ │Contract  │      │
│  │         │  │          │  │ Term    │  │   DB     │      │
│  └─────────┘  └──────────┘  └─────────┘  └──────────┘      │
│  ┌──────────────────────────────────────────────────┐       │
│  │ Quantifier Encoder (trigger inference)           │       │
│  └──────────────────────────────────────────────────┘       │
└────────────────┬────────────────────────────────────────────┘
                 │
┌────────────────▼────────────────────────────────────────────┐
│                   Solver Crate                              │
│  ┌─────────────────────┐  ┌──────────────────────┐          │
│  │  SolverBackend      │  │   create_default     │          │
│  │  (trait)            │  │   _backend()         │          │
│  └──────┬──────────────┘  └──────────────────────┘          │
│         │                                                    │
│  ┌──────▼─────────┐  ┌───────────────────┐                  │
│  │ SubprocessZ3   │  │ Z3NativeSolver    │                  │
│  │ (z3 CLI)       │  │ (z3 crate API)    │                  │
│  └────────────────┘  └───────────────────┘                  │
└────────────────┬────────────────────────────────────────────┘
                 │
┌────────────────▼────────────────────────────────────────────┐
│                  SMTLib Crate                               │
│  Term, Sort, Command, Script (SMT-LIB2 AST)                 │
└─────────────────────────────────────────────────────────────┘
```

### Crate Responsibilities

| Crate | Responsibility | Key Files |
|-------|----------------|-----------|
| **macros/** | Proc macros: `#[requires]`, `#[ensures]`, etc. → hidden doc attrs | `lib.rs` |
| **driver/** | rustc integration, contract extraction from HIR, parallel execution | `callbacks.rs`, `mir_converter.rs`, `parallel.rs` |
| **analysis/** | MIR→IR, VCGen, SMT encoding, quantifier triggers, contract database | `vcgen.rs`, `encode_quantifier.rs`, `contract_db.rs` |
| **solver/** | SolverBackend trait, subprocess/native Z3 backends | `backend.rs`, `z3_native.rs` |
| **smtlib/** | SMT-LIB2 AST types (Term, Sort, Command, Script) | `lib.rs`, `term.rs` |

### Data Flow

```
User Code (#[requires(x > 0)])
    ↓ (proc macro)
Hidden Doc Attribute (#[doc = "rust_fv::requires::x > 0"])
    ↓ (rustc compilation)
HIR with Attributes
    ↓ (driver::callbacks::extract_contracts)
Contracts Map (LocalDefId → Contracts)
    ↓ (driver::mir_converter)
IR Functions (with contracts)
    ↓ (analysis::vcgen::generate_vcs)
Verification Conditions (SMT scripts)
    ↓ (solver::SolverBackend::check_sat)
SolverResult (Sat/Unsat/Unknown)
    ↓ (driver::callbacks::print_results)
User-facing diagnostics
```

## Feature 1: Standard Library Contracts

### What It Is

Preloaded specifications for stdlib functions (Vec::len, Option::unwrap, etc.) so users don't need to annotate every stdlib call.

### Integration Point

**Component:** `analysis/contract_db.rs` (ContractDatabase)

**Current State:**
- ContractDatabase stores user-defined contracts extracted from HIR
- Populated in `driver/callbacks.rs::after_analysis` from contracts_map
- Queried during VCGen for inter-procedural verification

**Integration Approach:**

```rust
// NEW: analysis/src/stdlib_contracts.rs
pub struct StdlibContractRegistry {
    contracts: HashMap<String, FunctionSummary>,
}

impl StdlibContractRegistry {
    pub fn new() -> Self {
        let mut registry = Self::default();
        registry.register_core_contracts();
        registry.register_alloc_contracts();
        registry.register_collections_contracts();
        registry
    }

    fn register_core_contracts(&mut self) {
        // Vec::len
        self.insert("alloc::vec::Vec<T>::len", FunctionSummary {
            requires: vec![],
            ensures: vec![spec!("result >= 0")],
            param_names: vec!["self"],
            param_types: vec![Type::Ref(...)],
            return_ty: Type::Usize,
        });

        // Option::unwrap
        self.insert("core::option::Option<T>::unwrap", FunctionSummary {
            requires: vec![spec!("self.is_some()")],
            ensures: vec![spec!("result == self.unwrap()")],
            ...
        });
    }
}

// MODIFIED: analysis/src/contract_db.rs
pub struct ContractDatabase {
    user_contracts: HashMap<String, FunctionSummary>,
    stdlib_registry: StdlibContractRegistry,  // NEW
}

impl ContractDatabase {
    pub fn new() -> Self {
        Self {
            user_contracts: HashMap::new(),
            stdlib_registry: StdlibContractRegistry::new(),  // NEW
        }
    }

    pub fn lookup(&self, name: &str) -> Option<&FunctionSummary> {
        // User contracts override stdlib
        self.user_contracts.get(name)
            .or_else(|| self.stdlib_registry.lookup(name))  // NEW
    }
}
```

**Data Flow:**

```
Compilation Start
    ↓
ContractDatabase::new()
    ↓
StdlibContractRegistry::new() → Preload stdlib contracts
    ↓
extract_contracts(tcx) → User-defined contracts
    ↓
ContractDatabase::insert_user(...) → Merge with stdlib
    ↓
VCGen::lookup_contract(callee_name)
    ↓
Returns stdlib or user contract (user overrides stdlib)
```

**New Component:**

| File | Purpose | Lines Est. |
|------|---------|------------|
| `analysis/src/stdlib_contracts.rs` | Registry of stdlib function contracts | ~500 |

**Modified Components:**

| File | Modification | Complexity |
|------|--------------|------------|
| `analysis/src/contract_db.rs` | Add `StdlibContractRegistry` field, dual-lookup | Low |
| `analysis/src/lib.rs` | Export `stdlib_contracts` module | Trivial |

**No changes required:** driver, macros, solver, smtlib

---

## Feature 2: Trigger Customization

### What It Is

User-specified SMT quantifier trigger patterns via `#[trigger(...)]` attribute to override automatic trigger inference.

### Integration Points

**Components:**
1. `macros/lib.rs` - New `#[trigger]` proc macro
2. `analysis/ir.rs` - Add trigger field to SpecExpr
3. `analysis/encode_quantifier.rs` - Use user triggers if present

**Current State:**

- `encode_quantifier::infer_triggers()` automatically finds trigger patterns
- No user control over trigger selection
- Triggers embedded in SMT via `:pattern` attribute

**Integration Approach:**

```rust
// NEW: macros/src/lib.rs
#[proc_macro_attribute]
pub fn trigger(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse: #[trigger(f(x), g(y))]
    // Encode: rust_fv::trigger::f(x)::g(y)
    // Multiple triggers separated by ::
}

// MODIFIED: analysis/src/ir.rs
pub struct SpecExpr {
    pub raw: String,
    pub triggers: Option<Vec<Vec<String>>>,  // NEW: user-provided triggers
}

// MODIFIED: analysis/src/spec_parser.rs
fn parse_spec_expr(raw: &str) -> SpecExpr {
    // Extract triggers if embedded in doc string
    // Format: rust_fv::trigger::f(x)::g(y)
    let triggers = extract_triggers(&raw);
    SpecExpr { raw, triggers }
}

// MODIFIED: analysis/src/encode_quantifier.rs
pub fn encode_quantified(expr: &SpecExpr, bound_vars: &[String]) -> Term {
    let triggers = if let Some(user_triggers) = &expr.triggers {
        // Use user-provided triggers
        user_triggers.clone()
    } else {
        // Fallback to automatic inference
        infer_triggers(&body, bound_vars)
    };

    // Encode with :pattern attribute
    Term::Quantified {
        quantifier: Forall,
        vars: bound_vars.clone(),
        body: Box::new(body),
        patterns: triggers,  // Now user-controllable
    }
}
```

**Data Flow:**

```
User Code: #[trigger(vec.len())] #[ensures(forall(|i| i < vec.len()))]
    ↓ (proc macro)
Doc Attrs: rust_fv::ensures::forall(|i| ...) + rust_fv::trigger::vec.len()
    ↓ (driver extract_contracts)
SpecExpr { raw: "forall...", triggers: Some([["vec.len()"]]) }
    ↓ (VCGen → encode_quantifier)
Term::Quantified with :pattern ((vec.len))
    ↓ (SMT solver)
Controlled instantiation
```

**New Components:**

| Component | Purpose | Lines Est. |
|-----------|---------|------------|
| `macros/lib.rs::trigger()` | New proc macro for trigger annotation | ~50 |

**Modified Components:**

| File | Modification | Complexity |
|------|--------------|------------|
| `analysis/src/ir.rs` | Add `triggers: Option<Vec<Vec<String>>>` to SpecExpr | Trivial |
| `analysis/src/spec_parser.rs` | Extract triggers from doc attrs | Low (~50 lines) |
| `analysis/src/encode_quantifier.rs` | Use user triggers if present, else infer | Low (~30 lines) |
| `driver/callbacks.rs` | Parse trigger annotations during contract extraction | Low (~30 lines) |

**No changes required:** solver, smtlib (already support :pattern)

---

## Feature 3: IDE Integration (VSCode Extension + rust-analyzer)

### What It Is

VSCode extension that shows verification results inline and integrates with rust-analyzer for diagnostics.

### Architecture

**Two-Component System:**

```
┌─────────────────────────────────────────────────────────────┐
│                   VSCode Extension                          │
│  (TypeScript, new project: extensions/vscode-rust-fv/)      │
│                                                              │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐      │
│  │ Extension    │  │  Diagnostic  │  │   Status     │      │
│  │ Host         │→ │  Provider    │→ │   Bar        │      │
│  └──────┬───────┘  └──────────────┘  └──────────────┘      │
│         │                                                    │
│         ├─ Watches: target/rust-fv-cache/*.json             │
│         ├─ Parses: JSON verification results                │
│         └─ Renders: Inline diagnostics + gutter icons       │
└─────────────────────────────────────────────────────────────┘
                 │
                 │ (no direct integration needed)
                 │
┌────────────────▼────────────────────────────────────────────┐
│              rust-analyzer (existing)                       │
│  Standard LSP diagnostics (compiler errors, clippy)         │
└─────────────────────────────────────────────────────────────┘
                 │
┌────────────────▼────────────────────────────────────────────┐
│            rust-fv-driver (existing)                        │
│  RUST_FV_OUTPUT_FORMAT=json → JSON diagnostics              │
│  Written to: target/rust-fv-cache/verification.json         │
└─────────────────────────────────────────────────────────────┘
```

**Key Insight:** No rust-analyzer modification needed. VSCode extension reads JSON output from rust-fv-driver and displays as VSCode diagnostics (separate from rust-analyzer's diagnostics).

**Integration Approach:**

```typescript
// NEW: extensions/vscode-rust-fv/src/extension.ts
import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';

export function activate(context: vscode.ExtensionContext) {
    const diagnosticCollection = vscode.languages.createDiagnosticCollection('rust-fv');

    // Watch verification output file
    const watcher = vscode.workspace.createFileSystemWatcher(
        '**/target/rust-fv-cache/verification.json'
    );

    watcher.onDidChange(() => {
        refreshDiagnostics(diagnosticCollection);
    });

    // Command: Run verification
    vscode.commands.registerCommand('rust-fv.verify', async () => {
        const terminal = vscode.window.createTerminal('rust-fv');
        terminal.sendText('RUST_FV_VERIFY=1 RUST_FV_OUTPUT_FORMAT=json cargo check');
        terminal.show();
    });
}

function refreshDiagnostics(collection: vscode.DiagnosticCollection) {
    const jsonPath = path.join(vscode.workspace.rootPath!, 'target/rust-fv-cache/verification.json');
    const report = JSON.parse(fs.readFileSync(jsonPath, 'utf8'));

    const diagnosticsMap = new Map<string, vscode.Diagnostic[]>();

    for (const func of report.functions) {
        for (const failure of func.failures) {
            const uri = vscode.Uri.file(failure.source_file);
            const range = new vscode.Range(
                failure.source_line - 1, 0,
                failure.source_line - 1, 999
            );
            const diagnostic = new vscode.Diagnostic(
                range,
                `[rust-fv] ${failure.description}`,
                vscode.DiagnosticSeverity.Error
            );
            diagnostic.code = failure.vc_kind;
            diagnostic.source = 'rust-fv';

            if (!diagnosticsMap.has(uri.toString())) {
                diagnosticsMap.set(uri.toString(), []);
            }
            diagnosticsMap.get(uri.toString())!.push(diagnostic);
        }
    }

    // Clear all diagnostics
    collection.clear();

    // Set new diagnostics
    diagnosticsMap.forEach((diags, uriStr) => {
        collection.set(vscode.Uri.parse(uriStr), diags);
    });
}
```

**Data Flow:**

```
User runs: "Rust-FV: Verify" command
    ↓
Extension spawns: RUST_FV_VERIFY=1 RUST_FV_OUTPUT_FORMAT=json cargo check
    ↓
rust-fv-driver runs verification
    ↓
Writes: target/rust-fv-cache/verification.json
    ↓
FileSystemWatcher detects change
    ↓
Extension parses JSON
    ↓
Creates vscode.Diagnostic objects
    ↓
Sets diagnostics via DiagnosticCollection
    ↓
VSCode shows inline errors (separate from rust-analyzer diagnostics)
```

**New Project Structure:**

```
extensions/vscode-rust-fv/
├── package.json              # VSCode extension manifest
├── tsconfig.json             # TypeScript config
├── src/
│   ├── extension.ts          # Main extension entry point
│   ├── diagnostics.ts        # JSON → VSCode diagnostics conversion
│   └── commands.ts           # Verification commands
├── syntaxes/                 # (optional) Syntax highlighting for specs
└── README.md
```

**New Components:**

| Component | Purpose | Technology | Lines Est. |
|-----------|---------|------------|------------|
| `extensions/vscode-rust-fv/` | VSCode extension project | TypeScript + VSCode API | ~500 |
| `extension.ts` | Extension activation, file watcher | TypeScript | ~150 |
| `diagnostics.ts` | JSON parsing, diagnostic creation | TypeScript | ~200 |
| `commands.ts` | Verification commands, status bar | TypeScript | ~150 |

**Modified Components:**

| File | Modification | Complexity |
|------|--------------|------------|
| `driver/src/json_output.rs` | Already exists, may need schema adjustments | Low |

**No changes required:** macros, analysis, solver, smtlib, rust-analyzer (completely separate)

---

## Feature 4: bv2int Optimization

### What It Is

Z3 solver tactic that converts bit-vector arithmetic to integer arithmetic for faster solving when overflow checks are not needed.

### Integration Point

**Component:** `solver/backend.rs` + `solver/z3_native.rs`

**Current State:**

- SolverBackend::check_sat() receives SMT Script
- Z3NativeSolver directly translates Script → Z3 API calls
- No tactic pipeline applied

**Integration Approach:**

```rust
// MODIFIED: solver/src/backend.rs
pub trait SolverBackend {
    fn check_sat(&self, script: &Script) -> Result<SolverResult, SolverError>;

    // NEW: Optional tactic configuration
    fn with_tactics(&self, tactics: &[Tactic]) -> Box<dyn SolverBackend> {
        // Default: no-op (subprocess backend doesn't support tactics easily)
        Box::new(self)
    }
}

// NEW: solver/src/tactics.rs
pub enum Tactic {
    Bv2Int,           // Convert BV to Int when safe
    Simplify,         // Algebraic simplification
    SolveEqs,         // Solve equalities
}

pub struct TacticPipeline {
    tactics: Vec<Tactic>,
}

impl TacticPipeline {
    pub fn default() -> Self {
        Self {
            tactics: vec![
                Tactic::Simplify,
                Tactic::Bv2Int,    // NEW: apply bv2int
                Tactic::SolveEqs,
            ],
        }
    }

    pub fn apply(&self, ctx: &z3::Context, assertions: &[z3::ast::Bool]) -> z3::Solver {
        let goal = z3::Goal::new(ctx, false, false, false);
        for assertion in assertions {
            goal.assert(assertion);
        }

        // Build tactic sequence
        let tactic = self.tactics.iter().fold(
            z3::Tactic::new(ctx, "simplify"),
            |acc, t| match t {
                Tactic::Bv2Int => acc.and_then(ctx, &z3::Tactic::new(ctx, "bv2int")),
                Tactic::Simplify => acc.and_then(ctx, &z3::Tactic::new(ctx, "simplify")),
                Tactic::SolveEqs => acc.and_then(ctx, &z3::Tactic::new(ctx, "solve-eqs")),
            }
        );

        // Apply tactic pipeline
        let apply_result = tactic.apply(&goal);
        let solver = apply_result.get_solver();
        solver
    }
}

// MODIFIED: solver/src/z3_native.rs
pub struct Z3NativeSolver {
    config: SolverConfig,
    tactic_pipeline: Option<TacticPipeline>,  // NEW
}

impl Z3NativeSolver {
    pub fn with_tactics(mut self, tactics: TacticPipeline) -> Self {
        self.tactic_pipeline = Some(tactics);
        self
    }
}

impl SolverBackend for Z3NativeSolver {
    fn check_sat(&self, script: &Script) -> Result<SolverResult, SolverError> {
        let cfg = z3::Config::new();
        let ctx = z3::Context::new(&cfg);

        // Translate script to Z3 AST
        let assertions = translate_script_to_z3(&ctx, script)?;

        let solver = if let Some(pipeline) = &self.tactic_pipeline {
            // NEW: Apply tactic pipeline
            pipeline.apply(&ctx, &assertions)
        } else {
            // Original: Direct solver
            z3::Solver::new(&ctx)
        };

        for assertion in assertions {
            solver.assert(&assertion);
        }

        // Check and return result
        match solver.check() {
            z3::SatResult::Sat => Ok(SolverResult::Sat(...)),
            z3::SatResult::Unsat => Ok(SolverResult::Unsat),
            z3::SatResult::Unknown => Ok(SolverResult::Unknown(...)),
        }
    }
}

// MODIFIED: driver/src/parallel.rs
fn create_solver() -> Box<dyn SolverBackend> {
    let backend = solver::create_default_backend().unwrap();

    // NEW: Enable bv2int optimization
    if std::env::var("RUST_FV_BV2INT").is_ok() {
        backend.with_tactics(&TacticPipeline::default())
    } else {
        backend
    }
}
```

**Data Flow:**

```
VCGen produces SMT Script (with BV operations)
    ↓
SolverBackend::check_sat(script)
    ↓
Z3NativeSolver::translate_script_to_z3() → Z3 AST
    ↓
TacticPipeline::apply()
    ├─ simplify (algebraic reduction)
    ├─ bv2int (BV → Int conversion where safe)
    └─ solve-eqs (equation solving)
    ↓
Z3 Solver::check() on transformed formula
    ↓
SolverResult (potentially faster)
```

**New Components:**

| File | Purpose | Lines Est. |
|------|---------|------------|
| `solver/src/tactics.rs` | Tactic enum, TacticPipeline | ~150 |

**Modified Components:**

| File | Modification | Complexity |
|------|--------------|------------|
| `solver/src/backend.rs` | Add `with_tactics()` method to trait | Low (~20 lines) |
| `solver/src/z3_native.rs` | Integrate tactic pipeline into check_sat | Medium (~80 lines) |
| `driver/src/parallel.rs` | Conditionally enable tactics via env var | Trivial (~5 lines) |

**No changes required:** macros, analysis, smtlib

---

## Build Order and Dependencies

### Dependency Graph

```
stdlib_contracts ─┐
                  ├─→ All independent
trigger_macro ────┤    (can be built in parallel)
                  │
bv2int ───────────┘

ide_extension ─────→ Depends on JSON output (already exists)
```

### Recommended Build Order

**Phase 1: Core Extensions (Parallel)**
1. Stdlib Contracts - Pure data, no dependencies
2. Trigger Customization - Macro + analysis changes
3. bv2int Optimization - Solver-only changes

**Phase 2: User-Facing (After Phase 1)**
4. IDE Extension - Depends on stable JSON output

**Rationale:**
- Features 1-3 are independent backend improvements
- Feature 4 (IDE) is user-facing and benefits from having all backend features working first
- All features integrate via existing extension points (no core architecture changes)

---

## Integration Complexity Assessment

| Feature | New Components | Modified Components | Complexity | Risk |
|---------|----------------|---------------------|------------|------|
| **Stdlib Contracts** | 1 new module (~500 lines) | 2 files (~20 lines total) | Low | Low - Pure data |
| **Trigger Customization** | 1 macro (~50 lines) | 4 files (~150 lines total) | Low | Low - Well-defined integration |
| **bv2int Optimization** | 1 module (~150 lines) | 3 files (~100 lines total) | Medium | Medium - Z3 API complexity |
| **IDE Extension** | New project (~500 lines) | 1 file (minor) | Low | Low - Separate project |

**Total New Code:** ~1200 lines
**Total Modified Code:** ~270 lines
**New Projects:** 1 (VSCode extension)

---

## Anti-Patterns to Avoid

### Anti-Pattern 1: Tight Coupling Between IDE and Solver

**What NOT to do:** Make VSCode extension call rust-fv-driver directly or communicate via sockets.

**Why it's wrong:** Creates deployment complexity, version skew, and platform dependencies.

**Do this instead:** VSCode extension is a passive observer that reads JSON output files. All verification logic stays in rust-fv-driver.

### Anti-Pattern 2: Stdlib Contracts in Macros

**What NOT to do:** Embed stdlib contracts in proc macros or driver crate.

**Why it's wrong:** Stdlib contracts are semantic knowledge that belongs in analysis layer, not macro expansion or driver orchestration.

**Do this instead:** Stdlib contracts live in `analysis/stdlib_contracts.rs` and integrate with ContractDatabase lookup.

### Anti-Pattern 3: Hardcoded Trigger Inference

**What NOT to do:** Replace automatic trigger inference with user triggers only.

**Why it's wrong:** Most users won't provide triggers. Automatic inference must remain the default.

**Do this instead:** User triggers override automatic inference when present, with automatic inference as fallback.

### Anti-Pattern 4: bv2int Always-On

**What NOT to do:** Apply bv2int tactic unconditionally.

**Why it's wrong:** bv2int is unsound for overflow checking. Should be opt-in.

**Do this instead:** Enable via environment variable (`RUST_FV_BV2INT=1`) for performance-critical non-overflow VCs.

---

## Sources

**Language Server Protocol & VSCode Extensions:**
- [rust-analyzer LSP Architecture](https://rust-analyzer.github.io/)
- [VSCode Language Extensions](https://code.visualstudio.com/api/language-extensions/overview)
- [VSCode Extension TypeScript Guide 2026](https://abdulkadersafi.com/blog/building-vs-code-extensions-in-2026-the-complete-modern-guide)
- [vscode-languageserver-node](https://github.com/microsoft/vscode-languageserver-node)

**SMT Quantifiers & Triggers:**
- [SMT-LIB 2.7 Standard](https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-02-05.pdf)
- [F* Z3 Trigger Usage](https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html)
- [Trigger Selection Strategies](https://link.springer.com/chapter/10.1007/978-3-319-41528-4_20)
- [Tunable Automation in Verification](https://arxiv.org/html/2512.03926)

**Z3 Tactics & bv2int:**
- [Z3 Tactics Summary](https://microsoft.github.io/z3guide/docs/strategies/summary/)
- [Z3 Bit-vector Theory](https://microsoft.github.io/z3guide/docs/theories/Bitvectors/)
- [Z3 bv2int Issue](https://github.com/Z3Prover/z3/issues/7572)

**Formal Verification Contracts:**
- [Verus Overview](https://verus-lang.github.io/verus/guide/)
- [Prusti Project](https://link.springer.com/chapter/10.1007/978-3-031-06773-0_5)
- [Creusot Tutorial POPL 2026](https://popl26.sigplan.org/details/POPL-2026-tutorials/6/Creusot-Formal-verification-of-Rust-programs)
- [Rust Contracts Lang-Team Discussion](https://github.com/rust-lang/lang-team/blob/master/design-meeting-minutes/2022-11-25-contracts.md)

---

*Architecture research for: rust-fv v0.3 Production Features*
*Researched: 2026-02-14*
*Confidence: HIGH - Based on existing codebase analysis and current documentation*
