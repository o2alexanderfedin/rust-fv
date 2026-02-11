# Rust Compiler/Toolchain Integration for Formal Verification
## Research Summary

---

## Executive Summary

This document summarizes research on integrating formal verification tools with the Rust compiler and build toolchain. Five primary integration approaches exist, each with different trade-offs in terms of complexity, maintenance burden, and capabilities. The recommended approach depends on the verification tool's requirements and whether deep compiler integration or lightweight annotation processing is needed.

---

## 1. Integration Approaches

### 1.1 Procedural Macros (Attribute-based)

**Description**: Use procedural macros to define custom attributes for verification annotations, processing code at the token level during compilation.

**Technical Details**:
- Operate on token streams at compile time
- Three types available: derive macros, attribute-like macros, and function-like macros
- Process Rust syntax before type checking
- Cannot access type information or compiler internals without modification

**Advantages**:
- Stable API (works on stable Rust)
- Easiest to implement and maintain
- No compiler version pinning required
- Suitable for lightweight verification annotations
- Can generate verification conditions as separate code

**Disadvantages**:
- Limited access to semantic information
- Cannot inspect MIR or type system directly
- No integration with compiler analysis passes
- Must work at syntactic level only

**Example Use Cases**:
- Contract annotations (#[requires], #[ensures])
- Invariant declarations
- Ghost code generation
- Preprocessing for external verification tools

**References**:
- [Procedural Macros - The Rust Reference](https://doc.rust-lang.org/reference/procedural-macros.html)
- [Master Rust Macros in 2026](https://itch.io/blog/1150454/master-rust-macros-in-2026-a-complete-guide-to-metaprogramming-for-efficient-and-safe-code)

---

### 1.2 MIR Analysis Passes

**Description**: Implement custom analysis passes that operate on Rust's Mid-level Intermediate Representation (MIR), accessing semantic information after type checking.

**Technical Details**:
- MIR is a simplified control-flow graph representation
- Access to type information and borrow checking results
- Implement the `MirPass` trait with `run_pass` method
- Operates on `&mut Body` with access to `TyCtxt`
- Passes defined in `rustc_mir_transform` crate

**Advantages**:
- Full access to type information
- Simplified representation compared to AST/HIR
- Integration point for borrow checker
- Can perform dataflow analysis
- Suitable for abstract interpretation

**Disadvantages**:
- Requires nightly Rust with specific version pinning
- Unstable compiler API
- Complex integration (requires rustc_driver)
- High maintenance burden due to API changes

**Example Use Cases**:
- Abstract interpretation (like MIRAI)
- Taint analysis
- Alias analysis
- Verification condition generation from typed IR

**References**:
- [The MIR (Mid-level IR) - Rust Compiler Development Guide](https://rustc-dev-guide.rust-lang.org/mir/index.html)
- [MIR Passes and Queries](https://rustc-dev-guide.rust-lang.org/mir/passes.html)
- [MIRAI: Rust MIR Abstract Interpreter](https://github.com/facebookexperimental/MIRAI)

---

### 1.3 Custom Rustc Driver

**Description**: Build a custom compiler driver using `rustc_interface` and `rustc_driver`, allowing full control over compilation phases and custom query registration.

**Technical Details**:
- Use `rustc_interface` for low-level API access
- Override default compiler queries via callbacks
- Implement `Callbacks` trait to inject custom behavior
- Access to all compiler phases and data structures
- Can register custom query providers

**Advantages**:
- Maximum flexibility and control
- Access to all compiler internals
- Can integrate at any compilation phase
- Full control over optimization passes
- Can modify compilation behavior

**Disadvantages**:
- Most complex integration approach
- Requires deep compiler knowledge
- Must pin to specific nightly version
- High maintenance overhead
- Unstable API surface

**Example Use Cases**:
- Complete verification framework integration
- Custom type system extensions
- Whole-program analysis
- Compiler-integrated verification

**References**:
- [rustc_driver and rustc_interface](https://rustc-dev-guide.rust-lang.org/rustc-driver/intro.html)
- [Building your own rustc_driver](https://jyn.dev/rustc-driver/)
- [rustc_interface::passes](https://doc.rust-lang.org/stable/nightly-rustc/rustc_interface/passes/index.html)

---

### 1.4 Rustc_plugin Framework

**Description**: Use the `rustc_plugin` framework to build tools that integrate with the compiler API, handling toolchain management and marshalling.

**Technical Details**:
- Framework for experimental Rust tools
- Handles sysroot configuration and argument marshalling
- Implements `RustcPlugin` trait
- Used by research tools like Flowistry, Aquascope, Paralegal
- Provides structure for CLI and driver binaries

**Advantages**:
- Cleaner abstraction over rustc_driver
- Handles toolchain setup automatically
- Proven by multiple research projects
- Structured approach to plugin development

**Disadvantages**:
- Still requires nightly pinning
- Relatively new framework
- Limited documentation
- Smaller community than core rustc

**Example Use Cases**:
- Research verification tools
- Experimental static analyzers
- Custom dataflow analysis tools

**References**:
- [rustc_plugin Framework - Cognitive Engineering Lab](https://github.com/cognitive-engineering-lab/rustc_plugin)
- [rustc_plugin - Viper Project](https://github.com/viperproject/rustc-plugin)

---

### 1.5 Cargo Build Script Integration

**Description**: Use Cargo build scripts (build.rs) to invoke external verification tools, integrating verification into the standard Rust build process.

**Technical Details**:
- Execute custom code before package compilation
- Can invoke external SMT solvers and verification tools
- Access to cargo metadata and environment
- Run verification as part of CI/CD pipeline
- Output custom compiler directives

**Advantages**:
- Works with stable Rust
- Standard Cargo integration pattern
- Easy CI/CD integration
- Can use any external tools
- Well-documented and supported

**Disadvantages**:
- No direct compiler access
- Must parse source separately
- Cannot modify compilation
- Limited to pre-build phase

**Example Use Cases**:
- Invoking external SMT solvers (Z3, CVC5)
- Running verification tools like Verus
- Generating verification reports
- Pre-compilation contract checking

**References**:
- [Build Scripts - The Cargo Book](https://doc.rust-lang.org/cargo/reference/build-scripts.html)
- [External Tools - The Cargo Book](https://doc.rust-lang.org/cargo/reference/external-tools.html)
- [Cargo Metadata Integration](https://doc.rust-lang.org/cargo/commands/cargo-metadata.html)

---

## 2. Existing Formal Verification Tools Analysis

### 2.1 Prusti

**Approach**: Custom rustc driver with MIR analysis
**Backend**: Viper verification infrastructure
**Annotations**: Procedural macros for contracts

**Key Integration Points**:
- Uses procedural macros for user-facing annotations
- Custom rustc driver for MIR extraction
- Translates MIR to Viper intermediate language
- Leverages Rust type system to reduce annotation burden

**References**:
- [The Prusti Project: Formal Verification for Rust](https://link.springer.com/chapter/10.1007/978-3-031-06773-0_5)

---

### 2.2 Creusot

**Approach**: Compiler integration with translation to WhyML
**Backend**: Why3 platform with multiple SMT solvers
**Annotations**: Custom attributes via procedural macros

**Key Integration Points**:
- Extracts and translates Rust MIR to WhyML
- Contract specifications via attributes
- Tutorial at POPL 2026 showing active development

**References**:
- [Creusot: Formal Verification of Rust Programs](https://popl26.sigplan.org/details/POPL-2026-tutorials/6/Creusot-Formal-verification-of-Rust-programs)
- [Rust Formal Methods Interest Group](https://rust-formal-methods.github.io/)

---

### 2.3 Kani

**Approach**: Model checking via CBMC backend
**Backend**: CBMC (C Bounded Model Checker)
**Annotations**: Procedural macros

**Key Integration Points**:
- Translates Rust to CBMC's internal representation
- Integration with cargo via custom subcommand
- Working on ESBMC backend integration

**References**:
- [Expanding the Rust Formal Verification Ecosystem](https://rustfoundation.org/media/expanding-the-rust-formal-verification-ecosystem-welcoming-esbmc/)

---

### 2.4 MIRAI

**Approach**: MIR-based abstract interpretation
**Backend**: Custom abstract interpreter
**Annotations**: Standard Rust assertions and contracts

**Key Integration Points**:
- Implements custom MIR analysis pass
- Top-down path-sensitive analysis
- Works like `cargo check` but uses MIRAI analyzer
- Uses abstract interpretation over MIR

**References**:
- [MIRAI: Rust MIR Abstract Interpreter](https://github.com/facebookexperimental/MIRAI)
- [MIRAI Overview Documentation](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/Overview.md)

---

### 2.5 Clippy (Linter Architecture Reference)

**Approach**: Late lint pass with HIR/MIR analysis
**Integration**: Built into rustc as standard linter

**Key Integration Points**:
- Early lint passes operate on AST
- Late lint passes operate on HIR/MIR with type information
- Each lint in separate module implementing trait
- Extensive utility infrastructure (clippy_utils)

**Lessons for Verification Tools**:
- Modular lint/check organization
- Separation of early (syntactic) and late (semantic) passes
- Rich utility library for common operations
- Standard integration with cargo

**References**:
- [Clippy Architecture](https://github.com/rust-lang/rust-clippy)
- [Write Rust Lints Without Forking Clippy](https://blog.trailofbits.com/2021/11/09/write-rust-lints-without-forking-clippy/)

---

## 3. Technical Feasibility Assessment

### 3.1 Procedural Macros
- **Feasibility**: High
- **Implementation Complexity**: Low to Medium
- **Maintenance Burden**: Low
- **Capabilities**: Limited to syntactic processing
- **Recommended For**: Annotation syntax, contract DSLs

### 3.2 MIR Analysis Passes
- **Feasibility**: Medium to High
- **Implementation Complexity**: High
- **Maintenance Burden**: High (API instability)
- **Capabilities**: Full semantic analysis
- **Recommended For**: Abstract interpretation, dataflow analysis

### 3.3 Custom Rustc Driver
- **Feasibility**: Medium
- **Implementation Complexity**: Very High
- **Maintenance Burden**: Very High
- **Capabilities**: Maximum flexibility
- **Recommended For**: Complete verification frameworks

### 3.4 Rustc_plugin Framework
- **Feasibility**: Medium
- **Implementation Complexity**: High
- **Maintenance Burden**: High
- **Capabilities**: High flexibility with better abstraction
- **Recommended For**: Research tools, experimental analyzers

### 3.5 Cargo Build Scripts
- **Feasibility**: High
- **Implementation Complexity**: Low
- **Maintenance Burden**: Low
- **Capabilities**: External tool integration only
- **Recommended For**: SMT solver integration, external verifiers

---

## 4. Recommended Integration Strategy

### For the Rust-FV Project:

**Multi-Layer Approach** (combining multiple techniques):

1. **Layer 1: User Interface (Procedural Macros)**
   - Use procedural macros for contract annotations
   - Stable, easy to use, minimal maintenance
   - Example: `#[requires(...)]`, `#[ensures(...)]`, `#[invariant(...)]`

2. **Layer 2: Analysis (MIR Analysis or rustc_plugin)**
   - Use rustc_plugin framework for MIR extraction and analysis
   - Leverage type information and borrow checking results
   - Generate verification conditions from MIR

3. **Layer 3: Verification Backend (Cargo Integration)**
   - Use build scripts to invoke SMT solvers
   - Generate verification reports
   - Integrate with CI/CD pipelines

**Rationale**:
- Procedural macros provide stable user interface
- rustc_plugin gives semantic analysis without full driver complexity
- Cargo integration enables external tool usage
- Separation of concerns allows independent evolution
- Can start simple and add complexity as needed

---

## 5. Implementation Considerations

### 5.1 Compiler Version Management
- Pin specific nightly version for MIR-level integration
- Document required Rust version in rust-toolchain.toml
- Plan for periodic updates to track compiler changes

### 5.2 Query System Integration
- Leverage rustc's query system for caching
- Use hooks for downstream crate integration
- Register custom providers for verification queries

**References**:
- [Queries: Demand-driven Compilation](https://rustc-dev-guide.rust-lang.org/query.html)
- [TyCtxt Documentation](https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/ty/struct.TyCtxt.html)

### 5.3 Borrow Checker Integration
- Access borrow checking results via mir_borrowck query
- Leverage region inference for ownership verification
- Use MIR passes that run after borrowck for verification

**References**:
- [MIR Borrowck Integration](https://doc.rust-lang.org/stable/nightly-rustc/rustc_borrowck/index.html)

### 5.4 Testing and Validation
- Create test suite with verified and unverified code
- Use compiletest for integration testing
- Validate against existing verification benchmarks

---

## 6. Example Projects and References

### Active Verification Projects:
- **Prusti**: Deductive verification with Viper backend
- **Creusot**: Deductive verification with Why3 backend
- **Kani**: Bounded model checking with CBMC
- **MIRAI**: Abstract interpretation at MIR level
- **Verus**: Verification-first language built on Rust

### Compiler Integration Examples:
- **Clippy**: Standard linter with HIR/MIR analysis
- **Flowistry**: Information flow analysis tool
- **Aquascope**: Borrow checker visualization
- **Miri**: MIR interpreter for undefined behavior detection

---

## 7. Conclusion

The Rust compiler provides multiple integration points for formal verification tools, ranging from lightweight procedural macros to deep compiler integration via custom drivers. The recommended approach for rust-fv is a multi-layer architecture:

1. Procedural macros for stable annotation syntax
2. rustc_plugin or MIR passes for semantic analysis
3. Cargo build scripts for SMT solver integration

This approach balances:
- **Usability**: Stable user-facing API via procedural macros
- **Capability**: Deep semantic analysis via MIR access
- **Maintainability**: Structured integration with clear boundaries
- **Flexibility**: Can evolve from simple to complex as needed

The existence of successful verification tools (Prusti, Creusot, Kani, MIRAI) demonstrates the technical feasibility of this approach, while the active development community and POPL 2026 tutorials show ongoing innovation in this space.

---

## Sources

### Compiler Plugins and Architecture
- [Current State of Compiler Plugins](https://users.rust-lang.org/t/current-state-of-compiler-plugins-for-rust/131439)
- [rustc_plugin Framework - Cognitive Engineering Lab](https://github.com/cognitive-engineering-lab/rustc_plugin)
- [rustc_plugin - Viper Project](https://github.com/viperproject/rustc-plugin)
- [Compiler Plugins - Rust Unstable Book](https://dev-doc.rust-lang.org/beta/unstable-book/language-features/plugin.html)

### MIR and Analysis Passes
- [The MIR (Mid-level IR)](https://rustc-dev-guide.rust-lang.org/mir/index.html)
- [MIR Passes and Queries](https://rustc-dev-guide.rust-lang.org/mir/passes.html)
- [rustc_middle Documentation](https://doc.rust-lang.org/stable/nightly-rustc/rustc_middle/index.html)
- [MIRAI: Rust MIR Abstract Interpreter](https://github.com/facebookexperimental/MIRAI)
- [Introducing MIR](https://blog.rust-lang.org/2016/04/19/MIR.html)

### Procedural Macros
- [Procedural Macros - The Rust Reference](https://doc.rust-lang.org/reference/procedural-macros.html)
- [Master Rust Macros in 2026](https://itch.io/blog/1150454/master-rust-macros-in-2026-a-complete-guide-to-metaprogramming-for-efficient-and-safe-code)
- [Procedural Macros Handbook](https://www.freecodecamp.org/news/procedural-macros-in-rust/)

### Rustc Driver and Custom Compilation
- [rustc_driver and rustc_interface](https://rustc-dev-guide.rust-lang.org/rustc-driver/intro.html)
- [Building your own rustc_driver](https://jyn.dev/rustc-driver/)
- [rustc_interface::passes](https://doc.rust-lang.org/stable/nightly-rustc/rustc_interface/passes/index.html)
- [Overview of the Compiler](https://rustc-dev-guide.rust-lang.org/overview.html)

### Cargo Build System
- [Build Scripts - The Cargo Book](https://doc.rust-lang.org/cargo/reference/build-scripts.html)
- [External Tools - The Cargo Book](https://doc.rust-lang.org/cargo/reference/external-tools.html)
- [Cargo Build System Guide](https://rust-lang.github.io/rust-enhanced/build/index.html)

### Formal Verification Tools
- [Rust Formal Methods Interest Group](https://rust-formal-methods.github.io/)
- [The Prusti Project](https://link.springer.com/chapter/10.1007/978-3-031-06773-0_5)
- [Creusot at POPL 2026](https://popl26.sigplan.org/details/POPL-2026-tutorials/6/Creusot-Formal-verification-of-Rust-programs)
- [Expanding Rust Formal Verification Ecosystem](https://rustfoundation.org/media/expanding-the-rust-formal-verification-ecosystem-welcoming-esbmc/)
- [High Assurance Rust Tools](https://highassurance.rs/chp16_appendix/tools.html)

### Clippy Architecture
- [Clippy GitHub Repository](https://github.com/rust-lang/rust-clippy)
- [Write Rust Lints Without Forking Clippy](https://blog.trailofbits.com/2021/11/09/write-rust-lints-without-forking-clippy/)
- [Clippy Documentation](https://doc.rust-lang.org/clippy/)

### Query System and TyCtxt
- [Queries: Demand-driven Compilation](https://rustc-dev-guide.rust-lang.org/query.html)
- [Query Evaluation Model](https://rustc-dev-guide.rust-lang.org/queries/query-evaluation-model-in-detail.html)
- [TyCtxt Documentation](https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/ty/struct.TyCtxt.html)

---

**Document Version**: 1.0
**Research Date**: February 10, 2026
**Author**: AI Hive(R)
