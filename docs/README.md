# Research Documentation

This directory contains comprehensive research on formal verification for Rust.

## Overview

Read documents in this order:

1. **[00-SYNTHESIS.md](00-SYNTHESIS.md)** ⭐ **START HERE**
   - Executive summary and recommendations
   - Architecture decisions
   - Phased implementation plan
   - Next steps

2. **[formal_verification_research_summary.md](formal_verification_research_summary.md)**
   - Formal verification approaches (SMT, proof assistants, model checkers)
   - Existing Rust tools (Verus, Kani, Prusti, Creusot)
   - Success stories and limitations
   - Recommended approach

3. **[compiler-integration-research.md](compiler-integration-research.md)**
   - Rust compiler integration strategies
   - Procedural macros, MIR analysis, custom drivers
   - Multi-layer architecture recommendations
   - Example implementations

4. **[specification-language-research.md](specification-language-research.md)**
   - Specification language design
   - Handling ownership, lifetimes, mutable borrows
   - Prophecy operators and syntax proposals
   - Rust-specific approaches

5. **[proof-automation-strategies.md](proof-automation-strategies.md)**
   - Automated theorem proving techniques
   - Verification condition generation
   - Expected automation levels
   - Manual proof effort requirements

## Quick Start

For implementation work:
1. Read 00-SYNTHESIS.md for architecture and plan
2. Reference specific research docs for detailed decisions
3. Follow the phased implementation timeline

## Research Date

All research conducted: February 10, 2026
Sources: Academic papers, tool documentation, industry blogs (2024-2026)
