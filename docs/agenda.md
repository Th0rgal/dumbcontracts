# Research Agenda

## Phase 1: Problem & Landscape

- Clarify the intent vs. implementation gap with concrete historical bugs.
- Survey existing spec languages (e.g., Why3, K, Dafny, Coq, Scribble, Certora, Solidity SMTChecker) and their limitations.
- Identify the minimal DSL features that preserve auditability and avoid Turing-complete complexity.

## Phase 2: DSL Sketch & Semantics

- Define core primitives: state variables, invariants, pre/postconditions, and "hints".
- Decide execution model: state-diff proofs vs. transition proofs.
- Define safety constraints and decision procedures.

## Phase 3: Compilation & Proofs

- Determine compilation target: Solidity subset vs. direct EVM.
- Explore proof generation: proof obligations, SMT, or equivalence checking.
- Prototype a tiny end-to-end example (token transfer).

## Phase 4: Prototype MVP

- Create a reference DSL syntax and parser.
- Compile to a restricted Solidity implementation.
- Generate proof artifacts and document the pipeline.
