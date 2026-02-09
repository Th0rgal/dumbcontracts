# Roadmap (Lean-Only)

## Goal

Write very small specs in Lean, implement them in Lean, prove correctness, and
compile to valid Ethereum bytecode (via Yul) with a semantic preservation story.

## Milestone 1: Lean Contract Core

- Define a minimal contract state model (storage maps, balances, events/logs).
- Define msg context (sender, value, block) and execution context.
- Add reusable lemmas for frame conditions and invariants.

## Milestone 2: Spec/Impl/Proof Library

- Provide a small library of spec combinators (requires, ensures, modifies).
- Provide proof helpers for common patterns (transfer, mint, borrow/repay).
- Extend the Lean-only prototype to cover the token and lending examples.

## Milestone 3: Lean AST + Semantics

- Define a Lean AST subset for implementations.
- Define a small-step semantics for the subset (Env + storage).
- Extend semantics with calldata + return data modeling.
- Add proof helpers that connect the subset semantics to specs.

## Milestone 4: Lean -> Yul Compiler Skeleton

- Define a Yul AST and a pretty-printer.
- Emit Yul from the Lean AST subset.
- Compile Yul with `solc --strict-assembly`.
- Add minimal ABI dispatcher and 32-byte return encoding.

## Milestone 5: Semantic Preservation (Subset)

- Prove compiler correctness for the initial subset (arith + map updates + if/else).
- Validate with small end-to-end examples (transfer, mint, borrow).

## Milestone 6: Expand Coverage

- Add events/logs and error/revert handling.
- Add loops and bounded quantifiers.
- Expand the Yul subset until it covers the example suite.

## Milestone 7: EVM-Level Anchoring (Optional)

- Connect to an EVM semantics framework (e.g., KEVM/Act/Kontrol) for stronger guarantees.
