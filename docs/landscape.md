# Research Landscape (Lean-Only Focus)

## Lean as the Spec + Proof Language

- Lean 4 provides a single language for specifications, implementations, and proofs.
- This removes the DSL-to-proof mismatch and keeps the proof surface explicit.

## Yul as the Compilation Target

- Yul is Solidity's intermediate language and can be compiled to EVM bytecode.
- Stand-alone Yul can be compiled via `solc --strict-assembly` using object notation.
- Solidity's "via-IR" pipeline uses Yul as the IR between Solidity and bytecode.
- The `--strict-assembly` flag is the standard way to compile untyped EVM-flavored Yul.
- The deprecated `--yul` flag was for a typed dialect and is no longer relevant.

## Semantics Anchors (EVM-Level)

- KEVM provides a formal semantics for the EVM in K.
- Act is a spec language oriented around EVM state transitions with links to proof backends.
- Kontrol provides a symbolic-verification toolchain built on K/KEVM.

## Implications for Dumb Contracts

1. Lean-first specs and proofs can be compiled to Yul without a DSL in the loop.
2. Yul is a pragmatic compilation target with a clear path to bytecode.
3. KEVM/Act/Kontrol provide semantics anchors if we later want EVM-level proof alignment.

## Sources (Quick Links)

```text
https://lean-lang.org/
https://docs.soliditylang.org/en/v0.8.30/yul.html
https://docs.soliditylang.org/en/v0.8.30/yul.html#strict-assembly
https://soliditylang.org/blog/2024/07/12/a-closer-look-at-via-ir/
https://www.soliditylang.org/blog/2024/09/04/solidity-0.8.27-release-announcement/
https://ethereum.github.io/act/
https://docs.runtimeverification.com/kontrol
https://docs.runtimeverification.com/kevm/overview/repository-structure
https://github.com/runtimeverification/evm-semantics
```
