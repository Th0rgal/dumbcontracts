# Tooling Landscape

**Focus**
- Lean-only prototype -> Yul/EVM.

**Tools**
- Lean 4
- Yul
- solc (`--strict-assembly`, `--asm`)
- EVM asm POC (opcode compare)

**External Landscape (specs + verification)**
- Act: a high-level spec language for EVM bytecode (now maintained as a GitHub project).
- Scribble: runtime spec instrumentation for Solidity (contracts are rewritten to check properties).
- Certora Prover: CVL rule specs + SMT-based verification; frequent release cadence.
- Solidity SMTChecker: built-in formal verification engine with BMC/CHC modes.
- KEVM: K framework executable semantics of the EVM (formal reference + tooling).
- Kontrol: K-framework-based proof tooling integrated with Foundry.
- VerX: contract verification toolchain.
- Move Prover: formal specs for Move (relevant for cross-chain comparisons).
