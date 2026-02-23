# Audit Guide

Read this file first. It gives the minimum architecture and trust model needed to audit Verity.

For formal detail, see [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md) and [AXIOMS.md](AXIOMS.md).

## Architecture Overview

Verity has two compilation paths:

1. `EDSL -> ContractSpec -> IR -> Yul -> solc -> bytecode` (proof-backed path)
2. `Unified AST (--ast) -> Yul -> solc -> bytecode` (migration path)

Formal semantic guarantees apply to Path 1.
Path 2 is implemented and tested, but not in the same end-to-end proof chain.

## Verification Layers (Path 1)

- Layer 1: EDSL behavior matches `ContractSpec` behavior (proven).
- Layer 2: `ContractSpec` lowering to IR preserves behavior (proven).
- Layer 3: IR lowering to Yul preserves behavior (proven, with one documented axiom).
- `solc`: trusted external compiler.

## Current Code Structure

### ContractSpec path

- `Verity/`: EDSL contracts and proofs.
- `Compiler/ContractSpec.lean`: spec validation and lowering.
- `Compiler/Codegen.lean`: IR -> Yul AST lowering.
- `Compiler/Yul/PrettyPrint.lean`: Yul text rendering.

### AST path (`--ast`)

- `Verity/AST.lean`: unified AST.
- `Compiler/ASTCompile.lean`: AST statement compilation.
- `Compiler/ASTDriver.lean`: AST pipeline orchestration and ABI generation.

Current AST status:

- Implemented and tested.
- Supports mutability metadata (`isPayable`, `isView`, `isPure`) in specs/ABI.
- Not yet covered by the same Layer 2/3 proof chain as `ContractSpec`.

## Priority Files for Auditors

- `Compiler/ContractSpec.lean`
- `Compiler/Selector.lean`
- `Compiler/Selectors.lean`
- `Compiler/Linker.lean`
- `Compiler/ASTDriver.lean`
- `Compiler/ASTCompile.lean`
- `Verity/Core.lean`
- `scripts/check_yul_compiles.py`
- `scripts/check_selectors.py`
- `scripts/check_doc_counts.py`

## Trust Boundaries

1. `solc` correctness is trusted.
2. Keccak selector hashing uses one explicit axiom (cross-checked in CI).
3. Linked external Yul libraries are trusted for semantics.
4. Mapping slot collision freedom relies on the standard keccak assumption.
5. Gas is out of scope for formal semantics.

## Main Audit Risks

1. Revert-state modeling gap at high-level semantics: confirm checks-before-effects discipline.
2. Linked Yul libraries: audit separately as trusted code.
3. Wrapping arithmetic: verify it is intended or guarded.
4. AST/ContractSpec drift: review allowlist-backed differences explicitly.

## Minimal Audit Checklist

1. Confirm which path is used (`ContractSpec`, AST, or both).
2. Read `AXIOMS.md`; verify the axiom set is minimal and justified.
3. Read `TRUST_ASSUMPTIONS.md`; confirm deployment assumptions are acceptable.
4. Run selector, Yul compileability, storage-layout, and doc consistency checks.
5. If libraries are linked, include them in scope as TCB code.

## Readability Suggestions

1. Keep this file as an orientation document, not a proof transcript.
2. Use short sections with concrete file references.
3. Keep all counts script-backed (`check_doc_counts.py`).
4. Update this file in the same PR as any architecture/trust change.
