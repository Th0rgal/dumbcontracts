# Audit Guide

Read this file first. It gives the minimum architecture and trust model needed to audit Verity.

For formal detail, see [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md) and [AXIOMS.md](AXIOMS.md).

## Architecture Overview

Verity has two compilation paths:

1. `EDSL -> ContractSpec -> IR -> Yul -> solc -> bytecode` (proof-backed path)
2. `Unified AST (--ast) -> Yul -> solc -> bytecode` (migration path)

Formal semantic guarantees apply to Path 1. Path 2 is implemented and tested, but not in the same end-to-end proof chain.

### Terms You Must Separate

Audits are much easier when these names are not mixed:

1. `EDSL` (`Verity/Examples/*`): executable Lean contract code (`Contract α := ContractState -> ContractResult α`).
2. `Logical spec` (`Verity/Specs/*/Spec.lean`): properties as `Prop`.
3. `ContractSpec` (`Compiler/ContractSpec.lean`, instances in `Compiler/Specs.lean`): declarative compiler model with function bodies. This is not ABI-only data.

`ContractSpec` contains:
1. Interface metadata (name, params, returns, mutability, events).
2. Storage field declarations.
3. Function and constructor bodies (`Expr` and `Stmt`) used by the compiler.

### Why Path 2 Exists

Path 2 is not a replacement for Path 1 today. It exists for controlled migration and cross-checking.

Simple reasons:

1. It is the target architecture for the unification effort (`Compiler/ASTSpecs.lean`, `Compiler/ASTDriver.lean`).
2. It gives an independent compiler implementation, which helps detect regressions that can hide inside one pipeline.
3. It keeps migration incremental: contracts can move to unified AST without blocking the verified ContractSpec flow.

Where it is used now:

1. CLI path selection in `Compiler/Main.lean` via `--ast`.
2. CI generation of AST artifacts into `compiler/yul-ast` (`.github/workflows/verify.yml`).
3. AST pipeline regression modules: `Compiler/ASTCompileTest.lean`, `Compiler/ASTDriverTest.lean`, `Compiler/MainTest.lean`.
4. Cross-path checks:
   - `scripts/check_selectors.py` (selector consistency in `compiler/yul` and `compiler/yul-ast`)
   - `scripts/check_storage_layout.py` (EDSL/Spec/Compiler/AST slot drift)
   - `scripts/check_yul_compiles.py --compare-dirs ... --allow-compare-diff-file ...` (compileability plus controlled diff baseline)
   - `scripts/check_gas_model_coverage.py` on legacy, patched, and AST outputs

When Path 2 is useful during limitations:

1. During feature migration to unified AST, before full proof integration is complete.
2. When validating that ABI, storage, and dispatch behavior stay aligned across two compiler front-ends.
3. When investigating whether a bug is in ContractSpec lowering or in later shared Yul/solc stages.

Bug classes Path 2 helps catch:

1. Selector and dispatch table mismatches.
2. Constructor/deploy path regressions.
3. ABI mutability metadata drift (`isPayable`, `isView`, `isPure`).
4. Storage slot/type mismatches between layers.
5. Yul shape drift that breaks `solc` compileability or violates the known diff allowlist.

Why not keep only Path 1:

1. One path gives one failure signal; two paths provide differential evidence.
2. Removing Path 2 would reduce migration safety for the unification roadmap.
3. Several CI guards are designed to detect cross-path drift; those checks lose value without a second concrete pipeline.

## Verification Layers (Path 1)

- Layer 1: EDSL behavior matches `ContractSpec` behavior (proven per contract).
- Layer 2: `ContractSpec` lowering to IR preserves behavior (proven).
- Layer 3: IR lowering to Yul preserves behavior (proven, with one documented axiom).
- `solc`: trusted external compiler.

## Current Code Structure

### ContractSpec path

- `Verity/`: EDSL contracts and proofs.
- `Compiler/ContractSpec.lean`: spec validation and lowering.
- `Compiler/Codegen.lean`: IR to Yul AST lowering.
- `Compiler/Yul/PrettyPrint.lean`: Yul text rendering.

### AST path (`--ast`)

- `Verity/AST.lean`: unified AST.
- `Compiler/ASTCompile.lean`: AST statement compilation.
- `Compiler/ASTDriver.lean`: AST pipeline orchestration and ABI generation.

Current AST status:

- Implemented and tested.
- Supports mutability metadata (`isPayable`, `isView`, `isPure`) in specs and ABI.
- Not yet covered by the same Layer 2 and 3 proof chain as `ContractSpec`.

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
4. AST and ContractSpec drift: review allowlist-backed differences explicitly.

## Minimal Audit Checklist

1. Confirm which path is used (`ContractSpec`, AST, or both).
2. Read `AXIOMS.md`; verify the axiom set is minimal and justified.
3. Read `TRUST_ASSUMPTIONS.md`; confirm deployment assumptions are acceptable.
4. Run selector, Yul compileability, storage-layout, and doc consistency checks.
5. If libraries are linked, include them in scope as TCB code.

## Writing Suggestions for This File

1. Keep this file as orientation, not a proof transcript.
2. Use short sections with concrete file references.
3. Keep all counts script-backed (`check_doc_counts.py`).
4. Update this file in the same PR as any architecture or trust change.
