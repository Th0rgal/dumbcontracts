# Trust Assumptions and Verification Boundaries

This document states, in a formal and current way, what Verity proves and what Verity still trusts.

## Scope

Verity has two compilation paths:

1. `ContractSpec` path (proof-backed): `EDSL -> ContractSpec -> IR -> Yul -> solc -> bytecode`
2. AST path (`--ast`): `Unified AST -> Yul -> solc -> bytecode`

The formal Layer 1/2/3 guarantees apply to the `ContractSpec` path.

## Verification Chain

```
EDSL
  ↓ [Layer 1: FULLY VERIFIED]
ContractSpec
  ↓ [Layer 2: FULLY VERIFIED]
IR
  ↓ [Layer 3: FULLY VERIFIED, 1 axioms]
Yul
  ↓ [trusted external compiler]
EVM Bytecode
```

## Current Verified Facts

- Layer 1 (EDSL -> ContractSpec) is proven in Lean.
- Layer 2 (ContractSpec -> IR) is proven in Lean.
- Layer 3 (IR -> Yul) is proven in Lean except for one documented axiom.
- Unified AST equivalence proofs exist for migrated example contracts, but AST code generation is not yet inside the same end-to-end proof chain as ContractSpec compilation.

Metrics tracked by repository tooling:

- 431 theorems across 11 categories.
- 250 theorems have corresponding Foundry property tests.
- 58% runtime test coverage.

(These values are validated by `scripts/check_doc_counts.py` against `artifacts/verification_status.json`.)

## Trusted Components

### 1. Solidity Compiler (`solc`)

- Role: compiles Yul to EVM bytecode.
- **Version**: 0.8.33+commit.64118f21 (pinned).
- Status: trusted external tool, version pinned in `foundry.toml` (`solc_version = "0.8.33"`).
- Mitigation: CI enforces pin and Yul compileability checks.

### 2. Keccak-based Selector Computation

- Role: function selector derivation from signatures.
- Status: one explicit axiom in `Compiler/Selectors.lean` (see `AXIOMS.md`).
- Mitigation: CI selector cross-checks against `solc --hashes` and fixtures.

### 3. Linked Yul Libraries

- Role: external functions injected by linker.
- Status: outside formal semantic proofs.
- What is enforced: duplicate-name, collision, unresolved reference, and arity checks.
- What is trusted: semantic correctness of linked Yul code.

### 4. Mapping Slot Modeling Scope (Current Proof Backend)

- Role: proof interpreters currently use a verification-level tagged mapping model (`Compiler/Proofs/MappingSlot.lean`, `activeMappingSlotBackend = .tagged`) rather than keccak-derived flat storage slots.
- Implementation note: the dormant `.keccak` branch now computes Solidity slots via `solidityMappingSlot := keccak256(abi.encode(key, baseSlot))`, but this is not yet the active proof scope.
- Status: explicit modeling scope boundary; not yet fully EVM-faithful for mapping slot addressing.
- Mitigation: strict abstraction-boundary CI (`scripts/check_mapping_slot_boundary.py`) and explicit migration tracking in issue #259.

### 5. EVM Semantics and Gas

- Role: runtime execution model.
- Status: trusted EVM behavior; gas is not formally modeled by current proofs.
- Implication: semantic correctness does not imply gas-safety or gas-bounded liveness.

### 6. Foundational Lean Trust

- Role: proof checker and kernel soundness.
- Status: foundational assumption for all Lean-based verification.

## Semantic Caveats Auditors Must Track

### Wrapping Arithmetic

`Uint256` arithmetic in the formal model is wrapping modulo `2^256`. If Solidity parity requires checked overflow behavior, contracts must encode explicit checks.

### Revert-State Modeling

High-level semantics can expose intermediate state in a reverted computation model. EVM runtime reverts discard state. Contracts should preserve checks-before-effects discipline.

### AST Path Assurance Level

AST compilation (`--ast`) is tested and drift-checked, but not yet proven with the same end-to-end semantic preservation proofs as the `ContractSpec` path.

## Security Audit Checklist

1. Confirm whether deployment uses ContractSpec path, AST path, or both.
2. Review `AXIOMS.md` and ensure the axiom list is unchanged and justified.
3. If linked libraries are used, audit each linked Yul file as trusted code.
4. Validate selector checks, Yul compile checks, and storage-layout checks in CI.
5. Confirm arithmetic and revert assumptions are explicitly acceptable for the target contract.
6. For production readiness, include gas profiling and upper-bound testing.

## Change Control Requirement

Any source change that affects architecture, semantics, trust boundary, or CI safeguards must update this file in the same change set.

If this file is stale, audit conclusions may be invalid.

## Related Documents

- [AUDIT.md](AUDIT.md)
- [AXIOMS.md](AXIOMS.md)
- [docs/ROADMAP.md](docs/ROADMAP.md)
- [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md)

**Last Updated**: 2026-02-23
**Maintainer Rule**: Update on every trust-boundary-relevant code change.
