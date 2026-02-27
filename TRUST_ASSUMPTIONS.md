# Trust Assumptions and Verification Boundaries

This document states, in a formal and current way, what Verity proves and what Verity still trusts.

## Scope

Verity uses a single supported compilation path:

1. `ContractSpec` path (proof-backed): `EDSL -> ContractSpec -> IR -> Yul -> solc -> bytecode`

The formal Layer 1/2/3 guarantees apply to this path.

## Verification Chain

```
EDSL
  ↓ [Layer 1: FULLY VERIFIED]
ContractSpec
  ↓ [Layer 2: FULLY VERIFIED]
IR
  ↓ [Layer 3: FULLY VERIFIED, 1 axiom]
Yul
  ↓ [trusted external compiler]
EVM Bytecode
```

## Current Verified Facts

- Layer 1 (EDSL -> ContractSpec) is proven in Lean.
- Layer 2 (ContractSpec -> IR) is proven in Lean.
- Layer 3 (IR -> Yul) is proven in Lean except for one documented axiom.
- Unified AST equivalence proofs for migrated examples remain useful migration artifacts, but they are not a supported compiler backend path.

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

### 4. Mapping Slot Derivation and Crypto Assumptions

- Role: proof interpreters derive mapping slots with Solidity-compatible keccak hashing (`Compiler/Proofs/MappingSlot.lean`, `activeMappingSlotBackend = .keccak`), i.e. `solidityMappingSlot(base,key) = keccak256(abi.encode(key, baseSlot))`.
- Status: mapping addressing is EVM-faithful (flat storage addressing, no tagged slot abstraction in active semantics).
- Trust boundary: this relies on the external keccak implementation (`ffi.KEC` via EVMYul FFI) and standard collision-resistance assumptions for keccak256 (the same trust class as Solidity/EVM behavior).
- Mitigation: abstraction-boundary CI (`scripts/check_mapping_slot_boundary.py`), selector/hash cross-check CI, and explicit documentation in `AXIOMS.md`.

### 5. EVM Semantics and Gas

- Role: runtime execution model.
- Status: trusted EVM behavior; gas is not formally modeled by current proofs.
- Implication: semantic correctness does not imply gas-safety or gas-bounded liveness.

### 6. External Call Modules (ECMs)

- Role: reusable external call patterns (ERC-20 transfers, precompile calls, callbacks, generic ABI calls).
- Status: standard modules in `Compiler/Modules/` are maintained alongside the compiler.
- Trust boundary: the compiler trusts that `mod.compile` produces Yul that correctly implements the pattern described by the module's name, documentation, and axioms.
- Scope: a bug in one module does not affect contracts that don't use it.
- Third-party ECMs (external Lean packages) are outside the Verity team's trust boundary.
- Mitigation: ECM axioms are aggregated and reported at compile time (`--verbose`). Module-level validation (selector bounds, parameter checks) runs within the `compile` function. View/pure mutability enforcement uses `writesState`/`readsState` flags.
- See `docs/EXTERNAL_CALL_MODULES.md` and `AXIOMS.md` for details.

### 7. Foundational Lean Trust

- Role: proof checker and kernel soundness.
- Status: foundational assumption for all Lean-based verification.

### 8. ECM Interface Assumptions

- Role: trust that external contracts/precompiles conform to their declared ABI.
- Status: documented per-module in `AXIOMS.md` and aggregated at compile time.
- Scope: opt-in per contract — only contracts using a given ECM inherit its assumptions.
- Mitigation: axiom aggregation report, code review of standard modules.

## Semantic Caveats Auditors Must Track

### Wrapping Arithmetic

`Uint256` arithmetic in the formal model is wrapping modulo `2^256`. If Solidity parity requires checked overflow behavior, contracts must encode explicit checks.

### Revert-State Modeling

High-level semantics can expose intermediate state in a reverted computation model. EVM runtime reverts discard state. Contracts should preserve checks-before-effects discipline.

### AST Migration Artifacts

Unified AST artifacts are maintained for migration/interop and proof engineering. They are not a productized compilation backend.

## Security Audit Checklist

1. Confirm deployment uses the `ContractSpec` (`CompilationModel`) path.
2. Review `AXIOMS.md` and ensure the axiom list is unchanged and justified.
3. If linked libraries are used, audit each linked Yul file as trusted code.
4. Validate selector checks, Yul compile checks, and storage-layout checks in CI.
5. Confirm arithmetic and revert assumptions are explicitly acceptable for the target contract.
6. For production readiness, include gas profiling and upper-bound testing.
7. Review ECM axiom report (`--verbose`) and confirm all module trust assumptions are acceptable.
8. If third-party ECMs are used, audit their `AXIOMS.md` and `compile` implementations.

## Change Control Requirement

Any source change that affects architecture, semantics, trust boundary, or CI safeguards must update this file in the same change set.

If this file is stale, audit conclusions may be invalid.

## Related Documents

- [AUDIT.md](AUDIT.md)
- [AXIOMS.md](AXIOMS.md)
- [docs/EXTERNAL_CALL_MODULES.md](docs/EXTERNAL_CALL_MODULES.md)
- [docs/ROADMAP.md](docs/ROADMAP.md)
- [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md)

**Last Updated**: 2026-02-25
**Maintainer Rule**: Update on every trust-boundary-relevant code change.
