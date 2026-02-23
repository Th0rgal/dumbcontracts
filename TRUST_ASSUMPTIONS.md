# Trust Assumptions and Verification Boundaries

This document defines what Verity proves and what Verity still trusts.

## Scope

Verity supports two compilation paths:

1. `ContractSpec` path (proof-backed): `EDSL -> ContractSpec -> IR -> Yul -> solc -> bytecode`
2. AST path (`--ast`): `Unified AST -> Yul -> solc -> bytecode`

End-to-end Layer 1/2/3 semantic guarantees apply to the `ContractSpec` path.

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

## Verified Facts

- Layer 1 (`EDSL -> ContractSpec`) is proven in Lean.
- Layer 2 (`ContractSpec -> IR`) is proven in Lean.
- Layer 3 (`IR -> Yul`) is proven in Lean, except for one axiom.
- AST migration proofs exist for selected contracts, but AST codegen is not in the same full proof chain as `ContractSpec`.

Repository-tracked metrics (validated by `scripts/check_doc_counts.py` against `artifacts/verification_status.json`):

- 431 theorems across 11 categories.
- 250 theorems have corresponding Foundry property tests.
- 58% runtime test coverage.

## Trusted Components

### 1. Solidity compiler (`solc`)

- Role: compiles Yul to EVM bytecode.
- Status: trusted external component.
- Pin: `foundry.toml` (`solc_version = "0.8.33"`).
- Mitigation: version pin and Yul compile checks in CI.

### 2. Keccak selector computation

- Role: derives function selectors from signatures.
- Status: one explicit axiom in `Compiler/Selectors.lean`.
- Mitigation: CI cross-checks against `solc --hashes` and selector fixtures.

### 3. Linked Yul libraries

- Role: provide externally linked functions.
- Status: outside formal semantic proofs.
- Enforced checks: duplicate-name, collision, unresolved reference, and arity checks.
- Trusted part: linked library semantics.

### 4. Mapping slot collision freedom

- Role: mapping layout uses keccak-derived addressing.
- Status: standard Ethereum assumption.
- Mitigation: layout checks and explicit documentation.

### 5. EVM semantics and gas

- Role: runtime execution model.
- Status: EVM behavior trusted; gas not formally modeled.
- Consequence: semantic correctness does not imply gas safety or gas-bounded liveness.

### 6. Lean kernel and toolchain soundness

- Role: foundational basis for proof validity.
- Status: trusted.

## Semantic Caveats

### Wrapping arithmetic

`Uint256` arithmetic is modulo `2^256` in the model. Checked overflow behavior must be encoded explicitly when required.

### Revert-state modeling

High-level semantics may expose intermediate reverted state. EVM runtime discards reverted state. Contracts should follow checks-before-effects.

### AST assurance level

AST compilation is tested and drift-checked, but not proven in the same end-to-end semantic chain as `ContractSpec` compilation.

## Audit Checklist

1. Identify active compilation path(s) for the target deployment.
2. Review `AXIOMS.md`; verify the axiom set is minimal and justified.
3. Audit linked Yul libraries as trusted code when present.
4. Verify selector, Yul compileability, and layout checks in CI.
5. Confirm arithmetic and revert assumptions are acceptable for the target.
6. Add gas profiling and upper-bound testing for production readiness.

## Change Control Requirement

Any code change that affects architecture, semantics, trust boundaries, axioms, or CI safety checks must update this file in the same change set.

If this file is stale, trust analysis is stale.

## Related Documents

- [AUDIT.md](AUDIT.md)
- [AXIOMS.md](AXIOMS.md)
- [docs/ROADMAP.md](docs/ROADMAP.md)
- [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md)

**Last Updated**: 2026-02-23
**Maintainer Rule**: Update on every trust-boundary-relevant change.
