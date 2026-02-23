# Axioms in Verity

This file is the authoritative registry of axioms used by Verity proof code.

## Policy

Axioms are exceptional. When an axiom exists, it must have:

1. Explicit documentation in this file.
2. Source comment marking it as an axiom and linking to this file.
3. CI checks that validate usage assumptions.
4. A clear elimination path, when practical.

## Current Axioms

### 1. `keccak256_first_4_bytes`

**Location**: `Compiler/Selectors.lean:41`

**Statement**:
```lean
axiom keccak256_first_4_bytes (sig : String) : Nat
```

**Purpose**:
Computes function selectors (`bytes4(keccak256(signature))`) used in ABI dispatch.

**Why this is currently an axiom**:
Selector hashing is modeled as an external cryptographic primitive rather than reimplemented and proven in Lean.

**Soundness controls**:

- CI cross-checks selectors against `solc --hashes`.
- CI runs selector fixture checks to detect regressions.
- Compilation and tests fail if selector consistency drifts.

**Risk**: Low.

## Trusted Cryptographic Primitive (Non-Axiom)

### `ffi.KEC` (keccak256 via EVMYul FFI)

**Location**: used by `Compiler/Proofs/MappingSlot.lean` (`solidityMappingSlot`)

**Role**:
- Computes mapping storage slots as `keccak256(abi.encode(key, baseSlot))`.
- Aligns proof-level mapping addressing with Solidity/EVM flat storage layout.

**Why this is not listed as a Lean axiom**:
- It is a runtime external primitive (`@[extern]`-style FFI path), not a logical axiom in Lean's kernel.
- Trust is operational (correctness of linked crypto implementation), not proof-kernel extensibility.

**Operational trust assumptions**:
- Keccak implementation correctness in the linked FFI path.
- Standard collision-resistance assumptions for mapping-slot uniqueness/non-collision, matching Solidity/EVM assumptions.

**Soundness controls**:
- Mapping-slot abstraction boundary checks in CI.
- End-to-end proof/runtime regression suites that exercise mapping reads/writes through `mappingSlot`.

## Eliminated Axioms (Historical)

The repository removed prior axioms related to IR and Yul expression and statement equivalence and address injectivity by making interpreters total and by using a bounded-nat `Address` representation.

These removals reduced the active Lean axiom surface to one item.

## Trust Summary

- Active axioms: 1
- Production blockers from axioms: 0
- Enforcement: `scripts/check_axiom_locations.py` ensures this file tracks exact source location.

## Maintenance Rule

Any commit that adds, removes, renames, or moves an axiom must update this file in the same commit.

If this file is stale, trust analysis is stale.

**Last Updated**: 2026-02-23
