# Axioms in Verity

This is the canonical registry of axioms used by Verity proofs.

## Policy

Axioms are exceptional. Each axiom must have:

1. Documentation in this file.
2. A source comment marking it as an axiom and linking here.
3. CI checks validating usage assumptions.
4. A stated elimination path when practical.

## Active Axioms

### 1. `keccak256_first_4_bytes`

**Location**: `Compiler/Selectors.lean:41`

**Statement**:
```lean
axiom keccak256_first_4_bytes (sig : String) : Nat
```

**Purpose**:
Computes ABI selectors (`bytes4(keccak256(signature))`) for dispatch.

**Reason this is an axiom**:
Selector hashing is modeled as an external cryptographic primitive, not re-proven in Lean.

**Soundness controls**:

- CI cross-checks selectors against `solc --hashes`.
- CI runs selector fixture checks.
- Build/test fails on selector drift.

**Risk**: Low.

## Historical Note

Previous axioms for IR/Yul equivalence and address injectivity were removed after totalizing interpreters and adopting bounded-nat `Address` modeling.

## Trust Summary

- Active axioms: 1
- Production blockers from axioms: 0
- Enforcement: `scripts/check_axiom_locations.py` verifies location consistency.

## Maintenance Rule

Any commit that adds, removes, renames, or moves an axiom must update this file in the same commit.

If this file is stale, trust analysis is stale.

**Last Updated**: 2026-02-23
