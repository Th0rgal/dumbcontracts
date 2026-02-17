# External Library Examples

This directory contains example Yul library files that can be linked with Verity at compile time.

## Files

- **PoseidonT3.yul**: Placeholder Poseidon hash function for 2 inputs
- **PoseidonT4.yul**: Placeidon hash function for 3 inputs (1 input + padding)

## Quick Usage

Compile a contract with external library linking:

```bash
lake exe verity-compiler \
    --link examples/external-libs/PoseidonT3.yul \
    --link examples/external-libs/PoseidonT4.yul \
    -o compiler/yul
```

## Complete Guide

For a comprehensive guide on using external libraries, see the [Linking External Libraries](https://verity.dev/guides/linking-libraries) documentation.

The guide covers:
- Writing library files
- Creating Lean placeholders
- Adding external calls to your ContractSpec
- Validation and error handling
- Trust model considerations

## Note

These are **placeholder implementations** for demonstration purposes. In production, you would use:

1. Real Poseidon hash implementations from audited libraries
2. Groth16 verification functions from audited zk-SNARK libraries
3. Other cryptographic primitives from trusted sources

The key benefit is that you can prove properties about your contract logic using simple placeholders in Lean, then link with production-grade cryptographic implementations at compile time.

## Validation

The Linker performs several safety checks (see `Compiler/Linker.lean`):

1. **Duplicate names**: Detects if two libraries define the same function
2. **Name collisions**: Catches libraries that shadow generated code or Yul builtins
3. **External references**: Ensures all function calls are resolved by linked libraries
4. **Arity matching**: Validates that call sites match library function signatures

If validation fails, you'll get clear error messages:

```
Unresolved external references: myHash
Library function(s) shadow Yul builtins: add
Arity mismatch: myFunc called with 2 args but library defines 3 params
```

## Trust Model

External libraries are **outside the formal verification boundary**. Your Lean proofs verify the contract logic against placeholders. You must:

1. Use audited, battle-tested library implementations
2. Add Foundry tests that exercise linked contracts end-to-end
3. Document the trust assumption (see [TRUST_ASSUMPTIONS.md](https://github.com/Th0rgal/verity/blob/main/TRUST_ASSUMPTIONS.md#5-external-library-code-linker))
