/-!
# Function Selectors

This module defines function selectors using a keccak256 axiom with CI validation.

## Soundness

Function selectors are the first 4 bytes of keccak256(signature). While we cannot
prove keccak256 computation in Lean, we ensure correctness through:

1. **Axiom**: We axiomatize keccak256 computation
2. **CI Validation**: CI verifies all selectors match `solc --hashes` output
3. **Industry Standard**: solc is the ground truth for Solidity compilation

This approach is pragmatic and maintainable while eliminating the trust assumption
on manual selector computation.

## References

- Solidity ABI Spec: https://docs.soliditylang.org/en/latest/abi-spec.html#function-selector
- Trust Assumptions: TRUST_ASSUMPTIONS.md
-/

namespace Compiler

/-! ## Keccak256 Axiom

We axiomatize the first 4 bytes of keccak256 hash computation.

**Soundness**: This axiom is validated by CI against `solc --hashes` output.
Any mismatch between our axiom usage and solc's computation causes build failure.
-/

/-- Compute the first 4 bytes (32 bits) of keccak256(sig) as a function selector.

This is an axiom because we cannot implement keccak256 in Lean's logic.
However, it is validated by CI against solc's --hashes output.

**Example**: keccak256("transfer(address,uint256)")[:4] = 0xa9059cbb
-/
axiom keccak256_first_4_bytes (sig : String) : Nat

end Compiler
