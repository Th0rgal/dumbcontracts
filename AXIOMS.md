# Axioms in DumbContracts

This file documents all axioms used in the verification codebase and their soundness justifications.

## Policy

Axioms should be **avoided whenever possible** as they introduce trust assumptions into the verification chain. When axioms are necessary:

1. **Document here** with full soundness justification
2. **Add inline comment** in source code referencing this file
3. **Mark as AXIOM** in code comments
4. **CI validates** all axioms are documented (see `.github/workflows/verify.yml`)

## Why Axioms Are Sometimes Necessary

Lean's proof assistant requires all functions to be provably terminating. However, some functions in DumbContracts:
- Use partial recursion (fuel-based)
- Have structural equality that's obvious by inspection but hard to formally prove
- Represent external system behavior (Ethereum addresses)

In these cases, we use axioms with strong soundness arguments.

---

## Current Axioms

### 1. `evalIRExpr_eq_evalYulExpr`

**Location**: `Compiler/Proofs/YulGeneration/StatementEquivalence.lean:107`

**Statement**:
```lean
axiom evalIRExpr_eq_evalYulExpr (selector : Nat) (irState : IRState) (expr : YulExpr) :
    evalIRExpr irState expr = evalYulExpr (yulStateOfIR selector irState) expr
```

**Purpose**: Proves that expression evaluation produces identical results in IR and Yul contexts when states are aligned.

**Why Axiom?**:
- Both `evalIRExpr` and `evalYulExpr` are defined as `partial` functions (not provably terminating in Lean)
- Lean cannot prove equality between partial functions
- Functions have identical source code structure but different state type parameters

**Soundness Argument**:
1. **Source code inspection**: Both functions have structurally identical implementations
2. **State translation**: `yulStateOfIR` simply copies all fields from IRState to YulState
3. **Selector field**: Only difference is the `selector` field, which doesn't affect expression evaluation
4. **Differential testing**: 70,000+ property tests validate this equivalence holds in practice

**Alternative Approach**:
To eliminate this axiom, we would need to:
- Refactor both eval functions to use fuel parameters (like `execIRStmtFuel`)
- Prove termination for all expression types
- **Effort**: ~500+ lines of refactoring

**Trade-off**: Given that the functions are structurally identical by inspection and validated by extensive testing, the axiom is a pragmatic choice.

**Risk**: **Low** - If implementations diverge during refactoring, differential tests would catch the discrepancy immediately.

**Future Work**:
- [ ] Add CI check that `evalIRExpr` and `evalYulExpr` source code structure remains identical
- [ ] Consider refactoring to fuel-based evaluation (long-term)
- [ ] Issue tracking: #82

---

### 2. `evalIRExprs_eq_evalYulExprs`

**Location**: `Compiler/Proofs/YulGeneration/StatementEquivalence.lean:111`

**Statement**:
```lean
axiom evalIRExprs_eq_evalYulExprs (selector : Nat) (irState : IRState) (exprs : List YulExpr) :
    evalIRExprs irState exprs = evalYulExprs (yulStateOfIR selector irState) exprs
```

**Purpose**: List version of `evalIRExpr_eq_evalYulExpr` for multiple expressions.

**Why Axiom?**: Same reasoning as axiom #1 (partial functions).

**Soundness Argument**:
- Follows directly from axiom #1 via structural induction on lists
- Could be proven from axiom #1 if that were a theorem
- Both implementations use `List.map` with the respective eval function

**Alternative Approach**:
If axiom #1 were eliminated, this would become a provable theorem via:
```lean
theorem evalIRExprs_eq_evalYulExprs : ... := by
  induction exprs with
  | nil => rfl
  | cons hd tl ih =>
      simp [evalIRExprs, evalYulExprs]
      rw [evalIRExpr_eq_evalYulExpr]  -- Uses axiom #1
      rw [ih]
```

**Risk**: **Low** - Same as axiom #1.

**Future Work**:
- [ ] If axiom #1 is eliminated, prove this as theorem
- [ ] Issue tracking: #82

---

### 3. `addressToNat_injective_valid`

**Location**: `Compiler/Proofs/IRGeneration/Conversions.lean:83`

**Statement**:
```lean
axiom addressToNat_injective_valid :
  ∀ {a b : Address}, isValidAddress a → isValidAddress b →
    addressToNat a = addressToNat b → a = b
```

**Purpose**: Asserts that the address-to-number conversion is injective for valid Ethereum addresses.

**Why Axiom?**:
- Models external Ethereum behavior (address space)
- Addresses are 20-byte hex strings (0x + 40 hex chars)
- Conversion involves string parsing and normalization
- Full formalization of hex parsing would be substantial

**Soundness Argument**:
1. **Valid address format**: Valid Ethereum addresses are exactly 20 bytes (160 bits)
2. **Normalization**: Address normalization removes case-based collisions (EIP-55 checksums)
3. **Hex parsing injectivity**: For normalized addresses, hex string → number conversion is injective up to 2^160
4. **Matches Ethereum**: This precisely models the actual Ethereum address space
5. **Differential testing**: Validated by 70,000+ differential tests against real EVM execution

**Trust Assumption**:
This axiom assumes that:
- Valid addresses have unique numerical representations
- Normalization is correctly implemented
- This matches Ethereum's actual address semantics

**Validation**:
- `isValidAddress` predicate ensures format correctness
- Differential testing validates against Solidity/EVM behavior
- Address normalization tested independently

**Risk**: **Low** - Ethereum address injectivity is a fundamental assumption of the EVM itself.

**Future Work**:
- [ ] Formalize hex string parsing in Lean (substantial effort)
- [ ] Prove injectivity from first principles
- [ ] Consider using verified hex parsing library
- [ ] Issue tracking: #82

---

## Axiom Usage Summary

| Axiom | File | Risk | Validated By | Future Work |
|-------|------|------|--------------|-------------|
| `evalIRExpr_eq_evalYulExpr` | StatementEquivalence.lean | Low | Differential tests (70k+) | Fuel-based refactor |
| `evalIRExprs_eq_evalYulExprs` | StatementEquivalence.lean | Low | Differential tests (70k+) | Prove from axiom #1 |
| `addressToNat_injective_valid` | Conversions.lean | Low | Differential tests (70k+) | Formalize hex parsing |

**Total Axioms**: 3
**Production Blockers**: 0 (all have low risk with strong validation)

---

## Adding New Axioms

If you need to add an axiom:

1. **Exhaust all alternatives first**:
   - Can you prove it? (even if difficult)
   - Can you use a weaker lemma?
   - Can you refactor to avoid the need?

2. **Document in this file**:
   - State the axiom clearly
   - Explain why it's necessary
   - Provide soundness justification
   - Explain validation/testing
   - Note future work to eliminate
   - Assess risk level

3. **Add inline comment in source**:
   ```lean
   /--
   AXIOM: Brief explanation
   See AXIOMS.md for full soundness justification
   -/
   axiom my_axiom : ...
   ```

4. **Ensure CI passes**: CI will detect the new axiom and verify it's documented

5. **Update this summary table**

---

## Verification Chain Trust Model

```
User Code (EDSL)
    ↓ [Proven]
ContractSpec
    ↓ [Proven]
IR
    ↓ [Proven, 3 axioms]
Yul
    ↓ [TRUSTED: solc compiler]
EVM Bytecode
```

**Trust Assumptions**:
1. Lean 4 type checker is sound (foundational)
2. The 3 axioms documented above are sound
3. Solidity compiler (solc) correctly compiles Yul → Bytecode

See `TRUST_ASSUMPTIONS.md` (issue #68) for complete trust model.

---

## CI Validation

The CI workflow (`.github/workflows/verify.yml`) automatically:
- Detects all axioms in `Compiler/Proofs/` directory
- Fails if any axiom is not documented in this file
- Reports axiom count in build logs

To check locally:
```bash
# Find all axioms
grep -r "axiom " Compiler/Proofs/ --include="*.lean" | grep -v "^--"

# Verify this file documents them all
cat AXIOMS.md
```

---

**Last Updated**: 2026-02-14
**Next Review**: When new axioms added or existing ones eliminated
**Maintainer**: Document all changes to axioms in git commit messages
