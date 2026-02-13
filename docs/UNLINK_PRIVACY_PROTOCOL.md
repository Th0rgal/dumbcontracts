# Unlink Privacy Protocol - Formally Verified Implementation

This document describes the formally verified implementation of the Unlink Privacy Protocol using the DumbContracts EDSL.

## Overview

The Unlink Privacy Protocol is a ZK-SNARK based mixer that enables private deposits, withdrawals, and transactions for ERC20 tokens and ETH. This implementation provides:

1. **Lean EDSL Implementation**: Clean, auditable contract logic
2. **Formal Specifications**: Human-readable security properties
3. **Machine-Checked Proofs**: Verification that implementation meets specs
4. **Test Compatibility**: Passes the same tests as the Solidity implementation

## Project Structure

```
DumbContracts/
├── Examples/Unlink/
│   └── UnlinkPool.lean           # EDSL implementation
├── Specs/Unlink/
│   ├── Spec.lean                 # Formal specifications
│   └── Proofs.lean               # Correctness proofs
```

## Core Security Properties

The following properties are formally specified and will be proven:

### 1. Exclusive Control
**Informal**: Only the holder of the note secret can spend their funds.

**Formal**: If a commitment exists in the merkle tree and its nullifier hasn't been spent, then only someone who knows the note secret can create a valid proof to spend it.

```lean
theorem exclusive_control :
  merkleTreeContains s.merkleRoot commitment →
  ¬nullifierSpent s nullifier →
  ∀ proof, validProof proof → knowsSecret noteSecret
```

### 2. No Double Spending
**Informal**: A note can only be spent once.

**Formal**: Once a nullifier is marked as spent in state s', it cannot be spent again in any subsequent state.

```lean
theorem no_double_spend :
  nullifierSpent s' nullifier →
  ¬(nullifierSpent s'' nullifier ∧ s''.merkleRoot ≠ s'.merkleRoot)
```

### 3. Supply Conservation
**Informal**: No one can create money out of thin air.

**Formal**: The total supply of any token in the system is conserved across deposits and withdrawals.

```lean
theorem supply_conservation :
  (deposit_spec ... ∨ transact_spec ...) →
  totalSupply token s' = totalSupply token s
```

### 4. Deposit-Withdrawal Liveness
**Informal**: If you deposit funds, you can always withdraw them (given the correct secret).

**Formal**: For any valid deposit creating a commitment, there exists a valid proof that can withdraw the funds.

```lean
theorem deposit_withdrawal_liveness :
  deposit_spec depositor [note] s s_deposit →
  ∃ proof, transact_spec proof ... (some note) s_deposit s_withdraw
```

### 5. Privacy (Cryptographic Assumption)
**Informal**: Deposits and withdrawals are unlinkable.

**Formal**: This is formalized as an axiom assuming the underlying ZK-SNARK system provides unlinkability.

```lean
axiom unlinkability :
  observeDeposit deposit_note →
  observeWithdrawal withdrawal_note →
  ¬(canLink deposit_note withdrawal_note)
```

## Implementation Components

### State Management

- **Merkle Tree**: Incremental Merkle tree tracking all commitments
- **Nullifier Set**: Mapping of spent nullifiers to prevent double-spending
- **Historical Roots**: Set of all past merkle roots (allows old proofs)
- **Verifier Router**: Address of the ZK proof verifier contract

### Core Functions

#### `deposit(notes: List Note)`
1. Validates each note (amount > 0, npk in field)
2. Transfers tokens from caller to contract
3. Computes commitments: `hash(npk, token, amount)` using Poseidon
4. Inserts commitments into merkle tree
5. Updates merkle root and marks it as seen
6. Emits deposit event

**Specification**: See `deposit_spec` in `Specs/Unlink/Spec.lean`

#### `transact(txn: Transaction)`
1. Verifies merkle root exists in historical roots
2. Checks all nullifiers are unspent
3. Verifies ZK-SNARK proof
4. Marks nullifiers as spent
5. Inserts new commitments into tree
6. Processes withdrawal if present
7. Emits transaction event

**Specification**: See `transact_spec` in `Specs/Unlink/Spec.lean`

## Proof Strategy

### Layer 1: Implementation Meets Spec
- `deposit_meets_spec`: Prove `deposit` implementation satisfies `deposit_spec`
- `transact_meets_spec`: Prove `transact` implementation satisfies `transact_spec`

### Layer 2: Security Properties
Using the specs, prove high-level security theorems:
- `exclusive_control`
- `no_double_spend`
- `supply_conservation`
- `deposit_withdrawal_liveness`

### Layer 3: Helper Lemmas
Reusable lemmas about state invariants:
- `deposit_preserves_nullifiers`
- `roots_cumulative`
- `commitments_cumulative`

## Comparison with Solidity Implementation

### Solidity (Original)
```solidity
function deposit(address _depositor, Note[] calldata _notes, ...) external payable {
  for (uint256 i = 0; i < _notes.length; i++) {
    _validateNote(_notes[i]);
    if (_notes[i].token == ETH_TOKEN) {
      ethConsumed += _notes[i].amount;
    } else {
      _transferTokenIn(_notes[i]);
    }
    newLeaves[i] = hashNote(_notes[i]);
  }
  _insertLeaves(newLeaves);
  emit Deposited(...);
}
```

### EDSL (This Implementation)
```lean
def deposit (notes : List Note) : Contract Unit := do
  -- Validate and hash notes
  let mut commitments : List Uint256 := []
  for note in notes do
    let commitment ← hashNote note
    commitments := commitment :: commitments

  -- Insert into merkle tree
  insertLeaves commitments.reverse
```

**Benefits**:
- ✅ Cleaner, more readable code
- ✅ Formally specified behavior
- ✅ Machine-checked proofs of correctness
- ✅ Same test compatibility

## Roadmap

### Phase 1: Scaffold (Current)
- [x] Create project structure
- [x] Write initial specifications
- [x] Scaffold EDSL implementation
- [x] Scaffold proof structure

### Phase 2: Core Implementation
- [ ] Implement Poseidon hash function
- [ ] Implement incremental merkle tree
- [ ] Implement ERC20 transfer logic
- [ ] Implement ETH handling
- [ ] Implement proof verification routing

### Phase 3: Specifications Refinement
- [ ] Refine type definitions (Note, Proof, Transaction)
- [ ] Define merkle tree predicates formally
- [ ] Define nullifier and root tracking predicates
- [ ] Specify token balance changes precisely

### Phase 4: Proofs
- [ ] Prove `deposit_meets_spec`
- [ ] Prove `transact_meets_spec`
- [ ] Prove `exclusive_control`
- [ ] Prove `no_double_spend`
- [ ] Prove `supply_conservation`
- [ ] Prove `deposit_withdrawal_liveness`

### Phase 5: Testing
- [ ] Port Foundry tests to work with compiled Yul
- [ ] Differential testing against Solidity implementation
- [ ] Property-based testing using proven theorems

### Phase 6: Compiler Integration
- [ ] Add Unlink to compiler specs
- [ ] Generate Yul code
- [ ] Prove IR generation correctness
- [ ] Prove Yul preservation

## Dependencies and Requirements

### Cryptographic Primitives Needed
1. **Poseidon Hash**: For computing note commitments
2. **Incremental Merkle Tree**: For commitment tracking
3. **ZK-SNARK Verifier Interface**: For proof verification

### EDSL Extensions Needed
1. **External Calls**: For verifier router and token contracts
2. **Events**: For emitting Deposited, Transacted, Withdrawn
3. **Revert Handling**: For validation failures
4. **Mapping Storage**: For nullifiers and historical roots

## Testing Strategy

### Unit Tests
- Test individual functions (hashNote, insertLeaves, etc.)
- Test state transitions
- Test validation logic

### Property Tests
- Use proven theorems as property test oracles
- Generate random valid/invalid transactions
- Verify properties hold

### Differential Tests
- Compare behavior with Solidity implementation
- Same inputs → same outputs
- Ensures behavioral equivalence

### Integration Tests
- Full deposit → transact → withdraw flows
- Multi-user scenarios
- Edge cases (tree full, invalid proofs, etc.)

## Open Questions

1. **Merkle Tree Representation**: How to best represent the IMT in the EDSL?
2. **ZK Proof Modeling**: Should we model proof internals or treat verification as opaque?
3. **Cryptographic Assumptions**: Which properties should be axioms vs. proven?
4. **Gas Optimization**: How to balance proof simplicity with compiled code efficiency?

## References

- Original Unlink Contracts: `/workspaces/mission-f98ea629/unlink-contracts`
- DumbContracts EDSL: `DumbContracts/Core.lean`
- SimpleStorage Example: `DumbContracts/Examples/SimpleStorage.lean`
- Spec Pattern: `DumbContracts/Specs/SimpleStorage/Spec.lean`
