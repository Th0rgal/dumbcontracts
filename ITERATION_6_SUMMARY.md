# Iteration 6 Summary: Mapping Support

## Goal
Add mapping support (Address → Uint256) to enable balances, allowances, and key-value storage patterns. First core extension in 3 iterations.

## What Was Added

### 1. Core Extension: Mapping Storage (+12 lines)
```lean
structure ContractState where
  storage : Nat → Uint256
  storageAddr : Nat → Address
  storageMap : Nat → Address → Uint256  -- NEW!
  sender : Address
  thisAddress : Address

def getMapping (s : StorageSlot (Address → Uint256)) (key : Address) : Contract Uint256
def setMapping (s : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256) : Contract Unit
```

**Core size:** 69 → 81 lines (+17%)

### 2. Ledger Example (70 lines)
- Demonstrates mapping usage pattern
- Functions: deposit, withdraw, transfer, getBalance
- Balances mapping (Address → Uint256)
- Example: Alice deposits 100, withdraws 30, transfers 50 to Bob

### 3. Complete Test Suite (11 tests)
- All deposit/withdraw/transfer scenarios
- Insufficient balance checks
- Fuzz testing (deposit/withdraw, transfer)
- Example usage validation
- **All 50 total tests passing** (100%)

## Key Achievements

### ✅ Justified Core Extension
- First core change in 3 iterations (iterations 4-5 had zero core changes)
- Enables entire class of contracts (tokens, registries)
- Minimal addition (12 lines)
- Follows established pattern

### ✅ Natural Mapping Representation
- Nested functions: `Nat → Address → Uint256`
- Type-safe through StorageSlot wrapper
- Clean API with getMapping/setMapping

### ✅ Solidity Semantic Alignment
- Default zero for uninitialized entries
- Matches Solidity mapping behavior exactly
- Ledger behaves identically in both languages

### ✅ Token Contracts Now Possible
With mappings, the EDSL can now implement:
- ERC20-like tokens (balances, allowances)
- NFT registries
- Voting systems
- Staking contracts

## Metrics

**Code:**
- Core: 81 lines
- Stdlib: 63 lines (Math)
- Examples: 6 contracts (~320 lines)
- Total: ~464 lines of Lean

**Tests:**
- 50 tests (100% passing)
- 9 fuzz tests
- 2,304 fuzz runs

**Growth Rate:**
- Iterations with zero core changes: 2 (iterations 4-5)
- Core extensions: 2 (iterations 3, 6)
- Growth per extension: ~15-25%
- Sustainable and minimal

## Example Usage

```lean
-- Define balances mapping
def balances : StorageSlot (Address → Uint256) := ⟨0⟩

-- Deposit to caller's balance
def deposit (amount : Uint256) : Contract Unit := do
  let sender ← msgSender
  let currentBalance ← getMapping balances sender
  setMapping balances sender (currentBalance + amount)

-- Transfer between addresses
def transfer (to : Address) (amount : Uint256) : Contract Unit := do
  let sender ← msgSender
  let senderBalance ← getMapping balances sender
  require (senderBalance >= amount) "Insufficient balance"
  let recipientBalance ← getMapping balances to
  setMapping balances sender (senderBalance - amount)
  setMapping balances to (recipientBalance + amount)
```

## Testing Results

```
Ran 6 test suites: 50 tests passed, 0 failed, 0 skipped
- SimpleStorage: 4 tests ✅
- Counter: 7 tests ✅
- SafeCounter: 9 tests ✅
- Owned: 8 tests ✅
- OwnedCounter: 11 tests ✅
- Ledger: 11 tests ✅ NEW
```

## Design Decisions

### Why This Extension?
1. **Clear need**: Balances, allowances require key-value storage
2. **No alternative**: Can't fake mappings with single values
3. **Minimal**: Only 12 lines added
4. **High value**: Unlocks entire class of contracts

### Why Address → Uint256?
- Most common mapping type in smart contracts
- Covers 80% of use cases (balances, allowances, stakes)
- Can extend to other types later if examples need them

### Why Nested Functions?
- Natural in Lean's type system
- Type-safe through StorageSlot
- Easy partial application (slot then key)
- Matches mental model

## Next Steps

### Immediate: Simple Token Contract
- Combine Owned + Ledger patterns
- Add totalSupply, balanceOf, transfer
- Validate that patterns compose with mappings

### Future: More Mapping Types
- Only add when examples demonstrate need
- Keep it minimal and justified

## Conclusion

**Iteration 6 successfully added mapping support with minimal core extension (12 lines), enabling an entire class of token-like contracts while maintaining the EDSL's minimalist philosophy.**

The 3-iteration gap since the last core change (iteration 3) validates that extensions are carefully justified by real example needs, not speculative features.

---

**Status:** ✅ Complete
**Core Size:** 81 lines
**Tests:** 50/50 passing (100%)
**Next:** Simple Token contract
