# Dumb Contracts Research Status

## Current Iteration: Mapping Support (2026-02-10)

### Goal
Add mapping support (Address → Uint256) to enable balances, allowances, and other key-value patterns. This is the first core extension since iteration 3 and opens the door to token contracts and other realistic smart contract patterns.

### What I'm About to Do
1. Extend Core with mapping storage:
   - Add storageMap field to ContractState (Address → Uint256)
   - Add getMapping and setMapping operations
   - Minimal addition following the Address storage pattern

2. Create Ledger example contract:
   - Demonstrates mapping usage (balance per address)
   - Functions: deposit, withdraw, getBalance, transfer
   - Shows key-value storage pattern
   - Includes executable example

3. Add Foundry test suite:
   - Test basic deposit/withdraw
   - Test balance queries
   - Test transfer between addresses
   - Test edge cases (withdraw from empty, etc.)
   - Fuzz test for arbitrary amounts

### Why This Approach
Mapping support is the right next step because:
- First justified core extension since iteration 3 (3 iterations without core changes!)
- Enables entire class of realistic contracts (tokens, allowances, balances)
- Simple example (Ledger) demonstrates the pattern clearly
- Follows established pattern (like Address storage in iteration 3)
- Opens door to ERC20-like contracts in future iterations
- Minimal addition (expect ~10-15 lines of core code)

### Current State
- Previous: Math Safety Stdlib complete (5 examples, 39 tests passing)
- Core: 69 lines (cleaned up, stable since iteration 3)
- Stdlib: Math.lean (63 lines)
- Pattern library: SimpleStorage, Counter, SafeCounter, Owned, OwnedCounter
- Ready for first core extension in 3 iterations

### Expected Outcomes
- Core extended with mapping storage (~80-85 lines total)
- Ledger example demonstrating key-value patterns
- All tests passing (expect ~47-50 total)
- Validation that core extensions are justified by real examples
- Foundation for token contracts

### Next Steps After This Iteration
- Consider ERC20-like token contract (now enabled by mappings)
- More stdlib helpers (token transfer patterns)
- Events for observability (lower priority)
