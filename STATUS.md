# Dumb Contracts Research Status

## Current Iteration: Simple Token Contract (2026-02-10)

### Goal
Create a Simple Token contract that combines Owned and Ledger patterns to demonstrate pattern composition with mappings. This validates that ownership, access control, and mapping storage all work together seamlessly.

### What I'm About to Do
1. Create SimpleToken example contract:
   - Combine Owned (access control) + Ledger (balances mapping) patterns
   - Owner-controlled minting
   - Public transfer operations
   - Functions: mint (owner-only), transfer, balanceOf, totalSupply
   - Demonstrates that patterns compose with mappings

2. Add Foundry test suite:
   - Test initial supply is zero
   - Test owner can mint tokens
   - Test non-owner cannot mint
   - Test transfer between addresses
   - Test balanceOf queries
   - Test totalSupply tracking
   - Fuzz test for minting and transfers

### Why This Approach
Simple Token is the right next step because:
- Natural next step after Ledger (iteration 6) and Owned (iteration 3)
- Demonstrates that patterns compose with mappings
- Validates the architecture can handle realistic contracts
- Foundation pattern for DeFi-like contracts
- Zero core changes needed (uses existing primitives)
- Clean example that's easy to understand

### Current State
- Previous: Mapping Support complete (6 examples, 50 tests passing)
- Core: 82 lines (stable, mapping support added)
- Stdlib: Math.lean (63 lines)
- Pattern library: SimpleStorage, Counter, SafeCounter, Owned, OwnedCounter, Ledger
- Ready to validate pattern composition with mappings

### Expected Outcomes
- SimpleToken example (~80-90 lines)
- All tests passing (expect ~60-65 total)
- Validation that Owned + Ledger patterns compose
- Zero core changes needed
- Foundation for more complex token contracts

### Next Steps After This Iteration
- Consider allowances (ERC20-like approve/transferFrom pattern)
- More stdlib helpers based on token patterns
- Events for observability (lower priority)
