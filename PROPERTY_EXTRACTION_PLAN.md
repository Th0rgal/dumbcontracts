# Property Extraction Plan - Priority 3

## Goal
Convert proven Lean theorems into executable Foundry tests, creating a bridge between formal verification and runtime testing.

## Current Status
- **251 proven theorems** across 7 contracts
- All proofs verified with zero `sorry`
- Theorems cover: correctness, invariants, composition, edge cases

## Approach

### Phase 1: Manual Extraction (Proof of Concept)
Start with Counter contract (10 theorems) to establish patterns:

**Counter Theorems to Extract:**
1. `increment_state_preserved_except_count` - Only modifies slot 0
2. `decrement_state_preserved_except_count` - Only modifies slot 0
3. `getCount_state_preserved` - Read-only, no state changes
4. `increment_getCount_meets_spec` - Increment then read returns count+1
5. `decrement_getCount_meets_spec` - Decrement then read returns count-1
6. `two_increments_meets_spec` - Double increment adds 2
7. `increment_decrement_meets_cancel` - Increment then decrement cancels (bounded)
8. `getCount_preserves_wellformedness` - Read maintains invariants
9. `decrement_getCount_correct` - Decrement → getCount = count-1
10. `decrement_at_zero_wraps_max` - 0 - 1 = MAX_UINT256 (wraparound)

### Phase 2: Test Template Design

**Test Structure:**
```solidity
// test/PropertyCounter.t.sol
contract PropertyCounterTest is Test {
    Counter counter;

    // Property 1: increment_state_preserved_except_count
    function test_Increment_OnlyModifiesCount() public {
        // Setup: Deploy and set initial state
        // Action: Call increment
        // Assert: Only storage[0] changed
    }

    // Property 10: decrement_at_zero_wraps_max
    function testFuzz_Decrement_AtZero_WrapsToMax(uint256 initialCount) public {
        vm.assume(initialCount == 0);
        // Assert decrement results in MAX_UINT256
    }
}
```

### Phase 3: Implementation Strategy

**For each theorem:**
1. **Parse theorem signature** - Extract contract, operation, property
2. **Map to Solidity test** - Convert Lean state transitions to Solidity calls
3. **Generate assertions** - Translate Lean predicates to Foundry assertions
4. **Add fuzzing where applicable** - Properties with universal quantifiers

**Mapping Examples:**

| Lean Concept | Solidity Equivalent |
|--------------|---------------------|
| `s.storage 0` | `counter.getCount()` or direct storage read |
| `(increment).run s` | `counter.increment()` |
| `EVM.Uint256.add a 1` | `a + 1` (with overflow) |
| `state_preserved_except_count` | Check all other storage unchanged |

### Phase 4: Automation Potential

**Semi-automated extraction:**
- Parse Lean theorem signatures
- Generate test skeleton with placeholders
- Human fills in specific assertions
- Tool validates test matches theorem intent

**Challenges:**
- Lean proofs are abstract (state machines)
- Solidity tests are concrete (deployed contracts)
- Need to map between formal and executable representations

## Implementation Plan

### Step 1: Counter Property Tests (Manual)
Create `test/PropertyCounter.t.sol` with all 10 theorems as tests.

**Expected outcome:**
- 10 new property tests
- All tests pass (properties already verified formally)
- Demonstrates feasibility of extraction

### Step 2: Extend to Other Contracts
Repeat for:
- SimpleStorage (19 theorems)
- Owned (22 theorems)
- SafeCounter (25 theorems)
- Ledger (25 theorems)
- OwnedCounter (45 theorems)
- SimpleToken (75 theorems)

### Step 3: Document Pattern Library
Create reusable patterns:
- State preservation tests
- Composition tests
- Invariant tests
- Edge case tests

## Success Criteria

✅ All 251 theorems have corresponding Foundry tests
✅ All property tests pass
✅ Tests provide readable property documentation
✅ Coverage includes edge cases (overflow, underflow, zero)
✅ Fuzzing used for universal properties

## Benefits

1. **Runtime Validation** - Properties verified at runtime, not just compile-time
2. **Regression Detection** - Tests catch if implementation diverges from spec
3. **Documentation** - Tests serve as executable specification
4. **Confidence** - Dual verification (proofs + tests) increases trust
5. **Debugging** - Failed property tests pinpoint specification violations

## Next Steps

1. Create `test/PropertyCounter.t.sol`
2. Implement 10 Counter property tests manually
3. Run and verify all pass
4. Document patterns learned
5. Scale to remaining contracts
