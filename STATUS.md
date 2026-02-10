# Dumb Contracts Research Status

## Current Iteration: Verification Iteration 2 - Counter (2026-02-10)

### Goal
Add formal verification to Counter, proving arithmetic correctness properties. Build on SimpleStorage foundation to verify operations that modify state with arithmetic.

### What I'm About to Do

1. **Create specification files** (DumbContracts/Specs/Counter/):
   - `Spec.lean` - Formal specification of increment/decrement/getCount behavior
   - `Invariants.lean` - State invariants (well-formedness, count validity)

2. **Create proof files** (DumbContracts/Proofs/Counter/):
   - `Basic.lean` - Prove increment/decrement correctness
   - Prove: increment increases count by exactly 1
   - Prove: decrement decreases count by exactly 1
   - Prove: multiple operations compose correctly
   - Prove: getCount returns current count

3. **Document proof strategy**:
   - Arithmetic properties proven
   - State preservation properties
   - Composition properties
   - Assumptions about Nat arithmetic

### Why This Approach

Counter verification is the natural next step because:
- Builds on SimpleStorage verification patterns
- Introduces arithmetic operations (addition, subtraction)
- Tests composition of multiple operations
- Still relatively simple (single storage slot)
- Foundation for more complex contracts with arithmetic

### Key Properties to Prove

**Tier 1: Basic Correctness**
- `increment_adds_one`: increment increases count by exactly 1
- `decrement_subtracts_one`: decrement decreases count by exactly 1
- `getCount_reads_count`: getCount returns the current count
- `increment_meets_spec`: increment satisfies its formal specification
- `decrement_meets_spec`: decrement satisfies its formal specification

**Tier 2: Composition**
- `increment_twice_adds_two`: Two increments add 2
- `increment_decrement_cancel`: increment then decrement restores original value
- `operations_compose`: Multiple operations have cumulative effect

**Tier 3: State Invariants**
- `state_well_formed`: ContractState structure is valid
- `operations_preserve_wellformedness`: Operations maintain well-formed state

### Current State
- Previous: SimpleStorage verification complete (11 theorems proven)
- Core: 82 lines, stable
- Examples: 7 contracts (all runtime-tested)
- Verification: SimpleStorage complete, Counter starting

### Expected Outcomes
- Specs/Counter/ directory with formal specifications
- Proofs/Counter/ directory with proven theorems
- At least 5 complete proofs (basic correctness + composition)
- Documentation of arithmetic proof strategies
- Foundation for contracts with more complex arithmetic

### Next Steps After This Iteration
- Owned verification (access control properties)
- SimpleToken verification (complex invariants + arithmetic)

---

## Previous Work

### Verification Phase

**Iteration 1: SimpleStorage** ✅ Complete
- 11 theorems proven
- store_retrieve_correct proven
- Foundation established
- See VERIFICATION_ITERATION_1_SUMMARY.md

### Implementation Phase Complete

**7 iterations completed** (see RESEARCH.md for full details):
1. Bootstrap - 58-line minimal core
2. Counter - Arithmetic operations
3. Owned - Access control (+14 lines)
4. OwnedCounter - Pattern composition
5. Math Safety Stdlib - Extensibility
6. Mapping Support - Key-value storage (+13 lines)
7. SimpleToken - Realistic token contract

**Current State**: 82-line core, 7 examples, 62 tests (100% passing), 11 proofs (SimpleStorage)

**New Phase**: Formal verification via Lean proofs (Counter in progress)
