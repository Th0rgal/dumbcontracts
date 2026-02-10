# Dumb Contracts Research Status

## Current Iteration: Verification Iteration 1 - SimpleStorage (2026-02-10)

### Goal
Add formal verification to SimpleStorage, proving basic correctness properties. This establishes the foundation for verifying more complex contracts.

### What I'm About to Do

1. **Create specification files** (DumbContracts/Specs/SimpleStorage/):
   - `Spec.lean` - Formal specification of store/retrieve behavior
   - `Invariants.lean` - State invariants (well-formedness)

2. **Create proof files** (DumbContracts/Proofs/SimpleStorage/):
   - `Basic.lean` - Prove store/retrieve correctness
   - Prove: retrieve returns the last stored value
   - Prove: setStorage preserves state well-formedness

3. **Document proof strategy**:
   - What properties are proven
   - What assumptions are made
   - What remains unproven

### Why This Approach

SimpleStorage verification is the right starting point because:
- Simplest contract (store/retrieve only)
- Establishes proof patterns for future contracts
- Tests verification infrastructure
- No complex invariants (single storage slot)
- Foundation for Counter, Owned, etc.

### Key Properties to Prove

**Tier 1: Basic Correctness**
- `store_retrieve_correct`: After storing value v, retrieve returns v
- `store_updates_storage`: setStorage actually updates the storage slot
- `retrieve_reads_storage`: getStorage returns the value in the slot

**Tier 2: State Invariants**
- `state_well_formed`: ContractState structure is valid
- `storage_isolation`: Different slots don't interfere

### Current State
- Previous: Documentation website complete (PR #4)
- Core: 82 lines, stable
- Examples: 7 contracts (all runtime-tested)
- Verification: None yet (this is the first!)

### Expected Outcomes
- Specs/SimpleStorage/ directory with formal specifications
- Proofs/SimpleStorage/ directory with proven theorems
- At least 1 complete proof (store_retrieve_correct)
- Documentation of proof strategy and limitations
- Foundation for future verification work

### Next Steps After This Iteration
- Counter verification (arithmetic properties)
- Owned verification (access control properties)
- SimpleToken verification (complex invariants)

---

## Previous Work: Implementation Phase Complete

**7 iterations completed** (see RESEARCH.md for full details):
1. Bootstrap - 58-line minimal core
2. Counter - Arithmetic operations
3. Owned - Access control (+14 lines)
4. OwnedCounter - Pattern composition
5. Math Safety Stdlib - Extensibility
6. Mapping Support - Key-value storage (+13 lines)
7. SimpleToken - Realistic token contract

**Current State**: 82-line core, 7 examples, 62 tests (100% passing)

**New Phase**: Formal verification via Lean proofs
