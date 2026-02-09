# Dumb Contracts Research Log

## Iteration 1: Bootstrap (2026-02-09)

### What I Added
1. **Minimal Lean EDSL Core** (DumbContracts/Core.lean:1-58)
   - Basic Ethereum types: Address, Uint256, Bool', Bytes
   - StorageSlot abstraction for type-safe storage access
   - ContractState structure with storage map, sender, and contract address
   - Contract monad as StateM alias
   - Storage operations: getStorage, setStorage
   - Context accessors: msgSender, contractAddress
   - Require guard for validation

2. **SimpleStorage Example** (DumbContracts/Examples/SimpleStorage.lean:1-38)
   - Demonstrates basic storage pattern
   - Two functions: store and retrieve
   - Includes executable example that evaluates to 42
   - Clean, minimal syntax

3. **Foundry Test Suite** (test/SimpleStorage.t.sol:1-41)
   - Tests initial state (zero value)
   - Tests store and retrieve
   - Tests value updates
   - Fuzz test for arbitrary values
   - All 4 tests pass with 256 fuzz runs

### What I Tried

**Approach 1: Initial design with `get` and `set` function names**
- Problem: Name collision with StateM's get method
- Solution: Renamed to getStorage and setStorage for clarity

**Approach 2: Using `StateM.get` explicitly**
- Problem: StateM.get doesn't exist in Lean 4's API
- Solution: Use plain `get` which is automatically available in do-notation

**Approach 3: Using `example` as function name**
- Problem: `example` is a reserved keyword in Lean
- Solution: Renamed to `exampleUsage`

**Approach 4: Including Repr instance for ContractState**
- Problem: Repr can't handle function types (Nat → Uint256)
- Solution: Removed the deriving Repr clause

### Findings

**EDSL Design Principles That Work:**
1. **StateM is the right abstraction** for contract execution
   - Clean do-notation syntax
   - Natural fit for storage operations
   - Easy to reason about state changes

2. **Type-safe storage slots** prevent common errors
   - StorageSlot wrapper makes slots explicit
   - Type parameter ensures type consistency
   - Simple Nat-based addressing is sufficient for now

3. **Minimal is maintainable**
   - Only 58 lines of core code
   - Zero external dependencies
   - Everything needed for basic contracts

4. **Example-driven development works**
   - SimpleStorage guided the core API design
   - Real usage revealed naming conflicts early
   - Having a working example validates the approach

**Lean 4 Specifics:**
- Do-notation requires using plain `get` and `modify`, not `StateM.get`
- Function types can't derive Repr automatically
- `example` is a reserved keyword
- Lake build system is straightforward and fast

**Testing Strategy:**
- Parallel Solidity implementation validates semantics
- Foundry tests provide runtime confidence
- Fuzz testing catches edge cases
- Evaluating Lean code inline (with #eval) catches issues early

### Complexity Metrics
- Core EDSL: 58 lines
- SimpleStorage Example: 38 lines (24 lines of actual code)
- Ratio: ~0.66 - example is slightly smaller than core
- Test coverage: 4 tests, all passing

### Next Iteration Ideas
1. **Counter contract** - add increment/decrement pattern
2. **Ownership pattern** - introduce msg.sender checks
3. **Events** - add event emission support
4. **Math safety** - add checked arithmetic helpers
5. **Multiple storage types** - extend beyond Uint256

### Questions for Future Exploration
- Should we add syntactic sugar for common patterns?
- How to handle reverts more elegantly?
- Can we add event support without too much complexity?
- Should we create a standard library module?

### Files Modified This Iteration
- Created: DumbContracts/Core.lean
- Created: DumbContracts/Examples/SimpleStorage.lean
- Created: DumbContracts.lean
- Created: contracts/SimpleStorage.sol
- Created: test/SimpleStorage.t.sol
- Created: lean-toolchain
- Created: lakefile.lean
- Created: foundry.toml
- Created: STATUS.md
- Created: RESEARCH.md
- Created: .gitignore
