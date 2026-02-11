# DumbContracts Compiler Roadmap — Trustworthy, Simple, Auditable

PR you are working on: https://github.com/Th0rgal/dumbcontracts/pull/11

Mission: Turn the EDSL→EVM compiler into a generic, well‑tested, and eventually verified pipeline that is easy to audit and maintain.

Current state:
- ✅ Item 0 complete: EVM type system compatibility
- ✅ Item 1 complete: Generic compilation working
- ✅ Item 2 core complete: Differential testing infrastructure for all 7 contracts
- ✅ All Foundry tests passing (128 tests)
- ✅ All 252 proofs verified

Other agents are working on it: always pull the latest changes, review them, and check the pull request reviews that will report bugs and improvements you will need to fix or answer before starting. Additionally run foundry tests and lake build to detect additional issues.

---

## Priorities (in order):

### 0) ✅ EVM type system compatibility (HIGH PRIORITY) - COMPLETE
   - Dedicated `Uint256` type with modular semantics (`DumbContracts/Core/Uint256.lean`)
   - Compiler emits EVM‑native modular ops
   - All 7 contracts migrated + 252 proofs updated
   - Added EVM context (`msg.value`, `block.timestamp`) and bitwise ops

   **Success criteria**: ✅ All arithmetic has EVM‑compatible semantics, differential tests pass with zero mismatches

---

### 1) ✅ Generic compilation (no manual Translate.lean) - COMPLETE
   - Parse contract AST, infer storage, compute selectors (keccak)
   - Auto‑generate IR for all contracts
   - Fail fast on spec errors

   **Success criteria**: ✅ `lake exe compile --all` works for every contract + new contract compiles without Translate edits

---

### 2) 🔄 Differential testing (trust before proofs) - CORE COMPLETE
   - ✅ Lean interpreter + random transaction generator
   - ✅ Compare interpreter vs EVM results (storage, returns, reverts)
   - ✅ Foundry vm.ffi integration with proper state tracking
   - ✅ 7/7 contracts covered with differential tests
   - ✅ Random100 + Random1000 tests per contract passing
   - ⏳ Scale to 10k+ tests per contract in CI

   **Success criteria**: Zero mismatches across all contracts at 10k+ tests per contract

   **Status**: Core infrastructure complete. Coverage is full but test counts are still below the 10k goal.

---

### 3) Property extraction (proofs → tests) - NOT STARTED
   - Convert proven theorems to Foundry tests
   - Generate test cases from preconditions
   - Validate that proofs translate to executable checks

   **Success criteria**: All 252 theorems produce passing Foundry tests

   **Dependencies**: Items 0 and 2 (now complete)

---

### 4) Compiler verification (long‑term) - NOT STARTED
   - Prove compiled EVM matches EDSL semantics
   - Formalize Yul semantics in Lean
   - Prove IR → Yul transformation preserves semantics
   - Prove EDSL → IR transformation preserves semantics

   **Success criteria**: `lake build Compiler.Proofs` has zero `sorry`

---

## Current Issues Summary

### Remaining Work
1. 🔶 **Scale differential tests** to 10k+ per contract in CI
2. 🔶 **Property extraction** (proofs → tests)
3. 🔶 **Compiler verification** (long‑term)

---

## Workflow Reminders

1. **Always pull latest changes first**: `git pull origin feat/generic-compilation`
2. **Check PR reviews**: `gh pr view 11` - fix any Bugbot issues
3. **Run tests before committing**:
   - `lake build` (verify proofs)
   - `forge test` (verify contracts)
4. **Commit and push progress**: Don't leave uncommitted work
5. **Update this roadmap**: Mark items complete, add new findings

---

## Current Metrics

| Metric | Value |
|--------|-------|
| Contracts with differential tests | 7/7 |
| Random tests passing | 100 + 1000 per contract |
| Differential test mismatches | 0 |
| Foundry tests passing | 128/128 (100%) |
| Lean proofs verified | 252/252 (100%) |
| Manual IR lines eliminated | 266 → 0 |
| Contracts using EVM‑compatible types | 7/7 |

---

## Next Actions (Priority Order)

1. **Scale differential tests** to 10k+ per contract in CI
2. **Start property extraction** (proofs → tests)
3. **Begin compiler verification** roadmap and prerequisites
