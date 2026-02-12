# DumbContracts — Formally Provable Smart Contract EDSL

## Goal

DumbContracts is an embedded domain-specific language (EDSL) in Lean 4 for writing formally verified smart contracts. The goal is to enable developers to write Ethereum smart contracts with mathematical certainty about their correctness through machine-checked proofs.

Key properties:
- **Formally provable**: Every contract operation can be proven correct against its specification
- **Simple**: 212-line core implementation, minimal dependencies
- **Trustworthy**: 252 existing correctness proofs, zero axioms, verified compiler in progress

## Architecture

The project is organized into four main components:

### 1. **Documentation** (`docs/` and `docs-site/`)

- **`docs/`**: Technical documentation, verification summaries, and proof iteration logs
- **`docs-site/`**: Public documentation website built with modern web framework
  - Architecture guides
  - API references
  - Tutorial content

### 2. **Core EDSL & Examples** (`DumbContracts/`)

The core language implementation and verified contracts:

- **`Core/`**: 212-line EDSL core (ContractResult monad, storage operations, guards)
- **`Stdlib/`**: Safe arithmetic utilities (safeAdd, safeSub, safeMul, safeDiv)
- **`Examples/`**: 7 verified contracts (SimpleStorage, Counter, SafeCounter, Owned, OwnedCounter, Ledger, SimpleToken)
- **`Specs/`**: Formal specifications for each contract
  - Preconditions, postconditions, invariants
  - What each operation should do
- **`Proofs/`**: 252 machine-checked proofs of correctness
  - Safety properties (access control, no overdrafts, overflow protection)
  - Correctness (operations match specifications)
  - Invariants (state consistency preserved)
  - Conservation laws (exact balance/supply equations)

### 3. **Compiler** (`Compiler/`)

Verified compilation pipeline from EDSL to EVM bytecode:

- **`ContractSpec.lean`**: Declarative intermediate representation
- **`Specs.lean`**: Specifications for all 7 contracts
- **`IR.lean`**: Intermediate representation for code generation
- **`Codegen.lean`**: IR → Yul code generation
- **`Interpreter.lean`**: Reference interpreter for differential testing
- **`Proofs/`**: Compiler verification (Layer 1 complete!)
  - **✅ Layer 1: EDSL ≡ ContractSpec** — All 7 contracts proven
  - 🚧 Layer 2: ContractSpec → IR (semantic preservation) — In progress
  - 🔲 Layer 3: IR → Yul (codegen correctness) — Planned

**Testing strategy**:
- 70,000+ differential tests comparing EDSL interpreter vs EVM execution
- 58 property tests extracted from proven theorems
- Zero mismatches across all test suites

### 4. **Example Contracts & Tests** (`examples/` and `test/`)

- **`examples/solidity/`**: Reference Solidity implementations for comparison
- **`test/`**: Comprehensive Foundry test suite
  - 76 original tests
  - 130 differential tests (10k+ transactions per contract)
  - 58 property tests (automatically extracted from proofs)
  - 264/264 tests passing

## How It Works

1. **Write contracts in the EDSL**: Use Lean 4 to define contract logic with storage operations and guards
2. **Write specifications**: Formally specify what each operation should do
3. **Prove correctness**: Write machine-checked proofs that the implementation matches the specification
4. **Compile**: Use the verified compiler to generate EVM bytecode
5. **Test**: Run differential tests to validate that compiled bytecode matches EDSL semantics

## Current Status (PR #12)

**Contract Proofs:**
- ✅ 252 correctness proofs verified

**Compiler Verification:**
- ✅ **Layer 1 COMPLETE**: All 7 spec correctness proofs done
  - SimpleStorage, Counter, SafeCounter, Owned, OwnedCounter, Ledger, SimpleToken
  - 2,800+ lines of proofs
  - Zero `sorry`, zero axioms

**Testing:**
- ✅ 264 Foundry tests passing (100%)
- ✅ 70,000+ differential tests, zero mismatches

**Next Steps:**
- 🚧 Layer 2: Prove IR generation preserves semantics
- 🔲 Layer 3: Prove Yul codegen correctness

## Trust Model

**Verified:**
- ✅ EDSL contract semantics (252 proofs)
- ✅ Contract specifications accurately represent EDSL behavior (7 spec correctness proofs)

**Being verified (in progress):**
- 🚧 Compiler correctness (Spec → IR → Yul)

**Trusted:**
- Lean 4 kernel (~10k lines, extensively reviewed)
- Solidity compiler (Yul → EVM bytecode)
- EVM implementation (consensus-critical, well-tested)

**Empirically validated:**
- 70,000+ differential tests (zero mismatches)

---

## 🚨 IMPORTANT: Keeping Documentation Updated

**When you modify code in this repository, you MUST update the corresponding documentation:**

1. **After proving new theorems**: Update `Compiler/Proofs/README.md` and relevant status files
2. **After completing a verification layer**: Update this `AGENTS.md` and the main `README.md`
3. **After adding new contracts**: Update contract counts and examples in all docs
4. **After changing architecture**: Update the Architecture section above
5. **After test results change**: Update the Current Status section

**Files that need frequent updates:**
- `AGENTS.md` (this file) — High-level status and architecture
- `README.md` — User-facing documentation
- `Compiler/Proofs/README.md` — Detailed verification status
- `docs-site/content/*.mdx` — Web documentation

**Stale documentation breaks trust.** Keep it current!
