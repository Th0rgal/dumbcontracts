# Dumb Contracts

**Minimal Lean 4 EDSL for Smart Contracts with Formal Verification**

[![Build](https://img.shields.io/badge/build-passing-brightgreen)]()
[![Lean](https://img.shields.io/badge/lean-4.15.0-blue)]()
[![License](https://img.shields.io/badge/license-MIT-blue)]()

> From runtime testing to mathematical proof

An 82-line core that handles realistic smart contracts, backed by machine-checked formal proofs of correctness.

**Core Stats:**
- 82 lines of Lean (minimal core)
- 7 example contracts
- 62 runtime tests (100% passing)
- 11 formal proofs (100% verified)

## The Value Proposition

Traditional smart contract testing gives you confidence through examples. Formal verification gives you certainty through proofs.

**Before (Testing Only):**
```lean
def store (value : Uint256) : Contract Unit := ...
def retrieve : Contract Uint256 := ...
```
Result: High confidence from 256 fuzz runs

**After (Testing + Verification):**
```lean
theorem store_retrieve_correct (s : ContractState) (value : Uint256) :
  let s' := (store value).run s |>.2
  let result := retrieve.run s' |>.1
  result = value := by
  -- Machine-checked proof
```
Result: Mathematical certainty for all possible inputs

## Quick Example

```lean
-- Implementation
def storedData : StorageSlot Uint256 := ⟨0⟩

def store (value : Uint256) : Contract Unit := do
  setStorage storedData value

def retrieve : Contract Uint256 := do
  getStorage storedData

-- Proof: retrieve always returns what store stored
theorem store_retrieve_correct (s : ContractState) (value : Uint256) :
  let s' := (store value).run s |>.2
  let result := retrieve.run s' |>.1
  result = value := by
  have h_store := store_meets_spec s value
  have h_retrieve := retrieve_meets_spec ((store value).run s |>.2)
  simp [store_spec] at h_store
  simp [retrieve_spec] at h_retrieve
  simp only [h_retrieve, h_store.1]
```

Build and verify:
```bash
lake build  # Verifies all proofs
forge test  # Runs all tests
```

## Architecture

Clean three-layer separation:

```
DumbContracts/
├── Examples/           # Implementations (82-line core)
│   ├── SimpleStorage
│   ├── Counter
│   ├── Owned
│   └── SimpleToken
│
├── Specs/             # Formal specifications
│   └── SimpleStorage/
│       ├── Spec.lean
│       └── Invariants.lean
│
└── Proofs/            # Machine-checked proofs
    └── SimpleStorage/
        └── Basic.lean
```

Implementation, specification, and proofs remain completely separate.

## Proven Properties

**SimpleStorage** (11 theorems verified):

*Correctness*
- `store_retrieve_correct` — retrieve always returns what store stored
- `store_meets_spec` — store satisfies its formal specification
- `retrieve_meets_spec` — retrieve satisfies its formal specification

*Isolation*
- `setStorage_preserves_other_slots` — operations don't interfere between slots
- `setStorage_preserves_addr_storage` — type isolation for addresses
- `setStorage_preserves_map_storage` — type isolation for mappings

*State Preservation*
- `store_preserves_wellformedness` — operations maintain well-formed state
- `retrieve_preserves_state` — read operations are pure

See [VERIFICATION_ITERATION_1_SUMMARY.md](VERIFICATION_ITERATION_1_SUMMARY.md) for complete details.

## Example Contracts

| Contract | Lines | Tests | Proofs | Description |
|----------|-------|-------|--------|-------------|
| SimpleStorage | 38 | 4 | 11 ✓ | Basic state management |
| Counter | 50 | 7 | — | Arithmetic operations |
| Owned | 59 | 8 | — | Access control |
| OwnedCounter | 80 | 11 | — | Pattern composition |
| Ledger | 70 | 11 | — | Mapping storage |
| SimpleToken | 96 | 12 | — | ERC20-like token |

Total: 7 contracts, 62 tests (100% passing), 11 proofs (100% verified)

## Core API

The entire API in 82 lines:

```lean
-- Types
abbrev Address := String
abbrev Uint256 := Nat
structure StorageSlot (α : Type)
abbrev Contract (α : Type) := StateM ContractState α

-- Storage operations (type-safe)
def getStorage : StorageSlot Uint256 → Contract Uint256
def setStorage : StorageSlot Uint256 → Uint256 → Contract Unit
def getMapping : StorageSlot (Address → Uint256) → Address → Contract Uint256

-- Context
def msgSender : Contract Address
def contractAddress : Contract Address

-- Guards
def require : Bool → String → Contract Unit
```

Type safety at compile-time:
```lean
def owner : StorageSlot Address := ⟨0⟩
def count : StorageSlot Uint256 := ⟨1⟩

getStorage owner      -- Error: type mismatch
getStorageAddr owner  -- OK
```

## Design Evolution

The project evolved through 7 documented iterations, with 4 requiring zero core changes:

1. **Bootstrap** — 58-line minimal core
2. **Counter** — Arithmetic operations
3. **Owned** — Access control (+14 lines)
4. **OwnedCounter** — Pattern composition (0 core changes)
5. **Math Safety** — Stdlib extensibility (0 core changes)
6. **Mapping Support** — Key-value storage (+13 lines)
7. **SimpleToken** — Full token contract (0 core changes)

Then verification phase: formal proofs without changing implementations.

See [RESEARCH.md](RESEARCH.md) for complete design history.

## Design Principles

**Minimalism** — 82-line core, only essentials. 4 of 7 iterations needed zero core changes.

**Rigor** — Complete separation of specs, implementations, and proofs. Every design decision documented.

**Practicality** — Real contracts with both runtime tests and formal verification.

## Verification Roadmap

- [x] SimpleStorage — 11 theorems proven
- [ ] Counter — Arithmetic correctness
- [ ] Owned — Access control guarantees
- [ ] SimpleToken — Complex invariants (total supply = sum of balances)

## Getting Started

Requirements: [Lean 4](https://leanprover.github.io/) (4.15.0+) and [Foundry](https://getfoundry.sh/)

```bash
git clone https://github.com/Th0rgal/dumbcontracts.git
cd dumbcontracts
lake build   # Verifies all proofs
forge test   # Runs all tests
```

To write a verified contract:
1. Implementation → `DumbContracts/Examples/`
2. Specification → `DumbContracts/Specs/`
3. Proofs → `DumbContracts/Proofs/`
4. Tests → `test/`

See [VERIFICATION_ITERATION_1_SUMMARY.md](VERIFICATION_ITERATION_1_SUMMARY.md) for a complete walkthrough.

## Documentation

- [RESEARCH.md](RESEARCH.md) — Complete design history
- [ITERATION_*_SUMMARY.md](ITERATION_1_SUMMARY.md) — Detailed iteration breakdowns
- [VERIFICATION_ITERATION_1_SUMMARY.md](VERIFICATION_ITERATION_1_SUMMARY.md) — Proof details
- [docs-site/](docs-site/) — AI-friendly documentation website

## Key Results

**Minimalism** — 82-line core sufficient for realistic token contracts. 4 of 7 iterations required zero core changes.

**Verification** — 11 theorems proven for SimpleStorage, establishing clear patterns for verifying complex contracts.

**Composability** — Patterns combine naturally without special support (OwnedCounter, SimpleToken).

**Testing** — 62 Foundry tests (100% passing), 2,816 fuzz runs, 11 formal proofs.

## License

MIT

---

*From runtime confidence to mathematical certainty*
