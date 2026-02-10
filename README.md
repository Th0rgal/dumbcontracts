# Dumb Contracts

**Minimal Lean 4 EDSL for Smart Contracts with Formal Verification**

[![Build](https://img.shields.io/badge/build-passing-brightgreen)]()
[![Lean](https://img.shields.io/badge/lean-4.15.0-blue)]()
[![License](https://img.shields.io/badge/license-MIT-blue)]()

> From runtime testing to mathematical proof

A 212-line core that handles realistic smart contracts, backed by **230 machine-checked formal proofs** of correctness — zero sorry, zero axioms.

**Core Stats:**
- 212 lines of Lean (ContractResult monad core)
- 7 example contracts, all formally verified
- 62 runtime tests (100% passing)
- 230 formal proofs (100% verified)

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
lake build  # Verifies all 230 proofs
```

## Architecture

Clean three-layer separation:

```
DumbContracts/
├── Core.lean              # 212-line ContractResult monad
├── Stdlib/Math.lean       # Safe arithmetic (safeAdd, safeSub, safeMul, safeDiv)
├── Examples/              # 7 contract implementations
│   ├── SimpleStorage      # Basic state management
│   ├── Counter            # Arithmetic operations
│   ├── SafeCounter        # Checked arithmetic
│   ├── Owned              # Access control
│   ├── OwnedCounter       # Pattern composition
│   ├── Ledger             # Mapping storage
│   └── SimpleToken        # Full token contract
│
├── Specs/                 # Formal specifications (per contract)
│   └── {Contract}/
│       ├── Spec.lean
│       └── Invariants.lean
│
└── Proofs/                # Machine-checked proofs
    ├── Stdlib/Math.lean          # 14 theorems
    ├── SimpleStorage/            # 19 theorems
    ├── Counter/                  # 29 theorems
    ├── Owned/                    # 22 theorems
    ├── SimpleToken/              # 52 theorems (Basic + Correctness + Supply)
    ├── OwnedCounter/             # 31 theorems
    ├── Ledger/                   # 24 theorems
    └── SafeCounter/              # 24 theorems
```

Implementation, specification, and proofs remain completely separate.

## Verified Contracts

| Contract | Theorems | What's Proven |
|----------|----------|---------------|
| SimpleStorage | 19 | Store/retrieve roundtrip, state isolation, correctness specs |
| Counter | 29 | Arithmetic ops, composition, decrement-at-zero edge case |
| Owned | 22 | Access control, guard-protected ownership transfer |
| SimpleToken | 52 | Mint/transfer, supply conservation equations, revert proofs |
| OwnedCounter | 31 | Cross-pattern composition, ownership transfer isolation |
| Ledger | 24 | Mapping deposit/withdraw/transfer, balance guards |
| SafeCounter | 24 | Checked arithmetic, overflow/underflow revert proofs |
| Stdlib/Math | 14 | safeMul/safeDiv correctness, bounds, commutativity |

**Total: 230 theorems — zero sorry, zero axioms**

## Proven Properties

**Safety**: Balance non-negativity, access control, no overdrafts, overflow protection, safe arithmetic bounds

**Functional Correctness**: Every state transition matches its specification, constructor initialization, read operations

**Invariants**: WellFormedState preservation, owner stability, storage isolation, bounds preservation, supply invariant establishment

**Composition**: mint→balanceOf, transfer→balanceOf, store→retrieve roundtrip, increment→decrement cancellation, deposit→withdraw cancellation, cross-operation guard interaction

**Supply Conservation**: Exact sum equations for mint and transfer, transfer sum bounded

## Core API

```lean
-- Types
abbrev Address := String
abbrev Uint256 := Nat
structure StorageSlot (α : Type)

-- Contract monad with explicit success/failure
inductive ContractResult (α : Type) where
  | success : α → ContractState → ContractResult α
  | revert : String → ContractState → ContractResult α

abbrev Contract (α : Type) := ContractState → ContractResult α

-- Storage operations (type-safe)
def getStorage : StorageSlot Uint256 → Contract Uint256
def setStorage : StorageSlot Uint256 → Uint256 → Contract Unit
def getMapping : StorageSlot (Address → Uint256) → Address → Contract Uint256

-- Context
def msgSender : Contract Address
def contractAddress : Contract Address

-- Guards (explicit revert semantics)
def require : Bool → String → Contract Unit
```

## Design Evolution

The project evolved through 7 implementation iterations + verification phases:

1. **Bootstrap** — 58-line minimal core
2. **Counter** — Arithmetic operations
3. **Owned** — Access control (+14 lines)
4. **OwnedCounter** — Pattern composition (0 core changes)
5. **Math Safety** — Stdlib extensibility (0 core changes)
6. **Mapping Support** — Key-value storage (+13 lines)
7. **SimpleToken** — Full token contract (0 core changes)

Then verification: guard modeling, correctness proofs, supply conservation.

See [RESEARCH.md](RESEARCH.md) for complete design history.

## Verification Roadmap

- [x] SimpleStorage — 19 theorems proven
- [x] Counter — 29 theorems proven
- [x] Owned — 22 theorems proven
- [x] SimpleToken — 52 theorems proven (including supply conservation)
- [x] OwnedCounter — 31 theorems proven
- [x] Ledger — 24 theorems proven
- [x] SafeCounter — 24 theorems proven
- [x] Stdlib/Math — 14 theorems proven (safeMul/safeDiv)

## Getting Started

Requirements: [Lean 4](https://leanprover.github.io/) (4.15.0+)

```bash
git clone https://github.com/Th0rgal/dumbcontracts.git
cd dumbcontracts
lake build   # Verifies all 230 proofs
```

To write a verified contract:
1. Implementation → `DumbContracts/Examples/`
2. Specification → `DumbContracts/Specs/`
3. Proofs → `DumbContracts/Proofs/`

## Documentation

- [RESEARCH.md](RESEARCH.md) — Complete design history
- [STATUS.md](STATUS.md) — Current verification status (230 theorems)
- [ITERATION_*_SUMMARY.md](ITERATION_1_SUMMARY.md) — Detailed iteration breakdowns
- [docs-site/](docs-site/) — AI-friendly documentation website

## Key Results

**Minimalism** — 212-line core sufficient for realistic token contracts. 4 of 7 implementation iterations required zero core changes.

**Verification** — 230 theorems proven across 7 contracts + stdlib, establishing clear patterns for verifying smart contracts in Lean 4.

**Composability** — Patterns combine naturally without special support (OwnedCounter, SimpleToken).

**Supply Conservation** — Exact sum equations proven for mint and transfer operations, accounting for address occurrences in arbitrary lists.

## License

MIT

---

*From runtime confidence to mathematical certainty*
