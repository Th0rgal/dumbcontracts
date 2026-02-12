# Dumb Contracts

A minimal Lean 4 embedded DSL for writing and formally verifying smart contracts.

The core is 212 lines of Lean. It models contract state, storage operations, and `require` guards using an explicit success/revert result type. On top of this, 7 example contracts are implemented and verified with 252 machine-checked proofs (no `sorry`, no axioms).

## What's New (PR #12)

**🎉 Compiler Verification Layer 1 Complete!**

All 7 contracts now have **specification correctness proofs**: mathematical proof that the compiler's intermediate representation accurately captures the EDSL behavior.

- ✅ 2,800+ lines of new proofs
- ✅ SimpleStorage, Counter, SafeCounter, Owned, OwnedCounter, Ledger, SimpleToken
- ✅ Zero `sorry`, zero axioms
- ✅ All Lean builds passing

**Next**: Layer 2 (IR generation) and Layer 3 (Yul codegen)

## Example

```lean
-- Implementation
def storedData : StorageSlot Uint256 := ⟨0⟩

def store (value : Uint256) : Contract Unit := do
  setStorage storedData value

def retrieve : Contract Uint256 := do
  getStorage storedData

-- Proof: retrieve returns what store stored
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
lake build  # Type-checks all proofs (252 contract + 7 compiler)
```

## Contracts

| Contract | Theorems | What's verified |
|----------|----------|-----------------|
| SimpleStorage | 19 | Store/retrieve roundtrip, state isolation |
| Counter | 29 | Arithmetic, composition, decrement-at-zero |
| Owned | 22 | Access control, ownership transfer |
| SimpleToken | 64 | Mint/transfer, supply conservation, storage isolation |
| OwnedCounter | 34 | Cross-pattern composition, ownership transfer lockout |
| Ledger | 40 | Deposit/withdraw/transfer, balance conservation |
| SafeCounter | 30 | Overflow/underflow revert proofs |
| Stdlib/Math | 14 | safeMul/safeDiv correctness |

## What's proven

**Contract Correctness (252 proofs):**
- **Safety**: Access control (mint reverts for non-owner), no overdrafts (transfer reverts on insufficient balance), overflow protection
- **Correctness**: Each state-modifying operation matches its specification
- **Invariants**: WellFormedState preservation, owner stability, storage isolation between slot types
- **Composition**: Operation sequences produce expected results (mint then balanceOf, deposit then withdraw cancellation, ownership transfer locks out old owner)
- **Conservation**: Exact sum equations for token mint/transfer and ledger deposit/withdraw/transfer

**Compiler Verification (new!):**
- ✅ **Layer 1**: EDSL ≡ ContractSpec (7 spec correctness proofs)
- 🚧 **Layer 2**: ContractSpec → IR preservation (in progress)
- 🔲 **Layer 3**: IR → Yul codegen (planned)

## Project structure

```
DumbContracts/
├── Core/                      # Core types and 212-line EDSL
│   ├── State.lean            # ContractState, ContractResult monad
│   └── Uint256.lean          # Modular 256-bit arithmetic
├── Stdlib/Math.lean          # Safe arithmetic (safeAdd, safeSub, safeMul, safeDiv)
├── Examples/                  # 7 verified contract implementations
├── Specs/                     # Formal specifications (Spec.lean, Invariants.lean)
└── Proofs/                    # 252 machine-checked correctness proofs

Compiler/
├── ContractSpec.lean          # Declarative intermediate representation
├── Specs.lean                 # All 7 contract specifications
├── IR.lean                    # Intermediate representation for codegen
├── Codegen.lean               # IR → Yul generation
├── Interpreter.lean           # Reference interpreter (for diff tests)
└── Proofs/                    # Compiler verification (NEW!)
    ├── SpecCorrectness/       # Layer 1: EDSL ≡ Spec (7 proofs) ✅
    ├── IRGeneration/          # Layer 2: Spec → IR 🚧
    └── YulGeneration/         # Layer 3: IR → Yul 🔲

examples/solidity/             # Solidity reference contracts
compiler/yul/                  # Generated Yul output (auto-generated)
test/                          # 264 Foundry tests (all passing)
docs-site/                     # Documentation website
```

## Core API

```lean
-- Contract monad with explicit success/failure
inductive ContractResult (α : Type) where
  | success : α → ContractState → ContractResult α
  | revert : String → ContractState → ContractResult α

abbrev Contract (α : Type) := ContractState → ContractResult α

-- Storage operations
def getStorage : StorageSlot Uint256 → Contract Uint256
def setStorage : StorageSlot Uint256 → Uint256 → Contract Unit
def getMapping : StorageSlot (Address → Uint256) → Address → Contract Uint256
def setMapping : StorageSlot (Address → Uint256) → Address → Uint256 → Contract Unit

-- Guards
def require : Bool → String → Contract Unit
```

The `ContractResult` type makes `require` failures explicit. The custom `bind` short-circuits on `revert`, so do-notation works like Solidity: a failed `require` stops execution and reverts.

## Getting started

Requires [Lean 4](https://leanprover.github.io/) (4.15.0+).

```bash
git clone https://github.com/Th0rgal/dumbcontracts.git
cd dumbcontracts
lake build
```

To write a verified contract, add files in three places:
1. `DumbContracts/Examples/YourContract.lean` for the implementation
2. `DumbContracts/Specs/YourContract/` for the specifications
3. `DumbContracts/Proofs/YourContract/` for the proofs

## Compiler & Testing

**Compile contracts to Yul:**
```bash
lake exe dumbcontracts-compiler  # Outputs to compiler/yul/
```

**Run tests:**
```bash
forge test  # 264 tests: original + differential + property tests
```

**Test coverage:**
- 76 original functionality tests
- 130 differential tests (70,000+ transactions comparing EDSL vs EVM)
- 58 property tests (auto-generated from proven theorems)
- **Zero mismatches** across all differential tests

## Known limitations

- Transfer proofs require `sender != to` (self-transfer overwrites the sender deduction)
- Uint256 is a dedicated 256-bit modular type; `+`, `-`, `*`, `/`, and `%` wrap at `2^256`
- No multi-contract interaction
- No reentrancy modeling
- No Mathlib dependency, so `ring`, `linarith`, etc. are unavailable

## Documentation

- [AGENTS.md](AGENTS.md) - Project architecture and verification status
- [Compiler/Proofs/README.md](Compiler/Proofs/README.md) - Detailed compiler verification roadmap
- [docs-site/](docs-site/) - Documentation website

## License

MIT
