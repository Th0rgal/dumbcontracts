# Dumb Contracts

A minimal, elegant Lean 4 EDSL for smart contract development.

## Philosophy

**Dumb Contracts** is intentionally minimal. We only add features when concrete examples demonstrate the need. The goal is to make smart contract development:

- **Simple**: Minimal boilerplate, clear syntax
- **Safe**: Type-safe storage, explicit state management
- **Testable**: Paired with Foundry tests for runtime validation
- **Maintainable**: Small, focused examples that are easy to understand

## Project Structure

```
DumbContracts/
├── Core.lean                    # Minimal EDSL core (~60 lines)
├── Examples/                    # One contract per file
│   └── SimpleStorage.lean       # Basic storage pattern
└── Stdlib/                      # Common patterns (future)

contracts/                       # Solidity reference implementations
test/                           # Foundry tests for validation
```

## Quick Start

### Build the Lean project

```bash
lake build
```

### Run Foundry tests

```bash
forge test
```

## Examples

### SimpleStorage

The simplest possible contract - store and retrieve a value:

```lean
-- Storage layout
def storedData : StorageSlot Uint256 := ⟨0⟩

-- Set the stored value
def store (value : Uint256) : Contract Unit := do
  setStorage storedData value

-- Get the stored value
def retrieve : Contract Uint256 := do
  getStorage storedData
```

See `DumbContracts/Examples/SimpleStorage.lean` for the complete example.

## Development Process

Each iteration:
1. Pick ONE feature or pattern to showcase
2. Implement the smallest change that makes the EDSL easier to use
3. Add a focused example contract
4. Add a Foundry test
5. Update STATUS.md and RESEARCH.md

## Core API

### Types
- `Address` - Ethereum address (String for now)
- `Uint256` - Unsigned 256-bit integer (Nat)
- `StorageSlot α` - Type-safe storage location
- `Contract α` - Contract computation monad

### Storage
- `getStorage : StorageSlot Uint256 → Contract Uint256`
- `setStorage : StorageSlot Uint256 → Uint256 → Contract Unit`

### Context
- `msgSender : Contract Address`
- `contractAddress : Contract Address`

### Guards
- `require : Bool → String → Contract Unit`

## Status

See `STATUS.md` for current research goals and `RESEARCH.md` for detailed findings.

## License

MIT
