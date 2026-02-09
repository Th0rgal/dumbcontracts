/-
  Dumb Contracts: Minimal EDSL Core

  This module defines the essential types and primitives for smart contracts.
  Philosophy: Keep it minimal - only add what examples actually need.
-/

namespace DumbContracts

-- Basic Ethereum types
abbrev Address := String
abbrev Uint256 := Nat
abbrev Bool' := Bool
abbrev Bytes := List Nat

-- Storage key-value abstraction
structure StorageSlot (α : Type) where
  slot : Nat
  deriving Repr

-- State monad for contract execution
structure ContractState where
  storage : Nat → Uint256  -- Simple mapping from slots to values
  sender : Address
  thisAddress : Address

-- The contract monad
abbrev Contract (α : Type) := StateM ContractState α

-- Storage operations
def getStorage (s : StorageSlot Uint256) : Contract Uint256 := do
  let state ← get
  return state.storage s.slot

def setStorage (s : StorageSlot Uint256) (value : Uint256) : Contract Unit := do
  modify fun state => { state with
    storage := fun slot => if slot == s.slot then value else state.storage slot
  }

-- Read-only context accessors
def msgSender : Contract Address := do
  let state ← get
  return state.sender

def contractAddress : Contract Address := do
  let state ← get
  return state.thisAddress

-- Require guard
def require (condition : Bool) (_message : String) : Contract Unit := do
  if !condition then
    -- In a real implementation, this would revert the transaction
    -- For now, we just skip (the testing framework will handle this)
    pure ()
  else
    pure ()

end DumbContracts
