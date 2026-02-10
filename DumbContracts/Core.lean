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
  storage : Nat → Uint256                -- Uint256 storage mapping
  storageAddr : Nat → Address            -- Address storage mapping
  storageMap : Nat → Address → Uint256  -- Mapping storage (Address → Uint256)
  sender : Address
  thisAddress : Address

-- The contract monad
abbrev Contract (α : Type) := StateM ContractState α

-- Storage operations for Uint256
def getStorage (s : StorageSlot Uint256) : Contract Uint256 := do
  let state ← get
  return state.storage s.slot

def setStorage (s : StorageSlot Uint256) (value : Uint256) : Contract Unit := do
  modify fun state => { state with
    storage := fun slot => if slot == s.slot then value else state.storage slot
  }

-- Storage operations for Address
def getStorageAddr (s : StorageSlot Address) : Contract Address := do
  let state ← get
  return state.storageAddr s.slot

def setStorageAddr (s : StorageSlot Address) (value : Address) : Contract Unit := do
  modify fun state => { state with
    storageAddr := fun slot => if slot == s.slot then value else state.storageAddr slot
  }

-- Mapping operations (Address → Uint256)
def getMapping (s : StorageSlot (Address → Uint256)) (key : Address) : Contract Uint256 := do
  let state ← get
  return state.storageMap s.slot key

def setMapping (s : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256) : Contract Unit := do
  modify fun state => { state with
    storageMap := fun slot addr =>
      if slot == s.slot && addr == key then value
      else state.storageMap slot addr
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
