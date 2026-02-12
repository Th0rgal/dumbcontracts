/-
  Safe Multisig Base (Scaffold)

  This file is a minimal, compiling placeholder for the Safe base contract.
  The goal is to replace these definitions with the real EDSL implementation
  that mirrors the latest Safe base contract from safe-smart-account.

  TODO:
  - Implement core functions (setup, execTransaction, etc.) in EDSL
  - Align with Solidity ABI encoding rules
-/

import DumbContracts.Core

namespace DumbContracts.Examples.SafeMultisigBase

open DumbContracts

-- Safe base storage layout (linearized inheritance order).
-- NOTE: Some mappings use non-Address keys in Solidity; those are documented
-- in docs/safe-multisig-base/storage-layout.md and will be modeled later.
def singleton : StorageSlot Address := ⟨0⟩
def ownerCount : StorageSlot Uint256 := ⟨3⟩
def threshold : StorageSlot Uint256 := ⟨4⟩
def nonce : StorageSlot Uint256 := ⟨5⟩
def deprecatedDomainSeparator : StorageSlot Uint256 := ⟨6⟩

/-- Placeholder constructor: Safe singleton initializes threshold = 1. -/
def constructor : Contract Unit := do
  setStorage threshold 1

/-- Placeholder getter: returns threshold. -/
def getThreshold : Contract Uint256 := do
  getStorage threshold

end DumbContracts.Examples.SafeMultisigBase
