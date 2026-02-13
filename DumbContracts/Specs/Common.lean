/-
  Shared helpers for specs.

  Keep specs human-friendly by naming the common "unchanged" clauses
  instead of repeating field-by-field equality.
-/

import DumbContracts.Core

namespace DumbContracts.Specs

open DumbContracts

/-- Contract context (sender, address, msg value, timestamp) is unchanged. -/
def sameContext (s s' : ContractState) : Prop :=
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.msgValue = s.msgValue ∧
  s'.blockTimestamp = s.blockTimestamp

/-- Uint256 storage is unchanged. -/
def sameStorage (s s' : ContractState) : Prop :=
  s'.storage = s.storage

/-- Address storage is unchanged. -/
def sameStorageAddr (s s' : ContractState) : Prop :=
  s'.storageAddr = s.storageAddr

/-- Mapping storage is unchanged. -/
def sameStorageMap (s s' : ContractState) : Prop :=
  s'.storageMap = s.storageMap

end DumbContracts.Specs
