/-
  Formal specifications for Ledger contract operations.

  Ledger uses mapping storage (slot 0: Address → Uint256) for balances.
  Operations: deposit, withdraw, transfer, getBalance.
-/

import DumbContracts.Core
import DumbContracts.Specs.Common
import DumbContracts.EVM.Uint256
import DumbContracts.Examples.Ledger

namespace DumbContracts.Specs.Ledger

open DumbContracts
open DumbContracts.Examples.Ledger
open DumbContracts.EVM.Uint256

/-! ## Operation Specifications -/

/-- deposit: increases sender's balance by amount -/
def deposit_spec (amount : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 0 s.sender = add (s.storageMap 0 s.sender) amount ∧
  storageMapUnchangedExceptKeyAtSlot 0 s.sender s s' ∧
  sameStorageAddrContext s s'

/-- withdraw (when sufficient balance): decreases sender's balance by amount -/
def withdraw_spec (amount : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 0 s.sender = sub (s.storageMap 0 s.sender) amount ∧
  storageMapUnchangedExceptKeyAtSlot 0 s.sender s s' ∧
  sameStorageAddrContext s s'

/-- transfer (when sufficient balance, sender ≠ to):
    decreases sender balance, increases recipient balance -/
def transfer_spec (to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 0 s.sender = sub (s.storageMap 0 s.sender) amount ∧
  s'.storageMap 0 to = add (s.storageMap 0 to) amount ∧
  storageMapUnchangedExceptKeysAtSlot 0 s.sender to s s' ∧
  sameStorageAddrContext s s'

/-- getBalance: returns balance at given address, no state change -/
def getBalance_spec (addr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 0 addr

end DumbContracts.Specs.Ledger
