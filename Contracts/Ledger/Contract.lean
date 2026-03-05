import Contracts.MacroContracts.Core

namespace Contracts.Ledger

open Verity

def balances : StorageSlot (Address → Uint256) := ⟨0⟩

abbrev deposit := Contracts.MacroContracts.Ledger.deposit
abbrev withdraw := Contracts.MacroContracts.Ledger.withdraw
abbrev transfer := Contracts.MacroContracts.Ledger.transfer
abbrev getBalance := Contracts.MacroContracts.Ledger.getBalance

end Contracts.Ledger
