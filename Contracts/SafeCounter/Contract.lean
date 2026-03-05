import Contracts.MacroContracts.Core

namespace Contracts.SafeCounter

open Verity

def count : StorageSlot Uint256 := ⟨0⟩

abbrev increment := Contracts.MacroContracts.SafeCounter.increment
abbrev decrement := Contracts.MacroContracts.SafeCounter.decrement
abbrev getCount := Contracts.MacroContracts.SafeCounter.getCount

end Contracts.SafeCounter
