import Contracts.MacroContracts.Core

namespace Contracts.Counter

open Verity

def count : StorageSlot Uint256 := ⟨0⟩

abbrev increment := Contracts.MacroContracts.Counter.increment
abbrev decrement := Contracts.MacroContracts.Counter.decrement
abbrev getCount := Contracts.MacroContracts.Counter.getCount
abbrev previewAddTwice := Contracts.MacroContracts.Counter.previewAddTwice
abbrev previewOps := Contracts.MacroContracts.Counter.previewOps
abbrev previewEnvOps := Contracts.MacroContracts.Counter.previewEnvOps
abbrev previewLowLevel := Contracts.MacroContracts.Counter.previewLowLevel

end Contracts.Counter
