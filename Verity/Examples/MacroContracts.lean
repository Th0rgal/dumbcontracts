import Verity.Core
import Verity.EVM.Uint256
import Verity.Macro

namespace Verity.Examples.MacroContracts

open Verity
open Verity.EVM.Uint256

verity_contract Counter where
  storage
    count : Uint256 := slot 0

  function increment () : Unit := do
    let current ← getStorage count
    setStorage count (add current 1)

  function getCount () : Uint256 := do
    let current ← getStorage count
    return current

verity_contract Owned where
  storage
    owner : Address := slot 0

  function transferOwnership (newOwner : Address) : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"
    setStorageAddr owner newOwner

  function getOwner () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

end Verity.Examples.MacroContracts
