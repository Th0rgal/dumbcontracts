import Contracts.MacroContracts.Common

namespace Contracts.MacroContracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract SafeCounter where
  storage
    count : Uint256 := slot 0

  function increment () : Unit := do
    let current ← getStorage count
    let newCount ← requireSomeUint (safeAdd current 1) "Overflow in increment"
    setStorage count newCount

  function decrement () : Unit := do
    let current ← getStorage count
    let newCount ← requireSomeUint (safeSub current 1) "Underflow in decrement"
    setStorage count newCount

  function getCount () : Uint256 := do
    let current ← getStorage count
    return current

end Contracts.MacroContracts
