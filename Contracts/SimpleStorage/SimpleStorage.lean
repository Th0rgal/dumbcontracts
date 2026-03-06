import Contracts.Common

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract SimpleStorage where
  storage
    storedData : Uint256 := slot 0

  function store (value : Uint256) : Unit := do
    setStorage storedData value

  function retrieve () : Uint256 := do
    let current ← getStorage storedData
    return current

end Contracts
