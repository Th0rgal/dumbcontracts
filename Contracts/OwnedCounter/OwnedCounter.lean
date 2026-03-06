import Contracts.Common

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract OwnedCounter where
  storage
    owner : Address := slot 0
    count : Uint256 := slot 1

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  function increment () : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"
    let current ← getStorage count
    setStorage count (add current 1)

  function decrement () : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"
    let current ← getStorage count
    setStorage count (sub current 1)

  function getCount () : Uint256 := do
    let current ← getStorage count
    return current

  function getOwner () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

  function transferOwnership (newOwner : Address) : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"
    setStorageAddr owner newOwner

namespace OwnedCounter

def isOwner : Contract Bool := do
  let sender ← msgSender
  let currentOwner ← getStorageAddr owner
  return sender == currentOwner

def onlyOwner : Contract Unit := do
  let ownerCheck ← isOwner
  require ownerCheck "Caller is not the owner"

end OwnedCounter

end Contracts
