import Contracts.Common

namespace Contracts

open Verity hiding pure bind

verity_contract Owned where
  storage
    owner : Address := slot 0

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  function transferOwnership (newOwner : Address) : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"
    setStorageAddr owner newOwner

  function getOwner () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

namespace Owned

def isOwner : Contract Bool := do
  let sender ← msgSender
  let currentOwner ← getStorageAddr owner
  return sender == currentOwner

def onlyOwner : Contract Unit := do
  let ownerCheck ← isOwner
  require ownerCheck "Caller is not the owner"

end Owned

end Contracts
