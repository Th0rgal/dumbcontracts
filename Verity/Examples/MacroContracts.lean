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

verity_contract Ledger where
  storage
    balances : Address → Uint256 := slot 0

  function deposit (amount : Uint256) : Unit := do
    let sender ← msgSender
    let currentBalance ← getMapping balances sender
    setMapping balances sender (add currentBalance amount)

  function withdraw (amount : Uint256) : Unit := do
    let sender ← msgSender
    let currentBalance ← getMapping balances sender
    require (currentBalance >= amount) "Insufficient balance"
    setMapping balances sender (sub currentBalance amount)

  function transfer (to : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    let senderBalance ← getMapping balances sender
    require (senderBalance >= amount) "Insufficient balance"

    if sender == to then
      pure ()
    else
      let recipientBalance ← getMapping balances to
      setMapping balances sender (sub senderBalance amount)
      setMapping balances to (add recipientBalance amount)

  function getBalance (addr : Address) : Uint256 := do
    let currentBalance ← getMapping balances addr
    return currentBalance

end Verity.Examples.MacroContracts
