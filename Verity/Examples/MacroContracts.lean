import Verity.Core
import Verity.EVM.Uint256
import Verity.Macro
import Verity.Stdlib.Math

namespace Verity.Examples.MacroContracts

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract SimpleStorage where
  storage
    storedData : Uint256 := slot 0

  function store (value : Uint256) : Unit := do
    setStorage storedData value

  function retrieve () : Uint256 := do
    let current ← getStorage storedData
    return current

verity_contract Counter where
  storage
    count : Uint256 := slot 0

  function increment () : Unit := do
    let current ← getStorage count
    setStorage count (add current 1)

  function decrement () : Unit := do
    let current ← getStorage count
    setStorage count (sub current 1)

  function getCount () : Uint256 := do
    let current ← getStorage count
    return current

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

verity_contract SimpleToken where
  storage
    ownerSlot : Address := slot 0
    balancesSlot : Address → Uint256 := slot 1
    totalSupplySlot : Uint256 := slot 2

  constructor (initialOwner : Address) := do
    setStorageAddr ownerSlot initialOwner
    setStorage totalSupplySlot 0

  function mint (to : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr ownerSlot
    require (sender == currentOwner) "Caller is not the owner"
    let currentBalance ← getMapping balancesSlot to
    let newBalance ← requireSomeUint (safeAdd currentBalance amount) "Balance overflow"
    let currentSupply ← getStorage totalSupplySlot
    let newSupply ← requireSomeUint (safeAdd currentSupply amount) "Supply overflow"
    setMapping balancesSlot to newBalance
    setStorage totalSupplySlot newSupply

  function transfer (to : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    let senderBalance ← getMapping balancesSlot sender
    require (senderBalance >= amount) "Insufficient balance"

    if sender == to then
      pure ()
    else
      let recipientBalance ← getMapping balancesSlot to
      let newRecipientBalance ← requireSomeUint (safeAdd recipientBalance amount) "Recipient balance overflow"
      setMapping balancesSlot sender (sub senderBalance amount)
      setMapping balancesSlot to newRecipientBalance

  function balanceOf (addr : Address) : Uint256 := do
    let currentBalance ← getMapping balancesSlot addr
    return currentBalance

  function totalSupply () : Uint256 := do
    let currentSupply ← getStorage totalSupplySlot
    return currentSupply

  function owner () : Address := do
    let currentOwner ← getStorageAddr ownerSlot
    return currentOwner

verity_contract ERC20 where
  storage
    ownerSlot : Address := slot 0
    totalSupplySlot : Uint256 := slot 1
    balancesSlot : Address → Uint256 := slot 2
    allowancesSlot : Address → Address → Uint256 := slot 3

  constructor (initialOwner : Address) := do
    setStorageAddr ownerSlot initialOwner
    setStorage totalSupplySlot 0

  function mint (to : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr ownerSlot
    require (sender == currentOwner) "Caller is not the owner"
    let currentBalance ← getMapping balancesSlot to
    let newBalance ← requireSomeUint (safeAdd currentBalance amount) "Balance overflow"
    let currentSupply ← getStorage totalSupplySlot
    let newSupply ← requireSomeUint (safeAdd currentSupply amount) "Supply overflow"
    setMapping balancesSlot to newBalance
    setStorage totalSupplySlot newSupply

  function transfer (to : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    let senderBalance ← getMapping balancesSlot sender
    require (senderBalance >= amount) "Insufficient balance"

    if sender == to then
      pure ()
    else
      let recipientBalance ← getMapping balancesSlot to
      let newRecipientBalance ← requireSomeUint (safeAdd recipientBalance amount) "Recipient balance overflow"
      setMapping balancesSlot sender (sub senderBalance amount)
      setMapping balancesSlot to newRecipientBalance

  function approve (spender : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    setMapping2 allowancesSlot sender spender amount

  function transferFrom (fromAddr : Address, to : Address, amount : Uint256) : Unit := do
    let spender ← msgSender
    let currentAllowance ← getMapping2 allowancesSlot fromAddr spender
    require (currentAllowance >= amount) "Insufficient allowance"

    let fromBalance ← getMapping balancesSlot fromAddr
    require (fromBalance >= amount) "Insufficient balance"

    if fromAddr == to then
      pure ()
    else
      let toBalance ← getMapping balancesSlot to
      let newToBalance ← requireSomeUint (safeAdd toBalance amount) "Recipient balance overflow"
      setMapping balancesSlot fromAddr (sub fromBalance amount)
      setMapping balancesSlot to newToBalance

    if currentAllowance == 115792089237316195423570985008687907853269984665640564039457584007913129639935 then
      pure ()
    else
      setMapping2 allowancesSlot fromAddr spender (sub currentAllowance amount)

  function balanceOf (addr : Address) : Uint256 := do
    let currentBalance ← getMapping balancesSlot addr
    return currentBalance

  function allowanceOf (ownerAddr : Address, spender : Address) : Uint256 := do
    let currentAllowance ← getMapping2 allowancesSlot ownerAddr spender
    return currentAllowance

  function totalSupply () : Uint256 := do
    let currentSupply ← getStorage totalSupplySlot
    return currentSupply

  function owner () : Address := do
    let currentOwner ← getStorageAddr ownerSlot
    return currentOwner

end Verity.Examples.MacroContracts
