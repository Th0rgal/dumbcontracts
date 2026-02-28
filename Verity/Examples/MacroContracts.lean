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
    owner : Address := slot 0
    balances : Address → Uint256 := slot 1
    totalSupply : Uint256 := slot 2

  function mint (to : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"
    let currentBalance ← getMapping balances to
    let newBalance ← requireSomeUint (safeAdd currentBalance amount) "Balance overflow"
    let currentSupply ← getStorage totalSupply
    let newSupply ← requireSomeUint (safeAdd currentSupply amount) "Supply overflow"
    setMapping balances to newBalance
    setStorage totalSupply newSupply

  function transfer (to : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    let senderBalance ← getMapping balances sender
    require (senderBalance >= amount) "Insufficient balance"

    if sender == to then
      pure ()
    else
      let recipientBalance ← getMapping balances to
      let newRecipientBalance ← requireSomeUint (safeAdd recipientBalance amount) "Recipient balance overflow"
      setMapping balances sender (sub senderBalance amount)
      setMapping balances to newRecipientBalance

  function balanceOf (addr : Address) : Uint256 := do
    let currentBalance ← getMapping balances addr
    return currentBalance

  function getTotalSupply () : Uint256 := do
    let currentSupply ← getStorage totalSupply
    return currentSupply

  function getOwner () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

verity_contract ERC20 where
  storage
    owner : Address := slot 0
    totalSupply : Uint256 := slot 1
    balances : Address → Uint256 := slot 2
    allowances : Address → Address → Uint256 := slot 3

  function mint (to : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr owner
    require (sender == currentOwner) "Caller is not the owner"
    let currentBalance ← getMapping balances to
    let newBalance ← requireSomeUint (safeAdd currentBalance amount) "Balance overflow"
    let currentSupply ← getStorage totalSupply
    let newSupply ← requireSomeUint (safeAdd currentSupply amount) "Supply overflow"
    setMapping balances to newBalance
    setStorage totalSupply newSupply

  function transfer (to : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    let senderBalance ← getMapping balances sender
    require (senderBalance >= amount) "Insufficient balance"

    if sender == to then
      pure ()
    else
      let recipientBalance ← getMapping balances to
      let newRecipientBalance ← requireSomeUint (safeAdd recipientBalance amount) "Recipient balance overflow"
      setMapping balances sender (sub senderBalance amount)
      setMapping balances to newRecipientBalance

  function approve (spender : Address, amount : Uint256) : Unit := do
    let sender ← msgSender
    setMapping2 allowances sender spender amount

  function transferFrom (fromAddr : Address, to : Address, amount : Uint256) : Unit := do
    let spender ← msgSender
    let currentAllowance ← getMapping2 allowances fromAddr spender
    require (currentAllowance >= amount) "Insufficient allowance"

    let fromBalance ← getMapping balances fromAddr
    require (fromBalance >= amount) "Insufficient balance"

    if fromAddr == to then
      pure ()
    else
      let toBalance ← getMapping balances to
      let newToBalance ← requireSomeUint (safeAdd toBalance amount) "Recipient balance overflow"
      setMapping balances fromAddr (sub fromBalance amount)
      setMapping balances to newToBalance

    if currentAllowance == 115792089237316195423570985008687907853269984665640564039457584007913129639935 then
      pure ()
    else
      setMapping2 allowances fromAddr spender (sub currentAllowance amount)

  function balanceOf (addr : Address) : Uint256 := do
    let currentBalance ← getMapping balances addr
    return currentBalance

  function allowanceOf (ownerAddr : Address, spender : Address) : Uint256 := do
    let currentAllowance ← getMapping2 allowances ownerAddr spender
    return currentAllowance

  function getTotalSupply () : Uint256 := do
    let currentSupply ← getStorage totalSupply
    return currentSupply

  function getOwner () : Address := do
    let currentOwner ← getStorageAddr owner
    return currentOwner

end Verity.Examples.MacroContracts
