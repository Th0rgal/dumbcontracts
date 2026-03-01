import Verity.Core
import Verity.EVM.Uint256
import Verity.Macro
import Verity.Stdlib.Math

namespace Verity.Examples.MacroContracts

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

def bitAnd (a b : Uint256) : Uint256 := Verity.Core.Uint256.and a b
def bitOr (a b : Uint256) : Uint256 := Verity.Core.Uint256.or a b
def bitXor (a b : Uint256) : Uint256 := Verity.Core.Uint256.xor a b

def mulDivDown (a b c : Uint256) : Uint256 := div (mul a b) c
def mulDivUp (a b c : Uint256) : Uint256 := div (add (mul a b) (sub c 1)) c

def wMulDown (a b : Uint256) : Uint256 := mulDivDown a b 1000000000000000000
def wDivUp (a b : Uint256) : Uint256 := mulDivUp a 1000000000000000000 b

def min (a b : Uint256) : Uint256 := if a <= b then a else b
def max (a b : Uint256) : Uint256 := if a >= b then a else b
def ite (cond : Prop) [Decidable cond] (thenVal elseVal : Uint256) : Uint256 :=
  if cond then thenVal else elseVal
def logicalAnd (a b : Uint256) : Uint256 := if a != 0 && b != 0 then 1 else 0
def logicalOr (a b : Uint256) : Uint256 := if a != 0 || b != 0 then 1 else 0
def logicalNot (a : Uint256) : Uint256 := if a == 0 then 1 else 0
def calldatasize : Uint256 := 0
def returndataSize : Uint256 := 0
def calldataload (offset : Uint256) : Uint256 := offset
def mload (offset : Uint256) : Uint256 := offset
def extcodesize (addr : Uint256) : Uint256 := addr
def keccak256 (offset size : Uint256) : Uint256 := add offset size
def call (gas target value inOffset inSize outOffset outSize : Uint256) : Uint256 :=
  add gas (add target (add value (add inOffset (add inSize (add outOffset outSize)))))
def staticcall (gas target inOffset inSize outOffset outSize : Uint256) : Uint256 :=
  add gas (add target (add inOffset (add inSize (add outOffset outSize))))
def delegatecall (gas target inOffset inSize outOffset outSize : Uint256) : Uint256 :=
  add gas (add target (add inOffset (add inSize (add outOffset outSize))))
def calldatacopy (_destOffset _sourceOffset _size : Uint256) : Contract Unit := pure ()
def returndataCopy (_destOffset _sourceOffset _size : Uint256) : Contract Unit := pure ()
def revertReturndata : Contract Unit := pure ()
def mstore (_offset _value : Uint256) : Contract Unit := pure ()
def getMappingWord (_slot : StorageSlot (Uint256 → Uint256)) (_key _wordOffset : Uint256) :
    Contract Uint256 := pure 0
def setMappingWord (_slot : StorageSlot (Uint256 → Uint256)) (_key _wordOffset _value : Uint256) :
    Contract Unit := pure ()
def forEach (_name : String) (_count : Uint256) (body : Contract Unit) : Contract Unit := body
def blockTimestamp : Uint256 := 0
def contractAddress : Uint256 := 0
def chainid : Uint256 := 0

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

  function previewAddTwice (delta : Uint256) : Uint256 := do
    let base ← getStorage count
    let mut acc := base
    acc := add acc delta
    acc := add acc delta
    return acc

  function previewOps (x : Uint256, y : Uint256, z : Uint256) : Uint256 := do
    let product := mul x y
    let quotient := div product z
    let remainder := mod product z
    let lowBits := bitAnd product 255
    let mixed := bitOr lowBits (bitXor x y)
    let shifted := shl 2 mixed
    let unshifted := shr 1 shifted
    let bounded := min (max quotient remainder) unshifted
    let scaledDown := mulDivDown bounded x z
    let scaledUp := mulDivUp bounded y z
    let wadDown := wMulDown scaledDown scaledUp
    let wadUp := wDivUp wadDown z
    let chosen := ite (x > y) wadUp (sub wadUp 1)
    return chosen

  function previewEnvOps (x : Uint256, y : Uint256) : Uint256 := do
    let ts := blockTimestamp
    let self := contractAddress
    let cid := chainid
    let flagAnd := logicalAnd x y
    let flagOr := logicalOr x y
    let flagNot := logicalNot x
    let hashInput := add (add ts self) cid
    let memWord := mload hashInput
    let digest := keccak256 memWord 64
    return (add (add digest flagAnd) (add flagOr flagNot))

  function previewLowLevel (target : Uint256, count : Uint256) : Uint256 := do
    let cds := calldatasize
    let head := calldataload 0
    mstore 0 head
    calldatacopy 32 4 32
    let ok := call 50000 target 0 0 64 0 32
    let okStatic := staticcall 50000 target 0 64 0 32
    let okDelegate := delegatecall 50000 target 0 64 0 32
    forEach "i" count (do
      mstore 96 count
      pure ())
    if ok == 0 then
      revertReturndata
    else
      pure ()
    returndataCopy 0 0 32
    let rds := returndataSize
    return (add (add (add cds rds) okStatic) okDelegate)

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

verity_contract UintMapSmoke where
  storage
    values : Uint256 → Uint256 := slot 0

  function setValue (key : Uint256, value : Uint256) : Unit := do
    setMappingUint values key value

  function getValue (key : Uint256) : Uint256 := do
    let current ← getMappingUint values key
    return current

verity_contract Bytes32Smoke where
  storage
    value : Uint256 := slot 0

  function setDigest (digest : Bytes32) : Unit := do
    setStorage value digest

  function getDigest () : Bytes32 := do
    let digest ← getStorage value
    return digest

verity_contract MappingWordSmoke where
  storage
    words : Uint256 → Uint256 := slot 0

  function setWord1 (key : Uint256, value : Uint256) : Unit := do
    setMappingWord words key 1 value

  function getWord1 (key : Uint256) : Uint256 := do
    let word ← getMappingWord words key 1
    return word

#check_contract Counter
#check_contract UintMapSmoke
#check_contract Bytes32Smoke
#check_contract MappingWordSmoke

end Verity.Examples.MacroContracts
