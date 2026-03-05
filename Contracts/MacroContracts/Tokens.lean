import Contracts.MacroContracts.Common

namespace Contracts.MacroContracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

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

verity_contract ERC721 where
  storage
    ownerSlot : Address := slot 0
    totalSupplySlot : Uint256 := slot 1
    nextTokenIdSlot : Uint256 := slot 2
    ownersSlot : Uint256 → Uint256 := slot 3
    tokenApprovalsSlot : Uint256 → Uint256 := slot 4

  constructor (initialOwner : Address) := do
    setStorageAddr ownerSlot initialOwner
    setStorage totalSupplySlot 0
    setStorage nextTokenIdSlot 0

  function ownerOf (tokenId : Uint256) : Uint256 := do
    let ownerWord ← getMappingUint ownersSlot tokenId
    require (ownerWord != 0) "Token does not exist"
    return ownerWord

  function getApproved (tokenId : Uint256) : Uint256 := do
    let approvedWord ← getMappingUint tokenApprovalsSlot tokenId
    return approvedWord

  function approve (approved : Uint256, tokenId : Uint256) : Unit := do
    setMappingUint tokenApprovalsSlot tokenId approved

  function mint (to : Uint256) : Uint256 := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr ownerSlot
    require (sender == currentOwner) "Caller is not the owner"
    let tokenId ← getStorage nextTokenIdSlot
    let currentOwnerWord ← getMappingUint ownersSlot tokenId
    require (currentOwnerWord == 0) "Token already minted"
    let currentSupply ← getStorage totalSupplySlot
    let newSupply ← requireSomeUint (safeAdd currentSupply 1) "Supply overflow"
    setMappingUint ownersSlot tokenId to
    setStorage totalSupplySlot newSupply
    setStorage nextTokenIdSlot (add tokenId 1)
    return tokenId

  function transferFrom (fromAddr : Uint256, to : Uint256, tokenId : Uint256) : Unit := do
    let ownerWord ← getMappingUint ownersSlot tokenId
    require (ownerWord != 0) "Token does not exist"
    require (ownerWord == fromAddr) "From is not owner"
    let approvedWord ← getMappingUint tokenApprovalsSlot tokenId
    if approvedWord == 0 then
      pure ()
    else
      require (approvedWord == to) "Not authorized"
    setMappingUint ownersSlot tokenId to
    setMappingUint tokenApprovalsSlot tokenId 0

namespace SimpleToken

abbrev getTotalSupply : Contract Uint256 := totalSupply
abbrev getOwner : Contract Address := owner

def isOwner : Contract Bool := do
  let sender ← msgSender
  let currentOwner ← getStorageAddr ownerSlot
  return sender == currentOwner

def onlyOwner : Contract Unit := do
  let ownerCheck ← isOwner
  require ownerCheck "Caller is not the owner"

end SimpleToken

namespace ERC20

abbrev getTotalSupply : Contract Uint256 := totalSupply
abbrev getOwner : Contract Address := owner

def isOwner : Contract Bool := do
  let sender ← msgSender
  let currentOwner ← getStorageAddr ownerSlot
  return sender == currentOwner

def onlyOwner : Contract Unit := do
  let ownerCheck ← isOwner
  require ownerCheck "Caller is not the owner"

end ERC20


end Contracts.MacroContracts
