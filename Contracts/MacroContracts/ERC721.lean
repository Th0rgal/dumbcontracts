import Contracts.MacroContracts.Common

namespace Contracts.MacroContracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

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

end Contracts.MacroContracts
