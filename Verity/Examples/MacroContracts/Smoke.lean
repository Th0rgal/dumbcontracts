import Verity.Examples.MacroContracts.Core
import Verity.Examples.MacroContracts.Tokens

namespace Verity.Examples.MacroContracts

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

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

  function isWord1NonZero (key : Uint256) : Bool := do
    let word ← getMappingWord words key 1
    return (word != 0)

verity_contract StorageWordsSmoke where
  storage
    sentinel : Uint256 := slot 0

  function extSloadsLike (slots : Array Bytes32) : Array Uint256 := do
    returnStorageWords slots

verity_contract TupleSmoke where
  storage
    values : Uint256 → Uint256 := slot 0
    authorized : Address → Uint256 := slot 1

  function setFromPair (pair : Tuple [Uint256, Uint256]) : Unit := do
    let pair' := pair
    let _ignored := pair'
    pure ()

  function getPair (key : Uint256) : Tuple [Uint256, Uint256] := do
    returnValues [key, key]

  function processConfig (cfg : Tuple [Address, Address, Uint256]) : Unit := do
    let cfg' := cfg
    let _ignored := cfg'
    pure ()

verity_contract Uint8Smoke where
  storage
    sentinel : Uint256 := slot 0

  function acceptSig (sig : Tuple [Uint8, Bytes32, Bytes32]) : Unit := do
    let sig' := sig
    let _ignored := sig'
    pure ()

  function sigV () : Uint8 := do
    return 27

#check_contract Counter
#check_contract UintMapSmoke
#check_contract Bytes32Smoke
#check_contract MappingWordSmoke
#check_contract StorageWordsSmoke
#check_contract TupleSmoke
#check_contract Uint8Smoke

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Counter.increment_model : Compiler.CompilationModel.FunctionSpec)) =
    Counter.increment_modelBody := by
  simpa using Counter.increment_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Counter.increment_model : Compiler.CompilationModel.FunctionSpec)) =
    Counter.increment_modelBody := by
  simpa using Counter.increment_bridge

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Counter.decrement_model : Compiler.CompilationModel.FunctionSpec)) =
    Counter.decrement_modelBody := by
  simpa using Counter.decrement_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Counter.decrement_model : Compiler.CompilationModel.FunctionSpec)) =
    Counter.decrement_modelBody := by
  simpa using Counter.decrement_bridge

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Counter.getCount_model : Compiler.CompilationModel.FunctionSpec)) =
    Counter.getCount_modelBody := by
  simpa using Counter.getCount_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Counter.getCount_model : Compiler.CompilationModel.FunctionSpec)) =
    Counter.getCount_modelBody := by
  simpa using Counter.getCount_bridge

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (SimpleStorage.store_model : Compiler.CompilationModel.FunctionSpec)) =
    SimpleStorage.store_modelBody := by
  simpa using SimpleStorage.store_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (SimpleStorage.retrieve_model : Compiler.CompilationModel.FunctionSpec)) =
    SimpleStorage.retrieve_modelBody := by
  simpa using SimpleStorage.retrieve_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Owned.transferOwnership_model : Compiler.CompilationModel.FunctionSpec)) =
    Owned.transferOwnership_modelBody := by
  simpa using Owned.transferOwnership_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Owned.getOwner_model : Compiler.CompilationModel.FunctionSpec)) =
    Owned.getOwner_modelBody := by
  simpa using Owned.getOwner_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (SafeCounter.increment_model : Compiler.CompilationModel.FunctionSpec)) =
    SafeCounter.increment_modelBody := by
  simpa using SafeCounter.increment_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (SafeCounter.decrement_model : Compiler.CompilationModel.FunctionSpec)) =
    SafeCounter.decrement_modelBody := by
  simpa using SafeCounter.decrement_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (SafeCounter.getCount_model : Compiler.CompilationModel.FunctionSpec)) =
    SafeCounter.getCount_modelBody := by
  simpa using SafeCounter.getCount_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (OwnedCounter.increment_model : Compiler.CompilationModel.FunctionSpec)) =
    OwnedCounter.increment_modelBody := by
  simpa using OwnedCounter.increment_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (OwnedCounter.decrement_model : Compiler.CompilationModel.FunctionSpec)) =
    OwnedCounter.decrement_modelBody := by
  simpa using OwnedCounter.decrement_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (OwnedCounter.getCount_model : Compiler.CompilationModel.FunctionSpec)) =
    OwnedCounter.getCount_modelBody := by
  simpa using OwnedCounter.getCount_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (OwnedCounter.getOwner_model : Compiler.CompilationModel.FunctionSpec)) =
    OwnedCounter.getOwner_modelBody := by
  simpa using OwnedCounter.getOwner_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (OwnedCounter.transferOwnership_model : Compiler.CompilationModel.FunctionSpec)) =
    OwnedCounter.transferOwnership_modelBody := by
  simpa using OwnedCounter.transferOwnership_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Ledger.deposit_model : Compiler.CompilationModel.FunctionSpec)) =
    Ledger.deposit_modelBody := by
  simpa using Ledger.deposit_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Ledger.withdraw_model : Compiler.CompilationModel.FunctionSpec)) =
    Ledger.withdraw_modelBody := by
  simpa using Ledger.withdraw_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Ledger.transfer_model : Compiler.CompilationModel.FunctionSpec)) =
    Ledger.transfer_modelBody := by
  simpa using Ledger.transfer_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Ledger.getBalance_model : Compiler.CompilationModel.FunctionSpec)) =
    Ledger.getBalance_modelBody := by
  simpa using Ledger.getBalance_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (SimpleToken.mint_model : Compiler.CompilationModel.FunctionSpec)) =
    SimpleToken.mint_modelBody := by
  simpa using SimpleToken.mint_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (SimpleToken.transfer_model : Compiler.CompilationModel.FunctionSpec)) =
    SimpleToken.transfer_modelBody := by
  simpa using SimpleToken.transfer_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (SimpleToken.balanceOf_model : Compiler.CompilationModel.FunctionSpec)) =
    SimpleToken.balanceOf_modelBody := by
  simpa using SimpleToken.balanceOf_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (SimpleToken.totalSupply_model : Compiler.CompilationModel.FunctionSpec)) =
    SimpleToken.totalSupply_modelBody := by
  simpa using SimpleToken.totalSupply_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (SimpleToken.owner_model : Compiler.CompilationModel.FunctionSpec)) =
    SimpleToken.owner_modelBody := by
  simpa using SimpleToken.owner_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (ERC20.mint_model : Compiler.CompilationModel.FunctionSpec)) =
    ERC20.mint_modelBody := by
  simpa using ERC20.mint_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (ERC20.transfer_model : Compiler.CompilationModel.FunctionSpec)) =
    ERC20.transfer_modelBody := by
  simpa using ERC20.transfer_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (ERC20.approve_model : Compiler.CompilationModel.FunctionSpec)) =
    ERC20.approve_modelBody := by
  simpa using ERC20.approve_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (ERC20.transferFrom_model : Compiler.CompilationModel.FunctionSpec)) =
    ERC20.transferFrom_modelBody := by
  simpa using ERC20.transferFrom_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (ERC20.balanceOf_model : Compiler.CompilationModel.FunctionSpec)) =
    ERC20.balanceOf_modelBody := by
  simpa using ERC20.balanceOf_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (ERC20.allowanceOf_model : Compiler.CompilationModel.FunctionSpec)) =
    ERC20.allowanceOf_modelBody := by
  simpa using ERC20.allowanceOf_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (ERC20.totalSupply_model : Compiler.CompilationModel.FunctionSpec)) =
    ERC20.totalSupply_modelBody := by
  simpa using ERC20.totalSupply_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (ERC20.owner_model : Compiler.CompilationModel.FunctionSpec)) =
    ERC20.owner_modelBody := by
  simpa using ERC20.owner_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (ERC721.mint_model : Compiler.CompilationModel.FunctionSpec)) =
    ERC721.mint_modelBody := by
  simpa using ERC721.mint_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (ERC721.transferFrom_model : Compiler.CompilationModel.FunctionSpec)) =
    ERC721.transferFrom_modelBody := by
  simpa using ERC721.transferFrom_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (ERC721.ownerOf_model : Compiler.CompilationModel.FunctionSpec)) =
    ERC721.ownerOf_modelBody := by
  simpa using ERC721.ownerOf_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (ERC721.approve_model : Compiler.CompilationModel.FunctionSpec)) =
    ERC721.approve_modelBody := by
  simpa using ERC721.approve_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (ERC721.getApproved_model : Compiler.CompilationModel.FunctionSpec)) =
    ERC721.getApproved_modelBody := by
  simpa using ERC721.getApproved_semantic_preservation


end Verity.Examples.MacroContracts
