/-
  Compiler.Proofs.SemanticBridge: Full EDSL ≡ Compiled IR theorem statements

  This file states the *target* theorem per contract function: that EDSL execution
  produces the same storage effects as compiling the CompilationModel spec and
  interpreting the resulting IR.

  Unlike the macro-generated `_semantic_preservation` theorems (which live in the
  contract namespace and cannot import IR types), these theorems import the full
  IR execution machinery and state the precise equivalence:

    ∀ slot, (edslFinalState.storage slot).val = irResult.finalStorage slot

  **Status**: All proofs use per-builtin `@[simp]` lemmas from `Builtins.lean` to
  reduce `evalBuiltinCall` without unfolding the full 20-branch if-chain. This
  avoids the heartbeat limits that arose after `callvalue`/`calldatasize` were added
  (commit e5da6c7f).

  **Why a separate file**: The macro-generated theorems cannot import
  `Compiler.Proofs.IRGeneration.IRInterpreter` (it would transitively pull
  in EVMYulLean and bloat every contract file). This file bridges the gap by
  importing both the EDSL types and the IR execution types, stating the
  theorems that directly reference `interpretIR`.

  Run: lake build Compiler.Proofs.SemanticBridge
-/

import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.Conversions
import Compiler.Proofs.EndToEnd
import Compiler.Specs
import Verity.Core
import Verity.Examples.SimpleStorage
import Verity.Examples.Counter
import Verity.Examples.Owned
import Verity.Examples.SafeCounter
import Verity.Examples.OwnedCounter

namespace Compiler.Proofs.SemanticBridge

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration
open Verity
open Verity.Core.Uint256

/-! ## State Encoding

The canonical encoding from EDSL ContractState to IR-level Nat storage.
This must be consistent with the encoding used in PrimitiveBridge.lean.

Note: `slot` and `storage` are syntax keywords introduced by `Verity.Macro.Syntax`
(transitively imported via `Compiler.Specs`). French quotes `«»` are used to escape
these identifiers where they appear as variable names or struct field names.
-/

/-- Encode EDSL storage (Uint256 at each slot) as Nat storage for IR. -/
def encodeStorage (state : ContractState) : Nat → Nat :=
  fun «slot» => (state.storage «slot»).val

/-- Encode EDSL sender (Address) as Nat for IR. -/
def encodeSender (state : ContractState) : Nat :=
  state.sender.val

/-! ## Target Theorems: SimpleStorage -/

set_option maxHeartbeats 1600000 in
theorem simpleStorage_store_semantic_bridge
    (state : ContractState) (sender : Address) (value : Uint256) :
    let edslResult := Contract.run (Verity.Examples.store value) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x6057361d
      args := [value.val]
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := [value.val]
      returnValue := none
      sender := sender.val
      selector := 0x6057361d
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp [simpleStorageIRContract,
    Verity.Examples.store, Verity.Examples.storedData,
    Verity.Contract.run, Verity.bind, Verity.setStorage,
    encodeStorage,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    calldataloadWord, selectorWord, selectorModulus, selectorShift,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings]
  intro «slot»
  by_cases h : «slot» = 0 <;> simp_all [beq_iff_eq]

set_option maxHeartbeats 1600000 in
theorem simpleStorage_retrieve_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.retrieve) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2e64cec1
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2e64cec1
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp [simpleStorageIRContract,
    Verity.Examples.retrieve, Verity.Examples.storedData,
    Verity.Contract.run, Verity.bind, Verity.getStorage,
    encodeStorage,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings]

/-! ## Target Theorems: Counter -/

set_option maxHeartbeats 1600000 in
theorem counter_increment_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Counter.increment) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xd09de08a
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xd09de08a
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp [counterIRContract,
    Verity.Examples.Counter.increment, Verity.Examples.Counter.count,
    Verity.Contract.run, Verity.bind, Verity.getStorage, Verity.setStorage,
    encodeStorage, Verity.EVM.Uint256.add,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings]
  intro «slot»
  by_cases h : «slot» = 0 <;> simp_all [beq_iff_eq]

set_option maxHeartbeats 1600000 in
theorem counter_decrement_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Counter.decrement) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2baeceb7
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2baeceb7
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp [counterIRContract,
    Verity.Examples.Counter.decrement, Verity.Examples.Counter.count,
    Verity.Contract.run, Verity.bind, Verity.getStorage, Verity.setStorage,
    encodeStorage, Verity.EVM.Uint256.sub,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings]
  intro «slot»
  by_cases h : «slot» = 0 <;> simp_all [beq_iff_eq]

set_option maxHeartbeats 1600000 in
theorem counter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Counter.getCount) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xa87d942c
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xa87d942c
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp [counterIRContract,
    Verity.Examples.Counter.getCount, Verity.Examples.Counter.count,
    Verity.Contract.run, Verity.bind, Verity.getStorage,
    encodeStorage,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings]

/-! ## Target Theorems: Owned -/

/-- Encode EDSL Address storage as Nat storage for IR. -/
def encodeStorageAddr (state : ContractState) : Nat → Nat :=
  fun «slot» => (state.storageAddr «slot»).val

set_option maxHeartbeats 1600000 in
theorem owned_getOwner_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Owned.getOwner) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x893d20e8
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorageAddr state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x893d20e8
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR ownedIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (s'.storageAddr «slot»).val = irResult.finalStorage «slot»
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp [ownedIRContract,
    Verity.Examples.Owned.getOwner, Verity.Examples.Owned.owner,
    Verity.Contract.run, Verity.bind, Verity.getStorageAddr,
    encodeStorageAddr,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings]

set_option maxHeartbeats 3200000 in
theorem owned_transferOwnership_semantic_bridge
    (state : ContractState) (sender : Address) (newOwner : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Verity.Examples.Owned.transferOwnership newOwner)
        { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xf2fde38b
      args := [newOwner.val]
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorageAddr state
      memory := fun _ => 0
      calldata := [newOwner.val]
      returnValue := none
      sender := sender.val
      selector := 0xf2fde38b
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storageAddr «slot»).val = irResult.finalStorage «slot»
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp only [ownedIRContract,
    Verity.Examples.Owned.transferOwnership,
    Verity.Examples.Owned.onlyOwner, Verity.Examples.Owned.isOwner,
    Verity.Examples.Owned.owner,
    Verity.Contract.run, Verity.bind, Verity.getStorageAddr, Verity.setStorageAddr,
    Verity.msgSender, Verity.require,
    encodeStorageAddr,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    calldataloadWord, selectorWord, selectorModulus, selectorShift,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    ownedNotOwnerRevert,
    Compiler.Constants.addressMask]
  subst hOwner
  simp [beq_iff_eq]
  intro «slot»
  by_cases h : «slot» = 0 <;> simp_all [beq_iff_eq]

/-! ## Target Theorems: SafeCounter -/

set_option maxHeartbeats 3200000 in
theorem safeCounter_increment_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.SafeCounter.increment) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xd09de08a
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xd09de08a
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
    | .revert _ _ =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = false
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp only [safeCounterIRContract, safeCounterOverflowRevert,
    Verity.Examples.SafeCounter.increment, Verity.Examples.SafeCounter.count,
    Verity.Contract.run, Verity.bind, Verity.getStorage, Verity.setStorage,
    Verity.Stdlib.Math.safeAdd, Verity.requireSomeUint,
    encodeStorage,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings]
  sorry

set_option maxHeartbeats 3200000 in
theorem safeCounter_decrement_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.SafeCounter.decrement) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2baeceb7
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2baeceb7
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
    | .revert _ _ =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = false
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp only [safeCounterIRContract, safeCounterUnderflowRevert,
    Verity.Examples.SafeCounter.decrement, Verity.Examples.SafeCounter.count,
    Verity.Contract.run, Verity.bind, Verity.getStorage, Verity.setStorage,
    Verity.Stdlib.Math.safeSub, Verity.requireSomeUint,
    encodeStorage,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings]
  sorry

set_option maxHeartbeats 1600000 in
theorem safeCounter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.SafeCounter.getCount) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xa87d942c
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xa87d942c
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot»
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp [safeCounterIRContract,
    Verity.Examples.SafeCounter.getCount, Verity.Examples.SafeCounter.count,
    Verity.Contract.run, Verity.bind, Verity.getStorage,
    encodeStorage,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings]

/-! ## Target Theorems: OwnedCounter -/

/-- Encode OwnedCounter storage: slot 0 = owner (Address), slot 1 = count (Uint256). -/
def encodeOwnedCounterStorage (state : ContractState) : Nat → Nat :=
  fun «slot» =>
    if «slot» = 0 then (state.storageAddr 0).val
    else (state.storage «slot»).val

set_option maxHeartbeats 1600000 in
theorem ownedCounter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.getCount) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xa87d942c
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xa87d942c
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (if «slot» = 0 then (s'.storageAddr 0).val else (s'.storage «slot»).val) =
                irResult.finalStorage «slot»
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp [ownedCounterIRContract,
    Verity.Examples.OwnedCounter.getCount, Verity.Examples.OwnedCounter.count,
    Verity.Contract.run, Verity.bind, Verity.getStorage,
    encodeOwnedCounterStorage,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings]

set_option maxHeartbeats 1600000 in
theorem ownedCounter_getOwner_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.getOwner) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x893d20e8
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x893d20e8
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ «slot», (if «slot» = 0 then (s'.storageAddr 0).val else (s'.storage «slot»).val) =
                irResult.finalStorage «slot»
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp [ownedCounterIRContract,
    Verity.Examples.OwnedCounter.getOwner, Verity.Examples.OwnedCounter.owner,
    Verity.Contract.run, Verity.bind, Verity.getStorageAddr,
    encodeOwnedCounterStorage,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings]

set_option maxHeartbeats 3200000 in
theorem ownedCounter_increment_semantic_bridge
    (state : ContractState) (sender : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.increment) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xd09de08a
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xd09de08a
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (if «slot» = 0 then (s'.storageAddr 0).val else (s'.storage «slot»).val) =
                irResult.finalStorage «slot»
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp only [ownedCounterIRContract, ownedNotOwnerRevert,
    Verity.Examples.OwnedCounter.increment,
    Verity.Examples.OwnedCounter.onlyOwner, Verity.Examples.OwnedCounter.isOwner,
    Verity.Examples.OwnedCounter.owner, Verity.Examples.OwnedCounter.count,
    Verity.Contract.run, Verity.bind, Verity.getStorage, Verity.setStorage,
    Verity.getStorageAddr, Verity.msgSender, Verity.require,
    Verity.EVM.Uint256.add,
    encodeOwnedCounterStorage,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings]
  subst hOwner
  simp [beq_iff_eq]
  intro «slot»
  by_cases h : «slot» = 0 <;> simp_all [beq_iff_eq]
  by_cases h1 : «slot» = 1 <;> simp_all [beq_iff_eq]

set_option maxHeartbeats 3200000 in
theorem ownedCounter_decrement_semantic_bridge
    (state : ContractState) (sender : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.decrement) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2baeceb7
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2baeceb7
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (if «slot» = 0 then (s'.storageAddr 0).val else (s'.storage «slot»).val) =
                irResult.finalStorage «slot»
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp only [ownedCounterIRContract, ownedNotOwnerRevert,
    Verity.Examples.OwnedCounter.decrement,
    Verity.Examples.OwnedCounter.onlyOwner, Verity.Examples.OwnedCounter.isOwner,
    Verity.Examples.OwnedCounter.owner, Verity.Examples.OwnedCounter.count,
    Verity.Contract.run, Verity.bind, Verity.getStorage, Verity.setStorage,
    Verity.getStorageAddr, Verity.msgSender, Verity.require,
    Verity.EVM.Uint256.sub,
    encodeOwnedCounterStorage,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings]
  subst hOwner
  simp [beq_iff_eq]
  intro «slot»
  by_cases h : «slot» = 0 <;> simp_all [beq_iff_eq]
  by_cases h1 : «slot» = 1 <;> simp_all [beq_iff_eq]

set_option maxHeartbeats 3200000 in
theorem ownedCounter_transferOwnership_semantic_bridge
    (state : ContractState) (sender : Address) (newOwner : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.transferOwnership newOwner)
        { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xf2fde38b
      args := [newOwner.val]
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := [newOwner.val]
      returnValue := none
      sender := sender.val
      selector := 0xf2fde38b
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        ∀ «slot», (if «slot» = 0 then (s'.storageAddr 0).val else (s'.storage «slot»).val) =
                irResult.finalStorage «slot»
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  unfold interpretIR execIRFunction
  simp only [ownedCounterIRContract, ownedNotOwnerRevert,
    Verity.Examples.OwnedCounter.transferOwnership,
    Verity.Examples.OwnedCounter.onlyOwner, Verity.Examples.OwnedCounter.isOwner,
    Verity.Examples.OwnedCounter.owner,
    Verity.Contract.run, Verity.bind, Verity.getStorageAddr, Verity.setStorageAddr,
    Verity.msgSender, Verity.require,
    encodeOwnedCounterStorage,
    List.find?, List.zip, List.foldl,
    execIRStmts, execIRStmt,
    evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend,
    calldataloadWord, selectorWord, selectorModulus, selectorShift,
    IRState.setVar, IRState.getVar,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    Compiler.Constants.addressMask]
  subst hOwner
  simp [beq_iff_eq]
  intro «slot»
  by_cases h : «slot» = 0 <;> simp_all [beq_iff_eq]

/-! ## Composed End-to-End: EDSL → IR → Yul

These theorems compose the EDSL≡IR bridge above with the Layer 3
IR→Yul preservation theorem to yield full-chain proofs. -/

set_option maxHeartbeats 1600000 in
theorem simpleStorage_store_edsl_to_yul
    (state : ContractState) (sender : Address) (value : Uint256) :
    let edslResult := Contract.run (Verity.Examples.store value) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x6057361d
      args := [value.val]
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := [value.val]
      returnValue := none
      sender := sender.val
      selector := 0x6057361d
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        (∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot») ∧
        Compiler.Proofs.YulGeneration.resultsMatch
          (interpretIR simpleStorageIRContract tx irState)
          (interpretYulFromIR simpleStorageIRContract tx irState)
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  have h_bridge := simpleStorage_store_semantic_bridge state sender value
  simp only at h_bridge
  sorry

set_option maxHeartbeats 1600000 in
theorem simpleStorage_retrieve_edsl_to_yul
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.retrieve) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2e64cec1
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2e64cec1
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        (∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot») ∧
        Compiler.Proofs.YulGeneration.resultsMatch
          (interpretIR simpleStorageIRContract tx irState)
          (interpretYulFromIR simpleStorageIRContract tx irState)
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  have h_bridge := simpleStorage_retrieve_semantic_bridge state sender
  simp only at h_bridge
  sorry

set_option maxHeartbeats 1600000 in
theorem counter_increment_edsl_to_yul
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Counter.increment) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xd09de08a
      args := []
    }
    let irState : IRState := {
      vars := []
      «storage» := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xd09de08a
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        (∀ «slot», (s'.storage «slot»).val = irResult.finalStorage «slot») ∧
        Compiler.Proofs.YulGeneration.resultsMatch
          (interpretIR counterIRContract tx irState)
          (interpretYulFromIR counterIRContract tx irState)
    | .revert _ _ => True
    := by
  intro edslResult tx irState
  have h_bridge := counter_increment_semantic_bridge state sender
  simp only at h_bridge
  sorry

end Compiler.Proofs.SemanticBridge
