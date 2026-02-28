import Compiler.Lowering.FromEDSL
import Compiler.Proofs.SpecCorrectness.Counter
import Compiler.Proofs.SpecCorrectness.Ledger
import Compiler.Proofs.SpecCorrectness.Owned
import Compiler.Proofs.SpecCorrectness.OwnedCounter
import Compiler.Proofs.SpecCorrectness.SafeCounter
import Compiler.Proofs.SpecCorrectness.SimpleStorage
import Compiler.Proofs.SpecCorrectness.SimpleToken
import Verity.Proofs.Stdlib.SpecInterpreter

namespace Compiler.Proofs.Lowering

open Compiler.Lowering
open Compiler.Proofs.SpecCorrectness
open Verity.Proofs.Stdlib.SpecInterpreter

/-- Current transition theorem: lowering the wrapped `ContractCore`
is definitionally equal to the underlying `CompilationModel`. -/
@[simp] theorem lowerContractCore_eq_model (core : ContractCore) :
    lowerContractCore core = core.model := rfl

/-- Semantic preservation for the current transition lowering boundary. -/
@[simp] theorem lowerContractCore_preserves_interpretSpec
    (core : ContractCore)
    (initialStorage : SpecStorage)
    (tx : Compiler.DiffTestTypes.Transaction) :
    interpretSpec (lowerContractCore core) initialStorage tx =
      interpretSpec core.model initialStorage tx := by
  rfl

/-- Manual `CompilationModel` input is already inside the lowering boundary. -/
@[simp] theorem lowerLiftModel_eq (model : Compiler.CompilationModel.CompilationModel) :
    lowerContractCore (liftModel model) = model := rfl

/-- Semantic preservation specialized to the current manual-model path. -/
@[simp] theorem lowerLiftModel_preserves_interpretSpec
    (model : Compiler.CompilationModel.CompilationModel)
    (initialStorage : SpecStorage)
    (tx : Compiler.DiffTestTypes.Transaction) :
    interpretSpec (lowerContractCore (liftModel model)) initialStorage tx =
      interpretSpec model initialStorage tx := by
  rfl

/-- Manual bridge inputs lower to their wrapped `CompilationModel`. -/
@[simp] theorem lowerFromEDSLSubset_manualBridge_eq
    (core : ContractCore) :
    lowerFromEDSLSubset (.manualBridge core) = .ok (lowerContractCore core) := by
  rfl

/-- Supported EDSL subset constructors lower to their pinned targets. -/
@[simp] theorem lowerFromEDSLSubset_supported_eq
    (contract : SupportedEDSLContract) :
    lowerFromEDSLSubset (.supported contract) = .ok (lowerSupportedEDSLContract contract) := by
  rfl

/-- The supported-subset entrypoint preserves `interpretSpec` semantics
exactly at the lowering API boundary. -/
@[simp] theorem lowerFromEDSLSubset_supported_preserves_interpretSpec
    (contract : SupportedEDSLContract)
    (initialStorage : SpecStorage)
    (tx : Compiler.DiffTestTypes.Transaction) :
    interpretSpec
      (match lowerFromEDSLSubset (.supported contract) with
      | .ok lowered => lowered
      | .error _ => lowerSupportedEDSLContract contract)
      initialStorage tx =
    interpretSpec (lowerSupportedEDSLContract contract) initialStorage tx := by
  rfl

/-- The manual-bridge entrypoint preserves `interpretSpec` semantics
exactly at the lowering API boundary. -/
@[simp] theorem lowerFromEDSLSubset_manualBridge_preserves_interpretSpec
    (core : ContractCore)
    (initialStorage : SpecStorage)
    (tx : Compiler.DiffTestTypes.Transaction) :
    interpretSpec
      (match lowerFromEDSLSubset (.manualBridge core) with
      | .ok lowered => lowered
      | .error _ => lowerContractCore core)
      initialStorage tx =
    interpretSpec (lowerContractCore core) initialStorage tx := by
  rfl

@[simp] theorem lowerSupportedEDSLContract_simpleStorage_eq :
    lowerSupportedEDSLContract .simpleStorage = Compiler.Specs.simpleStorageSpec := rfl

@[simp] theorem lowerSupportedEDSLContract_counter_eq :
    lowerSupportedEDSLContract .counter = Compiler.Specs.counterSpec := rfl

@[simp] theorem lowerSupportedEDSLContract_owned_eq :
    lowerSupportedEDSLContract .owned = Compiler.Specs.ownedSpec := rfl

@[simp] theorem lowerSupportedEDSLContract_ledger_eq :
    lowerSupportedEDSLContract .ledger = Compiler.Specs.ledgerSpec := rfl

@[simp] theorem lowerSupportedEDSLContract_ownedCounter_eq :
    lowerSupportedEDSLContract .ownedCounter = Compiler.Specs.ownedCounterSpec := rfl

@[simp] theorem lowerSupportedEDSLContract_simpleToken_eq :
    lowerSupportedEDSLContract .simpleToken = Compiler.Specs.simpleTokenSpec := rfl

@[simp] theorem lowerSupportedEDSLContract_safeCounter_eq :
    lowerSupportedEDSLContract .safeCounter = Compiler.Specs.safeCounterSpec := rfl

/-- Transition bridge: lowering `.simpleStorage` preserves the existing
EDSL-vs-CompilationModel correctness theorem for `store`. -/
theorem lower_simpleStorage_store_correct
    (state : Verity.ContractState)
    (value : Nat)
    (sender : Verity.Address) :
    let edslFinal := (Verity.Examples.store (Verity.Core.Uint256.ofNat value)).runState { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "store"
      args := [value]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .simpleStorage)
      (simpleStorageEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = (edslFinal.storage 0).val := by
  simpa [lowerSupportedEDSLContract] using simpleStorage_store_correct state value sender

/-- Transition bridge: lowering `.simpleStorage` preserves the existing
EDSL-vs-CompilationModel correctness theorem for `retrieve`. -/
theorem lower_simpleStorage_retrieve_correct
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let edslValue := (Verity.Examples.retrieve.runValue { state with sender := sender }).val
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "retrieve"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .simpleStorage)
      (simpleStorageEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslValue := by
  simpa [lowerSupportedEDSLContract] using simpleStorage_retrieve_correct state sender

/-- Transition bridge: lowering `.simpleStorage` preserves retrieve read-only state behavior. -/
theorem lower_simpleStorage_retrieve_preserves_state
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let finalState := Verity.Examples.retrieve.runState { state with sender := sender }
    finalState.storage = state.storage := by
  simpa using simpleStorage_retrieve_preserves_state state sender

/-- Transition bridge: lowering `.counter` preserves the existing
EDSL-vs-CompilationModel correctness theorem for `increment`. -/
theorem lower_counter_increment_correct
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let edslFinal := (Verity.Examples.Counter.increment.runState { state with sender := sender })
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "increment"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .counter)
      (counterEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = (edslFinal.storage 0).val := by
  simpa [lowerSupportedEDSLContract] using counter_increment_correct state sender

/-- Transition bridge: lowering `.counter` preserves the existing
EDSL-vs-CompilationModel correctness theorem for `getCount`. -/
theorem lower_counter_getCount_correct
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let edslValue := (Verity.Examples.Counter.getCount.runValue { state with sender := sender }).val
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "getCount"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .counter)
      (counterEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslValue := by
  simpa [lowerSupportedEDSLContract] using counter_getCount_correct state sender

/-- Transition bridge: lowering `.counter` preserves getter read-only state behavior. -/
theorem lower_counter_getCount_preserves_state
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let finalState := Verity.Examples.Counter.getCount.runState { state with sender := sender }
    finalState.storage 0 = state.storage 0 := by
  simpa using counter_getCount_preserves_state state sender

/-- Transition bridge: lowering `.counter` preserves the existing
EDSL-vs-CompilationModel correctness theorem for `decrement`. -/
theorem lower_counter_decrement_correct
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let edslFinal := (Verity.Examples.Counter.decrement.runState { state with sender := sender })
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "decrement"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .counter)
      (counterEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = (edslFinal.storage 0).val := by
  simpa [lowerSupportedEDSLContract] using counter_decrement_correct state sender

/-- Transition bridge: lowering `.owned` preserves Layer-1 getter correctness. -/
theorem lower_owned_getOwner_correct
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let edslAddr := Verity.Examples.Owned.getOwner.runValue { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "getOwner"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .owned)
      (ownedEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.returnValue = some (Verity.Core.Address.val edslAddr) := by
  simpa [lowerSupportedEDSLContract] using owned_getOwner_correct state sender

/-- Transition bridge: lowering `.owned` preserves getter read-only state behavior. -/
theorem lower_owned_getOwner_preserves_state
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let finalState := Verity.Examples.Owned.getOwner.runState { state with sender := sender }
    finalState.storageAddr 0 = state.storageAddr 0 := by
  simpa using owned_getOwner_preserves_state state sender

/-- Transition bridge: lowering `.owned` preserves owner-only transfer semantics. -/
theorem lower_owned_transferOwnership_correct_as_owner
    (state : Verity.ContractState)
    (newOwner : Verity.Address)
    (sender : Verity.Address)
    (h : state.storageAddr 0 = sender) :
    let edslResult := (Verity.Examples.Owned.transferOwnership newOwner).run { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transferOwnership"
      args := [Verity.Core.Address.val newOwner]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .owned)
      (ownedEdslToSpecStorage state) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = Verity.Core.Address.val newOwner := by
  simpa [lowerSupportedEDSLContract] using
    owned_transferOwnership_correct_as_owner state newOwner sender h

/-- Transition bridge: lowering `.owned` preserves non-owner revert semantics. -/
theorem lower_owned_transferOwnership_reverts_as_nonowner
    (state : Verity.ContractState)
    (newOwner : Verity.Address)
    (sender : Verity.Address)
    (h : state.storageAddr 0 ≠ sender) :
    let edslResult := (Verity.Examples.Owned.transferOwnership newOwner).run { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transferOwnership"
      args := [Verity.Core.Address.val newOwner]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .owned)
      (ownedEdslToSpecStorage state) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  simpa [lowerSupportedEDSLContract] using
    owned_transferOwnership_reverts_as_nonowner state newOwner sender h

/-- Transition bridge: lowering `.ledger` preserves Layer-1 deposit correctness. -/
theorem lower_ledger_deposit_correct
    (state : Verity.ContractState)
    (amount : Nat)
    (sender : Verity.Address) :
    let edslResult := (Verity.Examples.Ledger.deposit (Verity.Core.Uint256.ofNat amount)).run { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "deposit"
      args := [amount]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ledger)
      (ledgerEdslToSpecStorageWithAddrs state [sender]) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getMapping 0 (sender.val) =
      (edslResult.getState.storageMap 0 sender).val := by
  simpa [lowerSupportedEDSLContract] using ledger_deposit_correct state amount sender

/-- Transition bridge: lowering `.ledger` preserves sufficient-balance withdraw semantics. -/
theorem lower_ledger_withdraw_correct_sufficient
    (state : Verity.ContractState)
    (amount : Nat)
    (sender : Verity.Address)
    (h : (state.storageMap 0 sender).val ≥ amount) :
    let edslResult := (Verity.Examples.Ledger.withdraw (Verity.Core.Uint256.ofNat amount)).run
      { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "withdraw"
      args := [amount]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ledger)
      (ledgerEdslToSpecStorageWithAddrs state [sender]) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getMapping 0 (sender.val) =
      (edslResult.getState.storageMap 0 sender).val := by
  simpa [lowerSupportedEDSLContract] using
    ledger_withdraw_correct_sufficient state amount sender h

/-- Transition bridge: lowering `.ledger` preserves insufficient-balance withdraw reverts. -/
theorem lower_ledger_withdraw_reverts_insufficient
    (state : Verity.ContractState)
    (amount : Nat)
    (sender : Verity.Address)
    (h_amount : amount < Verity.Core.Uint256.modulus)
    (h : (state.storageMap 0 sender).val < amount) :
    let edslResult := (Verity.Examples.Ledger.withdraw (Verity.Core.Uint256.ofNat amount)).run
      { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "withdraw"
      args := [amount]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ledger)
      (ledgerEdslToSpecStorageWithAddrs state [sender]) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  simpa [lowerSupportedEDSLContract] using
    ledger_withdraw_reverts_insufficient state amount sender h_amount h

/-- Transition bridge: lowering `.ledger` preserves getter correctness. -/
theorem lower_ledger_getBalance_correct
    (state : Verity.ContractState)
    (addr : Verity.Address)
    (sender : Verity.Address) :
    let edslValue := (Verity.Examples.Ledger.getBalance addr).runValue { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "getBalance"
      args := [addr.val]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ledger)
      (ledgerEdslToSpecStorageWithAddrs state [addr]) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslValue.val := by
  simpa [lowerSupportedEDSLContract] using ledger_getBalance_correct state addr sender

/-- Transition bridge: lowering `.ledger` preserves getter read-only state behavior. -/
theorem lower_ledger_getBalance_preserves_state
    (state : Verity.ContractState)
    (addr : Verity.Address)
    (sender : Verity.Address) :
    let finalState := (Verity.Examples.Ledger.getBalance addr).runState { state with sender := sender }
    ∀ a, finalState.storageMap 0 a = state.storageMap 0 a := by
  simpa using ledger_getBalance_preserves_state state addr sender

/-- Transition bridge: lowering `.ledger` preserves transfer semantics when balances permit. -/
theorem lower_ledger_transfer_correct_sufficient
    (state : Verity.ContractState)
    (to : Verity.Address)
    (amount : Nat)
    (sender : Verity.Address)
    (h : (state.storageMap 0 sender).val ≥ amount)
    (h_no_overflow : (state.storageMap 0 to).val + amount ≤ Verity.Stdlib.Math.MAX_UINT256) :
    let edslResult := (Verity.Examples.Ledger.transfer to (Verity.Core.Uint256.ofNat amount)).run
      { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transfer"
      args := [to.val, amount]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ledger)
      (ledgerEdslToSpecStorageWithAddrs state [sender, to]) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getMapping 0 (sender.val) =
      (edslResult.getState.storageMap 0 sender).val ∧
    specResult.finalStorage.getMapping 0 (to.val) =
      (edslResult.getState.storageMap 0 to).val := by
  simpa [lowerSupportedEDSLContract] using
    ledger_transfer_correct_sufficient state to amount sender h h_no_overflow

/-- Transition bridge: lowering `.ledger` preserves insufficient-balance transfer reverts. -/
theorem lower_ledger_transfer_reverts_insufficient
    (state : Verity.ContractState)
    (to : Verity.Address)
    (amount : Nat)
    (sender : Verity.Address)
    (h_amount : amount < Verity.Core.Uint256.modulus)
    (h : (state.storageMap 0 sender).val < amount) :
    let edslResult := (Verity.Examples.Ledger.transfer to (Verity.Core.Uint256.ofNat amount)).run
      { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transfer"
      args := [to.val, amount]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ledger)
      (ledgerEdslToSpecStorageWithAddrs state [sender, to]) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  simpa [lowerSupportedEDSLContract] using
    ledger_transfer_reverts_insufficient state to amount sender h_amount h

/-- Transition bridge: lowering `.ownedCounter` preserves Layer-1 getter correctness. -/
theorem lower_ownedCounter_getCount_correct
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let edslValue := (Verity.Examples.OwnedCounter.getCount.runValue { state with sender := sender }).val
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "getCount"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ownedCounter)
      (ownedCounterEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslValue := by
  simpa [lowerSupportedEDSLContract] using ownedCounter_getCount_correct state sender

/-- Transition bridge: lowering `.ownedCounter` preserves owner-only increment semantics. -/
theorem lower_ownedCounter_increment_correct_as_owner
    (state : Verity.ContractState)
    (sender : Verity.Address)
    (h : state.storageAddr 0 = sender) :
    let edslResult := Verity.Examples.OwnedCounter.increment.run { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "increment"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ownedCounter)
      (ownedCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getSlot 1 = (edslResult.getState.storage 1).val := by
  simpa [lowerSupportedEDSLContract] using
    ownedCounter_increment_correct_as_owner state sender h

/-- Transition bridge: lowering `.ownedCounter` preserves non-owner increment reverts. -/
theorem lower_ownedCounter_increment_reverts_as_nonowner
    (state : Verity.ContractState)
    (sender : Verity.Address)
    (h : state.storageAddr 0 ≠ sender) :
    let edslResult := Verity.Examples.OwnedCounter.increment.run { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "increment"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ownedCounter)
      (ownedCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  simpa [lowerSupportedEDSLContract] using
    ownedCounter_increment_reverts_as_nonowner state sender h

/-- Transition bridge: lowering `.ownedCounter` preserves owner-only decrement semantics. -/
theorem lower_ownedCounter_decrement_correct_as_owner
    (state : Verity.ContractState)
    (sender : Verity.Address)
    (h : state.storageAddr 0 = sender) :
    let edslResult := Verity.Examples.OwnedCounter.decrement.run { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "decrement"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ownedCounter)
      (ownedCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getSlot 1 = (edslResult.getState.storage 1).val := by
  simpa [lowerSupportedEDSLContract] using
    ownedCounter_decrement_correct_as_owner state sender h

/-- Transition bridge: lowering `.ownedCounter` preserves non-owner decrement reverts. -/
theorem lower_ownedCounter_decrement_reverts_as_nonowner
    (state : Verity.ContractState)
    (sender : Verity.Address)
    (h : state.storageAddr 0 ≠ sender) :
    let edslResult := Verity.Examples.OwnedCounter.decrement.run { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "decrement"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ownedCounter)
      (ownedCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  simpa [lowerSupportedEDSLContract] using
    ownedCounter_decrement_reverts_as_nonowner state sender h

/-- Transition bridge: lowering `.ownedCounter` preserves owner getter correctness. -/
theorem lower_ownedCounter_getOwner_correct
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let edslAddr := Verity.Examples.OwnedCounter.getOwner.runValue { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "getOwner"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ownedCounter)
      (ownedCounterEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslAddr.val := by
  simpa [lowerSupportedEDSLContract] using ownedCounter_getOwner_correct state sender

/-- Transition bridge: lowering `.ownedCounter` preserves getter read-only state behavior. -/
theorem lower_ownedCounter_getters_preserve_state
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let countState := Verity.Examples.OwnedCounter.getCount.runState { state with sender := sender }
    let ownerState := Verity.Examples.OwnedCounter.getOwner.runState { state with sender := sender }
    countState.storage 1 = state.storage 1 ∧
    ownerState.storageAddr 0 = state.storageAddr 0 := by
  simpa using ownedCounter_getters_preserve_state state sender

/-- Transition bridge: lowering `.ownedCounter` preserves owner-only transfer semantics. -/
theorem lower_ownedCounter_transferOwnership_correct_as_owner
    (state : Verity.ContractState)
    (newOwner : Verity.Address)
    (sender : Verity.Address)
    (h : state.storageAddr 0 = sender) :
    let edslResult := (Verity.Examples.OwnedCounter.transferOwnership newOwner).run
      { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transferOwnership"
      args := [newOwner.val]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ownedCounter)
      (ownedCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = newOwner.val := by
  simpa [lowerSupportedEDSLContract] using
    ownedCounter_transferOwnership_correct_as_owner state newOwner sender h

/-- Transition bridge: lowering `.ownedCounter` preserves non-owner transfer reverts. -/
theorem lower_ownedCounter_transferOwnership_reverts_as_nonowner
    (state : Verity.ContractState)
    (newOwner : Verity.Address)
    (sender : Verity.Address)
    (h : state.storageAddr 0 ≠ sender) :
    let edslResult := (Verity.Examples.OwnedCounter.transferOwnership newOwner).run
      { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transferOwnership"
      args := [newOwner.val]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .ownedCounter)
      (ownedCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  simpa [lowerSupportedEDSLContract] using
    ownedCounter_transferOwnership_reverts_as_nonowner state newOwner sender h

/-- Transition bridge: lowering `.simpleToken` preserves Layer-1 getter correctness. -/
theorem lower_simpleToken_getTotalSupply_correct
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let edslValue := (Verity.Examples.SimpleToken.getTotalSupply.runValue { state with sender := sender }).val
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "totalSupply"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .simpleToken)
      (tokenEdslToSpecStorageWithAddrs state []) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslValue := by
  simpa [lowerSupportedEDSLContract] using token_getTotalSupply_correct state sender

/-- Transition bridge: lowering `.simpleToken` preserves balance getter correctness. -/
theorem lower_simpleToken_balanceOf_correct
    (state : Verity.ContractState)
    (addr : Verity.Address)
    (sender : Verity.Address) :
    let edslValue := (Verity.Examples.SimpleToken.balanceOf addr).runValue { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "balanceOf"
      args := [addr.val]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .simpleToken)
      (tokenEdslToSpecStorageWithAddrs state [addr]) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslValue.val := by
  simpa [lowerSupportedEDSLContract] using token_balanceOf_correct state addr sender

/-- Transition bridge: lowering `.simpleToken` preserves owner getter correctness. -/
theorem lower_simpleToken_getOwner_correct
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let edslAddr := Verity.Examples.SimpleToken.getOwner.runValue { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "owner"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .simpleToken)
      (tokenEdslToSpecStorageWithAddrs state []) specTx
    specResult.success = true ∧
    specResult.returnValue = some (edslAddr.val) := by
  simpa [lowerSupportedEDSLContract] using token_getOwner_correct state sender

/-- Transition bridge: lowering `.simpleToken` preserves getter read-only state behavior. -/
theorem lower_simpleToken_getters_preserve_state
    (state : Verity.ContractState)
    (addr : Verity.Address)
    (sender : Verity.Address) :
    let balState := (Verity.Examples.SimpleToken.balanceOf addr).runState { state with sender := sender }
    let supplyState := Verity.Examples.SimpleToken.getTotalSupply.runState { state with sender := sender }
    let ownerState := Verity.Examples.SimpleToken.getOwner.runState { state with sender := sender }
    balState.storageMap 1 addr = state.storageMap 1 addr ∧
    supplyState.storage 2 = state.storage 2 ∧
    ownerState.storageAddr 0 = state.storageAddr 0 := by
  simpa using token_getters_preserve_state state addr sender

/-- Transition bridge: lowering `.simpleToken` preserves owner-only mint semantics. -/
theorem lower_simpleToken_mint_correct_as_owner
    (state : Verity.ContractState)
    (to : Verity.Address)
    (amount : Nat)
    (sender : Verity.Address)
    (h : state.storageAddr 0 = sender)
    (h_no_bal_overflow : (state.storageMap 1 to : Nat) + amount ≤ Verity.Stdlib.Math.MAX_UINT256)
    (h_no_sup_overflow : (state.storage 2 : Nat) + amount ≤ Verity.Stdlib.Math.MAX_UINT256) :
    let edslResult := (Verity.Examples.SimpleToken.mint to (Verity.Core.Uint256.ofNat amount)).run
      { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "mint"
      args := [to.val, amount]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .simpleToken)
      (tokenEdslToSpecStorageWithAddrs state [to]) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getMapping 1 (to.val) = (edslResult.getState.storageMap 1 to).val ∧
    specResult.finalStorage.getSlot 2 = (edslResult.getState.storage 2).val := by
  simpa [lowerSupportedEDSLContract] using
    token_mint_correct_as_owner state to amount sender h h_no_bal_overflow h_no_sup_overflow

/-- Transition bridge: lowering `.simpleToken` preserves non-owner mint reverts. -/
theorem lower_simpleToken_mint_reverts_as_nonowner
    (state : Verity.ContractState)
    (to : Verity.Address)
    (amount : Nat)
    (sender : Verity.Address)
    (h : state.storageAddr 0 ≠ sender) :
    let edslResult := (Verity.Examples.SimpleToken.mint to (Verity.Core.Uint256.ofNat amount)).run
      { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "mint"
      args := [to.val, amount]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .simpleToken)
      (tokenEdslToSpecStorageWithAddrs state [to]) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  simpa [lowerSupportedEDSLContract] using
    token_mint_reverts_as_nonowner state to amount sender h

/-- Transition bridge: lowering `.simpleToken` preserves transfer semantics when balance is sufficient. -/
theorem lower_simpleToken_transfer_correct_sufficient
    (state : Verity.ContractState)
    (to : Verity.Address)
    (amount : Nat)
    (sender : Verity.Address)
    (h : (state.storageMap 1 sender).val ≥ amount)
    (h_no_overflow : sender ≠ to →
      (state.storageMap 1 to).val + amount ≤ Verity.Stdlib.Math.MAX_UINT256) :
    let edslResult := (Verity.Examples.SimpleToken.transfer to (Verity.Core.Uint256.ofNat amount)).run
      { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transfer"
      args := [to.val, amount]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .simpleToken)
      (tokenEdslToSpecStorageWithAddrs state [sender, to]) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getMapping 1 (sender.val) =
      (edslResult.getState.storageMap 1 sender).val ∧
    specResult.finalStorage.getMapping 1 (to.val) =
      (edslResult.getState.storageMap 1 to).val := by
  simpa [lowerSupportedEDSLContract] using
    token_transfer_correct_sufficient state to amount sender h h_no_overflow

/-- Transition bridge: lowering `.simpleToken` preserves insufficient-balance transfer reverts. -/
theorem lower_simpleToken_transfer_reverts_insufficient
    (state : Verity.ContractState)
    (to : Verity.Address)
    (amount : Nat)
    (sender : Verity.Address)
    (h_amount : amount < Verity.Core.Uint256.modulus)
    (h : (state.storageMap 1 sender).val < amount) :
    let edslResult := (Verity.Examples.SimpleToken.transfer to (Verity.Core.Uint256.ofNat amount)).run
      { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transfer"
      args := [to.val, amount]
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .simpleToken)
      (tokenEdslToSpecStorageWithAddrs state [sender, to]) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  simpa [lowerSupportedEDSLContract] using
    token_transfer_reverts_insufficient state to amount sender h_amount h

/-- Transition bridge: lowering `.safeCounter` preserves Layer-1 getter correctness. -/
theorem lower_safeCounter_getCount_correct
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let edslValue := (Verity.Examples.SafeCounter.getCount.runValue { state with sender := sender }).val
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "getCount"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .safeCounter)
      (safeCounterEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslValue := by
  simpa [lowerSupportedEDSLContract] using safeGetCount_correct state sender

/-- Transition bridge: lowering `.safeCounter` preserves getter read-only state behavior. -/
theorem lower_safeCounter_getCount_preserves_state
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let finalState := Verity.Examples.SafeCounter.getCount.runState { state with sender := sender }
    finalState.storage 0 = state.storage 0 := by
  simpa using safeGetCount_preserves_state state sender

/-- Transition bridge: lowering `.safeCounter` preserves increment semantics. -/
theorem lower_safeCounter_increment_correct
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let edslResult := Verity.Examples.SafeCounter.increment.run { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "increment"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .safeCounter)
      (safeCounterEdslToSpecStorage state) specTx
    (edslResult.isSuccess = true ↔ specResult.success = true) ∧
    (edslResult.isSuccess = true →
      specResult.finalStorage.getSlot 0 = ((Verity.ContractResult.getState edslResult).storage 0).val) := by
  simpa [lowerSupportedEDSLContract] using safeIncrement_correct state sender

/-- Transition bridge: lowering `.safeCounter` preserves overflow revert semantics. -/
theorem lower_safeCounter_increment_reverts_at_max
    (state : Verity.ContractState)
    (sender : Verity.Address)
    (h : (state.storage 0).val = Verity.Core.MAX_UINT256) :
    let edslResult := Verity.Examples.SafeCounter.increment.run { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "increment"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .safeCounter)
      (safeCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  have h_edsl : (Verity.Examples.SafeCounter.increment.run { state with sender := sender }).isSuccess = false := by
    simpa using safeIncrement_reverts_at_max state sender h
  have h_not_spec_true :
      (interpretSpec (lowerSupportedEDSLContract .safeCounter)
        (safeCounterEdslToSpecStorage state)
        { sender := sender, functionName := "increment", args := [] }).success ≠ true := by
    intro h_spec_true
    have h_equiv_true :
        (Verity.Examples.SafeCounter.increment.run { state with sender := sender }).isSuccess = true := by
      exact (safeIncrement_correct state sender).1.mpr (by simpa [lowerSupportedEDSLContract] using h_spec_true)
    rw [h_edsl] at h_equiv_true
    cases h_equiv_true
  constructor
  · simpa using h_edsl
  · by_cases h_spec_true : (interpretSpec (lowerSupportedEDSLContract .safeCounter)
        (safeCounterEdslToSpecStorage state)
        { sender := sender, functionName := "increment", args := [] }).success = true
    · exact False.elim (h_not_spec_true h_spec_true)
    · cases h_spec : (interpretSpec (lowerSupportedEDSLContract .safeCounter)
          (safeCounterEdslToSpecStorage state)
          { sender := sender, functionName := "increment", args := [] }).success <;> simp_all

/-- Transition bridge: lowering `.safeCounter` preserves decrement semantics. -/
theorem lower_safeCounter_decrement_correct
    (state : Verity.ContractState)
    (sender : Verity.Address) :
    let edslResult := Verity.Examples.SafeCounter.decrement.run { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "decrement"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .safeCounter)
      (safeCounterEdslToSpecStorage state) specTx
    (edslResult.isSuccess = true ↔ specResult.success = true) ∧
    (edslResult.isSuccess = true →
      specResult.finalStorage.getSlot 0 = ((Verity.ContractResult.getState edslResult).storage 0).val) := by
  simpa [lowerSupportedEDSLContract] using safeDecrement_correct state sender

/-- Transition bridge: lowering `.safeCounter` preserves underflow revert semantics. -/
theorem lower_safeCounter_decrement_reverts_at_zero
    (state : Verity.ContractState)
    (sender : Verity.Address)
    (h : (state.storage 0).val = 0) :
    let edslResult := Verity.Examples.SafeCounter.decrement.run { state with sender := sender }
    let specTx : Compiler.DiffTestTypes.Transaction := {
      sender := sender
      functionName := "decrement"
      args := []
    }
    let specResult := interpretSpec (lowerSupportedEDSLContract .safeCounter)
      (safeCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  have h_edsl : (Verity.Examples.SafeCounter.decrement.run { state with sender := sender }).isSuccess = false := by
    simpa using safeDecrement_reverts_at_zero state sender h
  have h_not_spec_true :
      (interpretSpec (lowerSupportedEDSLContract .safeCounter)
        (safeCounterEdslToSpecStorage state)
        { sender := sender, functionName := "decrement", args := [] }).success ≠ true := by
    intro h_spec_true
    have h_equiv_true :
        (Verity.Examples.SafeCounter.decrement.run { state with sender := sender }).isSuccess = true := by
      exact (safeDecrement_correct state sender).1.mpr (by simpa [lowerSupportedEDSLContract] using h_spec_true)
    rw [h_edsl] at h_equiv_true
    cases h_equiv_true
  constructor
  · simpa using h_edsl
  · by_cases h_spec_true : (interpretSpec (lowerSupportedEDSLContract .safeCounter)
        (safeCounterEdslToSpecStorage state)
        { sender := sender, functionName := "decrement", args := [] }).success = true
    · exact False.elim (h_not_spec_true h_spec_true)
    · cases h_spec : (interpretSpec (lowerSupportedEDSLContract .safeCounter)
          (safeCounterEdslToSpecStorage state)
          { sender := sender, functionName := "decrement", args := [] }).success <;> simp_all

/-- Supported-contract parser round-trips through the CLI-stable name map. -/
@[simp] theorem parseSupportedEDSLContract_roundtrip
    (contract : SupportedEDSLContract) :
    parseSupportedEDSLContract? (supportedEDSLContractName contract) = some contract := by
  cases contract <;> rfl

/-- CLI-stable supported-contract names are injective. -/
@[simp] theorem supportedEDSLContractName_injective :
    ∀ a b : SupportedEDSLContract,
      supportedEDSLContractName a = supportedEDSLContractName b → a = b := by
  intro a b h
  cases a <;> cases b <;> simp [supportedEDSLContractName] at h ⊢

/-- Supported-contract parser round-trips are unique. -/
@[simp] theorem parseSupportedEDSLContract_roundtrip_unique
    (requested parsed : SupportedEDSLContract) :
    parseSupportedEDSLContract? (supportedEDSLContractName requested) = some parsed ↔
      requested = parsed := by
  constructor
  · intro h
    have hEq : some requested = some parsed := by
      simpa [parseSupportedEDSLContract_roundtrip requested] using h
    exact Option.some.inj hEq
  · intro hEq
    cases hEq
    simpa using parseSupportedEDSLContract_roundtrip requested

/-- Canonical supported contract names always parse to their constructor. -/
@[simp] theorem parseSupportedEDSLContract_name_eq_implies_some
    (raw : String)
    (contract : SupportedEDSLContract)
    (hName : supportedEDSLContractName contract = raw) :
    parseSupportedEDSLContract? raw = some contract := by
  rw [← hName]
  simpa using parseSupportedEDSLContract_roundtrip contract

@[simp] theorem parseSupportedEDSLContract_eq_ok
    (raw : String)
    (contract : SupportedEDSLContract)
    (hParse : parseSupportedEDSLContract? raw = some contract) :
    parseSupportedEDSLContract raw = .ok contract := by
  unfold parseSupportedEDSLContract
  rw [hParse]

@[simp] theorem lowerFromParsedSupportedContract_eq_ok
    (raw : String)
    (contract : SupportedEDSLContract)
    (hParse : parseSupportedEDSLContract? raw = some contract) :
    lowerFromParsedSupportedContract raw = .ok (lowerSupportedEDSLContract contract) := by
  unfold lowerFromParsedSupportedContract
  rw [parseSupportedEDSLContract_eq_ok raw contract hParse]
  rfl

/-- CLI-selected supported IDs preserve `interpretSpec` semantics through lowering. -/
@[simp] theorem lowerParsedSupportedContract_preserves_interpretSpec
    (raw : String)
    (contract : SupportedEDSLContract)
    (hParse : parseSupportedEDSLContract? raw = some contract)
    (initialStorage : SpecStorage)
    (tx : Compiler.DiffTestTypes.Transaction) :
    interpretSpec
      (match lowerFromParsedSupportedContract raw with
      | .ok lowered => lowered
      | .error _ => lowerSupportedEDSLContract contract)
      initialStorage tx =
    interpretSpec (lowerSupportedEDSLContract contract) initialStorage tx := by
  simpa [lowerFromParsedSupportedContract_eq_ok raw contract hParse]

/-- Unsupported CLI-selected IDs fail closed with the boundary diagnostic. -/
@[simp] theorem lowerFromParsedSupportedContract_unknown_eq_error
    (raw : String)
    (hParse : parseSupportedEDSLContract? raw = none) :
    lowerFromParsedSupportedContract raw = .error (unsupportedEDSLContractMessage raw) := by
  unfold lowerFromParsedSupportedContract parseSupportedEDSLContract
  rw [hParse]
  rfl

/-- CLI-selected supported IDs preserve `interpretSpec` semantics through lowering. -/
@[simp] theorem lowerFromParsedSupportedContract_preserves_interpretSpec
    (raw : String)
    (contract : SupportedEDSLContract)
    (hParse : parseSupportedEDSLContract? raw = some contract)
    (initialStorage : SpecStorage)
    (tx : Compiler.DiffTestTypes.Transaction) :
    interpretSpec
      (match parseSupportedEDSLContract? raw with
      | some parsed =>
          match lowerFromEDSLSubset (.supported parsed) with
          | .ok lowered => lowered
          | .error _ => lowerSupportedEDSLContract contract
      | none => lowerSupportedEDSLContract contract)
      initialStorage tx =
    interpretSpec (lowerSupportedEDSLContract contract) initialStorage tx := by
  rw [hParse]
  simpa using
    (lowerFromEDSLSubset_supported_preserves_interpretSpec contract initialStorage tx)

/-- CLI-stable supported-contract names are pairwise distinct. -/
@[simp] theorem supportedEDSLContractNames_nodup :
    supportedEDSLContractNames.Nodup := by
  decide

/-- The current manual compile path is preserved through the lowering boundary. -/
@[simp] theorem lowerModelPath_eq_ok
    (model : Compiler.CompilationModel.CompilationModel) :
    lowerModelPath model = .ok model := by
  rfl

/-- Semantic preservation for the current lowered manual path. -/
@[simp] theorem lowerModelPath_preserves_interpretSpec
    (model : Compiler.CompilationModel.CompilationModel)
    (initialStorage : SpecStorage)
    (tx : Compiler.DiffTestTypes.Transaction) :
    interpretSpec
      (match lowerModelPath model with
      | .ok lowered => lowered
      | .error _ => model)
      initialStorage tx =
    interpretSpec model initialStorage tx := by
  rfl

end Compiler.Proofs.Lowering
