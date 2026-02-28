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
    simp [parseSupportedEDSLContract_roundtrip]

/-- Canonical supported contract names always parse to their constructor. -/
@[simp] theorem parseSupportedEDSLContract_name_eq_implies_some
    (raw : String)
    (contract : SupportedEDSLContract)
    (hName : supportedEDSLContractName contract = raw) :
    parseSupportedEDSLContract? raw = some contract := by
  rw [← hName]
  simp [parseSupportedEDSLContract_roundtrip]

@[simp] theorem parseSupportedEDSLContract_eq_ok
    (raw : String)
    (contract : SupportedEDSLContract)
    (hParse : parseSupportedEDSLContract? raw = some contract) :
    parseSupportedEDSLContract raw = .ok contract := by
  unfold parseSupportedEDSLContract
  rw [hParse]

@[simp] theorem parseSupportedEDSLContract_eq_error_of_unknown
    (raw : String)
    (hParse : parseSupportedEDSLContract? raw = none) :
    parseSupportedEDSLContract raw = .error (unsupportedEDSLContractMessage raw) := by
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
  simp [lowerFromParsedSupportedContract_eq_ok raw contract hParse]

/-- Unsupported CLI-selected IDs fail closed with the boundary diagnostic. -/
@[simp] theorem lowerFromParsedSupportedContract_unknown_eq_error
    (raw : String)
    (hParse : parseSupportedEDSLContract? raw = none) :
    lowerFromParsedSupportedContract raw = .error (unsupportedEDSLContractMessage raw) := by
  unfold lowerFromParsedSupportedContract
  rw [parseSupportedEDSLContract_eq_error_of_unknown raw hParse]
  rfl

/-- Parse-stage selected-ID failures propagate through parsed-ID lowering. -/
@[simp] theorem lowerFromParsedSupportedContract_eq_error_of_parse_error
    (raw : String)
    (err : String)
    (hParse : parseSupportedEDSLContract raw = .error err) :
    lowerFromParsedSupportedContract raw = .error err := by
  unfold lowerFromParsedSupportedContract
  rw [hParse]
  rfl

/-- A singleton selected-ID map traversal reflects any established successful lowering. -/
@[simp] theorem lowerFromParsedSupportedContract_singleton_eq_ok
    (raw : String)
    (lowered : Compiler.CompilationModel.CompilationModel)
    (hLower : lowerFromParsedSupportedContract raw = .ok lowered) :
    [raw].mapM lowerFromParsedSupportedContract = .ok [lowered] := by
  rw [List.mapM_cons, hLower]
  rfl

/-- A singleton selected-ID map traversal lowers successfully when parsing succeeds. -/
@[simp] theorem lowerFromParsedSupportedContract_singleton_eq_ok_of_parse_ok
    (raw : String)
    (contract : SupportedEDSLContract)
    (hParse : parseSupportedEDSLContract? raw = some contract) :
    [raw].mapM lowerFromParsedSupportedContract =
      .ok [lowerSupportedEDSLContract contract] := by
  apply lowerFromParsedSupportedContract_singleton_eq_ok
  exact lowerFromParsedSupportedContract_eq_ok raw contract hParse

/-- A singleton selected-ID map traversal reflects any established fail-closed lowering error. -/
@[simp] theorem lowerFromParsedSupportedContract_singleton_eq_error
    (raw : String)
    (err : String)
    (hLower : lowerFromParsedSupportedContract raw = .error err) :
    [raw].mapM lowerFromParsedSupportedContract = .error err := by
  rw [List.mapM_cons, hLower]
  rfl

/-- A cons selected-ID map traversal reflects any established successful
lowering at the head and tail. -/
@[simp] theorem lowerFromParsedSupportedContract_cons_eq_ok_of_lower_ok
    (rawHead : String)
    (rawTail : List String)
    (loweredHead : Compiler.CompilationModel.CompilationModel)
    (loweredTail : List Compiler.CompilationModel.CompilationModel)
    (hLowerHead : lowerFromParsedSupportedContract rawHead = .ok loweredHead)
    (hLowerTail : rawTail.mapM lowerFromParsedSupportedContract = .ok loweredTail) :
    (rawHead :: rawTail).mapM lowerFromParsedSupportedContract =
      .ok (loweredHead :: loweredTail) := by
  rw [List.mapM_cons]
  rw [hLowerHead]
  rw [hLowerTail]
  rfl

/-- A cons selected-ID map traversal fails closed to any established tail
map-traversal lowering error once the head lowering succeeds. -/
@[simp] theorem lowerFromParsedSupportedContract_cons_eq_error_of_tail_error
    (rawHead : String)
    (rawTail : List String)
    (headContract : SupportedEDSLContract)
    (err : String)
    (hParseHead : parseSupportedEDSLContract? rawHead = some headContract)
    (hTailError : rawTail.mapM lowerFromParsedSupportedContract = .error err) :
    (rawHead :: rawTail).mapM lowerFromParsedSupportedContract = .error err := by
  rw [List.mapM_cons]
  rw [lowerFromParsedSupportedContract_eq_ok rawHead headContract hParseHead]
  rw [hTailError]
  rfl

/-- A cons selected-ID map traversal fails closed to any established head
lowering error. -/
@[simp] theorem lowerFromParsedSupportedContract_cons_eq_error_of_head_error
    (rawHead : String)
    (rawTail : List String)
    (err : String)
    (hHeadError : lowerFromParsedSupportedContract rawHead = .error err) :
    (rawHead :: rawTail).mapM lowerFromParsedSupportedContract = .error err := by
  rw [List.mapM_cons]
  rw [hHeadError]
  rfl

/-- A two-ID selected map traversal reflects any established successful lowerings. -/
@[simp] theorem lowerFromParsedSupportedContract_pair_eq_ok_of_lower_ok
    (rawA rawB : String)
    (loweredA loweredB : Compiler.CompilationModel.CompilationModel)
    (hLowerA : lowerFromParsedSupportedContract rawA = .ok loweredA)
    (hLowerB : lowerFromParsedSupportedContract rawB = .ok loweredB) :
    [rawA, rawB].mapM lowerFromParsedSupportedContract = .ok [loweredA, loweredB] := by
  have hTailOk : [rawB].mapM lowerFromParsedSupportedContract = .ok [loweredB] := by
    simpa using lowerFromParsedSupportedContract_singleton_eq_ok rawB loweredB hLowerB
  simpa using
    lowerFromParsedSupportedContract_cons_eq_ok_of_lower_ok
      rawA
      [rawB]
      loweredA
      [loweredB]
      hLowerA
      hTailOk

/-- A two-ID selected map traversal lowers successfully when both IDs parse successfully. -/
@[simp] theorem lowerFromParsedSupportedContract_pair_eq_ok_of_parse_ok
    (rawA rawB : String)
    (contractA contractB : SupportedEDSLContract)
    (hParseA : parseSupportedEDSLContract? rawA = some contractA)
    (hParseB : parseSupportedEDSLContract? rawB = some contractB) :
    [rawA, rawB].mapM lowerFromParsedSupportedContract =
      .ok [lowerSupportedEDSLContract contractA, lowerSupportedEDSLContract contractB] := by
  apply lowerFromParsedSupportedContract_pair_eq_ok_of_lower_ok
  exact lowerFromParsedSupportedContract_eq_ok rawA contractA hParseA
  exact lowerFromParsedSupportedContract_eq_ok rawB contractB hParseB

/-- Ordered parse-success witness for selected contract IDs. -/
inductive SelectedIDsParseTo : List String → List SupportedEDSLContract → Prop where
  | nil : SelectedIDsParseTo [] []
  | cons
      (hParse : parseSupportedEDSLContract? raw = some contract)
      (hTail : SelectedIDsParseTo rawTail contractTail) :
      SelectedIDsParseTo (raw :: rawTail) (contract :: contractTail)

/-- Selected-ID map traversal lowers successfully for any list once each selected ID
is known to parse to a supported contract in order. -/
@[simp] theorem lowerFromParsedSupportedContract_mapM_eq_ok_of_parse_ok
    (rawContracts : List String)
    (contracts : List SupportedEDSLContract)
    (hParseAll : SelectedIDsParseTo rawContracts contracts) :
    rawContracts.mapM lowerFromParsedSupportedContract =
      .ok (contracts.map lowerSupportedEDSLContract) := by
  induction hParseAll with
  | nil =>
      rfl
  | @cons raw contract rawTail contractTail hParse hRest ih =>
      rw [List.mapM_cons]
      rw [lowerFromParsedSupportedContract_eq_ok raw contract hParse]
      rw [ih]
      rfl

/-- Parsed selected IDs lower to an ordered append decomposition when the strict
prefix and strict suffix are known to parse successfully in order and the middle
selected ID parses to a supported contract. -/
@[simp] theorem lowerFromParsedSupportedContract_append_eq_ok_of_parse_ok
    (rawPrefix : List String)
    (rawMid : String)
    (rawSuffix : List String)
    (prefixContracts : List SupportedEDSLContract)
    (midContract : SupportedEDSLContract)
    (suffixContracts : List SupportedEDSLContract)
    (hPrefixParse : SelectedIDsParseTo rawPrefix prefixContracts)
    (hParseMid : parseSupportedEDSLContract? rawMid = some midContract)
    (hSuffixParse : SelectedIDsParseTo rawSuffix suffixContracts) :
    (rawPrefix ++ rawMid :: rawSuffix).mapM lowerFromParsedSupportedContract =
      .ok
        (prefixContracts.map lowerSupportedEDSLContract ++
          lowerSupportedEDSLContract midContract ::
            suffixContracts.map lowerSupportedEDSLContract) := by
  rw [List.mapM_append]
  rw [lowerFromParsedSupportedContract_mapM_eq_ok_of_parse_ok
      rawPrefix prefixContracts hPrefixParse]
  rw [List.mapM_cons]
  rw [lowerFromParsedSupportedContract_eq_ok rawMid midContract hParseMid]
  rw [lowerFromParsedSupportedContract_mapM_eq_ok_of_parse_ok
      rawSuffix suffixContracts hSuffixParse]
  rfl

/-- Any append-position parse-stage failure propagates fail-closed through selected-ID
map traversal once the strict prefix is known to parse successfully in order. -/
@[simp] theorem lowerFromParsedSupportedContract_append_eq_error_of_parse_error
    (rawPrefix : List String)
    (rawBad : String)
    (rawSuffix : List String)
    (prefixContracts : List SupportedEDSLContract)
    (err : String)
    (hPrefixParse : SelectedIDsParseTo rawPrefix prefixContracts)
    (hParseBad : parseSupportedEDSLContract rawBad = .error err) :
    (rawPrefix ++ rawBad :: rawSuffix).mapM lowerFromParsedSupportedContract = .error err := by
  rw [List.mapM_append]
  rw [lowerFromParsedSupportedContract_mapM_eq_ok_of_parse_ok
        rawPrefix
        prefixContracts
        hPrefixParse]
  rw [List.mapM_cons]
  rw [lowerFromParsedSupportedContract_eq_error_of_parse_error rawBad err hParseBad]
  rfl

/-- Empty selected-ID input follows the default canonical-name lowering path. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_default_eq :
    lowerRequestedSupportedEDSLContracts [] =
      supportedEDSLContractNames.mapM lowerFromParsedSupportedContract := by
  rfl

/-- Canonical supported-contract IDs lower to the canonical supported-contract model list. -/
@[simp] theorem supportedEDSLContractNames_mapM_lowerFromParsed_eq_ok :
    supportedEDSLContractNames.mapM lowerFromParsedSupportedContract =
      .ok (supportedEDSLContracts.map lowerSupportedEDSLContract) := by
  rfl

/-- Empty selected-ID input lowers to the canonical supported-contract model list. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_default_eq_ok_supported :
    lowerRequestedSupportedEDSLContracts [] =
      .ok (supportedEDSLContracts.map lowerSupportedEDSLContract) := by
  rw [lowerRequestedSupportedEDSLContracts_default_eq]
  simp [supportedEDSLContractNames_mapM_lowerFromParsed_eq_ok]

/-- Duplicate selected IDs fail closed through the centralized helper boundary. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_duplicate_eq_error
    (rawContracts : List String)
    (dup : String)
    (hDup : findDuplicateRawContract? [] rawContracts = some dup) :
    lowerRequestedSupportedEDSLContracts rawContracts =
      .error s!"Duplicate --edsl-contract value: {dup}" := by
  unfold lowerRequestedSupportedEDSLContracts
  have hDup' : findDuplicateRawContract? ∅ rawContracts = some dup := by
    simpa using hDup
  rw [hDup']
  rfl

/-- Non-empty duplicate-free selected IDs lower exactly through parsed-ID map traversal. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_eq
    (rawContracts : List String)
    (hNoDup : findDuplicateRawContract? [] rawContracts = none)
    (hNonEmpty : rawContracts ≠ []) :
    lowerRequestedSupportedEDSLContracts rawContracts =
      rawContracts.mapM lowerFromParsedSupportedContract := by
  unfold lowerRequestedSupportedEDSLContracts
  have hNoDup' : findDuplicateRawContract? ∅ rawContracts = none := by
    simpa using hNoDup
  rw [hNoDup']
  simp [hNonEmpty]

/-- Non-empty duplicate-free selected IDs lower to any explicitly established
ordered `mapM` lowering result through the centralized helper boundary. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_eq_ok_of_mapM_lower_ok
    (rawContracts : List String)
    (loweredContracts : List Compiler.CompilationModel.CompilationModel)
    (hNoDup : findDuplicateRawContract? [] rawContracts = none)
    (hNonEmpty : rawContracts ≠ [])
    (hLowerAll : rawContracts.mapM lowerFromParsedSupportedContract = .ok loweredContracts) :
    lowerRequestedSupportedEDSLContracts rawContracts =
      .ok loweredContracts := by
  rw [lowerRequestedSupportedEDSLContracts_selected_eq rawContracts hNoDup hNonEmpty]
  exact hLowerAll

/-- Non-empty duplicate-free selected IDs lower to the ordered supported-contract
target list once each selected ID is known to parse successfully in order. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_eq_ok_of_parse_ok
    (rawContracts : List String)
    (contracts : List SupportedEDSLContract)
    (hNoDup : findDuplicateRawContract? [] rawContracts = none)
    (hNonEmpty : rawContracts ≠ [])
    (hParseAll : SelectedIDsParseTo rawContracts contracts) :
    lowerRequestedSupportedEDSLContracts rawContracts =
      .ok (contracts.map lowerSupportedEDSLContract) := by
  apply lowerRequestedSupportedEDSLContracts_selected_eq_ok_of_mapM_lower_ok
    rawContracts
    (contracts.map lowerSupportedEDSLContract)
    hNoDup
    hNonEmpty
  exact lowerFromParsedSupportedContract_mapM_eq_ok_of_parse_ok
    rawContracts
    contracts
    hParseAll

/-- Non-empty duplicate-free selected IDs fail closed to any explicitly established
ordered `mapM` lowering error through the centralized helper boundary. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_eq_error_of_mapM_lower_error
    (rawContracts : List String)
    (err : String)
    (hNoDup : findDuplicateRawContract? [] rawContracts = none)
    (hNonEmpty : rawContracts ≠ [])
    (hLowerAll : rawContracts.mapM lowerFromParsedSupportedContract = .error err) :
    lowerRequestedSupportedEDSLContracts rawContracts =
      .error err := by
  rw [lowerRequestedSupportedEDSLContracts_selected_eq rawContracts hNoDup hNonEmpty]
  exact hLowerAll

/-- Duplicate-free selected IDs fail closed with an arbitrary established lower-error
at any append position once the strict prefix is already known to lower successfully. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_append_eq_error_of_lower_error
    (rawPrefix : List String)
    (rawBad : String)
    (rawSuffix : List String)
    (loweredPrefixContracts : List Compiler.CompilationModel.CompilationModel)
    (err : String)
    (hNoDup : findDuplicateRawContract? [] (rawPrefix ++ rawBad :: rawSuffix) = none)
    (hPrefixOk : rawPrefix.mapM lowerFromParsedSupportedContract = .ok loweredPrefixContracts)
    (hLowerBad : lowerFromParsedSupportedContract rawBad = .error err) :
    lowerRequestedSupportedEDSLContracts (rawPrefix ++ rawBad :: rawSuffix) =
      .error err := by
  have hNonEmpty : (rawPrefix ++ rawBad :: rawSuffix) ≠ [] := by simp
  rw [lowerRequestedSupportedEDSLContracts_selected_eq
    (rawPrefix ++ rawBad :: rawSuffix) hNoDup hNonEmpty]
  rw [List.mapM_append, hPrefixOk]
  rw [List.mapM_cons]
  rw [hLowerBad]
  rfl

/-- A singleton selected ID fails closed to any explicitly established
parse-stage error through the centralized helper boundary. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_singleton_eq_error_of_lower_error
    (raw : String)
    (err : String)
    (hLower : lowerFromParsedSupportedContract raw = .error err) :
    lowerRequestedSupportedEDSLContracts [raw] = .error err := by
  have hNoDup : findDuplicateRawContract? [] [raw] = none := by
    simp [findDuplicateRawContract?]
  have hNonEmpty : [raw] ≠ [] := by
    simp
  apply lowerRequestedSupportedEDSLContracts_selected_eq_error_of_mapM_lower_error
    [raw] err hNoDup hNonEmpty
  simpa using lowerFromParsedSupportedContract_singleton_eq_error raw err hLower

/-- A singleton selected ID fails closed to any explicitly established
parse-stage error through the centralized helper boundary. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_singleton_eq_error_of_parse_error
    (raw : String)
    (err : String)
    (hParse : parseSupportedEDSLContract raw = .error err) :
    lowerRequestedSupportedEDSLContracts [raw] = .error err := by
  apply lowerRequestedSupportedEDSLContracts_selected_singleton_eq_error_of_lower_error raw err
  simpa using lowerFromParsedSupportedContract_eq_error_of_parse_error raw err hParse

/-- Non-empty selected IDs fail closed to any explicitly established parse-stage
error when the head selected ID fails parsing. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_cons_eq_error_of_head_error
    (rawHead : String)
    (rawTail : List String)
    (err : String)
    (hNoDup : findDuplicateRawContract? [] (rawHead :: rawTail) = none)
    (hHeadError : lowerFromParsedSupportedContract rawHead = .error err) :
    lowerRequestedSupportedEDSLContracts (rawHead :: rawTail) =
      .error err := by
  have hLowerAll : (rawHead :: rawTail).mapM lowerFromParsedSupportedContract = .error err := by
    exact lowerFromParsedSupportedContract_cons_eq_error_of_head_error rawHead rawTail err hHeadError
  have hNonEmpty : (rawHead :: rawTail) ≠ [] := by
    simp
  exact lowerRequestedSupportedEDSLContracts_selected_eq_error_of_mapM_lower_error
    (rawHead :: rawTail) err hNoDup hNonEmpty hLowerAll

/-- Non-empty selected IDs fail closed to any explicitly established parse-stage
error when the head selected ID fails parsing. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_head_eq_error_of_parse_error
    (rawBad : String)
    (rest : List String)
    (err : String)
    (hNoDup : findDuplicateRawContract? [] (rawBad :: rest) = none)
    (hParseBad : parseSupportedEDSLContract rawBad = .error err) :
    lowerRequestedSupportedEDSLContracts (rawBad :: rest) =
      .error err := by
  apply lowerRequestedSupportedEDSLContracts_selected_cons_eq_error_of_head_error
    rawBad rest err hNoDup
  simpa using lowerFromParsedSupportedContract_eq_error_of_parse_error rawBad err hParseBad

/-- Duplicate-free selected IDs with a known-valid head ID fail closed to any
explicitly established tail map-traversal lowering error. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_cons_eq_error_of_tail_error
    (rawHead : String)
    (rawTail : List String)
    (headContract : SupportedEDSLContract)
    (err : String)
    (hNoDup : findDuplicateRawContract? [] (rawHead :: rawTail) = none)
    (hParseHead : parseSupportedEDSLContract? rawHead = some headContract)
    (hTailError : rawTail.mapM lowerFromParsedSupportedContract = .error err) :
    lowerRequestedSupportedEDSLContracts (rawHead :: rawTail) =
      .error err := by
  have hNonEmpty : (rawHead :: rawTail) ≠ [] := by
    simp
  have hLowerAll :
      (rawHead :: rawTail).mapM lowerFromParsedSupportedContract = .error err := by
    exact
      lowerFromParsedSupportedContract_cons_eq_error_of_tail_error
        rawHead
        rawTail
        headContract
        err
        hParseHead
        hTailError
  exact lowerRequestedSupportedEDSLContracts_selected_eq_error_of_mapM_lower_error
    (rawHead :: rawTail) err hNoDup hNonEmpty hLowerAll

/-- Duplicate-free selected IDs with a known-valid head ID fail closed to any
explicitly established lower-error at the head of the tail list. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_cons_eq_error_of_lower_error
    (rawHead : String)
    (rawBad : String)
    (rawSuffix : List String)
    (headContract : SupportedEDSLContract)
    (err : String)
    (hNoDup : findDuplicateRawContract? [] (rawHead :: rawBad :: rawSuffix) = none)
    (hParseHead : parseSupportedEDSLContract? rawHead = some headContract)
    (hLowerBad : lowerFromParsedSupportedContract rawBad = .error err) :
    lowerRequestedSupportedEDSLContracts (rawHead :: rawBad :: rawSuffix) =
      .error err := by
  have hTailError :
      (rawBad :: rawSuffix).mapM lowerFromParsedSupportedContract = .error err := by
    rw [List.mapM_cons]
    rw [hLowerBad]
    rfl
  simpa using
    lowerRequestedSupportedEDSLContracts_selected_cons_eq_error_of_tail_error
      rawHead
      (rawBad :: rawSuffix)
      headContract
      err
      hNoDup
      hParseHead
      hTailError

/-- Non-empty selected IDs fail closed to any explicitly established parse-stage
error when a tail selected ID fails parsing after a known-valid head ID. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_cons_eq_error_of_parse_error
    (rawHead : String)
    (rawBad : String)
    (rawSuffix : List String)
    (headContract : SupportedEDSLContract)
    (err : String)
    (hNoDup : findDuplicateRawContract? [] (rawHead :: rawBad :: rawSuffix) = none)
    (hParseHead : parseSupportedEDSLContract? rawHead = some headContract)
    (hParseBad : parseSupportedEDSLContract rawBad = .error err) :
    lowerRequestedSupportedEDSLContracts (rawHead :: rawBad :: rawSuffix) =
      .error err := by
  have hPrefixParse : SelectedIDsParseTo [rawHead] [headContract] := by
    exact SelectedIDsParseTo.cons hParseHead SelectedIDsParseTo.nil
  have hLowerAll :
      (rawHead :: rawBad :: rawSuffix).mapM lowerFromParsedSupportedContract = .error err := by
    simpa using lowerFromParsedSupportedContract_append_eq_error_of_parse_error
      [rawHead]
      rawBad
      rawSuffix
      [headContract]
      err
      hPrefixParse
      hParseBad
  have hNonEmpty : (rawHead :: rawBad :: rawSuffix) ≠ [] := by
    simp
  exact lowerRequestedSupportedEDSLContracts_selected_eq_error_of_mapM_lower_error
    (rawHead :: rawBad :: rawSuffix)
    err
    hNoDup
    hNonEmpty
    hLowerAll

/-- Non-empty selected IDs fail closed to any explicitly established parse-stage
error when a tail selected ID fails parsing after a known-valid head ID. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_tail_eq_error_of_parse_error
    (rawOk rawBad : String)
    (rest : List String)
    (contract : SupportedEDSLContract)
    (err : String)
    (hNoDup : findDuplicateRawContract? [] (rawOk :: rawBad :: rest) = none)
    (hParseOk : parseSupportedEDSLContract? rawOk = some contract)
    (hParseBad : parseSupportedEDSLContract rawBad = .error err) :
    lowerRequestedSupportedEDSLContracts (rawOk :: rawBad :: rest) =
      .error err := by
  simpa using
    lowerRequestedSupportedEDSLContracts_selected_cons_eq_error_of_parse_error
      rawOk
      rawBad
      rest
      contract
      err
      hNoDup
      hParseOk
      hParseBad

/-- Duplicate-free selected IDs fail closed to a parse-stage error at any position
when every strictly preceding selected ID is already known to lower successfully. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_append_eq_error_of_parse_error
    (rawPrefix : List String)
    (rawBad : String)
    (rawSuffix : List String)
    (loweredPrefixContracts : List Compiler.CompilationModel.CompilationModel)
    (err : String)
    (hNoDup : findDuplicateRawContract? [] (rawPrefix ++ rawBad :: rawSuffix) = none)
    (hPrefixOk : rawPrefix.mapM lowerFromParsedSupportedContract = .ok loweredPrefixContracts)
    (hParseBad : parseSupportedEDSLContract rawBad = .error err) :
    lowerRequestedSupportedEDSLContracts (rawPrefix ++ rawBad :: rawSuffix) =
      .error err := by
  apply lowerRequestedSupportedEDSLContracts_selected_append_eq_error_of_lower_error
    rawPrefix rawBad rawSuffix loweredPrefixContracts err hNoDup hPrefixOk
  simpa using lowerFromParsedSupportedContract_eq_error_of_parse_error rawBad err hParseBad

/-- Duplicate-free selected IDs fail closed to a parse-stage error at any append
position once the strict prefix is known to parse successfully in order. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_append_eq_error_of_prefix_parse_ok
    (rawPrefix : List String)
    (rawBad : String)
    (rawSuffix : List String)
    (prefixContracts : List SupportedEDSLContract)
    (err : String)
    (hNoDup : findDuplicateRawContract? [] (rawPrefix ++ rawBad :: rawSuffix) = none)
    (hPrefixParse : SelectedIDsParseTo rawPrefix prefixContracts)
    (hParseBad : parseSupportedEDSLContract rawBad = .error err) :
    lowerRequestedSupportedEDSLContracts (rawPrefix ++ rawBad :: rawSuffix) =
      .error err := by
  have hNonEmpty : (rawPrefix ++ rawBad :: rawSuffix) ≠ [] := by
    simp
  apply lowerRequestedSupportedEDSLContracts_selected_eq_error_of_mapM_lower_error
    (rawPrefix ++ rawBad :: rawSuffix)
    err
    hNoDup
    hNonEmpty
  exact lowerFromParsedSupportedContract_append_eq_error_of_parse_error
    rawPrefix
    rawBad
    rawSuffix
    prefixContracts
    err
    hPrefixParse
    hParseBad

/-- Explicit full selected-ID input is definitionally equivalent to default selected-ID input. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_full_eq_default :
    lowerRequestedSupportedEDSLContracts supportedEDSLContractNames =
      lowerRequestedSupportedEDSLContracts [] := by
  have hNoDup : findDuplicateRawContract? [] supportedEDSLContractNames = none := by
    decide
  have hNonEmpty : supportedEDSLContractNames ≠ [] := by
    decide
  rw [lowerRequestedSupportedEDSLContracts_selected_eq supportedEDSLContractNames hNoDup hNonEmpty]
  rw [lowerRequestedSupportedEDSLContracts_default_eq]

/-- Duplicate-free selected IDs lower to an ordered append decomposition when
the prefix, middle, and suffix map traversals are already known to lower
successfully. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_append_eq_ok_of_lower_ok
    (rawPrefix : List String)
    (rawMid : String)
    (rawSuffix : List String)
    (loweredPrefixContracts : List Compiler.CompilationModel.CompilationModel)
    (loweredMidContract : Compiler.CompilationModel.CompilationModel)
    (loweredSuffixContracts : List Compiler.CompilationModel.CompilationModel)
    (hNoDup : findDuplicateRawContract? [] (rawPrefix ++ rawMid :: rawSuffix) = none)
    (hPrefixOk : rawPrefix.mapM lowerFromParsedSupportedContract = .ok loweredPrefixContracts)
    (hLowerMid : lowerFromParsedSupportedContract rawMid = .ok loweredMidContract)
    (hSuffixOk : rawSuffix.mapM lowerFromParsedSupportedContract = .ok loweredSuffixContracts) :
    lowerRequestedSupportedEDSLContracts (rawPrefix ++ rawMid :: rawSuffix) =
      .ok (loweredPrefixContracts ++ loweredMidContract :: loweredSuffixContracts) := by
  have hNonEmpty : (rawPrefix ++ rawMid :: rawSuffix) ≠ [] := by simp
  rw [lowerRequestedSupportedEDSLContracts_selected_eq
      (rawPrefix ++ rawMid :: rawSuffix) hNoDup hNonEmpty]
  rw [List.mapM_append, hPrefixOk]
  rw [List.mapM_cons]
  rw [hLowerMid]
  rw [hSuffixOk]
  rfl

/-- Duplicate-free selected IDs lower to an ordered append decomposition when
the prefix and suffix map traversals are already known to lower successfully and
the middle selected ID parses to a supported contract. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_append_eq_ok_of_split_ok
    (rawPrefix : List String)
    (rawMid : String)
    (rawSuffix : List String)
    (loweredPrefixContracts : List Compiler.CompilationModel.CompilationModel)
    (midContract : SupportedEDSLContract)
    (loweredSuffixContracts : List Compiler.CompilationModel.CompilationModel)
    (hNoDup : findDuplicateRawContract? [] (rawPrefix ++ rawMid :: rawSuffix) = none)
    (hPrefixOk : rawPrefix.mapM lowerFromParsedSupportedContract = .ok loweredPrefixContracts)
    (hParseMid : parseSupportedEDSLContract? rawMid = some midContract)
    (hSuffixOk : rawSuffix.mapM lowerFromParsedSupportedContract = .ok loweredSuffixContracts) :
    lowerRequestedSupportedEDSLContracts (rawPrefix ++ rawMid :: rawSuffix) =
      .ok
        (loweredPrefixContracts ++
          lowerSupportedEDSLContract midContract :: loweredSuffixContracts) := by
  apply lowerRequestedSupportedEDSLContracts_selected_append_eq_ok_of_lower_ok
      rawPrefix
      rawMid
      rawSuffix
      loweredPrefixContracts
      (lowerSupportedEDSLContract midContract)
      loweredSuffixContracts
      hNoDup
      hPrefixOk
      ?_
      hSuffixOk
  exact lowerFromParsedSupportedContract_eq_ok rawMid midContract hParseMid

/-- Duplicate-free selected IDs lower to an ordered append decomposition when the
strict prefix and strict suffix selected IDs are known to parse successfully in order
and the middle selected ID parses to a supported contract. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_append_eq_ok_of_parse_ok
    (rawPrefix : List String)
    (rawMid : String)
    (rawSuffix : List String)
    (prefixContracts : List SupportedEDSLContract)
    (midContract : SupportedEDSLContract)
    (suffixContracts : List SupportedEDSLContract)
    (hNoDup : findDuplicateRawContract? [] (rawPrefix ++ rawMid :: rawSuffix) = none)
    (hPrefixParse : SelectedIDsParseTo rawPrefix prefixContracts)
    (hParseMid : parseSupportedEDSLContract? rawMid = some midContract)
    (hSuffixParse : SelectedIDsParseTo rawSuffix suffixContracts) :
    lowerRequestedSupportedEDSLContracts (rawPrefix ++ rawMid :: rawSuffix) =
      .ok
        (prefixContracts.map lowerSupportedEDSLContract ++
          lowerSupportedEDSLContract midContract ::
            suffixContracts.map lowerSupportedEDSLContract) := by
  have hNonEmpty : (rawPrefix ++ rawMid :: rawSuffix) ≠ [] := by
    simp
  apply lowerRequestedSupportedEDSLContracts_selected_eq_ok_of_mapM_lower_ok
    (rawPrefix ++ rawMid :: rawSuffix)
    (prefixContracts.map lowerSupportedEDSLContract ++
      lowerSupportedEDSLContract midContract ::
        suffixContracts.map lowerSupportedEDSLContract)
    hNoDup
    hNonEmpty
  exact lowerFromParsedSupportedContract_append_eq_ok_of_parse_ok
    rawPrefix
    rawMid
    rawSuffix
    prefixContracts
    midContract
    suffixContracts
    hPrefixParse
    hParseMid
    hSuffixParse

/-- Duplicate-free selected IDs with a known-good head ID lower to the expected
ordered `head :: tail` list once the tail map traversal is already known to lower
successfully. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_cons_eq_ok_of_lower_ok
    (rawHead : String)
    (rawTail : List String)
    (loweredHeadContract : Compiler.CompilationModel.CompilationModel)
    (loweredTailContracts : List Compiler.CompilationModel.CompilationModel)
    (hNoDup : findDuplicateRawContract? [] (rawHead :: rawTail) = none)
    (hLowerHead : lowerFromParsedSupportedContract rawHead = .ok loweredHeadContract)
    (hTailOk : rawTail.mapM lowerFromParsedSupportedContract = .ok loweredTailContracts) :
    lowerRequestedSupportedEDSLContracts (rawHead :: rawTail) =
      .ok (loweredHeadContract :: loweredTailContracts) := by
  have hNonEmpty : (rawHead :: rawTail) ≠ [] := by
    simp
  have hLowerAll :
      (rawHead :: rawTail).mapM lowerFromParsedSupportedContract =
        .ok (loweredHeadContract :: loweredTailContracts) := by
    exact
      lowerFromParsedSupportedContract_cons_eq_ok_of_lower_ok
        rawHead
        rawTail
        loweredHeadContract
        loweredTailContracts
        hLowerHead
        hTailOk
  exact lowerRequestedSupportedEDSLContracts_selected_eq_ok_of_mapM_lower_ok
    (rawHead :: rawTail)
    (loweredHeadContract :: loweredTailContracts)
    hNoDup
    hNonEmpty
    hLowerAll

/-- Duplicate-free selected IDs with a known-good head ID lower to the expected
ordered `head :: tail` list once the tail map traversal is already known to lower
successfully. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_cons_eq_ok_of_tail_ok
    (rawHead : String)
    (rawTail : List String)
    (headContract : SupportedEDSLContract)
    (loweredTailContracts : List Compiler.CompilationModel.CompilationModel)
    (hNoDup : findDuplicateRawContract? [] (rawHead :: rawTail) = none)
    (hParseHead : parseSupportedEDSLContract? rawHead = some headContract)
    (hTailOk : rawTail.mapM lowerFromParsedSupportedContract = .ok loweredTailContracts) :
    lowerRequestedSupportedEDSLContracts (rawHead :: rawTail) =
      .ok (lowerSupportedEDSLContract headContract :: loweredTailContracts) := by
  apply lowerRequestedSupportedEDSLContracts_selected_cons_eq_ok_of_lower_ok
      rawHead
      rawTail
      (lowerSupportedEDSLContract headContract)
      loweredTailContracts
      hNoDup
      ?_
      hTailOk
  exact lowerFromParsedSupportedContract_eq_ok rawHead headContract hParseHead

/-- Duplicate-free selected IDs with a parser-confirmed head and parser-confirmed tail
lower to the expected ordered `head :: tail` list. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_cons_eq_ok_of_parse_ok
    (rawHead : String)
    (rawTail : List String)
    (headContract : SupportedEDSLContract)
    (tailContracts : List SupportedEDSLContract)
    (hNoDup : findDuplicateRawContract? [] (rawHead :: rawTail) = none)
    (hParseHead : parseSupportedEDSLContract? rawHead = some headContract)
    (hTailParse : SelectedIDsParseTo rawTail tailContracts) :
    lowerRequestedSupportedEDSLContracts (rawHead :: rawTail) =
      .ok (lowerSupportedEDSLContract headContract :: tailContracts.map lowerSupportedEDSLContract) := by
  have hNonEmpty : (rawHead :: rawTail) ≠ [] := by
    simp
  have hParseAll : SelectedIDsParseTo (rawHead :: rawTail) (headContract :: tailContracts) := by
    exact SelectedIDsParseTo.cons hParseHead hTailParse
  simpa using
    lowerRequestedSupportedEDSLContracts_selected_eq_ok_of_parse_ok
      (rawHead :: rawTail)
      (headContract :: tailContracts)
      hNoDup
      hNonEmpty
      hParseAll

/-- A singleton selected ID lowers successfully whenever its parser result is known. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_singleton_eq_ok_of_parse_ok
    (raw : String)
    (contract : SupportedEDSLContract)
    (hParse : parseSupportedEDSLContract? raw = some contract) :
    lowerRequestedSupportedEDSLContracts [raw] =
      .ok [lowerSupportedEDSLContract contract] := by
  have hNoDup : findDuplicateRawContract? [] [raw] = none := by
    simp [findDuplicateRawContract?]
  simpa using lowerRequestedSupportedEDSLContracts_selected_cons_eq_ok_of_parse_ok
    raw
    []
    contract
    []
    hNoDup
    hParse
    SelectedIDsParseTo.nil

/-- A singleton selected canonical ID lowers to the expected singleton model list. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_singleton_eq_ok
    (contract : SupportedEDSLContract) :
    lowerRequestedSupportedEDSLContracts [supportedEDSLContractName contract] =
      .ok [lowerSupportedEDSLContract contract] := by
  exact lowerRequestedSupportedEDSLContracts_selected_singleton_eq_ok_of_parse_ok
    (supportedEDSLContractName contract)
    contract
    (parseSupportedEDSLContract_roundtrip contract)

/-- A duplicate-free selected pair of known IDs lowers to the expected ordered pair. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_pair_eq_ok
    (rawA rawB : String)
    (contractA contractB : SupportedEDSLContract)
    (hNoDup : findDuplicateRawContract? [] [rawA, rawB] = none)
    (hParseA : parseSupportedEDSLContract? rawA = some contractA)
    (hParseB : parseSupportedEDSLContract? rawB = some contractB) :
    lowerRequestedSupportedEDSLContracts [rawA, rawB] =
      .ok [lowerSupportedEDSLContract contractA, lowerSupportedEDSLContract contractB] := by
  have hTailParse : SelectedIDsParseTo [rawB] [contractB] := by
    exact SelectedIDsParseTo.cons hParseB SelectedIDsParseTo.nil
  simpa using lowerRequestedSupportedEDSLContracts_selected_cons_eq_ok_of_parse_ok
    rawA
    [rawB]
    contractA
    [contractB]
    hNoDup
    hParseA
    hTailParse

/-- A duplicate-free selected triple of known IDs lowers to the expected ordered triple. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_triple_eq_ok
    (rawA rawB rawC : String)
    (contractA contractB contractC : SupportedEDSLContract)
    (hNoDup : findDuplicateRawContract? [] [rawA, rawB, rawC] = none)
    (hParseA : parseSupportedEDSLContract? rawA = some contractA)
    (hParseB : parseSupportedEDSLContract? rawB = some contractB)
    (hParseC : parseSupportedEDSLContract? rawC = some contractC) :
    lowerRequestedSupportedEDSLContracts [rawA, rawB, rawC] =
      .ok
        [ lowerSupportedEDSLContract contractA
        , lowerSupportedEDSLContract contractB
        , lowerSupportedEDSLContract contractC
        ] := by
  have hTailParse : SelectedIDsParseTo [rawB, rawC] [contractB, contractC] := by
    exact
      SelectedIDsParseTo.cons
        hParseB
        (SelectedIDsParseTo.cons hParseC SelectedIDsParseTo.nil)
  simpa using lowerRequestedSupportedEDSLContracts_selected_cons_eq_ok_of_parse_ok
    rawA
    [rawB, rawC]
    contractA
    [contractB, contractC]
    hNoDup
    hParseA
    hTailParse

/-- Non-empty selected IDs fail closed with the unsupported-ID diagnostic
when the head selected ID is unknown. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_unknown_head_eq_error
    (raw : String)
    (rest : List String)
    (hNoDup : findDuplicateRawContract? [] (raw :: rest) = none)
    (hParse : parseSupportedEDSLContract? raw = none) :
    lowerRequestedSupportedEDSLContracts (raw :: rest) =
      .error (unsupportedEDSLContractMessage raw) := by
  apply lowerRequestedSupportedEDSLContracts_selected_cons_eq_error_of_head_error
    raw rest (unsupportedEDSLContractMessage raw) hNoDup
  simpa using lowerFromParsedSupportedContract_unknown_eq_error raw hParse

/-- A singleton unknown selected ID fails closed with the same unsupported-ID diagnostic. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_singleton_unknown_eq_error
    (raw : String)
    (hParse : parseSupportedEDSLContract? raw = none) :
    lowerRequestedSupportedEDSLContracts [raw] =
      .error (unsupportedEDSLContractMessage raw) := by
  apply lowerRequestedSupportedEDSLContracts_selected_singleton_eq_error_of_lower_error
    raw
    (unsupportedEDSLContractMessage raw)
  simpa using lowerFromParsedSupportedContract_unknown_eq_error raw hParse

/-- Duplicate-free selected IDs fail closed with the unsupported-ID diagnostic
when any selected ID is unknown after an already parse-confirmed prefix. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_append_unknown_eq_error_of_prefix_parse_ok
    (rawPrefix : List String)
    (rawBad : String)
    (rawSuffix : List String)
    (prefixContracts : List SupportedEDSLContract)
    (hNoDup : findDuplicateRawContract? [] (rawPrefix ++ rawBad :: rawSuffix) = none)
    (hPrefixParse : SelectedIDsParseTo rawPrefix prefixContracts)
    (hParseBad : parseSupportedEDSLContract? rawBad = none) :
    lowerRequestedSupportedEDSLContracts (rawPrefix ++ rawBad :: rawSuffix) =
      .error (unsupportedEDSLContractMessage rawBad) := by
  apply lowerRequestedSupportedEDSLContracts_selected_append_eq_error_of_prefix_parse_ok
    rawPrefix
    rawBad
    rawSuffix
    prefixContracts
    (unsupportedEDSLContractMessage rawBad)
    hNoDup
    hPrefixParse
  exact parseSupportedEDSLContract_eq_error_of_unknown rawBad hParseBad

/-- Non-empty selected IDs fail closed with the unsupported-ID diagnostic
when a tail selected ID is unknown after a known-valid head ID. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_unknown_tail_eq_error
    (rawOk rawBad : String)
    (rest : List String)
    (contract : SupportedEDSLContract)
    (hNoDup : findDuplicateRawContract? [] (rawOk :: rawBad :: rest) = none)
    (hParseOk : parseSupportedEDSLContract? rawOk = some contract)
    (hParseBad : parseSupportedEDSLContract? rawBad = none) :
    lowerRequestedSupportedEDSLContracts (rawOk :: rawBad :: rest) =
      .error (unsupportedEDSLContractMessage rawBad) := by
  have hPrefixParse : SelectedIDsParseTo [rawOk] [contract] := by
    exact SelectedIDsParseTo.cons hParseOk SelectedIDsParseTo.nil
  simpa using
    lowerRequestedSupportedEDSLContracts_selected_append_unknown_eq_error_of_prefix_parse_ok
      [rawOk]
      rawBad
      rest
      [contract]
      hNoDup
      hPrefixParse
      hParseBad

/-- Duplicate-free selected IDs fail closed with the unsupported-ID diagnostic
when any selected ID is unknown after an already-lowered prefix. -/
@[simp] theorem lowerRequestedSupportedEDSLContracts_selected_append_unknown_eq_error
    (rawPrefix : List String)
    (rawBad : String)
    (rawSuffix : List String)
    (loweredPrefixContracts : List Compiler.CompilationModel.CompilationModel)
    (hNoDup : findDuplicateRawContract? [] (rawPrefix ++ rawBad :: rawSuffix) = none)
    (hPrefixOk : rawPrefix.mapM lowerFromParsedSupportedContract = .ok loweredPrefixContracts)
    (hParseBad : parseSupportedEDSLContract? rawBad = none) :
    lowerRequestedSupportedEDSLContracts (rawPrefix ++ rawBad :: rawSuffix) =
      .error (unsupportedEDSLContractMessage rawBad) := by
  apply lowerRequestedSupportedEDSLContracts_selected_append_eq_error_of_lower_error
    rawPrefix rawBad rawSuffix loweredPrefixContracts
    (unsupportedEDSLContractMessage rawBad) hNoDup hPrefixOk
  simpa using lowerFromParsedSupportedContract_unknown_eq_error rawBad hParseBad

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
  exact lowerFromEDSLSubset_supported_preserves_interpretSpec contract initialStorage tx

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

/-!
## Generalized EDSL Lowering Boundary

Preservation theorems for the generalized `lowerFromModel` path, which accepts
any `CompilationModel` that does not require linked external libraries.
-/

/-- Models with empty externals always pass the generalized boundary. -/
theorem lowerFromModel_ok_of_empty_externals
    (model : Compiler.CompilationModel.CompilationModel)
    (h : model.externals = []) :
    lowerFromModel model = .ok model := by
  unfold lowerFromModel modelRequiresLinkedLibraries
  simp [h]

/-- When `lowerFromModel` succeeds, the lowered model is the input model. -/
theorem lowerFromModel_ok_eq
    (model : Compiler.CompilationModel.CompilationModel)
    (lowered : Compiler.CompilationModel.CompilationModel)
    (h : lowerFromModel model = .ok lowered) :
    lowered = model := by
  unfold lowerFromModel at h
  unfold modelRequiresLinkedLibraries at h
  split at h <;> simp_all

/-- Semantic preservation for the generalized lowering boundary: when
`lowerFromModel` succeeds, `interpretSpec` semantics are preserved. -/
theorem lowerFromModel_preserves_interpretSpec
    (model : Compiler.CompilationModel.CompilationModel)
    (lowered : Compiler.CompilationModel.CompilationModel)
    (h : lowerFromModel model = .ok lowered)
    (initialStorage : SpecStorage)
    (tx : Compiler.DiffTestTypes.Transaction) :
    interpretSpec lowered initialStorage tx =
      interpretSpec model initialStorage tx := by
  rw [lowerFromModel_ok_eq model lowered h]

/-- Models with non-empty externals are rejected at the generalized boundary. -/
theorem lowerFromModel_error_of_nonempty_externals
    (model : Compiler.CompilationModel.CompilationModel)
    (ext : Compiler.CompilationModel.ExternalFunction)
    (rest : List Compiler.CompilationModel.ExternalFunction)
    (h : model.externals = ext :: rest) :
    lowerFromModel model = .error (.requiresLinkedLibraries model.name) := by
  unfold lowerFromModel modelRequiresLinkedLibraries
  simp [h]

/-- `lowerModels` succeeds when every model has empty externals. -/
theorem lowerModels_ok_of_all_empty_externals
    (models : List Compiler.CompilationModel.CompilationModel)
    (h : ∀ m ∈ models, m.externals = []) :
    lowerModels models = .ok models := by
  induction models with
  | nil => rfl
  | cons hd tl ih =>
    have h_hd : hd.externals = [] := by
      apply h; simp
    have h_tl : ∀ m ∈ tl, m.externals = [] := by
      intro m hm; apply h; simp [hm]
    have ih' : tl.mapM lowerFromModel = .ok tl := ih h_tl
    show (hd :: tl).mapM lowerFromModel = .ok (hd :: tl)
    rw [List.mapM_cons, lowerFromModel_ok_of_empty_externals hd h_hd, ih']
    rfl

/-- The generalized boundary subsumes the curated subset: every curated
contract's pinned spec passes `lowerFromModel` validation. -/
theorem lowerFromModel_ok_of_supported
    (contract : SupportedEDSLContract) :
    lowerFromModel (lowerSupportedEDSLContract contract) =
      .ok (lowerSupportedEDSLContract contract) := by
  cases contract <;> rfl

/-- The generalized boundary preserves `interpretSpec` semantics for every
curated contract, matching the existing per-contract bridge theorems. -/
theorem lowerFromModel_supported_preserves_interpretSpec
    (contract : SupportedEDSLContract)
    (initialStorage : SpecStorage)
    (tx : Compiler.DiffTestTypes.Transaction) :
    interpretSpec
      (match lowerFromModel (lowerSupportedEDSLContract contract) with
      | .ok lowered => lowered
      | .error _ => lowerSupportedEDSLContract contract)
      initialStorage tx =
    interpretSpec (lowerSupportedEDSLContract contract) initialStorage tx := by
  rw [lowerFromModel_ok_of_supported]

end Compiler.Proofs.Lowering
