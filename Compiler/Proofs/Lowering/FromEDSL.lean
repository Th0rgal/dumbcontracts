import Compiler.Lowering.FromEDSL
import Compiler.Proofs.SpecCorrectness.Counter
import Compiler.Proofs.SpecCorrectness.SimpleStorage
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

@[simp] theorem lowerSupportedEDSLContract_simpleStorage_eq :
    lowerSupportedEDSLContract .simpleStorage = Compiler.Specs.simpleStorageSpec := rfl

@[simp] theorem lowerSupportedEDSLContract_counter_eq :
    lowerSupportedEDSLContract .counter = Compiler.Specs.counterSpec := rfl

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

/-- Supported-contract parser round-trips through the CLI-stable name map. -/
@[simp] theorem parseSupportedEDSLContract_roundtrip
    (contract : SupportedEDSLContract) :
    parseSupportedEDSLContract? (supportedEDSLContractName contract) = some contract := by
  cases contract <;> rfl

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
