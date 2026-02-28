import Compiler.Lowering.FromEDSL
import Verity.Proofs.Stdlib.SpecInterpreter

namespace Compiler.Proofs.Lowering

open Compiler.Lowering
open Verity.Proofs.Stdlib.SpecInterpreter

/-- Lowering the wrapped `ContractCore` is definitionally the underlying model. -/
@[simp] theorem lowerContractCore_eq_model (core : ContractCore) :
    lowerContractCore core = core.model := rfl

/-- Semantic preservation for the lowering boundary. -/
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

/-- Semantic preservation for the lifted manual-model path. -/
@[simp] theorem lowerLiftModel_preserves_interpretSpec
    (model : Compiler.CompilationModel.CompilationModel)
    (initialStorage : SpecStorage)
    (tx : Compiler.DiffTestTypes.Transaction) :
    interpretSpec (lowerContractCore (liftModel model)) initialStorage tx =
      interpretSpec model initialStorage tx := by
  rfl

@[simp] theorem lowerModelPath_eq_ok (model : Compiler.CompilationModel.CompilationModel) :
    lowerModelPath model = .ok model := by
  rfl

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

@[simp] theorem parseEDSLContract_eq_ok_of_some
    (raw : String)
    (contract : EDSLContract)
    (hParse : parseEDSLContract? raw = some contract) :
    parseEDSLContract raw = .ok contract := by
  unfold parseEDSLContract
  simp [hParse]

@[simp] theorem parseEDSLContract_eq_error_of_none
    (raw : String)
    (hParse : parseEDSLContract? raw = none) :
    parseEDSLContract raw = .error (unsupportedEDSLContractIdMessage raw) := by
  unfold parseEDSLContract
  simp [hParse]

@[simp] theorem lowerRequestedEDSLContracts_default_eq
    : lowerRequestedEDSLContracts [] =
      edslContractIds.mapM (fun raw => do
        let contract ← parseEDSLContract raw
        match lowerModelPath contract with
        | .ok lowered => .ok lowered
        | .error err => .error err.message) := by
  simp [lowerRequestedEDSLContracts, findDuplicateRawContract?]

end Compiler.Proofs.Lowering
