import Compiler.Lowering.FromEDSL
import Verity.Proofs.Stdlib.SpecInterpreter

namespace Compiler.Proofs.Lowering

open Compiler.Lowering
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
