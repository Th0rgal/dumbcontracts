import Compiler.CompilationModel

namespace Compiler.Lowering

open Compiler.CompilationModel

/-- Explicit core input artifact for the compiler lowering boundary.
Today this wraps `CompilationModel`; future work will populate it from a
compilable EDSL subset with verified reification. -/
structure ContractCore where
  model : CompilationModel
  deriving Repr

/-- Deterministic diagnostics for unsupported EDSL-input lowering. -/
inductive LoweringError where
  | unsupported (details : String)
  deriving Repr

def LoweringError.message : LoweringError → String
  | .unsupported details =>
      "EDSL input mode is reserved for verified automatic lowering and is not wired in this CLI yet. " ++
      "Use --input model for now (manual CompilationModel path). " ++
      details

/-- Transition helper: embeds today's manual compiler input into the future
core-lowering boundary. -/
def liftModel (model : CompilationModel) : ContractCore :=
  { model := model }

/-- Lower core compiler input to `CompilationModel`.
For the current transition stage, this is structurally the wrapped model. -/
def lowerContractCore (core : ContractCore) : CompilationModel :=
  core.model

/-- Placeholder entry point for EDSL-subset reification/lowering.
It is intentionally fail-closed until verified lowering is wired. -/
def lowerFromEDSLSubset : Except LoweringError CompilationModel :=
  .error (.unsupported "(pending verified EDSL subset reification/lowering)")

def edslInputReservedMessage : String :=
  LoweringError.message (.unsupported "(pending verified EDSL subset reification/lowering)")

end Compiler.Lowering
