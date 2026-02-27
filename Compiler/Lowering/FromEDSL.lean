import Compiler.CompilationModel

namespace Compiler.Lowering

open Compiler.CompilationModel

/-- Explicit core input artifact for the compiler lowering boundary.
Today this wraps `CompilationModel`; future work will populate it from a
compilable EDSL subset with verified reification. -/
structure ContractCore where
  model : CompilationModel
  deriving Repr

/-- Transitional representation of compilable EDSL input.
`manualBridge` keeps the current path explicit while the real reifier lands. -/
inductive EDSLSubsetInput where
  | manualBridge (core : ContractCore)
  | unsupported (details : String)
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

/-- Lower a compilable EDSL-subset input to `CompilationModel`.
This currently supports the explicit manual-bridge case and fails closed
for unimplemented automatic reification cases. -/
def lowerFromEDSLSubset (input : EDSLSubsetInput) : Except LoweringError CompilationModel :=
  match input with
  | .manualBridge core => .ok (lowerContractCore core)
  | .unsupported details => .error (.unsupported details)

/-- Current manual compilation path routed through the lowering boundary. -/
def lowerModelPath (model : CompilationModel) : Except LoweringError CompilationModel :=
  lowerFromEDSLSubset (.manualBridge (liftModel model))

def edslInputReservedMessage : String :=
  LoweringError.message (.unsupported "(pending verified EDSL subset reification/lowering)")

end Compiler.Lowering
