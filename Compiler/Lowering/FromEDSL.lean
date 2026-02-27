import Compiler.CompilationModel
import Compiler.Specs

namespace Compiler.Lowering

open Compiler.CompilationModel

/-- Explicit core input artifact for the compiler lowering boundary.
Today this wraps `CompilationModel`; future work will populate it from a
compilable EDSL subset with verified reification. -/
structure ContractCore where
  model : CompilationModel
  deriving Repr

/-- Curated EDSL subset currently accepted by the compiler input path.
Each constructor names an EDSL contract whose lowering target is pinned. -/
inductive SupportedEDSLContract where
  | simpleStorage
  | counter
  | owned
  | ledger
  | ownedCounter
  | simpleToken
  | safeCounter
  deriving Repr, DecidableEq

/-- Transitional representation of compilable EDSL input.
`manualBridge` keeps the current path explicit while the real reifier lands. -/
inductive EDSLSubsetInput where
  | supported (contract : SupportedEDSLContract)
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

/-- Lowering target pinned for each currently supported EDSL contract. -/
def lowerSupportedEDSLContract : SupportedEDSLContract → CompilationModel
  | .simpleStorage => Compiler.Specs.simpleStorageSpec
  | .counter => Compiler.Specs.counterSpec
  | .owned => Compiler.Specs.ownedSpec
  | .ledger => Compiler.Specs.ledgerSpec
  | .ownedCounter => Compiler.Specs.ownedCounterSpec
  | .simpleToken => Compiler.Specs.simpleTokenSpec
  | .safeCounter => Compiler.Specs.safeCounterSpec

/-- Ordered list used by the CLI when compiling `--input edsl`. -/
def supportedEDSLContracts : List SupportedEDSLContract := [
  .simpleStorage,
  .counter,
  .owned,
  .ledger,
  .ownedCounter,
  .simpleToken,
  .safeCounter
]

/-- Lower a compilable EDSL-subset input to `CompilationModel`.
This currently supports the explicit manual-bridge case and fails closed
for unimplemented automatic reification cases. -/
def lowerFromEDSLSubset (input : EDSLSubsetInput) : Except LoweringError CompilationModel :=
  match input with
  | .supported contract => .ok (lowerSupportedEDSLContract contract)
  | .manualBridge core => .ok (lowerContractCore core)
  | .unsupported details => .error (.unsupported details)

/-- Current manual compilation path routed through the lowering boundary. -/
def lowerModelPath (model : CompilationModel) : Except LoweringError CompilationModel :=
  lowerFromEDSLSubset (.manualBridge (liftModel model))

def edslInputReservedMessage : String :=
  LoweringError.message (.unsupported "(pending verified EDSL subset reification/lowering)")

def edslInputLinkedLibrariesUnsupportedMessage : String :=
  "Linked external Yul libraries are not yet supported through --input edsl. " ++
  "Use --input model when compiling specs that depend on --link (for example CryptoHash)."

end Compiler.Lowering
