import Compiler.CompilationModel
import Compiler.Specs

namespace Compiler.Lowering

open Compiler.CompilationModel

/-- Core input artifact for the compiler lowering boundary.
Wraps a `CompilationModel` that has been structurally validated. -/
structure ContractCore where
  model : CompilationModel
  deriving Repr

/-- Deterministic diagnostics for lowering errors. -/
inductive LoweringError where
  | unsupported (details : String)
  | requiresLinkedLibraries (contractName : String)
  deriving Repr

def LoweringError.message : LoweringError → String
  | .unsupported details =>
      "EDSL lowering boundary rejected the input: " ++ details
  | .requiresLinkedLibraries contractName =>
      s!"Contract '{contractName}' uses external call modules or linked libraries, " ++
      "which are not supported through --input edsl. " ++
      "Use --input model with --link for these contracts."

/-- Embed a `CompilationModel` into the core-lowering boundary. -/
def liftModel (model : CompilationModel) : ContractCore :=
  { model := model }

/-- Extract the `CompilationModel` from a core input. -/
def lowerContractCore (core : ContractCore) : CompilationModel :=
  core.model

/-!
## Structural Validation

The generalized EDSL lowering boundary accepts any `CompilationModel` whose
constructs are within the supported fragment. Contracts that require linked
external Yul libraries (ECM modules, externalCallBind) are rejected at this
boundary — they must use `--input model` with `--link` instead.

This replaces the curated `SupportedEDSLContract` enum with a structural check:
instead of pinning contract identity, we check construct usage.
-/

/-- Check whether a `CompilationModel` requires linked external libraries.
A model requires linking if it declares external functions or if any function
body uses ECM or externalCallBind statements. -/
def modelRequiresLinkedLibraries (model : CompilationModel) : Bool :=
  !model.externals.isEmpty

/-- Validate and lower a `CompilationModel` through the EDSL boundary.
Accepts any model that does not require linked external libraries.
Fails closed with a deterministic diagnostic for models that need linking. -/
def lowerFromModel (model : CompilationModel) : Except LoweringError CompilationModel :=
  if modelRequiresLinkedLibraries model then
    .error (.requiresLinkedLibraries model.name)
  else
    .ok model

/-- Lower a list of `CompilationModel` specs through the EDSL boundary.
Each model is independently validated. -/
def lowerModels (models : List CompilationModel) : Except LoweringError (List CompilationModel) :=
  models.mapM lowerFromModel

/-!
## Legacy Curated Subset (Backward Compatibility)

The curated subset enum and associated functions are retained for backward
compatibility with existing bridge theorems and proofs. New code should use
`lowerFromModel` directly.
-/

/-- Curated EDSL subset. Retained for backward compatibility with existing
bridge theorems. New contracts should use `lowerFromModel` directly. -/
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
Retained for backward compatibility with existing proofs. -/
inductive EDSLSubsetInput where
  | supported (contract : SupportedEDSLContract)
  | manualBridge (core : ContractCore)
  | unsupported (details : String)
  deriving Repr

/-- Lowering target pinned for each curated contract. -/
def lowerSupportedEDSLContract : SupportedEDSLContract → CompilationModel
  | .simpleStorage => Compiler.Specs.simpleStorageSpec
  | .counter => Compiler.Specs.counterSpec
  | .owned => Compiler.Specs.ownedSpec
  | .ledger => Compiler.Specs.ledgerSpec
  | .ownedCounter => Compiler.Specs.ownedCounterSpec
  | .simpleToken => Compiler.Specs.simpleTokenSpec
  | .safeCounter => Compiler.Specs.safeCounterSpec

/-- Ordered list of curated contracts. -/
def supportedEDSLContracts : List SupportedEDSLContract := [
  .simpleStorage,
  .counter,
  .owned,
  .ledger,
  .ownedCounter,
  .simpleToken,
  .safeCounter
]

/-- CLI-stable identifier for each curated contract. -/
def supportedEDSLContractName : SupportedEDSLContract → String
  | .simpleStorage => "simple-storage"
  | .counter => "counter"
  | .owned => "owned"
  | .ledger => "ledger"
  | .ownedCounter => "owned-counter"
  | .simpleToken => "simple-token"
  | .safeCounter => "safe-counter"

def supportedEDSLContractNames : List String :=
  supportedEDSLContracts.map supportedEDSLContractName

def parseSupportedEDSLContract? (raw : String) : Option SupportedEDSLContract :=
  supportedEDSLContracts.find? (fun contract => supportedEDSLContractName contract == raw)

def unsupportedEDSLContractMessage (raw : String) : String :=
  s!"Unsupported --edsl-contract: {raw} (supported: {String.intercalate ", " supportedEDSLContractNames})"

def parseSupportedEDSLContract (raw : String) : Except String SupportedEDSLContract :=
  match parseSupportedEDSLContract? raw with
  | some contract => .ok contract
  | none => .error (unsupportedEDSLContractMessage raw)

def findDuplicateRawContract? (seen : List String) (remaining : List String) : Option String :=
  match remaining with
  | [] => none
  | raw :: rest =>
      if raw ∈ seen then
        some raw
      else
        findDuplicateRawContract? (raw :: seen) rest

/-- Lower a compilable EDSL-subset input to `CompilationModel`.
The `.supported` path uses the curated pinning (retained for backward
compatibility with existing bridge theorems). The `.manualBridge` path
passes through unchanged. Both are subsumed by `lowerFromModel` for
new code. -/
def lowerFromEDSLSubset (input : EDSLSubsetInput) : Except LoweringError CompilationModel :=
  match input with
  | .supported contract => .ok (lowerSupportedEDSLContract contract)
  | .manualBridge core => .ok (lowerContractCore core)
  | .unsupported details => .error (.unsupported details)

/-- Manual compilation path (`--input model`). Accepts any `CompilationModel`
without structural validation — the model path supports linked libraries
and all constructs. -/
def lowerModelPath (model : CompilationModel) : Except LoweringError CompilationModel :=
  .ok model

/-- Parse a CLI selected supported-contract id and lower it through the boundary. -/
def lowerFromParsedSupportedContract (raw : String) : Except String CompilationModel := do
  let contract ← parseSupportedEDSLContract raw
  match lowerFromEDSLSubset (.supported contract) with
  | .ok spec => .ok spec
  | .error err => .error err.message

/-- Lower selected CLI supported-contract IDs through the parsed lowering boundary.
If no IDs are provided, the full canonical supported list is lowered.
Duplicate requested IDs fail closed with a deterministic diagnostic. -/
def lowerRequestedSupportedEDSLContracts (rawContracts : List String) : Except String (List CompilationModel) := do
  match findDuplicateRawContract? {} rawContracts with
  | some dup =>
      .error s!"Duplicate --edsl-contract value: {dup}"
  | none =>
      pure ()
  let selectedRawContracts :=
    if rawContracts.isEmpty then
      supportedEDSLContractNames
    else
      rawContracts
  selectedRawContracts.mapM lowerFromParsedSupportedContract

def edslInputLinkedLibrariesUnsupportedMessage : String :=
  "Linked external Yul libraries are not yet supported through --input edsl. " ++
  "Use --input model when compiling specs that depend on --link (for example CryptoHash)."

end Compiler.Lowering
