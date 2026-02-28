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
      "EDSL input mode is active only for the curated supported subset. " ++
      "For unsupported contracts, use --input model (manual CompilationModel path) " ++
      "or select a supported EDSL contract with --edsl-contract. " ++
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

/-- CLI-stable identifier for each currently supported EDSL contract. -/
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

def edslInputReservedMessage : String :=
  LoweringError.message (.unsupported "(pending verified EDSL subset reification/lowering)")

def edslInputLinkedLibrariesUnsupportedMessage : String :=
  "Linked external Yul libraries are not yet supported through --input edsl. " ++
  "Use --input model when compiling specs that depend on --link (for example CryptoHash)."

/-! ## Generalized selected-contract lowering (authoritative path)

This path derives selectable `--edsl-contract` IDs directly from `Specs.allSpecs`
and lowers those models through the existing lowering boundary, without enum pinning.
-/

abbrev EDSLContract := CompilationModel

private def isAlphaNum (c : Char) : Bool :=
  c.isAlpha || c.isDigit

private def kebabFromSpecName (name : String) : String :=
  let rec go (remaining : List Char) (prev : Option Char) (out : String) : String :=
    match remaining with
    | [] => out
    | c :: rest =>
        if isAlphaNum c then
          let needsDash :=
            match prev with
            | some p => c.isUpper && (p.isLower || p.isDigit)
            | none => false
          let out := if needsDash then out.push '-' else out
          go rest (some c) (out.push (Char.toLower c))
        else
          go rest prev (out.push '-')
  go name.data none ""

/-- CLI identifier for a lowered EDSL contract, derived from model name. -/
def edslContractId (contract : EDSLContract) : String :=
  kebabFromSpecName contract.name

/-- Ordered list of all EDSL-compileable contracts. -/
def edslContracts : List EDSLContract :=
  Compiler.Specs.allSpecs

/-- Ordered CLI-stable IDs derived from `edslContracts`. -/
def edslContractIds : List String :=
  edslContracts.map edslContractId

def parseEDSLContract? (raw : String) : Option EDSLContract :=
  edslContracts.find? (fun contract => edslContractId contract == raw)

def unsupportedEDSLContractIdMessage (raw : String) : String :=
  s!"Unsupported --edsl-contract: {raw} (supported: {String.intercalate ", " edslContractIds})"

def parseEDSLContract (raw : String) : Except String EDSLContract :=
  match parseEDSLContract? raw with
  | some contract => .ok contract
  | none => .error (unsupportedEDSLContractIdMessage raw)

/-- Lower selected CLI EDSL-contract IDs through the generalized parsing boundary.
If no IDs are provided, the full canonical EDSL list is lowered.
Duplicate requested IDs fail closed with a deterministic diagnostic. -/
def lowerRequestedEDSLContracts (rawContracts : List String) : Except String (List CompilationModel) := do
  match findDuplicateRawContract? {} rawContracts with
  | some dup =>
      .error s!"Duplicate --edsl-contract value: {dup}"
  | none =>
      pure ()
  let selectedRawContracts :=
    if rawContracts.isEmpty then
      edslContractIds
    else
      rawContracts
  selectedRawContracts.mapM (fun raw => do
    let contract ← parseEDSLContract raw
    match lowerModelPath contract with
    | .ok lowered => .ok lowered
    | .error err => .error err.message)

/- Back-compat aliases retained temporarily while proofs/tests are migrated. -/
abbrev supportedEDSLContractIds : List String := edslContractIds

end Compiler.Lowering
