import Compiler.CompilationModel
import Compiler.Specs

namespace Compiler.Lowering

open Compiler.CompilationModel

/-- Explicit core input artifact for the compiler lowering boundary.
Today this wraps `CompilationModel`; future work can populate it from
an elaborated contract AST. -/
structure ContractCore where
  model : CompilationModel
  deriving Repr

/-- Deterministic diagnostics for unsupported EDSL-input lowering. -/
inductive LoweringError where
  | unsupported (details : String)
  deriving Repr

def LoweringError.message : LoweringError → String
  | .unsupported details =>
      "Unsupported EDSL lowering input. " ++
      "Use the generalized EDSL/macro path for compiler input. " ++
      details

/-- Transition helper: embeds today's manual compiler input into the
lowering boundary. -/
def liftModel (model : CompilationModel) : ContractCore :=
  { model := model }

/-- Lower core compiler input to `CompilationModel`.
For the current stage this is structurally the wrapped model. -/
def lowerContractCore (core : ContractCore) : CompilationModel :=
  core.model

def findDuplicateRawContract? (seen : List String) (remaining : List String) : Option String :=
  match remaining with
  | [] => none
  | raw :: rest =>
      if raw ∈ seen then
        some raw
      else
        findDuplicateRawContract? (raw :: seen) rest

/-- Current manual compilation path routed through the lowering boundary. -/
def lowerModelPath (model : CompilationModel) : Except LoweringError CompilationModel :=
  .ok (lowerContractCore (liftModel model))

def edslInputReservedMessage : String :=
  LoweringError.message (.unsupported "(pending extended verified EDSL elaboration/lowering)")

def edslInputLinkedLibrariesUnsupportedMessage : String :=
  "Linked external Yul libraries are not yet supported through --input edsl. " ++
  "External-library specs cannot be compiled through the edsl-only CLI path."

/-! ## Generalized selected-contract lowering (authoritative path)

This path derives selectable `--edsl-contract` IDs directly from `Specs.allSpecs`
and lowers those models through the lowering boundary, without enum pinning.
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

/-- Ordered list of all EDSL-compilable contracts. -/
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
  match findDuplicateRawContract? [] rawContracts with
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

end Compiler.Lowering
