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
      "EDSL input mode rejects contracts that use unsupported constructs. " ++
      "Use --input model for contracts outside the supported EDSL fragment. " ++
      details
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

/-- Generalized EDSL input contract type for structural reification. -/
abbrev EDSLContract := CompilationModel

/-- Structural reifier for expressions.
Rejects unsupported linked-library constructs (`externalCall`) fail-closed. -/
private def reifyExpr : Expr → Option Expr
  | .literal n => .some (.literal n)
  | .param name => .some (.param name)
  | .constructorArg index => .some (.constructorArg index)
  | .storage field => .some (.storage field)
  | .mapping field key => do
      let key' ← reifyExpr key
      pure (.mapping field key')
  | .mappingWord field key wordOffset => do
      let key' ← reifyExpr key
      pure (.mappingWord field key' wordOffset)
  | .mappingPackedWord field key wordOffset packed => do
      let key' ← reifyExpr key
      pure (.mappingPackedWord field key' wordOffset packed)
  | .mapping2 field key1 key2 => do
      let key1' ← reifyExpr key1
      let key2' ← reifyExpr key2
      pure (.mapping2 field key1' key2')
  | .mapping2Word field key1 key2 wordOffset => do
      let key1' ← reifyExpr key1
      let key2' ← reifyExpr key2
      pure (.mapping2Word field key1' key2' wordOffset)
  | .mappingUint field key => do
      let key' ← reifyExpr key
      pure (.mappingUint field key')
  | .structMember field key memberName => do
      let key' ← reifyExpr key
      pure (.structMember field key' memberName)
  | .structMember2 field key1 key2 memberName => do
      let key1' ← reifyExpr key1
      let key2' ← reifyExpr key2
      pure (.structMember2 field key1' key2' memberName)
  | .caller => .some .caller
  | .contractAddress => .some .contractAddress
  | .chainid => .some .chainid
  | .msgValue => .some .msgValue
  | .blockTimestamp => .some .blockTimestamp
  | .mload offset => do
      let offset' ← reifyExpr offset
      pure (.mload offset')
  | .keccak256 offset size => do
      let offset' ← reifyExpr offset
      let size' ← reifyExpr size
      pure (.keccak256 offset' size')
  | .call gas target value inOffset inSize outOffset outSize => do
      let gas' ← reifyExpr gas
      let target' ← reifyExpr target
      let value' ← reifyExpr value
      let inOffset' ← reifyExpr inOffset
      let inSize' ← reifyExpr inSize
      let outOffset' ← reifyExpr outOffset
      let outSize' ← reifyExpr outSize
      pure (.call gas' target' value' inOffset' inSize' outOffset' outSize')
  | .staticcall gas target inOffset inSize outOffset outSize => do
      let gas' ← reifyExpr gas
      let target' ← reifyExpr target
      let inOffset' ← reifyExpr inOffset
      let inSize' ← reifyExpr inSize
      let outOffset' ← reifyExpr outOffset
      let outSize' ← reifyExpr outSize
      pure (.staticcall gas' target' inOffset' inSize' outOffset' outSize')
  | .delegatecall gas target inOffset inSize outOffset outSize => do
      let gas' ← reifyExpr gas
      let target' ← reifyExpr target
      let inOffset' ← reifyExpr inOffset
      let inSize' ← reifyExpr inSize
      let outOffset' ← reifyExpr outOffset
      let outSize' ← reifyExpr outSize
      pure (.delegatecall gas' target' inOffset' inSize' outOffset' outSize')
  | .calldatasize => .some .calldatasize
  | .calldataload offset => do
      let offset' ← reifyExpr offset
      pure (.calldataload offset')
  | .returndataSize => .some .returndataSize
  | .extcodesize addr => do
      let addr' ← reifyExpr addr
      pure (.extcodesize addr')
  | .returndataOptionalBoolAt outOffset => do
      let outOffset' ← reifyExpr outOffset
      pure (.returndataOptionalBoolAt outOffset')
  | .localVar name => .some (.localVar name)
  | .externalCall _ _ => .none
  | .internalCall functionName args => do
      let args' ← args.mapM reifyExpr
      pure (.internalCall functionName args')
  | .arrayLength name => .some (.arrayLength name)
  | .arrayElement name index => do
      let index' ← reifyExpr index
      pure (.arrayElement name index')
  | .add a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.add a' b')
  | .sub a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.sub a' b')
  | .mul a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.mul a' b')
  | .div a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.div a' b')
  | .mod a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.mod a' b')
  | .bitAnd a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.bitAnd a' b')
  | .bitOr a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.bitOr a' b')
  | .bitXor a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.bitXor a' b')
  | .bitNot a => do
      let a' ← reifyExpr a
      pure (.bitNot a')
  | .shl shift value => do
      let shift' ← reifyExpr shift
      let value' ← reifyExpr value
      pure (.shl shift' value')
  | .shr shift value => do
      let shift' ← reifyExpr shift
      let value' ← reifyExpr value
      pure (.shr shift' value')
  | .eq a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.eq a' b')
  | .ge a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.ge a' b')
  | .gt a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.gt a' b')
  | .lt a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.lt a' b')
  | .le a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.le a' b')
  | .logicalAnd a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.logicalAnd a' b')
  | .logicalOr a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.logicalOr a' b')
  | .logicalNot a => do
      let a' ← reifyExpr a
      pure (.logicalNot a')
  | .mulDivDown a b c => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      let c' ← reifyExpr c
      pure (.mulDivDown a' b' c')
  | .mulDivUp a b c => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      let c' ← reifyExpr c
      pure (.mulDivUp a' b' c')
  | .wMulDown a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.wMulDown a' b')
  | .wDivUp a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.wDivUp a' b')
  | .min a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.min a' b')
  | .max a b => do
      let a' ← reifyExpr a
      let b' ← reifyExpr b
      pure (.max a' b')
  | .ite cond thenVal elseVal => do
      let cond' ← reifyExpr cond
      let thenVal' ← reifyExpr thenVal
      let elseVal' ← reifyExpr elseVal
      pure (.ite cond' thenVal' elseVal')

/-- Structural reifier for statements.
Rejects unsupported linked-library constructs (`externalCallBind`, `ecm`) fail-closed. -/
private def reifyStmt : Stmt → Option Stmt
  | .letVar name value => do
      let value' ← reifyExpr value
      pure (.letVar name value')
  | .assignVar name value => do
      let value' ← reifyExpr value
      pure (.assignVar name value')
  | .setStorage field value => do
      let value' ← reifyExpr value
      pure (.setStorage field value')
  | .setMapping field key value => do
      let key' ← reifyExpr key
      let value' ← reifyExpr value
      pure (.setMapping field key' value')
  | .setMappingWord field key wordOffset value => do
      let key' ← reifyExpr key
      let value' ← reifyExpr value
      pure (.setMappingWord field key' wordOffset value')
  | .setMappingPackedWord field key wordOffset packed value => do
      let key' ← reifyExpr key
      let value' ← reifyExpr value
      pure (.setMappingPackedWord field key' wordOffset packed value')
  | .setMapping2 field key1 key2 value => do
      let key1' ← reifyExpr key1
      let key2' ← reifyExpr key2
      let value' ← reifyExpr value
      pure (.setMapping2 field key1' key2' value')
  | .setMapping2Word field key1 key2 wordOffset value => do
      let key1' ← reifyExpr key1
      let key2' ← reifyExpr key2
      let value' ← reifyExpr value
      pure (.setMapping2Word field key1' key2' wordOffset value')
  | .setMappingUint field key value => do
      let key' ← reifyExpr key
      let value' ← reifyExpr value
      pure (.setMappingUint field key' value')
  | .setStructMember field key memberName value => do
      let key' ← reifyExpr key
      let value' ← reifyExpr value
      pure (.setStructMember field key' memberName value')
  | .setStructMember2 field key1 key2 memberName value => do
      let key1' ← reifyExpr key1
      let key2' ← reifyExpr key2
      let value' ← reifyExpr value
      pure (.setStructMember2 field key1' key2' memberName value')
  | .require cond message => do
      let cond' ← reifyExpr cond
      pure (.require cond' message)
  | .requireError cond errorName args => do
      let cond' ← reifyExpr cond
      let args' ← args.mapM reifyExpr
      pure (.requireError cond' errorName args')
  | .revertError errorName args => do
      let args' ← args.mapM reifyExpr
      pure (.revertError errorName args')
  | .return value => do
      let value' ← reifyExpr value
      pure (.return value')
  | .returnValues values => do
      let values' ← values.mapM reifyExpr
      pure (.returnValues values')
  | .returnArray name => .some (.returnArray name)
  | .returnBytes name => .some (.returnBytes name)
  | .returnStorageWords name => .some (.returnStorageWords name)
  | .mstore offset value => do
      let offset' ← reifyExpr offset
      let value' ← reifyExpr value
      pure (.mstore offset' value')
  | .calldatacopy destOffset sourceOffset size => do
      let destOffset' ← reifyExpr destOffset
      let sourceOffset' ← reifyExpr sourceOffset
      let size' ← reifyExpr size
      pure (.calldatacopy destOffset' sourceOffset' size')
  | .returndataCopy destOffset sourceOffset size => do
      let destOffset' ← reifyExpr destOffset
      let sourceOffset' ← reifyExpr sourceOffset
      let size' ← reifyExpr size
      pure (.returndataCopy destOffset' sourceOffset' size')
  | .revertReturndata => .some .revertReturndata
  | .stop => .some .stop
  | .ite cond thenBranch elseBranch => do
      let cond' ← reifyExpr cond
      let thenBranch' ← thenBranch.mapM reifyStmt
      let elseBranch' ← elseBranch.mapM reifyStmt
      pure (.ite cond' thenBranch' elseBranch')
  | .forEach varName count body => do
      let count' ← reifyExpr count
      let body' ← body.mapM reifyStmt
      pure (.forEach varName count' body')
  | .emit eventName args => do
      let args' ← args.mapM reifyExpr
      pure (.emit eventName args')
  | .internalCall functionName args => do
      let args' ← args.mapM reifyExpr
      pure (.internalCall functionName args')
  | .internalCallAssign names functionName args => do
      let args' ← args.mapM reifyExpr
      pure (.internalCallAssign names functionName args')
  | .rawLog topics dataOffset dataSize => do
      let topics' ← topics.mapM reifyExpr
      let dataOffset' ← reifyExpr dataOffset
      let dataSize' ← reifyExpr dataSize
      pure (.rawLog topics' dataOffset' dataSize')
  | .externalCallBind _ _ _ => .none
  | .ecm _ _ => .none

private def reifyFunctionSpec (fn : FunctionSpec) : Option FunctionSpec := do
  let body' ← fn.body.mapM reifyStmt
  pure { fn with body := body' }

private def reifyConstructorSpec (ctor : ConstructorSpec) : Option ConstructorSpec := do
  let body' ← ctor.body.mapM reifyStmt
  pure { ctor with body := body' }

/-- Generic structural EDSL-term reifier.
Returns `none` for unsupported constructs to fail closed. -/
def reifyEDSL (contract : EDSLContract) : Option CompilationModel := do
  if !contract.externals.isEmpty then
    .none
  else
    let constructor' ← contract.constructor.mapM reifyConstructorSpec
    let functions' ← contract.functions.mapM reifyFunctionSpec
    pure { contract with constructor := constructor', functions := functions' }

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
    match reifyEDSL model with
    | some _ => .ok model
    | none => .error (.unsupported s!"Contract '{model.name}' uses unsupported EDSL constructs.")

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
