import Compiler.Constants
import Compiler.IR
import Compiler.Yul.PrettyPrint
import Compiler.Yul.PatchFramework
import Compiler.Yul.PatchRules

namespace Compiler

open Yul
open Compiler.Constants (selectorShift)

inductive BackendProfile where
  | semantic
  | solidityParityOrdering
  | solidityParity
  deriving Repr, DecidableEq

instance : Inhabited BackendProfile where
  default := .semantic

structure YulEmitOptions where
  backendProfile : BackendProfile := .semantic
  patchConfig : Yul.PatchPassConfig := { enabled := false }
  /-- Scratch memory base used by compiler-generated mapping-slot helpers.
      Default `0` preserves historical behavior (`mstore(0, key); mstore(32, baseSlot)`). -/
  mappingSlotScratchBase : Nat := 0

/-- Runtime emission output plus patch audit report for tool/CI consumption. -/
structure RuntimeEmitReport where
  runtimeCode : List YulStmt
  patchReport : Yul.PatchPassReport

private def yulDatacopy : YulStmt :=
  YulStmt.expr (YulExpr.call "datacopy" [
    YulExpr.lit 0,
    YulExpr.call "dataoffset" [YulExpr.str "runtime"],
    YulExpr.call "datasize" [YulExpr.str "runtime"]
  ])

private def yulReturnRuntime : YulStmt :=
  YulStmt.expr (YulExpr.call "return" [
    YulExpr.lit 0,
    YulExpr.call "datasize" [YulExpr.str "runtime"]
  ])

def mappingSlotFuncAt (scratchBase : Nat) : YulStmt :=
  let keyPtr := scratchBase
  let slotPtr := scratchBase + 32
  YulStmt.funcDef "mappingSlot" ["baseSlot", "key"] ["slot"] [
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit keyPtr, YulExpr.ident "key"]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit slotPtr, YulExpr.ident "baseSlot"]),
    YulStmt.assign "slot" (YulExpr.call "keccak256" [YulExpr.lit keyPtr, YulExpr.lit 64])
  ]

def mappingSlotFunc : YulStmt :=
  mappingSlotFuncAt 0

/-- Revert if ETH is sent to a non-payable function. -/
def callvalueGuard : YulStmt :=
  YulStmt.if_ (YulExpr.call "callvalue" [])
    [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]

/-- Revert if calldata is shorter than expected (4-byte selector + 32 bytes per param). -/
def calldatasizeGuard (numParams : Nat) : YulStmt :=
  YulStmt.if_ (YulExpr.call "lt" [
    YulExpr.call "calldatasize" [],
    YulExpr.lit (4 + numParams * 32)])
    [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]

private def dispatchBody (payable : Bool) (label : String) (body : List YulStmt) : List YulStmt :=
  let valueGuard := if payable then [] else [callvalueGuard]
  [YulStmt.comment label] ++ valueGuard ++ body

private def defaultDispatchCase
    (fallback : Option IREntrypoint)
    (receive : Option IREntrypoint) : List YulStmt :=
  match receive, fallback with
  | none, none =>
      [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
  | none, some fb =>
      dispatchBody fb.payable "fallback()" fb.body
  | some rc, none =>
      [YulStmt.block [
        YulStmt.let_ "__is_empty_calldata" (YulExpr.call "eq" [YulExpr.call "calldatasize" [], YulExpr.lit 0]),
        YulStmt.if_ (YulExpr.ident "__is_empty_calldata")
          (dispatchBody rc.payable "receive()" rc.body),
        YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__is_empty_calldata"])
          [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
      ]]
  | some rc, some fb =>
      [YulStmt.block [
        YulStmt.let_ "__is_empty_calldata" (YulExpr.call "eq" [YulExpr.call "calldatasize" [], YulExpr.lit 0]),
        YulStmt.if_ (YulExpr.ident "__is_empty_calldata")
          (dispatchBody rc.payable "receive()" rc.body),
        YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__is_empty_calldata"])
          (dispatchBody fb.payable "fallback()" fb.body)
      ]]

private def insertBy [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) (x : α) : List α → List α
  | [] => [x]
  | head :: tail =>
      if key x < key head then x :: head :: tail
      else head :: insertBy key x tail

private def insertionSortBy [LT β] [DecidableRel (α := β) (· < ·)] (key : α → β) (xs : List α) : List α :=
  xs.foldl (fun acc x => insertBy key x acc) []

def buildSwitch
    (funcs : List IRFunction)
    (fallback : Option IREntrypoint := none)
    (receive : Option IREntrypoint := none)
    (sortCasesBySelector : Bool := false) : YulStmt :=
  let funcs :=
    if sortCasesBySelector then
      insertionSortBy (·.selector) funcs
    else
      funcs
  let selectorExpr := YulExpr.call "shr" [YulExpr.lit selectorShift, YulExpr.call "calldataload" [YulExpr.lit 0]]
  let cases := funcs.map (fun fn =>
    let body := dispatchBody fn.payable s!"{fn.name}()" ([calldatasizeGuard fn.params.length] ++ fn.body)
    (fn.selector, body)
  )
  let defaultCase := defaultDispatchCase fallback receive
  YulStmt.block [
    YulStmt.let_ "__has_selector"
      (YulExpr.call "iszero" [YulExpr.call "lt" [YulExpr.call "calldatasize" [], YulExpr.lit 4]]),
    YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]) defaultCase,
    YulStmt.if_ (YulExpr.ident "__has_selector")
      [YulStmt.switch selectorExpr cases (some defaultCase)]
  ]

def runtimeCode (contract : IRContract) : List YulStmt :=
  let mapping := if contract.usesMapping then [mappingSlotFuncAt 0] else []
  let internals := contract.internalFunctions
  mapping ++ internals ++ [buildSwitch contract.functions contract.fallbackEntrypoint contract.receiveEntrypoint]

private def profileSortsOutput (profile : BackendProfile) : Bool :=
  match profile with
  | .semantic => false
  | .solidityParityOrdering => true
  | .solidityParity => true

private def profileSortsDispatchCases (profile : BackendProfile) : Bool :=
  profileSortsOutput profile

private def profileSortsInternalHelpers (profile : BackendProfile) : Bool :=
  profileSortsOutput profile

private def internalHelperName? (stmt : YulStmt) : Option String :=
  match stmt with
  | .funcDef name _ _ _ => some name
  | _ => none

private def sortInternalHelpersByName (helpers : List YulStmt) : List YulStmt :=
  let named := helpers.filterMap (fun stmt =>
    match internalHelperName? stmt with
    | some name => some (name, stmt)
    | none => none)
  if named.length == helpers.length then
    (insertionSortBy Prod.fst named).map Prod.snd
  else
    helpers

private def internalHelpersForProfile (profile : BackendProfile) (helpers : List YulStmt) : List YulStmt :=
  if profileSortsInternalHelpers profile then
    sortInternalHelpersByName helpers
  else
    helpers

def runtimeCodeWithEmitOptions (contract : IRContract) (options : YulEmitOptions) : List YulStmt :=
  let mapping := if contract.usesMapping then [mappingSlotFuncAt options.mappingSlotScratchBase] else []
  let internals := internalHelpersForProfile options.backendProfile contract.internalFunctions
  let sortCases := profileSortsDispatchCases options.backendProfile
  mapping ++ internals ++ [buildSwitch contract.functions contract.fallbackEntrypoint contract.receiveEntrypoint sortCases]

/-- Emit runtime code and keep the patch pass report (manifest + iteration count). -/
def runtimeCodeWithOptionsReport (contract : IRContract) (options : YulEmitOptions) : RuntimeEmitReport :=
  let base := runtimeCodeWithEmitOptions contract options
  let patchReport := Yul.runExprPatchPass options.patchConfig Yul.foundationExprPatchPack base
  { runtimeCode := patchReport.patched, patchReport := patchReport }

def runtimeCodeWithOptions (contract : IRContract) (options : YulEmitOptions) : List YulStmt :=
  (runtimeCodeWithOptionsReport contract options).runtimeCode

private def deployCodeWithProfile (contract : IRContract) (profile : BackendProfile) : List YulStmt :=
  let valueGuard := if contract.constructorPayable then [] else [callvalueGuard]
  let internals := internalHelpersForProfile profile contract.internalFunctions
  valueGuard ++ internals ++ contract.deploy ++ [yulDatacopy, yulReturnRuntime]

private def deployCode (contract : IRContract) : List YulStmt :=
  deployCodeWithProfile contract .semantic

def emitYul (contract : IRContract) : YulObject :=
  { name := contract.name
    deployCode := deployCode contract
    runtimeCode := runtimeCode contract }

def emitYulWithOptions (contract : IRContract) (options : YulEmitOptions) : YulObject :=
  { name := contract.name
    deployCode := deployCodeWithProfile contract options.backendProfile
    runtimeCode := runtimeCodeWithOptions contract options }

/-- Emit Yul and preserve patch-pass audit details for downstream reporting. -/
def emitYulWithOptionsReport (contract : IRContract) (options : YulEmitOptions) :
    YulObject × Yul.PatchPassReport :=
  let runtimeReport := runtimeCodeWithOptionsReport contract options
  ({ name := contract.name
     deployCode := deployCodeWithProfile contract options.backendProfile
     runtimeCode := runtimeReport.runtimeCode },
   runtimeReport.patchReport)

/-- Regression guard: report and legacy runtime APIs stay in sync. -/
example (contract : IRContract) (options : YulEmitOptions) :
    (runtimeCodeWithOptionsReport contract options).runtimeCode = runtimeCodeWithOptions contract options := by
  rfl

/-- Regression guard: report and legacy object APIs stay in sync. -/
example (contract : IRContract) (options : YulEmitOptions) :
    (emitYulWithOptionsReport contract options).1 = emitYulWithOptions contract options := by
  rfl

/-- Regression guard: object report API returns the exact patch report from runtime emission. -/
example (contract : IRContract) (options : YulEmitOptions) :
    (emitYulWithOptionsReport contract options).2 =
      (runtimeCodeWithOptionsReport contract options).patchReport := by
  rfl

end Compiler
