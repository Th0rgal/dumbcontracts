import Std
import Compiler.ContractSpec
import Compiler.Hex

namespace Compiler.Selector

open Compiler.ContractSpec
open Compiler.Hex

private def functionSignature (fn : FunctionSpec) : String :=
  let params := fn.params.map (fun p => paramTypeToSolidityString p.ty)
  let paramStr := String.intercalate "," params
  s!"{fn.name}({paramStr})"

private def externalFunctions (spec : ContractSpec) : List FunctionSpec :=
  spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)

private def parseSelectorLine (line : String) : Option Nat :=
  let trimmed := line.trim
  parseHexNat? trimmed

def runKeccak (sigs : List String) : IO (List Nat) := do
  if sigs.isEmpty then
    return []
  let args := #["scripts/keccak256.py"] ++ sigs.toArray
  let result ← IO.Process.output { cmd := "python3", args := args }
  if result.exitCode != 0 then
    throw (IO.userError s!"keccak256.py failed: {result.stderr}")
  let lines := result.stdout.trim.splitOn "\n"
  if lines.length != sigs.length then
    throw (IO.userError s!"keccak256.py returned {lines.length} lines for {sigs.length} signatures: {result.stdout}")
  let selectors := lines.filterMap parseSelectorLine
  if selectors.length != sigs.length then
    throw (IO.userError s!"Failed to parse selector output: {result.stdout}")
  return selectors

/-- Compute Solidity-compatible selectors for external functions in a spec.
    Internal functions and special entrypoints (fallback/receive) are excluded
    since they are not dispatched via selector. Uses `isInteropEntrypointName`
    so this filter stays in sync with `ContractSpec.compile`. -/
def computeSelectors (spec : ContractSpec) : IO (List Nat) := do
  let externalFns := externalFunctions spec
  let sigs := externalFns.map functionSignature
  runKeccak sigs

/-- Validate that caller-provided selectors exactly match canonical Solidity
    selectors for each external function in declaration order. -/
def validateSelectors (spec : ContractSpec) (selectors : List Nat) : IO (Except String Unit) := do
  let externalFns := externalFunctions spec
  let expected ← computeSelectors spec
  if selectors.length != expected.length then
    return .error s!"Selector count mismatch for {spec.name}: {selectors.length} selectors for {expected.length} external functions"
  match ((externalFns.zip selectors).zip expected).find? (fun ((_, provided), canonical) => provided != canonical) with
  | some ((fn, provided), canonical) =>
      return .error s!"Selector mismatch in {spec.name} for function '{fn.name}': expected {natToHex canonical}, got {natToHex provided}"
  | none =>
      return .ok ()

/-- Checked compilation boundary for caller-supplied selector lists.
    Validates selectors against canonical Solidity signatures before invoking
    the core pure compiler. -/
def compileChecked (spec : ContractSpec) (selectors : List Nat) : IO (Except String IRContract) := do
  match ← validateSelectors spec selectors with
  | .error err => return .error err
  | .ok () => return Compiler.ContractSpec.compile spec selectors

end Compiler.Selector
