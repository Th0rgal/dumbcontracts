import Compiler.Specs

namespace Compiler.CompilationModelFeatureTest

open Compiler
open Compiler.CompilationModel

private def expectTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"✗ {label}")
  IO.println s!"✓ {label}"

private def contains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | c :: cs =>
        if (c :: cs).take n.length == n then true
        else go cs
    go h

private def selectorCount (spec : CompilationModel) : Nat :=
  (spec.functions.filter (fun fn => !fn.isInternal && fn.name != "fallback" && fn.name != "receive")).length

private def selectorsFor (spec : CompilationModel) : List Nat :=
  List.range (selectorCount spec)

#eval! do
  let specs := Compiler.Specs.allSpecs
  let allCompiled :=
    specs.all (fun spec =>
      match Compiler.CompilationModel.compile spec (selectorsFor spec) with
      | .ok _ => true
      | .error _ => false)
  expectTrue "all shipped CompilationModel specs compile with deterministic selectors" allCompiled

  -- Regression: selector mismatch must fail closed.
  let mismatchRejected :=
    match Compiler.CompilationModel.compile Compiler.Specs.counterSpec [] with
    | .ok _ => false
    | .error msg => contains msg "Selector count mismatch"
  expectTrue "selector mismatch is rejected with deterministic diagnostic" mismatchRejected

end Compiler.CompilationModelFeatureTest
