import Compiler.CompileDriver

namespace Compiler.CompileDriverTest

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

private def expectFailureContains (label : String) (action : IO Unit) (needle : String) : IO Unit := do
  try
    action
    throw (IO.userError s!"✗ {label}: expected failure, command succeeded")
  catch e =>
    let msg := e.toString
    if !contains msg needle then
      throw (IO.userError s!"✗ {label}: expected '{needle}', got:\n{msg}")
    IO.println s!"✓ {label}"

private def fileExists (path : String) : IO Bool := do
  try
    let _ ← IO.FS.readFile path
    pure true
  catch _ =>
    pure false

#eval! do
  let outDir := "/tmp/verity-compile-driver-test-out"
  let abiDir := "/tmp/verity-compile-driver-test-abi"
  let missingLib := "/tmp/definitely-missing-library.yul"
  let failingAbi := s!"{abiDir}/CryptoHash.abi.json"
  let successfulAbi := s!"{abiDir}/SimpleStorage.abi.json"

  IO.FS.createDirAll outDir
  IO.FS.createDirAll abiDir

  -- Remove stale ABI outputs from previous runs so this check is deterministic.
  try IO.FS.removeFile failingAbi catch _ => pure ()
  try IO.FS.removeFile successfulAbi catch _ => pure ()

  expectFailureContains
    "compileAllWithOptions reports missing linked library"
    (compileAllWithOptions outDir false [missingLib] {} none (some abiDir))
    missingLib

  let hasFailingAbi ← fileExists failingAbi
  if hasFailingAbi then
    throw (IO.userError s!"✗ expected no ABI artifact for failing contract, found: {failingAbi}")
  IO.println "✓ no ABI artifact emitted for failing contract"

  let hasSuccessfulAbi ← fileExists successfulAbi
  if !hasSuccessfulAbi then
    throw (IO.userError s!"✗ expected ABI artifact for successful contract, missing: {successfulAbi}")
  IO.println "✓ ABI artifacts still emitted for contracts compiled before failure"

end Compiler.CompileDriverTest
