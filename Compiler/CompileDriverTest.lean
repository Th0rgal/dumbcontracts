import Compiler.CompileDriver
import Compiler.Lowering.FromEDSL

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

private def expectFileEquals (label : String) (lhs rhs : String) : IO Unit := do
  let lhsText ← IO.FS.readFile lhs
  let rhsText ← IO.FS.readFile rhs
  if lhsText != rhsText then
    throw (IO.userError s!"✗ {label}: files differ\nlhs: {lhs}\nrhs: {rhs}")
  IO.println s!"✓ {label}"

private def expectSupportedSubsetParity
    (modelOutDir edslOutDir modelAbiDir edslAbiDir : String) : IO Unit := do
  for contract in Compiler.Lowering.supportedEDSLContracts do
    let spec := Compiler.Lowering.lowerSupportedEDSLContract contract
    expectFileEquals
      s!"supported subset Yul parity: {spec.name}"
      s!"{modelOutDir}/{spec.name}.yul"
      s!"{edslOutDir}/{spec.name}.yul"
    expectFileEquals
      s!"supported subset ABI parity: {spec.name}"
      s!"{modelAbiDir}/{spec.name}.abi.json"
      s!"{edslAbiDir}/{spec.name}.abi.json"

private def expectOnlySelectedArtifacts
    (label : String)
    (selected : List Compiler.Lowering.SupportedEDSLContract)
    (outDir abiDir : String) : IO Unit := do
  for contract in Compiler.Lowering.supportedEDSLContracts do
    let spec := Compiler.Lowering.lowerSupportedEDSLContract contract
    let shouldExist := selected.contains contract
    let yulExists ← fileExists s!"{outDir}/{spec.name}.yul"
    let abiExists ← fileExists s!"{abiDir}/{spec.name}.abi.json"
    if yulExists != shouldExist then
      throw (IO.userError
        s!"✗ {label}: unexpected Yul artifact presence for {spec.name} (expected={shouldExist}, found={yulExists})")
    if abiExists != shouldExist then
      throw (IO.userError
        s!"✗ {label}: unexpected ABI artifact presence for {spec.name} (expected={shouldExist}, found={abiExists})")
  IO.println s!"✓ {label}"

#eval! (do
  let nonce ← IO.rand 0 1000000000
  let outDir := s!"/tmp/verity-compile-driver-test-{nonce}-out"
  let abiDir := s!"/tmp/verity-compile-driver-test-{nonce}-abi"
  let modelOutDir := s!"/tmp/verity-compile-driver-test-{nonce}-model-out"
  let edslOutDir := s!"/tmp/verity-compile-driver-test-{nonce}-edsl-out"
  let modelAbiDir := s!"/tmp/verity-compile-driver-test-{nonce}-model-abi"
  let edslAbiDir := s!"/tmp/verity-compile-driver-test-{nonce}-edsl-abi"
  let selectedOutDir := s!"/tmp/verity-compile-driver-test-{nonce}-selected-out"
  let selectedAbiDir := s!"/tmp/verity-compile-driver-test-{nonce}-selected-abi"
  let missingLib := "/tmp/definitely-missing-library.yul"
  let failingAbi := s!"{abiDir}/CryptoHash.abi.json"
  let successfulAbi := s!"{abiDir}/SimpleStorage.abi.json"

  IO.FS.createDirAll outDir
  IO.FS.createDirAll abiDir
  IO.FS.createDirAll modelOutDir
  IO.FS.createDirAll edslOutDir
  IO.FS.createDirAll modelAbiDir
  IO.FS.createDirAll edslAbiDir
  IO.FS.createDirAll selectedOutDir
  IO.FS.createDirAll selectedAbiDir

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

  compileAllWithOptions modelOutDir false [] {} none (some modelAbiDir)
  compileAllFromEDSLWithOptions edslOutDir false [] ["simple-storage"] {} none (some edslAbiDir)
  expectFileEquals
    "edsl selected contract Yul matches model-path artifact"
    s!"{modelOutDir}/SimpleStorage.yul"
    s!"{edslOutDir}/SimpleStorage.yul"
  expectFileEquals
    "edsl selected contract ABI matches model-path artifact"
    s!"{modelAbiDir}/SimpleStorage.abi.json"
    s!"{edslAbiDir}/SimpleStorage.abi.json"

  compileAllFromEDSLWithOptions edslOutDir false [] [] {} none (some edslAbiDir)
  expectSupportedSubsetParity modelOutDir edslOutDir modelAbiDir edslAbiDir

  compileAllFromEDSLWithOptions
    selectedOutDir
    false
    []
    ["simple-storage", "counter"]
    {}
    none
    (some selectedAbiDir)
  expectOnlySelectedArtifacts
    "edsl multi-select emits only requested contract artifacts"
    [Compiler.Lowering.SupportedEDSLContract.simpleStorage, Compiler.Lowering.SupportedEDSLContract.counter]
    selectedOutDir
    selectedAbiDir

  expectFailureContains
    "duplicate selected EDSL contracts fail closed"
    (compileAllFromEDSLWithOptions edslOutDir false [] ["counter", "counter"] {} none (some edslAbiDir))
    "Duplicate --edsl-contract value: counter"
  : IO Unit)

end Compiler.CompileDriverTest
