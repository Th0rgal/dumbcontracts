import Compiler.Main
import Compiler.Linker
import Compiler.Lowering.FromEDSL
import Compiler.Specs

namespace Compiler.MainTest

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

private def expectErrorContains (label : String) (args : List String) (needle : String) : IO Unit := do
  try
    main args
    throw (IO.userError s!"✗ {label}: expected failure, command succeeded")
  catch e =>
    let msg := e.toString
    if !contains msg needle then
      throw (IO.userError s!"✗ {label}: expected '{needle}', got:\n{msg}")
    IO.println s!"✓ {label}"

private def expectTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"✗ {label}")
  IO.println s!"✓ {label}"

private def fileExists (path : String) : IO Bool := do
  try
    let _ ← IO.FS.readFile path
    pure true
  catch _ =>
    pure false

#eval! do
  expectErrorContains "missing --link value" ["--link"] "Missing value for --link"
  expectErrorContains "missing --output value" ["--output"] "Missing value for --output"
  expectErrorContains "missing -o value" ["-o"] "Missing value for --output"
  expectErrorContains "missing --abi-output value" ["--abi-output"] "Missing value for --abi-output"
  expectErrorContains "missing --input value" ["--input"] "Missing value for --input"
  expectErrorContains "invalid --input value" ["--input", "ast"] "Invalid value for --input: ast"
  expectErrorContains "missing --edsl-contract value" ["--edsl-contract"] "Missing value for --edsl-contract"
  expectErrorContains
    "--edsl-contract requires edsl input mode"
    ["--edsl-contract", "counter"]
    "--edsl-contract requires --input edsl"
  expectErrorContains
    "unknown --edsl-contract value"
    ["--input", "edsl", "--edsl-contract", "does-not-exist"]
    "Unsupported --edsl-contract: does-not-exist"
  expectErrorContains
    "duplicate --edsl-contract value"
    ["--input", "edsl", "--edsl-contract", "counter", "--edsl-contract", "counter"]
    "Duplicate --edsl-contract value: counter"
  let nonce ← IO.monoMsNow
  let edslOutDir := s!"/tmp/verity-main-test-{nonce}-edsl-out"
  IO.FS.createDirAll edslOutDir
  main ["--input", "edsl", "--output", edslOutDir]
  let edslArtifact ← fileExists s!"{edslOutDir}/SimpleStorage.yul"
  expectTrue "edsl input mode compiles supported subset artifact" edslArtifact
  let singleContractOutDir := s!"/tmp/verity-main-test-{nonce}-edsl-single-contract-out"
  IO.FS.createDirAll singleContractOutDir
  main ["--input", "edsl", "--edsl-contract", "counter", "--output", singleContractOutDir]
  let singleContractArtifact ← fileExists s!"{singleContractOutDir}/Counter.yul"
  expectTrue "edsl input mode compiles explicitly selected contract" singleContractArtifact
  expectErrorContains
    "edsl input mode rejects linked-library path"
    ["--input", "edsl", "--link", "examples/external-libs/PoseidonT3.yul", "--output", edslOutDir]
    "Linked external Yul libraries are not yet supported through --input edsl"
  expectErrorContains "missing --patch-report value" ["--patch-report"] "Missing value for --patch-report"
  expectErrorContains "missing --patch-max-iterations value" ["--patch-max-iterations"] "Missing value for --patch-max-iterations"
  expectErrorContains "missing --backend-profile value" ["--backend-profile"] "Missing value for --backend-profile"
  expectErrorContains "invalid --backend-profile value" ["--backend-profile", "invalid-profile"] "Invalid value for --backend-profile: invalid-profile"
  expectErrorContains "missing --parity-pack value" ["--parity-pack"] "Missing value for --parity-pack"
  expectErrorContains "invalid --parity-pack value" ["--parity-pack", "invalid-pack"] "Invalid value for --parity-pack: invalid-pack"
  expectErrorContains "reject duplicate --parity-pack" ["--parity-pack", "solc-0.8.28-o200-viair-false-evm-shanghai", "--parity-pack", "solc-0.8.28-o999999-viair-true-evm-paris"] "Cannot specify --parity-pack more than once"
  expectErrorContains "reject backend-profile + parity-pack conflict (profile first)" ["--backend-profile", "semantic", "--parity-pack", "solc-0.8.28-o200-viair-false-evm-shanghai"] "Cannot combine --parity-pack with --backend-profile"
  expectErrorContains "reject backend-profile + parity-pack conflict (pack first)" ["--parity-pack", "solc-0.8.28-o200-viair-false-evm-shanghai", "--backend-profile", "semantic"] "Cannot combine --backend-profile with --parity-pack"
  expectErrorContains "missing --mapping-slot-scratch-base value" ["--mapping-slot-scratch-base"] "Missing value for --mapping-slot-scratch-base"
  expectErrorContains "invalid --mapping-slot-scratch-base value" ["--mapping-slot-scratch-base", "not-a-number"] "Invalid value for --mapping-slot-scratch-base: not-a-number"
  expectErrorContains "removed --ast flag is rejected" ["--ast"] "Unknown argument: --ast"
  expectErrorContains "unknown argument still reported" ["--definitely-unknown-flag"] "Unknown argument: --definitely-unknown-flag"
  expectTrue "shipped parity packs have proof composition metadata"
    Compiler.allParityPacksProofCompositionValid
  let invalidPack : Compiler.ParityPack :=
    { id := "invalid-proof-pack"
      compat := {
        solcVersion := "0.8.28"
        solcCommit := "7893614a"
        optimizerRuns := 200
        viaIR := false
        evmVersion := "shanghai"
        metadataMode := "default"
      }
      backendProfile := .solidityParity
      forcePatches := true
      defaultPatchMaxIterations := 2
      rewriteBundleId := Compiler.Yul.solcCompatRewriteBundleId
      compositionProofRef := ""
      requiredProofRefs := [] }
  expectTrue "parity pack proof composition rejects empty metadata" (!invalidPack.proofCompositionValid)
  let missingBundlePack := { invalidPack with
    compositionProofRef := "Compiler.Proofs.YulGeneration.PatchRulesProofs.foundation_patch_pack_obligations"
    requiredProofRefs := Compiler.Yul.foundationProofAllowlist
    rewriteBundleId := "missing-rewrite-bundle" }
  expectTrue "parity pack proof composition rejects unknown rewrite bundle IDs"
    (!missingBundlePack.proofCompositionValid)
  expectTrue "manual model path lowers successfully through EDSL boundary"
    (match Compiler.Lowering.lowerModelPath Compiler.Specs.simpleStorageSpec with
    | .ok lowered => lowered.name == Compiler.Specs.simpleStorageSpec.name
    | .error _ => false)
  let unsupportedMsg :=
    match Compiler.Lowering.lowerFromEDSLSubset (.unsupported "(test unsupported feature)") with
    | .ok _ => ""
    | .error err => err.message
  expectTrue "explicit unsupported EDSL subset input returns deterministic diagnostic"
    (contains unsupportedMsg "test unsupported feature")
  let supportedNames := Compiler.Lowering.supportedEDSLContractNames
  expectTrue "supported --edsl-contract names are unique"
    (supportedNames.eraseDups.length == supportedNames.length)
  let parserRoundtripUnique :=
    Compiler.Lowering.supportedEDSLContracts.all (fun requested =>
      match Compiler.Lowering.parseSupportedEDSLContract? (Compiler.Lowering.supportedEDSLContractName requested) with
      | some parsed => parsed == requested
      | none => false)
  expectTrue "supported --edsl-contract parser roundtrip is unique" parserRoundtripUnique

  let libWithCommentAndStringBraces :=
    "{\n" ++
    "function PoseidonT3_hash(a, b) -> result {\n" ++
    "  // } stray brace in comment\n" ++
    "  result := add(a, b)\n" ++
    "}\n\n" ++
    "function PoseidonT4_hash(a, b, c) -> result {\n" ++
    "  let marker := \"} in string\"\n" ++
    "  result := add(add(a, b), c)\n" ++
    "}\n" ++
    "}\n"

  let parsed := Compiler.Linker.parseLibrary libWithCommentAndStringBraces
  expectTrue "linker parses two functions when braces appear in comments/strings" (parsed.length == 2)
  expectTrue "linker keeps first function boundary intact" ((parsed.getD 0 {name := "", arity := 0, body := []}).name == "PoseidonT3_hash")
  expectTrue "linker keeps second function boundary intact" ((parsed.getD 1 {name := "", arity := 0, body := []}).name == "PoseidonT4_hash")
  let firstBody := String.intercalate "\n" ((parsed.getD 0 {name := "", arity := 0, body := []}).body)
  expectTrue "first function body does not swallow next function" (!contains firstBody "function PoseidonT4_hash")

end Compiler.MainTest
