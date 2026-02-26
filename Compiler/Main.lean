import Compiler.CompileDriver
import Compiler.ASTDriver
import Compiler.ParityPacks

/-!
## CLI Argument Parsing

Supports:
- `--link <path>` : Link external Yul library (can be specified multiple times)
- `--output <dir>` or `-o <dir>` : Output directory (default: "compiler/yul")
- `--ast` : Use unified AST compilation path (issue #364)
- `--verbose` or `-v` : Verbose output
- `--help` or `-h` : Show help message
-/

private structure CLIArgs where
  outDir : String := "compiler/yul"
  abiOutDir : Option String := none
  libs : List String := []
  verbose : Bool := false
  useAST : Bool := false
  backendProfile : Compiler.BackendProfile := .semantic
  backendProfileExplicit : Bool := false
  parityPackId : Option String := none
  patchEnabled : Bool := false
  patchMaxIterations : Nat := 2
  patchMaxIterationsExplicit : Bool := false
  patchReportPath : Option String := none
  mappingSlotScratchBase : Nat := 0

private def profileForcesPatches (profile : Compiler.BackendProfile) : Bool :=
  match profile with
  | .solidityParity => true
  | _ => false

private def packForcesPatches (cfg : CLIArgs) : Bool :=
  match cfg.parityPackId with
  | some packId =>
      match Compiler.findParityPack? packId with
      | some pack => pack.forcePatches
      | none => false
  | none => false

private def patchEnabledFor (cfg : CLIArgs) : Bool :=
  cfg.patchEnabled || profileForcesPatches cfg.backendProfile || packForcesPatches cfg

private def parseBackendProfile (raw : String) : Option Compiler.BackendProfile :=
  match raw with
  | "semantic" => some .semantic
  | "solidity-parity-ordering" => some .solidityParityOrdering
  | "solidity-parity" => some .solidityParity
  | _ => none

private def backendProfileString (profile : Compiler.BackendProfile) : String :=
  match profile with
  | .semantic => "semantic"
  | .solidityParityOrdering => "solidity-parity-ordering"
  | .solidityParity => "solidity-parity"

private def parseArgs (args : List String) : IO CLIArgs := do
  let rec go (remaining : List String) (cfg : CLIArgs) : IO CLIArgs :=
    match remaining with
    | [] => pure { cfg with libs := cfg.libs.reverse }
    | "--help" :: _ | "-h" :: _ => do
        IO.println "Verity Compiler"
        IO.println ""
        IO.println "Usage: verity-compiler [options]"
        IO.println ""
        IO.println "Options:"
        IO.println "  --link <path>      Link external Yul library (can be used multiple times)"
        IO.println "  --output <dir>     Output directory (default: compiler/yul)"
        IO.println "  -o <dir>           Short form of --output"
        IO.println "  --ast              Use unified AST compilation path (#364)"
        IO.println "  --abi-output <dir> Output ABI JSON artifacts (one <Contract>.abi.json per spec)"
        IO.println "  --backend-profile <semantic|solidity-parity-ordering|solidity-parity>"
        IO.println "  --parity-pack <id> Versioned parity-pack tuple (see docs/PARITY_PACKS.md)"
        IO.println "  --enable-patches   Enable deterministic Yul patch pass"
        IO.println "  --patch-max-iterations <n>  Max patch-pass fixpoint iterations (default: 2)"
        IO.println "  --patch-report <path>       Write TSV patch coverage report"
        IO.println "  --mapping-slot-scratch-base <n>  Scratch memory base for mappingSlot helper (default: 0)"
        IO.println "  --verbose          Enable verbose output"
        IO.println "  -v                 Short form of --verbose"
        IO.println "  --help             Show this help message"
        IO.println "  -h                 Short form of --help"
        IO.println ""
        IO.println "Example:"
        IO.println "  verity-compiler --link examples/external-libs/PoseidonT3.yul -o compiler/yul"
        IO.println "  verity-compiler --ast -v  # compile using unified AST path"
        IO.println "  verity-compiler --enable-patches --patch-report compiler/patch-report.tsv"
        throw (IO.userError "help")
    | "--link" :: path :: rest =>
        go rest { cfg with libs := path :: cfg.libs }
    | ["--link"] =>
        throw (IO.userError "Missing value for --link")
    | "--output" :: dir :: rest | "-o" :: dir :: rest =>
        go rest { cfg with outDir := dir }
    | ["--output"] | ["-o"] =>
        throw (IO.userError "Missing value for --output")
    | "--abi-output" :: dir :: rest =>
        go rest { cfg with abiOutDir := some dir }
    | ["--abi-output"] =>
        throw (IO.userError "Missing value for --abi-output")
    | "--ast" :: rest =>
        go rest { cfg with useAST := true }
    | "--backend-profile" :: raw :: rest =>
        if cfg.parityPackId.isSome then
          throw (IO.userError "Cannot combine --backend-profile with --parity-pack")
        else
          match parseBackendProfile raw with
          | some profile => go rest { cfg with backendProfile := profile, backendProfileExplicit := true }
          | none =>
              throw (IO.userError s!"Invalid value for --backend-profile: {raw} (expected semantic, solidity-parity-ordering, or solidity-parity)")
    | ["--backend-profile"] =>
        throw (IO.userError "Missing value for --backend-profile")
    | "--parity-pack" :: raw :: rest =>
        if cfg.parityPackId.isSome then
          throw (IO.userError "Cannot specify --parity-pack more than once")
        else if cfg.backendProfileExplicit then
          throw (IO.userError "Cannot combine --parity-pack with --backend-profile")
        else
          match Compiler.findParityPack? raw with
          | some pack =>
              if !pack.proofCompositionValid then
                throw (IO.userError
                  s!"Parity pack '{pack.id}' is missing valid proof composition metadata")
              else
                go rest {
                  cfg with
                    parityPackId := some pack.id
                    backendProfile := pack.backendProfile
                    patchEnabled := cfg.patchEnabled || pack.forcePatches
                    patchMaxIterations :=
                      if cfg.patchMaxIterationsExplicit then cfg.patchMaxIterations else pack.defaultPatchMaxIterations
               }
          | none =>
              throw (IO.userError
                s!"Invalid value for --parity-pack: {raw} (supported: {String.intercalate ", " Compiler.supportedParityPackIds})")
    | ["--parity-pack"] =>
        throw (IO.userError "Missing value for --parity-pack")
    | "--enable-patches" :: rest =>
        go rest { cfg with patchEnabled := true }
    | "--patch-max-iterations" :: raw :: rest =>
        match raw.toNat? with
        | some n => go rest { cfg with patchEnabled := true, patchMaxIterations := n, patchMaxIterationsExplicit := true }
        | none => throw (IO.userError s!"Invalid value for --patch-max-iterations: {raw}")
    | ["--patch-max-iterations"] =>
        throw (IO.userError "Missing value for --patch-max-iterations")
    | "--patch-report" :: path :: rest =>
        go rest { cfg with patchEnabled := true, patchReportPath := some path }
    | ["--patch-report"] =>
        throw (IO.userError "Missing value for --patch-report")
    | "--mapping-slot-scratch-base" :: raw :: rest =>
        match raw.toNat? with
        | some n => go rest { cfg with mappingSlotScratchBase := n }
        | none => throw (IO.userError s!"Invalid value for --mapping-slot-scratch-base: {raw}")
    | ["--mapping-slot-scratch-base"] =>
        throw (IO.userError "Missing value for --mapping-slot-scratch-base")
    | "--verbose" :: rest | "-v" :: rest =>
        go rest { cfg with verbose := true }
    | unknown :: _ =>
        throw (IO.userError s!"Unknown argument: {unknown}\nUse --help for usage information")
  go args {}

def main (args : List String) : IO Unit := do
  try
    let cfg ← parseArgs args
    if cfg.verbose then
      IO.println s!"Output directory: {cfg.outDir}"
      if cfg.useAST then
        IO.println "Mode: unified AST compilation"
      IO.println s!"Backend profile: {backendProfileString cfg.backendProfile}"
      match cfg.parityPackId with
      | some packId =>
          IO.println s!"Parity pack: {packId}"
          match Compiler.findParityPack? packId with
          | some pack =>
              IO.println s!"  target solc: {pack.compat.solcVersion}+commit.{pack.compat.solcCommit}"
              IO.println s!"  optimizer runs: {pack.compat.optimizerRuns}"
              IO.println s!"  viaIR: {pack.compat.viaIR}"
              IO.println s!"  evmVersion: {pack.compat.evmVersion}"
              IO.println s!"  metadataMode: {pack.compat.metadataMode}"
          | none => pure ()
      | none => pure ()
      match cfg.abiOutDir with
      | some dir => IO.println s!"ABI output directory: {dir}"
      | none => pure ()
      let patchEnabled := patchEnabledFor cfg
      if patchEnabled then
        IO.println s!"Patch pass: enabled (max iterations = {cfg.patchMaxIterations})"
      if !cfg.libs.isEmpty then
        IO.println s!"External libraries: {cfg.libs.length}"
        for lib in cfg.libs do
          IO.println s!"  - {lib}"
      match cfg.patchReportPath with
      | some path => IO.println s!"Patch report: {path}"
      | none => pure ()
      IO.println s!"Mapping slot scratch base: {cfg.mappingSlotScratchBase}"
      IO.println ""
    let patchEnabled := patchEnabledFor cfg
    let packRequiredProofRefs :=
      match cfg.parityPackId with
      | some packId =>
          match Compiler.findParityPack? packId with
          | some pack => pack.requiredProofRefs
          | none => []
      | none => []
    let options : Compiler.YulEmitOptions := {
      backendProfile := cfg.backendProfile
      patchConfig := {
        enabled := patchEnabled
        maxIterations := cfg.patchMaxIterations
        packId := cfg.parityPackId.getD ""
        requiredProofRefs := packRequiredProofRefs
      }
      mappingSlotScratchBase := cfg.mappingSlotScratchBase
    }
    if cfg.useAST then
      Compiler.ASTDriver.compileAllASTWithOptions cfg.outDir cfg.verbose cfg.libs options cfg.patchReportPath cfg.abiOutDir
    else
      compileAllWithOptions cfg.outDir cfg.verbose cfg.libs options cfg.patchReportPath cfg.abiOutDir
  catch e =>
    if e.toString == "help" then
      -- Help was shown, exit cleanly
      return ()
    else
      throw e
