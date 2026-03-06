import Lake
open Lake DSL

package «verity-compiler» where
  version := v!"0.1.0"

require «verity-edsl» from "../verity-edsl"

lean_lib «Compiler» where
  srcDir := "../.."
  globs := #[
    .one `Compiler,
    .andSubmodules `Compiler,
    .one `Verity.Macro,
    .andSubmodules `Verity.Macro,
    .one `Verity.Core.Free.TypedIRCompiler,
    .one `Verity.Core.Free.TypedIRCompilerCorrectness,
    .one `Verity.Core.Free.TypedIRLowering,
    .one `Verity.Proofs.Stdlib.Automation,
    .one `Verity.Proofs.Stdlib.MappingAutomation
  ]

lean_exe «verity-compiler» where
  srcDir := "../.."
  root := `Compiler.Main
