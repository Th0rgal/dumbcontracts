import Lake
open Lake DSL

package «verity-compiler» where
  version := v!"0.1.0"

require «verity-edsl» from "../verity-edsl"

lean_lib «Compiler» where
  srcDir := "../.."
  globs := #[
    .one `Compiler,
    .andSubmodules `Compiler.ABI,
    .andSubmodules `Compiler.Backends,
    .andSubmodules `Compiler.Codegen,
    .andSubmodules `Compiler.CompilationModel,
    .andSubmodules `Compiler.Gas,
    .andSubmodules `Compiler.Linker,
    .andSubmodules `Compiler.Lowering,
    .andSubmodules `Compiler.ParityPacks,
    .andSubmodules `Compiler.Pipeline,
    .andSubmodules `Compiler.Proofs,
    .andSubmodules `Compiler.Selector,
    .andSubmodules `Compiler.Yul,
    .one `Compiler.CompileDriver,
    .one `Compiler.Main,
    .one `Compiler.MainTest,
    .one `Compiler.Specs,
    .one `Compiler.CompilationModelFeatureTest
  ]

lean_exe «verity-compiler» where
  root := `Compiler.Main
