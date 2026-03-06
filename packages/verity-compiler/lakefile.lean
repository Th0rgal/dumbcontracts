import Lake
open Lake DSL

package «verity-compiler» where
  version := v!"0.1.0"

require «verity-edsl» from "../verity-edsl"

lean_lib «Compiler» where
  srcDir := "../.."
  globs := #[.andSubmodules `Compiler]

lean_exe «verity-compiler» where
  root := `Compiler.Main
