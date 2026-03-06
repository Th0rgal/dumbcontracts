import Lake
open Lake DSL

package «verity-edsl» where
  version := v!"0.1.0"

require evmyul from git
  "https://github.com/NethermindEth/EVMYulLean.git"@"047f63070309f436b66c61e276ab3b6d1169265a"

lean_lib «Verity» where
  srcDir := "../.."
  globs := #[
    .one `Verity,
    .andSubmodules `Verity.Core,
    .submodules `Verity.EVM,
    .andSubmodules `Verity.Macro,
    .submodules `Verity.Stdlib,
    .andSubmodules `Verity.Specs.Common,
    .submodules `Verity.Proofs.Stdlib
  ]
