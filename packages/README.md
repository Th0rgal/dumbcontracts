# Package Split

This repository now exposes three first-class Lake packages:

- `packages/verity-edsl`: Verity EDSL, macro system, semantics, and proof helpers.
- `packages/verity-compiler`: compiler pipeline and CLI (`verity-compiler`) depending on `verity-edsl`.
- `packages/verity-examples`: contracts/examples and differential tooling depending on both.

Current caveat: `Verity.Macro` and the proof/lowering helpers that depend on
`Compiler.CompilationModel` are shipped from `verity-compiler`, not
`verity-edsl`, until #1313 moves the shared model types into the EDSL layer.

These packages are intentionally buildable on their own with `lake build` from each package directory.
