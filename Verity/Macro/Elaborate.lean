import Lean
import Verity.Macro.Syntax
import Verity.Macro.Translate
import Verity.Macro.Bridge

namespace Verity.Macro

open Lean
open Lean.Elab
open Lean.Elab.Command

set_option hygiene false

@[command_elab verityContractCmd]
def elabVerityContract : CommandElab := fun stx => do
  let (contractName, fields, ctor, functions) ← parseContractSyntax stx

  elabCommand (← `(namespace $contractName))

  for field in fields do
    elabCommand (← mkStorageDefCommandPublic field)

  for fn in functions do
    let fnCmds ← mkFunctionCommandsPublic fields fn
    for cmd in fnCmds do
      elabCommand cmd
    elabCommand (← mkBridgeCommand fn.ident)
    -- Emit semantic preservation theorem skeleton (Issue #998, Phase 3).
    -- This generates a per-function theorem connecting the EDSL execution
    -- to the CompilationModel spec, replacing the interpretSpec dependency.
    elabCommand (← mkSemanticBridgeCommand contractName fn)

  elabCommand (← mkSpecCommandPublic (toString contractName.getId) fields ctor functions)

  elabCommand (← `(end $contractName))

end Verity.Macro
