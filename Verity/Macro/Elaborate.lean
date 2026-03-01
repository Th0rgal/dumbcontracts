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

  elabCommand (← mkSpecCommandPublic (toString contractName.getId) fields ctor functions)

  -- Emit edslToSpecStorage and semantic preservation theorems AFTER spec
  -- generation, since the theorems reference `spec` and `edslToSpecStorage`.
  -- Issue #998 Phase 3: each theorem states EDSL ≡ interpretSpec(spec, ...).
  elabCommand (← mkEdslToSpecStorageCommand fields)
  for fn in functions do
    elabCommand (← mkSemanticBridgeCommand contractName fields fn)

  elabCommand (← `(end $contractName))

end Verity.Macro
