import Compiler.Codegen
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Semantics

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Yul

/-! ## IR ↔ Yul State Alignment -/

def yulStateOfIR (selector : Nat) (state : IRState) : YulState :=
  { vars := state.vars
    storage := state.storage
    mappings := state.mappings
    memory := state.memory
    calldata := state.calldata
    selector := selector
    returnValue := state.returnValue
    sender := state.sender }

/-! ## Bridging IR and Yul Semantics

These helpers wire IR-level execution to Yul runtime execution so we can
compare results directly in smoke tests.
-/

noncomputable def interpretYulFromIR (contract : IRContract) (tx : IRTransaction) (state : IRState) : YulResult :=
  let yulTx : YulTransaction := {
    sender := tx.sender
    functionSelector := tx.functionSelector
    args := tx.args
  }
  interpretYulRuntime (Compiler.emitYul contract).runtimeCode yulTx state.storage state.mappings

def resultsMatchOn (slots : List Nat) (mappingKeys : List (Nat × Nat))
    (ir : IRResult) (yul : YulResult) : Bool :=
  ir.success == yul.success &&
  ir.returnValue == yul.returnValue &&
  slots.all (fun slot => ir.finalStorage slot == yul.finalStorage slot) &&
  mappingKeys.all (fun (base, key) => ir.finalMappings base key == yul.finalMappings base key)

end Compiler.Proofs.YulGeneration
