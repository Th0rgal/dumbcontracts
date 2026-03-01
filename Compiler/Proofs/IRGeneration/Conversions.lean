/-
  Type Conversions: bridge between EDSL-side values and IR execution state.
-/

import Compiler.Proofs.IRGeneration.IRInterpreter

namespace Compiler.Proofs.IRGeneration

open Compiler
open Verity
open DiffTestTypes

/-- Convert Address to Nat for IR execution. -/
def addressToNat (addr : Address) : Nat := addr.val

/-- Extract Nat value from Uint256. -/
def uint256ToNat (u : Uint256) : Nat := u.val

/-- Convert ContractState to IRState for IR execution. -/
def contractStateToIRState (state : ContractState) : IRState :=
  { vars := []
    storage := fun slot => uint256ToNat (state.storage slot)
    memory := fun _ => 0
    calldata := []
    returnValue := none
    sender := addressToNat state.sender
    selector := 0 }

@[simp] theorem contractStateToIRState_memory (state : ContractState) (offset : Nat) :
    (contractStateToIRState state).memory offset = 0 := by
  rfl

/-- Convert Spec transaction metadata into IR transaction shape. -/
def transactionToIRTransaction (tx : Transaction) (selector : Nat) : IRTransaction :=
  { sender := addressToNat tx.sender
    functionSelector := selector
    args := tx.args }

end Compiler.Proofs.IRGeneration
