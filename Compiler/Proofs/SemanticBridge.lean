/-
  Compiler.Proofs.SemanticBridge: Full EDSL ≡ Compiled IR theorem statements

  This file states the *target* theorem per contract function: that EDSL execution
  produces the same storage effects as compiling the CompilationModel spec and
  interpreting the resulting IR.

  Unlike the macro-generated `_semantic_preservation` theorems (which live in the
  contract namespace and cannot import IR types), these theorems import the full
  IR execution machinery and state the precise equivalence:

    ∀ slot, (edslFinalState.storage slot).val = irResult.finalStorage slot

  For SimpleStorage, the proofs attempt full discharge (no sorry) via
  direct simp unfolding of both EDSL and IR execution. For more complex
  contracts, the proofs compose:
  1. Primitive bridge lemmas (PrimitiveBridge.lean)
  2. EndToEnd composition (EndToEnd.lean)
  3. ArithmeticProfile bridge (ArithmeticProfile.lean)

  **Why a separate file**: The macro-generated theorems cannot import
  `Compiler.Proofs.IRGeneration.IRInterpreter` (it would transitively pull
  in EVMYulLean and bloat every contract file). This file bridges the gap by
  importing both the EDSL types and the IR execution types, stating the
  theorems that directly reference `interpretIR`.

  Run: lake build Compiler.Proofs.SemanticBridge
-/

import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.Conversions
import Compiler.Proofs.EndToEnd
import Compiler.Specs
import Verity.Core
import Verity.Examples.SimpleStorage

namespace Compiler.Proofs.SemanticBridge

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration
open Verity
open Verity.Core.Uint256

/-! ## State Encoding

The canonical encoding from EDSL ContractState to IR-level Nat storage.
This must be consistent with the encoding used in PrimitiveBridge.lean.
-/

/-- Encode EDSL storage (Uint256 at each slot) as Nat storage for IR. -/
def encodeStorage (state : ContractState) : Nat → Nat :=
  fun slot => (state.storage slot).val

/-- Encode EDSL sender (Address) as Nat for IR. -/
def encodeSender (state : ContractState) : Nat :=
  state.sender.val

/-! ## Target Theorems: SimpleStorage

These theorems state the *real* equivalence: EDSL execution produces the
same storage/return values as compiling the CompilationModel spec to IR
and interpreting it. When discharged, `interpretSpec` is no longer needed.

The trust chain becomes: EDSL ≡ IR ≡ Yul ≡ EVMYulLean (all machine-checked).
-/

/-- SimpleStorage.store: EDSL execution matches compiled IR execution.

This is the *target* theorem for Issue #998. When verified by the build:
- `interpretSpec` is no longer needed for SimpleStorage.store
- The trust chain becomes: EDSL ≡ IR ≡ Yul ≡ EVMYulLean (all machine-checked)

Proof strategy:
1. Show `compile simpleStorageSpec selectors = .ok simpleStorageIRContract` by `rfl`
2. Unfold `store value` into `setStorage storedData value`
3. Show the IR compilation of the spec produces `sstore(0, value)` by `rfl`
4. Show the IR interpreter executes `sstore(0, value)` to update slot 0
5. Both sides agree: slot 0 = value.val, all other slots unchanged -/
theorem simpleStorage_store_semantic_bridge
    (state : ContractState) (sender : Address) (value : Uint256) :
    let edslResult := Contract.run (Verity.Examples.store value) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x6057361d
      args := [value.val]
    }
    let irState : IRState := {
      vars := []
      storage := encodeStorage state
      memory := fun _ => 0
      calldata := [value.val]
      returnValue := none
      sender := sender.val
      selector := 0x6057361d
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        ∀ slot, (s'.storage slot).val = irResult.finalStorage slot
    | .revert _ _ => True
    := by
  -- Both sides are fully concrete for SimpleStorage.
  -- EDSL: store value = setStorage ⟨0⟩ value → updates slot 0, success.
  -- IR: interpretIR dispatches to store function, executes:
  --   let value := calldataload(4)  →  binds "value" to calldata[0] = value.val
  --   sstore(0, value)              →  storage[0] := value.val
  --   stop                          →  .stop (success, no return value)
  -- Both produce: success=true, storage[0]=value.val, storage[k]=unchanged for k≠0.
  -- calldataload(4) returns value.val % evmModulus; reduce to value.val
  have hmod : value.val % Compiler.Constants.evmModulus = value.val :=
    Nat.mod_eq_of_lt (by simp [Compiler.Constants.evmModulus, UINT256_MODULUS]; exact value.isLt)
  simp [Verity.Examples.store, Verity.Examples.storedData, Contract.run,
    setStorage, bind, encodeStorage,
    interpretIR, simpleStorageIRContract,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    calldataloadWord, selectorWord, hmod,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    IRState.setVar, IRState.getVar]
  intro slot
  by_cases h : slot = 0 <;> simp_all [beq_iff_eq]

/-- SimpleStorage.retrieve: EDSL execution matches compiled IR execution.

When discharged, this proves that `interpretSpec` is unnecessary for
SimpleStorage.retrieve — the EDSL and compiled IR agree directly on
both the return value and the final storage. -/
theorem simpleStorage_retrieve_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.retrieve) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2e64cec1
      args := []
    }
    let irState : IRState := {
      vars := []
      storage := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2e64cec1
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ slot, (s'.storage slot).val = irResult.finalStorage slot
    | .revert _ _ => True
    := by
  -- Both sides are fully concrete for SimpleStorage.
  -- EDSL: retrieve = getStorage ⟨0⟩ → returns (state.storage 0), state unchanged.
  -- IR: interpretIR dispatches to retrieve function, executes:
  --   mstore(0, sload(0))  →  memory[0] := storage[0] = (state.storage 0).val
  --   return(0, 32)         →  .return (memory[0]) = some (state.storage 0).val
  -- Both: success=true, returnValue=(state.storage 0).val, storage unchanged.
  simp [Verity.Examples.retrieve, Verity.Examples.storedData, Contract.run,
    getStorage, bind, pure, encodeStorage,
    interpretIR, simpleStorageIRContract,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    IRState.setVar, IRState.getVar]

/-! ## Generic Bridge Template

For contracts with N functions, we need N theorems of this shape.
The macro-generated `_semantic_preservation` theorems provide the
type-checked skeleton. This file provides the concrete IR-connected
instances.

The composition chain for each function f:
  1. EDSL(f).run state ≡ IR(compile(f.spec)).exec irState
     (this file, via primitive bridge lemmas)
  2. IR(compile(spec)).exec ≡ Yul(emitYul(compile(spec))).exec
     (EndToEnd.lean, via Layer 3)
  3. Yul builtins ≡ EVMYulLean builtins
     (ArithmeticProfile.lean, for pure builtins)

Composing 1+2+3 gives the target:
  EDSL(f).run state ≡ EVMYulLean(compile(spec))(f, state)
-/

end Compiler.Proofs.SemanticBridge
