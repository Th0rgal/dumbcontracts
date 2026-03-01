/-
  Compiler.Proofs.SemanticBridge: Full EDSL ≡ Compiled IR theorem statements

  This file states the *target* theorem per contract function: that EDSL execution
  produces the same storage effects as compiling the CompilationModel spec and
  interpreting the resulting IR.

  Unlike the macro-generated `_semantic_preservation` theorems (which live in the
  contract namespace and cannot import IR types), these theorems import the full
  IR execution machinery and state the precise equivalence:

    ∀ slot, (edslFinalState.storage slot).val = irResult.finalStorage slot

  The proofs are `sorry` — to be discharged by composing:
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

This is the *target* theorem for Issue #998. When the `sorry` is discharged:
- `interpretSpec` is no longer needed for SimpleStorage.store
- The trust chain becomes: EDSL ≡ IR ≡ Yul ≡ EVMYulLean (all machine-checked)

Proof strategy:
1. Show `compile simpleStorageSpec selectors = .ok simpleStorageIRContract` by `rfl`
2. Unfold `store value` into `setStorage storedData value`
3. Show the IR compilation of the spec produces `sstore(0, value)` by `rfl`
4. Show the IR interpreter executes `sstore(0, value)` to update slot 0
5. Both sides agree: slot 0 = value.val, all other slots unchanged -/
theorem simpleStorage_store_semantic_bridge
    (state : ContractState) (sender : Address) (value : Uint256)
    (selectors : List Nat)
    (hSel : selectors = [0x6057361d, 0x2e64cec1]) :
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
        match CompilationModel.compile Compiler.Specs.simpleStorageSpec selectors with
        | .ok irContract =>
          let irResult := interpretIR irContract tx irState
          irResult.success = true ∧
          ∀ slot, (s'.storage slot).val = irResult.finalStorage slot
        | .error _ => False  -- Compilation must succeed
    | .revert _ _ => True
    := by
  sorry -- TODO(#998 Phase 4): Compose primitive bridge lemmas.
        -- Proof sketch:
        -- 1. `compile simpleStorageSpec selectors = .ok simpleStorageIRContract` by rfl
        -- 2. `interpretIR` dispatches to the store function, executes sstore(0, value)
        -- 3. EDSL `store value` executes setStorage storedData value
        -- 4. Both update slot 0 to value.val, leaving others unchanged
        -- 5. QED by ext on storage functions

/-- SimpleStorage.retrieve: EDSL execution matches compiled IR execution.

When discharged, this proves that `interpretSpec` is unnecessary for
SimpleStorage.retrieve — the EDSL and compiled IR agree directly on
both the return value and the final storage. -/
theorem simpleStorage_retrieve_semantic_bridge
    (state : ContractState) (sender : Address)
    (selectors : List Nat)
    (hSel : selectors = [0x6057361d, 0x2e64cec1]) :
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
        match CompilationModel.compile Compiler.Specs.simpleStorageSpec selectors with
        | .ok irContract =>
          let irResult := interpretIR irContract tx irState
          irResult.success = true ∧
          irResult.returnValue = some val.val ∧
          ∀ slot, (s'.storage slot).val = irResult.finalStorage slot
        | .error _ => False
    | .revert _ _ => True
    := by
  sorry -- TODO(#998 Phase 4): Same strategy as store, but for sload + return.

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
