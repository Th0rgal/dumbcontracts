/-
  Layer 2: ContractSpec → IR Preservation for SimpleStorage

  Prove that compiling SimpleStorage spec to IR preserves semantics:
    interpretIR (compile simpleStorageSpec) = interpretSpec simpleStorageSpec

  This is the first step in Layer 2 verification, demonstrating the approach
  on the simplest possible contract.
-/

import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.Conversions
import Compiler.Proofs.IRGeneration.Expr
import DumbContracts.Proofs.Stdlib.SpecInterpreter
import Compiler.Specs
import Compiler.ContractSpec

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.Specs
open Compiler.ContractSpec
open DiffTestTypes
open DumbContracts.Proofs.Stdlib.SpecInterpreter

/-! ## SimpleStorage IR Compilation -/

/-- Compile SimpleStorage spec to IR
    Note: We need to provide selectors manually for now -/
def simpleStorageIR : Except String IRContract :=
  compile simpleStorageSpec [0x6057361d, 0x2e64cec1]

/-! ## Preservation Theorems -/

/-- The store function preserves semantics: IR execution matches Spec execution.

    This statement now uses the explicit conversion layer:
    - `transactionToIRTransaction` for the call
    - `specStorageToIRState` for initial IR state
    This cleanly relates Spec and IR representations.
-/
theorem store_preserves_semantics (value : Nat) (sender : Address) :
  let spec := simpleStorageSpec
  let irContract := compile spec [0x6057361d, 0x2e64cec1]
  let tx : Transaction := {
    sender := sender
    functionName := "store"
    args := [value]
  }
  -- Create IR transaction via conversion layer
  let irTx : IRTransaction := transactionToIRTransaction tx 0x6057361d
  -- Execute both sides
  let specResult := interpretSpec spec (SpecStorage.empty) tx
  match irContract with
  | .ok ir =>
      let irResult := interpretIR ir irTx (specStorageToIRState SpecStorage.empty sender)
      -- Results should match
      resultsMatch ir.usesMapping [] irResult specResult
  | .error _ => False
  :=
  simpleStorage_store_correct_with_sender value sender

/-- The retrieve function preserves semantics -/
theorem retrieve_preserves_semantics (sender : Address) :
  let spec := simpleStorageSpec
  let irContract := compile spec [0x6057361d, 0x2e64cec1]
  let tx : Transaction := {
    sender := sender
    functionName := "retrieve"
    args := []
  }
  -- Create IR transaction via conversion layer
  let irTx : IRTransaction := transactionToIRTransaction tx 0x2e64cec1
  let specResult := interpretSpec spec (SpecStorage.empty) tx
  match irContract with
  | .ok ir =>
      let irResult := interpretIR ir irTx (specStorageToIRState SpecStorage.empty sender)
      resultsMatch ir.usesMapping [] irResult specResult
  | .error _ => False
  :=
  simpleStorage_retrieve_correct_with_sender sender

/-! ## Contract-Level Preservation (Dispatch)

This theorem generalizes the per-function results by connecting a
transaction's `functionName` to its selector and showing that the compiled
IR preserves Spec semantics for well-formed calls. Incorrect arities are
treated as out-of-scope for now (the result is vacuously true).
-/

theorem simpleStorage_contract_preserves_semantics (tx : Transaction) :
  let spec := simpleStorageSpec
  let irContract := compile spec [0x6057361d, 0x2e64cec1]
  let specResult := interpretSpec spec SpecStorage.empty tx
  match irContract with
  | .ok ir =>
      match tx.functionName, tx.args with
      | "store", [value] =>
          let irTx := transactionToIRTransaction tx 0x6057361d
          let irResult := interpretIR ir irTx (specStorageToIRState SpecStorage.empty tx.sender)
          resultsMatch ir.usesMapping [] irResult specResult
      | "retrieve", [] =>
          let irTx := transactionToIRTransaction tx 0x2e64cec1
          let irResult := interpretIR ir irTx (specStorageToIRState SpecStorage.empty tx.sender)
          resultsMatch ir.usesMapping [] irResult specResult
      | _, _ => True
  | .error _ => False
  := by
  by_cases hstore : tx.functionName = "store"
  · subst hstore
    cases hargs : tx.args with
    | nil =>
        simp [simpleStorageSelectorMap, SelectorMap.lookup, hargs]
    | cons value rest =>
        cases rest with
        | nil =>
            simpa [simpleStorageSelectorMap, SelectorMap.lookup, hargs] using
              (store_preserves_semantics value tx.sender)
        | cons _ _ =>
            simp [simpleStorageSelectorMap, SelectorMap.lookup, hargs]
  · by_cases hretrieve : tx.functionName = "retrieve"
    · subst hretrieve
      cases hargs : tx.args with
      | nil =>
          simpa [simpleStorageSelectorMap, SelectorMap.lookup, hargs] using
            (retrieve_preserves_semantics tx.sender)
      | cons _ _ =>
          simp [simpleStorageSelectorMap, SelectorMap.lookup, hargs]
    · simp [simpleStorageSelectorMap, SelectorMap.lookup, hstore, hretrieve]

/-! ## Notes on Proof Strategy

The main challenge for Layer 2 proofs is aligning type representations:

**Spec Side**:
- Uses ContractState with Uint256, Address types
- SpecStorage with slots/mappings
- Transaction with sender : Address

**IR Side**:
- Uses IRState with only Nat
- IRTransaction with sender : Nat, functionSelector : Nat
- No type-level distinction between addresses and values

**Solution Approach**:
1. Define conversion functions: ContractState → IRState, Transaction → IRTransaction
2. Define relation: IRResult ≈ SpecInterpreter.Result (modulo type conversions)
3. Prove compilation preserves this relation

**Why This is Simpler than Layer 1**:
- IR semantics are more operational (variables, assignment, sstore)
- No nested monadic structure to reduce
- Clearer separation between compilation (ContractSpec → IR) and execution (IR → Result)
- The `compile` function is deterministic and structural

**Next Steps**:
1. Extend contract-level dispatch theorems to the remaining contracts
2. Lift from empty initial storage to arbitrary initial storage where needed
3. Reuse `SelectorMap` to avoid hand-wiring selector tables

-/

end Compiler.Proofs.IRGeneration
