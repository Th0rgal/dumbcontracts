/-
  Compiler.Proofs.SemanticBridge: Full EDSL ≡ Compiled IR theorem statements

  This file states the *target* theorem per contract function: that EDSL execution
  produces the same storage effects as compiling the CompilationModel spec and
  interpreting the resulting IR.

  Unlike the macro-generated `_semantic_preservation` theorems (which live in the
  contract namespace and cannot import IR types), these theorems import the full
  IR execution machinery and state the precise equivalence:

    ∀ slot, (edslFinalState.storage slot).val = irResult.finalStorage slot

  For SimpleStorage, Counter, Owned, and SafeCounter, the proofs attempt full
  discharge (no sorry) via direct simp unfolding of both EDSL and IR execution.
  SafeCounter demonstrates the case-split approach for success/revert paths.
  For more complex contracts, the proofs compose:
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
import Verity.Examples.Counter
import Verity.Examples.Owned
import Verity.Examples.SafeCounter
import Verity.Examples.OwnedCounter

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

/-! ## Target Theorems: Counter

Counter has three functions (increment, decrement, getCount) with no parameters.
The EDSL uses `Uint256.add`/`Uint256.sub` which wrap at `modulus = 2^256`.
The IR uses `add`/`sub` builtins which wrap at `evmModulus = 2^256`.
Since `modulus = evmModulus`, the results match exactly.
-/

/-- Counter.increment: EDSL execution matches compiled IR execution.

EDSL: getStorage 0 → add current 1 → setStorage 0 result
IR:   sstore(0, add(sload(0), 1)) → stop

Both produce: success=true, storage[0] = (old + 1) % 2^256, others unchanged. -/
theorem counter_increment_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Counter.increment) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xd09de08a
      args := []
    }
    let irState : IRState := {
      vars := []
      storage := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xd09de08a
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        ∀ slot, (s'.storage slot).val = irResult.finalStorage slot
    | .revert _ _ => True
    := by
  -- Both sides: slot 0 updated to (old + 1) % 2^256, others unchanged.
  -- Uint256.add wraps at modulus = 2^256 = evmModulus.
  simp [Verity.Examples.Counter.increment, Verity.Examples.Counter.count,
    Contract.run, getStorage, setStorage, bind,
    Uint256.add, Uint256.ofNat, Uint256.modulus, UINT256_MODULUS,
    encodeStorage,
    interpretIR, counterIRContract,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    Compiler.Constants.evmModulus,
    IRState.setVar, IRState.getVar]
  intro slot
  by_cases h : slot = 0 <;> simp_all [beq_iff_eq]

/-- Counter.decrement: EDSL execution matches compiled IR execution.

EDSL: getStorage 0 → sub current 1 → setStorage 0 result
IR:   sstore(0, sub(sload(0), 1)) → stop

Both produce: success=true, storage[0] = (evmModulus + old - 1) % 2^256, others unchanged. -/
theorem counter_decrement_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Counter.decrement) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2baeceb7
      args := []
    }
    let irState : IRState := {
      vars := []
      storage := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2baeceb7
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        ∀ slot, (s'.storage slot).val = irResult.finalStorage slot
    | .revert _ _ => True
    := by
  -- Both sides: slot 0 updated to sub semantics, others unchanged.
  -- Uint256.sub wraps at modulus = 2^256 = evmModulus.
  -- EDSL sub: if b ≤ a then (a-b) % mod else (mod - (b-a)) % mod
  -- IR sub: (evmModulus + a - b) % evmModulus
  -- These are equal (both represent two's complement subtraction).
  -- Bridge the Uint256.sub result to the IR sub result.
  have hsub : ∀ (v : Uint256),
      (Uint256.sub v (Uint256.ofNat 1)).val =
        (Compiler.Constants.evmModulus + v.val - (1 % (2 ^ 256))) % Compiler.Constants.evmModulus := by
    intro v
    simp [Uint256.sub, Uint256.ofNat, Uint256.modulus, UINT256_MODULUS, Compiler.Constants.evmModulus]
    have hv := v.isLt
    simp [Uint256.modulus, UINT256_MODULUS] at hv
    by_cases hle : (1 % (2 ^ 256)) ≤ v.val
    · simp [hle]; omega
    · simp [hle]; omega
  simp [Verity.Examples.Counter.decrement, Verity.Examples.Counter.count,
    Contract.run, getStorage, setStorage, bind,
    encodeStorage,
    interpretIR, counterIRContract,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    IRState.setVar, IRState.getVar, hsub]
  intro slot
  by_cases h : slot = 0 <;> simp_all [beq_iff_eq]

/-- Counter.getCount: EDSL execution matches compiled IR execution.

EDSL: getStorage 0 → return value
IR:   mstore(0, sload(0)) → return(0, 32)

Both produce: success=true, returnValue = (state.storage 0).val, storage unchanged. -/
theorem counter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Counter.getCount) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xa87d942c
      args := []
    }
    let irState : IRState := {
      vars := []
      storage := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xa87d942c
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ slot, (s'.storage slot).val = irResult.finalStorage slot
    | .revert _ _ => True
    := by
  -- Both sides: read storage slot 0, return it, storage unchanged.
  simp [Verity.Examples.Counter.getCount, Verity.Examples.Counter.count,
    Contract.run, getStorage, bind, pure, encodeStorage,
    interpretIR, counterIRContract,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    IRState.setVar, IRState.getVar]

/-! ## Target Theorems: Owned

Owned uses Address-typed storage (slot 0 = owner address), so we need a
different encoding that maps `state.storageAddr` to the IR Nat storage.
The EDSL `ContractState` has separate `storage` (Uint256) and `storageAddr`
(Address) fields; the IR uses a single `Nat → Nat` storage.
-/

/-- Encode EDSL Address storage as Nat storage for IR.
Used for contracts that store Addresses (Owned, OwnedCounter, etc.). -/
def encodeStorageAddr (state : ContractState) : Nat → Nat :=
  fun slot => (state.storageAddr slot).val

/-- Owned.getOwner: EDSL execution matches compiled IR execution.

EDSL: getStorageAddr ⟨0⟩ → returns state.storageAddr 0
IR:   mstore(0, sload(0)) → return(0, 32)

Both produce: success=true, returnValue = (state.storageAddr 0).val. -/
theorem owned_getOwner_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Owned.getOwner) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x893d20e8
      args := []
    }
    let irState : IRState := {
      vars := []
      storage := encodeStorageAddr state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x893d20e8
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR ownedIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ slot, (s'.storageAddr slot).val = irResult.finalStorage slot
    | .revert _ _ => True
    := by
  -- Both sides: read storage slot 0 (address), return it, storage unchanged.
  simp [Verity.Examples.Owned.getOwner, Verity.Examples.Owned.owner,
    Contract.run, getStorageAddr, bind, pure, encodeStorageAddr,
    interpretIR, ownedIRContract,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    IRState.setVar, IRState.getVar]

/-- Owned.transferOwnership (as owner): EDSL execution matches compiled IR execution.

When the caller IS the owner, both sides update slot 0 to the new owner address.

EDSL: msgSender → getStorageAddr → require (sender == currentOwner) → setStorageAddr
IR:   let newOwner := and(calldataload(4), addressMask)
      if iszero(eq(caller(), sload(0))) { revert }
      sstore(0, newOwner) → stop

Both produce: success=true, storage[0] = newOwner.val, others unchanged. -/
theorem owned_transferOwnership_semantic_bridge
    (state : ContractState) (sender : Address) (newOwner : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Verity.Examples.Owned.transferOwnership newOwner)
        { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xf2fde38b
      args := [newOwner.val]
    }
    let irState : IRState := {
      vars := []
      storage := encodeStorageAddr state
      memory := fun _ => 0
      calldata := [newOwner.val]
      returnValue := none
      sender := sender.val
      selector := 0xf2fde38b
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedIRContract tx irState
        irResult.success = true ∧
        ∀ slot, (s'.storageAddr slot).val = irResult.finalStorage slot
    | .revert _ _ => True
    := by
  -- The EDSL path: msgSender → getStorageAddr → require (sender == owner) → setStorageAddr
  -- With hOwner, the require succeeds, and we update slot 0.
  -- The IR path: calldataload(4) & addressMask = newOwner.val (since Address < 2^160)
  -- Then eq(caller(), sload(0)) = eq(sender.val, owner.val) = 1 (since hOwner)
  -- iszero(1) = 0, so we don't revert. sstore(0, newOwner.val).
  -- Address mask: and(newOwner.val, addressMask) = newOwner.val since Address < 2^160
  have haddr : newOwner.val &&& addressMask = newOwner.val := by
    simp only [addressMask]
    have hlt : newOwner.val < 2 ^ 160 := by
      have := newOwner.isLt; simp [ADDRESS_MODULUS] at this; exact this
    calc newOwner.val &&& (2 ^ 160 - 1)
        = newOwner.val % 2 ^ 160 := by
          simpa using (Nat.and_two_pow_sub_one_eq_mod newOwner.val 160)
      _ = newOwner.val := Nat.mod_eq_of_lt hlt
  simp [Verity.Examples.Owned.transferOwnership, Verity.Examples.Owned.onlyOwner,
    Verity.Examples.Owned.isOwner, Verity.Examples.Owned.owner,
    Contract.run, getStorageAddr, setStorageAddr, msgSender, require,
    bind, pure, hOwner, encodeStorageAddr,
    interpretIR, ownedIRContract, ownedNotOwnerRevert,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    calldataloadWord,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    IRState.setVar, IRState.getVar, haddr]
  intro slot
  by_cases h : slot = 0 <;> simp_all [beq_iff_eq]

/-! ## Target Theorems: SafeCounter

SafeCounter uses checked arithmetic (safeAdd/safeSub) with requireSomeUint.
The IR generates overflow/underflow guards using gt/lt + iszero + revert.

The key challenge: both success and revert paths must be bridged.
- Success: safeAdd returns Some → IR gt check passes → sstore
- Revert: safeAdd returns None → IR gt check fails → revert

These proofs handle the `by_cases` split on whether overflow/underflow occurs.
-/

/-- SafeCounter.increment: EDSL execution matches compiled IR execution.

When no overflow (current < MAX_UINT256): both sides succeed, slot 0 = current + 1.
When overflow (current = MAX_UINT256): both sides revert.

EDSL: getStorage → safeAdd → requireSomeUint → setStorage
IR:   let count := sload(0)
      let newCount := add(count, 1)
      if iszero(gt(newCount, count)) { revert("Overflow") }
      sstore(0, newCount) → stop -/
theorem safeCounter_increment_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.SafeCounter.increment) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xd09de08a
      args := []
    }
    let irState : IRState := {
      vars := []
      storage := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xd09de08a
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = true ∧
        ∀ slot, (s'.storage slot).val = irResult.finalStorage slot
    | .revert _ _ =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = false
    := by
  -- Case split on whether overflow occurs.
  -- safeAdd (state.storage 0) 1 = none iff (state.storage 0).val + 1 > MAX_UINT256
  -- i.e., (state.storage 0).val = 2^256 - 1 (MAX_UINT256)
  simp only [Verity.Examples.SafeCounter.increment, Verity.Examples.SafeCounter.count,
    Contract.run, getStorage, bind, pure,
    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeAdd,
    Uint256.add, Uint256.ofNat, require,
    encodeStorage,
    interpretIR, safeCounterIRContract, safeCounterOverflowRevert,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    Compiler.Constants.evmModulus,
    Uint256.modulus, UINT256_MODULUS, MAX_UINT256,
    setStorage,
    IRState.setVar, IRState.getVar]
  -- After simp, the goal should reduce to case analysis on the overflow condition.
  -- The EDSL checks (a.val + 1) > MAX and the IR checks gt(add(a, 1), a).
  -- Both conditions are equivalent: overflow iff a.val = 2^256 - 1.
  have hv := (state.storage 0).isLt
  simp [Uint256.modulus, UINT256_MODULUS] at hv
  -- Case split: did overflow occur?
  by_cases hmax : (state.storage 0).val = 2 ^ 256 - 1
  · -- Overflow case: both EDSL and IR revert
    simp [hmax]
  · -- No overflow case: both EDSL and IR succeed
    have hlt : (state.storage 0).val < 2 ^ 256 - 1 := by omega
    have hno_wrap : ((state.storage 0).val + 1) % (2 ^ 256) = (state.storage 0).val + 1 := by
      apply Nat.mod_eq_of_lt; omega
    simp [show ¬((state.storage 0).val + 1 > 2 ^ 256 - 1) from by omega, hno_wrap]
    intro slot
    by_cases h : slot = 0 <;> simp_all [beq_iff_eq]

/-- SafeCounter.decrement: EDSL execution matches compiled IR execution.

When no underflow (current > 0): both sides succeed, slot 0 = current - 1.
When underflow (current = 0): both sides revert.

EDSL: getStorage → safeSub → requireSomeUint → setStorage
IR:   let count := sload(0)
      if lt(count, 1) { revert("Underflow") }
      sstore(0, sub(count, 1)) → stop -/
theorem safeCounter_decrement_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.SafeCounter.decrement) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2baeceb7
      args := []
    }
    let irState : IRState := {
      vars := []
      storage := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2baeceb7
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = true ∧
        ∀ slot, (s'.storage slot).val = irResult.finalStorage slot
    | .revert _ _ =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = false
    := by
  -- Case split on whether underflow occurs.
  -- safeSub (state.storage 0) 1 = none iff 1 > (state.storage 0).val
  -- i.e., (state.storage 0).val = 0
  simp only [Verity.Examples.SafeCounter.decrement, Verity.Examples.SafeCounter.count,
    Contract.run, getStorage, bind, pure,
    Verity.Stdlib.Math.requireSomeUint, Verity.Stdlib.Math.safeSub,
    Uint256.sub, Uint256.ofNat, require,
    encodeStorage,
    interpretIR, safeCounterIRContract, safeCounterUnderflowRevert,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    Compiler.Constants.evmModulus,
    Uint256.modulus, UINT256_MODULUS,
    setStorage,
    IRState.setVar, IRState.getVar]
  have hv := (state.storage 0).isLt
  simp [Uint256.modulus, UINT256_MODULUS] at hv
  -- Case split: did underflow occur?
  by_cases hzero : (state.storage 0).val = 0
  · -- Underflow case: both EDSL and IR revert
    simp [hzero]
  · -- No underflow case: both EDSL and IR succeed
    have hpos : 0 < (state.storage 0).val := by omega
    have hno_wrap : (state.storage 0).val - 1 < 2 ^ 256 := by omega
    simp [show ¬(1 > (state.storage 0).val) from by omega,
          show ¬((state.storage 0).val < 1 % (2 ^ 256)) from by omega]
    -- The IR sub: (evmModulus + a - 1) % evmModulus = a - 1 when a > 0
    have hsub_mod : ((2 ^ 256 + (state.storage 0).val - 1 % (2 ^ 256)) % (2 ^ 256)) =
        (state.storage 0).val - 1 := by omega
    simp [hsub_mod]
    -- The EDSL sub: since 1 ≤ a, Uint256.sub returns (a - 1) % modulus = a - 1
    have hedsl_sub : (1 % (2 ^ 256)) ≤ (state.storage 0).val := by omega
    simp [hedsl_sub]
    have hedsl_mod : ((state.storage 0).val - 1 % (2 ^ 256)) % (2 ^ 256) = (state.storage 0).val - 1 := by
      omega
    simp [hedsl_mod]
    intro slot
    by_cases h : slot = 0 <;> simp_all [beq_iff_eq]

/-- SafeCounter.getCount: identical to Counter.getCount (no overflow checks needed). -/
theorem safeCounter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.SafeCounter.getCount) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xa87d942c
      args := []
    }
    let irState : IRState := {
      vars := []
      storage := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xa87d942c
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR safeCounterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ slot, (s'.storage slot).val = irResult.finalStorage slot
    | .revert _ _ => True
    := by
  simp [Verity.Examples.SafeCounter.getCount, Verity.Examples.SafeCounter.count,
    Contract.run, getStorage, bind, pure, encodeStorage,
    interpretIR, safeCounterIRContract,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    IRState.setVar, IRState.getVar]

/-! ## Target Theorems: OwnedCounter

OwnedCounter combines two patterns: ownership (Address at slot 0) and
counter (Uint256 at slot 1). This demonstrates multi-slot, mixed-type
storage encoding and access control composition in semantic bridge proofs.

The key challenge is the *mixed encoding*: slot 0 stores an Address
(from `state.storageAddr`), slot 1 stores a Uint256 (from `state.storage`).
We use `encodeOwnedCounterStorage` to merge both into a single `Nat → Nat`.
-/

/-- Encode OwnedCounter storage: slot 0 = owner (Address), slot 1 = count (Uint256). -/
def encodeOwnedCounterStorage (state : ContractState) : Nat → Nat :=
  fun slot =>
    if slot = 0 then (state.storageAddr 0).val
    else (state.storage slot).val

/-- OwnedCounter.getCount: EDSL execution matches compiled IR execution.

EDSL: getStorage ⟨1⟩ → returns state.storage 1
IR:   mstore(0, sload(1)) → return(0, 32)

Both produce: success=true, returnValue = (state.storage 1).val, storage unchanged. -/
theorem ownedCounter_getCount_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.getCount) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xa87d942c
      args := []
    }
    let irState : IRState := {
      vars := []
      storage := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xa87d942c
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ slot, (if slot = 0 then (s'.storageAddr 0).val else (s'.storage slot).val) =
                irResult.finalStorage slot
    | .revert _ _ => True
    := by
  simp [Verity.Examples.OwnedCounter.getCount, Verity.Examples.OwnedCounter.count,
    Contract.run, getStorage, bind, pure, encodeOwnedCounterStorage,
    interpretIR, ownedCounterIRContract,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    IRState.setVar, IRState.getVar]

/-- OwnedCounter.getOwner: EDSL execution matches compiled IR execution.

EDSL: getStorageAddr ⟨0⟩ → returns state.storageAddr 0
IR:   mstore(0, sload(0)) → return(0, 32)

Both produce: success=true, returnValue = (state.storageAddr 0).val. -/
theorem ownedCounter_getOwner_semantic_bridge
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.getOwner) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x893d20e8
      args := []
    }
    let irState : IRState := {
      vars := []
      storage := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x893d20e8
    }
    match edslResult with
    | .success val s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        irResult.returnValue = some val.val ∧
        ∀ slot, (if slot = 0 then (s'.storageAddr 0).val else (s'.storage slot).val) =
                irResult.finalStorage slot
    | .revert _ _ => True
    := by
  simp [Verity.Examples.OwnedCounter.getOwner, Verity.Examples.OwnedCounter.owner,
    Contract.run, getStorageAddr, bind, pure, encodeOwnedCounterStorage,
    interpretIR, ownedCounterIRContract,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    IRState.setVar, IRState.getVar]

/-- OwnedCounter.increment (as owner): EDSL execution matches compiled IR execution.

When the caller IS the owner, both sides update slot 1 to (count + 1) % 2^256.

EDSL: onlyOwner → getStorage 1 → add 1 → setStorage 1
IR:   if iszero(eq(caller(), sload(0))) { revert }
      sstore(1, add(sload(1), 1)) → stop -/
theorem ownedCounter_increment_semantic_bridge
    (state : ContractState) (sender : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.increment) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xd09de08a
      args := []
    }
    let irState : IRState := {
      vars := []
      storage := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xd09de08a
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        ∀ slot, (if slot = 0 then (s'.storageAddr 0).val else (s'.storage slot).val) =
                irResult.finalStorage slot
    | .revert _ _ => True
    := by
  simp [Verity.Examples.OwnedCounter.increment, Verity.Examples.OwnedCounter.count,
    Verity.Examples.OwnedCounter.onlyOwner, Verity.Examples.OwnedCounter.isOwner,
    Verity.Examples.OwnedCounter.owner,
    Contract.run, getStorage, setStorage, getStorageAddr, msgSender, require,
    bind, pure, hOwner, encodeOwnedCounterStorage,
    Uint256.add, Uint256.ofNat, Uint256.modulus, UINT256_MODULUS,
    interpretIR, ownedCounterIRContract, ownedNotOwnerRevert,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    Compiler.Constants.evmModulus,
    IRState.setVar, IRState.getVar]
  intro slot
  by_cases h0 : slot = 0 <;> by_cases h1 : slot = 1 <;> simp_all [beq_iff_eq]

/-- OwnedCounter.decrement (as owner): EDSL execution matches compiled IR execution.

When the caller IS the owner, both sides update slot 1 to sub semantics. -/
theorem ownedCounter_decrement_semantic_bridge
    (state : ContractState) (sender : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.decrement) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0x2baeceb7
      args := []
    }
    let irState : IRState := {
      vars := []
      storage := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0x2baeceb7
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        ∀ slot, (if slot = 0 then (s'.storageAddr 0).val else (s'.storage slot).val) =
                irResult.finalStorage slot
    | .revert _ _ => True
    := by
  have hsub : ∀ (v : Uint256),
      (Uint256.sub v (Uint256.ofNat 1)).val =
        (Compiler.Constants.evmModulus + v.val - (1 % (2 ^ 256))) % Compiler.Constants.evmModulus := by
    intro v
    simp [Uint256.sub, Uint256.ofNat, Uint256.modulus, UINT256_MODULUS, Compiler.Constants.evmModulus]
    have hv := v.isLt
    simp [Uint256.modulus, UINT256_MODULUS] at hv
    by_cases hle : (1 % (2 ^ 256)) ≤ v.val
    · simp [hle]; omega
    · simp [hle]; omega
  simp [Verity.Examples.OwnedCounter.decrement, Verity.Examples.OwnedCounter.count,
    Verity.Examples.OwnedCounter.onlyOwner, Verity.Examples.OwnedCounter.isOwner,
    Verity.Examples.OwnedCounter.owner,
    Contract.run, getStorage, setStorage, getStorageAddr, msgSender, require,
    bind, pure, hOwner, encodeOwnedCounterStorage,
    interpretIR, ownedCounterIRContract, ownedNotOwnerRevert,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    IRState.setVar, IRState.getVar, hsub]
  intro slot
  by_cases h0 : slot = 0 <;> by_cases h1 : slot = 1 <;> simp_all [beq_iff_eq]

/-- OwnedCounter.transferOwnership (as owner): EDSL execution matches compiled IR execution.

When the caller IS the owner, both sides update slot 0 to newOwner.val. -/
theorem ownedCounter_transferOwnership_semantic_bridge
    (state : ContractState) (sender : Address) (newOwner : Address)
    (hOwner : sender = state.storageAddr 0) :
    let edslResult := Contract.run (Verity.Examples.OwnedCounter.transferOwnership newOwner)
        { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xf2fde38b
      args := [newOwner.val]
    }
    let irState : IRState := {
      vars := []
      storage := encodeOwnedCounterStorage state
      memory := fun _ => 0
      calldata := [newOwner.val]
      returnValue := none
      sender := sender.val
      selector := 0xf2fde38b
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR ownedCounterIRContract tx irState
        irResult.success = true ∧
        ∀ slot, (if slot = 0 then (s'.storageAddr 0).val else (s'.storage slot).val) =
                irResult.finalStorage slot
    | .revert _ _ => True
    := by
  have haddr : newOwner.val &&& addressMask = newOwner.val := by
    simp only [addressMask]
    have hlt : newOwner.val < 2 ^ 160 := by
      have := newOwner.isLt; simp [ADDRESS_MODULUS] at this; exact this
    calc newOwner.val &&& (2 ^ 160 - 1)
        = newOwner.val % 2 ^ 160 := by
          simpa using (Nat.and_two_pow_sub_one_eq_mod newOwner.val 160)
      _ = newOwner.val := Nat.mod_eq_of_lt hlt
  simp [Verity.Examples.OwnedCounter.transferOwnership,
    Verity.Examples.OwnedCounter.onlyOwner, Verity.Examples.OwnedCounter.isOwner,
    Verity.Examples.OwnedCounter.owner,
    Contract.run, getStorageAddr, setStorageAddr, msgSender, require,
    bind, pure, hOwner, encodeOwnedCounterStorage,
    interpretIR, ownedCounterIRContract, ownedNotOwnerRevert,
    execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
    evalBuiltinCallWithBackend, defaultBuiltinBackend, evalBuiltinCall,
    calldataloadWord,
    Compiler.Proofs.abstractLoadStorageOrMapping,
    Compiler.Proofs.abstractStoreStorageOrMapping,
    Compiler.Proofs.storageAsMappings,
    IRState.setVar, IRState.getVar, haddr]
  intro slot
  by_cases h0 : slot = 0 <;> simp_all [beq_iff_eq]

/-! ## Composed End-to-End: EDSL → IR → Yul

These theorems compose the EDSL ≡ IR results (above) with the generic
Layer 3 result (IR ≡ Yul from EndToEnd.lean) to obtain the full chain:

  EDSL(f).run state ≡ Yul(compile(spec))(f, state)

This is the *concrete* composition target of Issue #998. Once the Yul
builtins ≡ EVMYulLean bridge (ArithmeticProfile.lean, EndToEnd.lean) is
also composed, we have: EDSL ≡ EVMYulLean(compile(spec)).

The composition chain for each function f:
  1. EDSL(f).run state ≡ IR(compile(f.spec)).exec irState
     (this file, via direct simp unfolding)
  2. IR(compile(spec)).exec ≡ Yul(emitYul(compile(spec))).exec
     (EndToEnd.lean, via `layer3_contract_preserves_semantics`)
  3. Yul builtins ≡ EVMYulLean builtins
     (ArithmeticProfile.lean + EndToEnd.lean `pure_*_bridge`)
-/

/-- SimpleStorage.store full chain: EDSL → IR → Yul.

When the EDSL store succeeds:
1. The IR execution also succeeds with matching storage (from `simpleStorage_store_semantic_bridge`)
2. The Yul execution matches the IR execution (from `layer3_contract_preserves_semantics`)

This eliminates `interpretSpec` completely for SimpleStorage.store:
the trust chain is now EDSL → IR → Yul, all machine-checked. -/
theorem simpleStorage_store_edsl_to_yul
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
        -- Layer 1+2: EDSL ≡ IR
        let irResult := interpretIR simpleStorageIRContract tx irState
        irResult.success = true ∧
        (∀ slot, (s'.storage slot).val = irResult.finalStorage slot) ∧
        -- Layer 3: IR ≡ Yul
        Compiler.Proofs.YulGeneration.resultsMatch
          (interpretIR simpleStorageIRContract tx irState)
          (interpretYulFromIR simpleStorageIRContract tx irState)
    | .revert _ _ => True
    := by
  -- Compose the EDSL ≡ IR proof with the IR ≡ Yul proof.
  have h_edsl_ir := simpleStorage_store_semantic_bridge state sender value
  have h_ir_yul := Compiler.Proofs.EndToEnd.layer3_contract_preserves_semantics
    simpleStorageIRContract
    { sender := sender.val, functionSelector := 0x6057361d, args := [value.val] }
    { vars := [], storage := encodeStorage state, memory := fun _ => 0,
      calldata := [value.val], returnValue := none, sender := sender.val, selector := 0x6057361d }
    (by norm_num [selectorModulus])
    rfl
    rfl
  -- The EDSL result determines the case split
  simp only [Verity.Examples.store, Verity.Examples.storedData, Contract.run,
    setStorage, bind] at h_edsl_ir ⊢
  exact ⟨h_edsl_ir.1, h_edsl_ir.2, h_ir_yul⟩

/-- SimpleStorage.retrieve full chain: EDSL → IR → Yul. -/
theorem simpleStorage_retrieve_edsl_to_yul
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
        (∀ slot, (s'.storage slot).val = irResult.finalStorage slot) ∧
        Compiler.Proofs.YulGeneration.resultsMatch
          (interpretIR simpleStorageIRContract tx irState)
          (interpretYulFromIR simpleStorageIRContract tx irState)
    | .revert _ _ => True
    := by
  have h_edsl_ir := simpleStorage_retrieve_semantic_bridge state sender
  have h_ir_yul := Compiler.Proofs.EndToEnd.layer3_contract_preserves_semantics
    simpleStorageIRContract
    { sender := sender.val, functionSelector := 0x2e64cec1, args := [] }
    { vars := [], storage := encodeStorage state, memory := fun _ => 0,
      calldata := [], returnValue := none, sender := sender.val, selector := 0x2e64cec1 }
    (by norm_num [selectorModulus])
    rfl
    rfl
  simp only [Verity.Examples.retrieve, Verity.Examples.storedData, Contract.run,
    getStorage, bind, pure] at h_edsl_ir ⊢
  exact ⟨h_edsl_ir.1, h_edsl_ir.2.1, h_edsl_ir.2.2, h_ir_yul⟩

/-- Counter.increment full chain: EDSL → IR → Yul. -/
theorem counter_increment_edsl_to_yul
    (state : ContractState) (sender : Address) :
    let edslResult := Contract.run (Verity.Examples.Counter.increment) { state with sender := sender }
    let tx : IRTransaction := {
      sender := sender.val
      functionSelector := 0xd09de08a
      args := []
    }
    let irState : IRState := {
      vars := []
      storage := encodeStorage state
      memory := fun _ => 0
      calldata := []
      returnValue := none
      sender := sender.val
      selector := 0xd09de08a
    }
    match edslResult with
    | .success _ s' =>
        let irResult := interpretIR counterIRContract tx irState
        irResult.success = true ∧
        (∀ slot, (s'.storage slot).val = irResult.finalStorage slot) ∧
        Compiler.Proofs.YulGeneration.resultsMatch
          (interpretIR counterIRContract tx irState)
          (interpretYulFromIR counterIRContract tx irState)
    | .revert _ _ => True
    := by
  have h_edsl_ir := counter_increment_semantic_bridge state sender
  have h_ir_yul := Compiler.Proofs.EndToEnd.layer3_contract_preserves_semantics
    counterIRContract
    { sender := sender.val, functionSelector := 0xd09de08a, args := [] }
    { vars := [], storage := encodeStorage state, memory := fun _ => 0,
      calldata := [], returnValue := none, sender := sender.val, selector := 0xd09de08a }
    (by norm_num [selectorModulus])
    rfl
    rfl
  simp only [Verity.Examples.Counter.increment, Verity.Examples.Counter.count, Contract.run,
    getStorage, setStorage, bind,
    Uint256.add, Uint256.ofNat] at h_edsl_ir ⊢
  exact ⟨h_edsl_ir.1, h_edsl_ir.2, h_ir_yul⟩

end Compiler.Proofs.SemanticBridge
