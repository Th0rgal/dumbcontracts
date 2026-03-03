import Compiler.Constants
import Compiler.Proofs.MappingSlot
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter

namespace Compiler.Proofs.YulGeneration

open Compiler.Proofs
export Compiler.Constants (evmModulus selectorModulus selectorShift)

def selectorWord (selector : Nat) : Nat :=
  (selector % selectorModulus) * (2 ^ selectorShift)

def calldataloadWord (selector : Nat) (calldata : List Nat) (offset : Nat) : Nat :=
  if offset = 0 then
    selectorWord selector
  else if offset < 4 then
    0
  else
    let wordOffset := offset - 4
    if wordOffset % 32 != 0 then
      0
    else
      let idx := wordOffset / 32
      calldata.getD idx 0 % evmModulus

def evalBuiltinCall
    (storage : Nat → Nat)
    (sender : Nat)
    (selector : Nat)
    (calldata : List Nat)
    (func : String)
    (argVals : List Nat) : Option Nat :=
  if func = "mappingSlot" then
    match argVals with
    | [base, key] => some (Compiler.Proofs.abstractMappingSlot base key)
    | _ => none
  else if func = "sload" then
    match argVals with
    | [slot] => some (Compiler.Proofs.abstractLoadStorageOrMapping storage slot)
    | _ => none
  else if func = "add" then
    match argVals with
    | [a, b] => some ((a + b) % evmModulus)
    | _ => none
  else if func = "sub" then
    match argVals with
    | [a, b] => some ((evmModulus + a - b) % evmModulus)
    | _ => none
  else if func = "mul" then
    match argVals with
    | [a, b] => some ((a * b) % evmModulus)
    | _ => none
  else if func = "div" then
    match argVals with
    | [a, b] => if b = 0 then some 0 else some (a / b)
    | _ => none
  else if func = "mod" then
    match argVals with
    | [a, b] => if b = 0 then some 0 else some (a % b)
    | _ => none
  else if func = "lt" then
    match argVals with
    | [a, b] => some (if a < b then 1 else 0)
    | _ => none
  else if func = "gt" then
    match argVals with
    | [a, b] => some (if a > b then 1 else 0)
    | _ => none
  else if func = "eq" then
    match argVals with
    | [a, b] => some (if a = b then 1 else 0)
    | _ => none
  else if func = "iszero" then
    match argVals with
    | [a] => some (if a = 0 then 1 else 0)
    | _ => none
  else if func = "and" then
    match argVals with
    | [a, b] => some (a &&& b)
    | _ => none
  else if func = "or" then
    match argVals with
    | [a, b] => some (a ||| b)
    | _ => none
  else if func = "xor" then
    match argVals with
    | [a, b] => some (Nat.xor a b)
    | _ => none
  else if func = "not" then
    match argVals with
    | [a] => some (Nat.xor a (evmModulus - 1))
    | _ => none
  else if func = "shl" then
    match argVals with
    | [shift, value] => some ((value * (2 ^ shift)) % evmModulus)
    | _ => none
  else if func = "shr" then
    match argVals with
    | [shift, value] => some (value / (2 ^ shift))
    | _ => none
  else if func = "caller" then
    match argVals with
    | [] => some sender
    | _ => none
  else if func = "calldataload" then
    match argVals with
    | [offset] => some (calldataloadWord selector calldata offset)
    | _ => none
  else if func = "callvalue" then
    match argVals with
    | [] => some 0
    | _ => none
  else if func = "calldatasize" then
    match argVals with
    | [] => some (4 + calldata.length * 32)
    | _ => none
  else
    none

/-! ## Per-Builtin Simp Lemmas

These lemmas let `simp` reduce specific `evalBuiltinCall` invocations without
unfolding the entire 20-branch if-then-else chain. This is necessary because
the full chain exceeds heartbeat limits in large proof terms (Issue #1089).

Each lemma reduces to `rfl` after `simp [evalBuiltinCall]` resolves the
string comparisons in the if-chain. -/

@[simp] theorem evalBuiltinCall_mappingSlot (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (base key : Nat) :
    evalBuiltinCall storage sender selector calldata "mappingSlot" [base, key] =
      some (Compiler.Proofs.abstractMappingSlot base key) := by
  simp [evalBuiltinCall]

@[simp] theorem evalBuiltinCall_sload (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (slot : Nat) :
    evalBuiltinCall storage sender selector calldata "sload" [slot] =
      some (Compiler.Proofs.abstractLoadStorageOrMapping storage slot) := by
  simp [evalBuiltinCall]

@[simp] theorem evalBuiltinCall_add (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "add" [a, b] =
      some ((a + b) % evmModulus) := by
  simp [evalBuiltinCall]

@[simp] theorem evalBuiltinCall_sub (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "sub" [a, b] =
      some ((evmModulus + a - b) % evmModulus) := by
  simp [evalBuiltinCall]

@[simp] theorem evalBuiltinCall_mul (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "mul" [a, b] =
      some ((a * b) % evmModulus) := by
  simp [evalBuiltinCall]

@[simp] theorem evalBuiltinCall_lt (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "lt" [a, b] =
      some (if a < b then 1 else 0) := by
  simp [evalBuiltinCall]

@[simp] theorem evalBuiltinCall_gt (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "gt" [a, b] =
      some (if a > b then 1 else 0) := by
  simp [evalBuiltinCall]

@[simp] theorem evalBuiltinCall_eq (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "eq" [a, b] =
      some (if a = b then 1 else 0) := by
  simp [evalBuiltinCall]

@[simp] theorem evalBuiltinCall_iszero (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCall storage sender selector calldata "iszero" [a] =
      some (if a = 0 then 1 else 0) := by
  simp [evalBuiltinCall]

@[simp] theorem evalBuiltinCall_and (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCall storage sender selector calldata "and" [a, b] =
      some (a &&& b) := by
  simp [evalBuiltinCall]

@[simp] theorem evalBuiltinCall_caller (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) :
    evalBuiltinCall storage sender selector calldata "caller" [] =
      some sender := by
  simp [evalBuiltinCall]

@[simp] theorem evalBuiltinCall_calldataload (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (offset : Nat) :
    evalBuiltinCall storage sender selector calldata "calldataload" [offset] =
      some (calldataloadWord selector calldata offset) := by
  simp [evalBuiltinCall]

@[simp] theorem evalBuiltinCall_callvalue (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) :
    evalBuiltinCall storage sender selector calldata "callvalue" [] =
      some 0 := by
  simp [evalBuiltinCall]

@[simp] theorem evalBuiltinCall_calldatasize (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) :
    evalBuiltinCall storage sender selector calldata "calldatasize" [] =
      some (4 + calldata.length * 32) := by
  simp [evalBuiltinCall]

inductive BuiltinBackend where
  | verity
  | evmYulLean
  deriving DecidableEq, Repr

abbrev defaultBuiltinBackend : BuiltinBackend := .verity

def evalBuiltinCallWithBackend
    (backend : BuiltinBackend)
    (storage : Nat → Nat)
    (sender : Nat)
    (selector : Nat)
    (calldata : List Nat)
    (func : String)
    (argVals : List Nat) : Option Nat :=
  match backend with
  | .verity =>
      evalBuiltinCall storage sender selector calldata func argVals
  | .evmYulLean =>
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean
        storage sender selector calldata func argVals

@[simp] theorem evalBuiltinCallWithBackend_verity
    (storage : Nat → Nat) (sender selector : Nat) (calldata : List Nat) (func : String) (argVals : List Nat) :
    evalBuiltinCallWithBackend .verity storage sender selector calldata func argVals =
      evalBuiltinCall storage sender selector calldata func argVals := by
  simp [evalBuiltinCallWithBackend]

@[simp] theorem defaultBuiltinBackend_eq : defaultBuiltinBackend = BuiltinBackend.verity := rfl

end Compiler.Proofs.YulGeneration
