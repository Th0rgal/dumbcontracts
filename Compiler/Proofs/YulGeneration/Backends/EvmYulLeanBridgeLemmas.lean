import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgePredicates
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBuiltinSemantics
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeLowering
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanPureBuiltinLemmas
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanSignedArithSpec

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Proofs.IRGeneration (IRStorageWord IRStorageSlot)

/-!
Native EVMYulLean builtin routing facts.

The historical reference-oracle comparison layer has been removed. These lemmas
record only the native `.evmYulLean` dispatch surface used by the public
EndToEnd target and by reporting scripts that audit available builtin coverage.
-/

@[simp] theorem evalBuiltinCall_add_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "add" [a, b] =
      evalPureBuiltinViaEvmYulLean "add" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_sub_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "sub" [a, b] =
      evalPureBuiltinViaEvmYulLean "sub" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_mul_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "mul" [a, b] =
      evalPureBuiltinViaEvmYulLean "mul" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_div_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "div" [a, b] =
      evalPureBuiltinViaEvmYulLean "div" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_mod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "mod" [a, b] =
      evalPureBuiltinViaEvmYulLean "mod" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_addmod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b n : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "addmod" [a, b, n] =
      evalPureBuiltinViaEvmYulLean "addmod" [a, b, n] := by
  rfl

@[simp] theorem evalBuiltinCall_mulmod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b n : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "mulmod" [a, b, n] =
      evalPureBuiltinViaEvmYulLean "mulmod" [a, b, n] := by
  rfl

@[simp] theorem evalBuiltinCall_exp_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "exp" [a, b] =
      evalPureBuiltinViaEvmYulLean "exp" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_sdiv_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "sdiv" [a, b] =
      evalPureBuiltinViaEvmYulLean "sdiv" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_smod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "smod" [a, b] =
      evalPureBuiltinViaEvmYulLean "smod" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_lt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "lt" [a, b] =
      evalPureBuiltinViaEvmYulLean "lt" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_gt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "gt" [a, b] =
      evalPureBuiltinViaEvmYulLean "gt" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_slt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "slt" [a, b] =
      evalPureBuiltinViaEvmYulLean "slt" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_sgt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "sgt" [a, b] =
      evalPureBuiltinViaEvmYulLean "sgt" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_eq_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "eq" [a, b] =
      evalPureBuiltinViaEvmYulLean "eq" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_iszero_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "iszero" [a] =
      evalPureBuiltinViaEvmYulLean "iszero" [a] := by
  rfl

@[simp] theorem evalBuiltinCall_and_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "and" [a, b] =
      evalPureBuiltinViaEvmYulLean "and" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_or_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "or" [a, b] =
      evalPureBuiltinViaEvmYulLean "or" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_xor_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "xor" [a, b] =
      evalPureBuiltinViaEvmYulLean "xor" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCall_not_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "not" [a] =
      evalPureBuiltinViaEvmYulLean "not" [a] := by
  rfl

@[simp] theorem evalBuiltinCall_shl_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "shl" [shift, value] =
      evalPureBuiltinViaEvmYulLean "shl" [shift, value] := by
  rfl

@[simp] theorem evalBuiltinCall_shr_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "shr" [shift, value] =
      evalPureBuiltinViaEvmYulLean "shr" [shift, value] := by
  rfl

@[simp] theorem evalBuiltinCall_sar_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "sar" [shift, value] =
      evalPureBuiltinViaEvmYulLean "sar" [shift, value] := by
  rfl

@[simp] theorem evalBuiltinCall_signextend_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (byteIdx value : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "signextend" [byteIdx, value] =
      evalPureBuiltinViaEvmYulLean "signextend" [byteIdx, value] := by
  rfl

@[simp] theorem evalBuiltinCall_byte_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (i x : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "byte" [i, x] =
      evalPureBuiltinViaEvmYulLean "byte" [i, x] := by
  rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_sload (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "sload" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_caller (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "caller" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_address (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "address" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_callvalue (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "callvalue" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_timestamp (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "timestamp" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_number (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "number" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_chainid (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "chainid" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_blobbasefee (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "blobbasefee" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_calldataload (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "calldataload" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_calldatasize (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "calldatasize" args = none := by
  cases args <;> rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_mappingSlot (args : List Nat) :
    evalPureBuiltinViaEvmYulLean "mappingSlot" args = none := by
  cases args with
  | nil => rfl
  | cons a t => cases t with
    | nil => rfl
    | cons b t2 => rfl

@[simp] theorem evalBuiltinCall_calldataload_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (offset : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "calldataload" [offset] =
      some (Compiler.Proofs.YulGeneration.calldataloadWord selector calldata offset) := by
  rfl

@[simp] theorem evalBuiltinCall_sload_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (slot : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "sload" [slot] =
      some (storage (IRStorageSlot.ofNat slot)).toNat := by
  rfl

@[simp] theorem evalBuiltinCall_mappingSlot_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (base key : Nat) :
    evalBuiltinCallViaEvmYulLean storage sender selector calldata "mappingSlot" [base, key] =
      some (Compiler.Proofs.abstractMappingSlot base key) := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_add_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "add" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "add" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_sub_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "sub" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "sub" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_mul_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "mul" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "mul" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_div_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "div" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "div" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_mod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "mod" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "mod" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_eq_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "eq" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "eq" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_iszero_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "iszero" [a] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "iszero" [a] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_lt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "lt" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "lt" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_gt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "gt" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "gt" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_and_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "and" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "and" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_or_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "or" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "or" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_xor_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "xor" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "xor" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_not_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "not" [a] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "not" [a] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_shl_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "shl" [shift, value] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "shl" [shift, value] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_shr_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "shr" [shift, value] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "shr" [shift, value] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_addmod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b n : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "addmod" [a, b, n] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "addmod" [a, b, n] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_mulmod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b n : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "mulmod" [a, b, n] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "mulmod" [a, b, n] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_byte_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (i x : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "byte" [i, x] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "byte" [i, x] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_slt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "slt" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "slt" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_sgt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "sgt" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "sgt" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_exp_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "exp" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "exp" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_sdiv_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "sdiv" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "sdiv" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_smod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "smod" [a, b] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "smod" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_sar_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (shift value : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "sar" [shift, value] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "sar" [shift, value] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackend_evmYulLean_signextend_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender selector : Nat) (calldata : List Nat) (byteIdx value : Nat) :
    evalBuiltinCallWithBackend .evmYulLean storage sender selector calldata "signextend" [byteIdx, value] =
      evalBuiltinCallViaEvmYulLean storage sender selector calldata "signextend" [byteIdx, value] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_add_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "add" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata "add" [a, b] := by
  rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_sub_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "sub" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "sub" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_mul_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "mul" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "mul" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_div_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "div" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "div" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_mod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "mod" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "mod" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_eq_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "eq" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "eq" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_iszero_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "iszero" [a] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "iszero" [a] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_lt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "lt" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "lt" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_gt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "gt" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "gt" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_slt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "slt" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "slt" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_sgt_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "sgt" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "sgt" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_and_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "and" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "and" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_or_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "or" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "or" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_xor_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "xor" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "xor" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_not_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "not" [a] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "not" [a] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_shl_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "shl" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "shl" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_shr_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "shr" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "shr" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_addmod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b c : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "addmod" [a, b, c] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "addmod" [a, b, c] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_mulmod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b c : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "mulmod" [a, b, c] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "mulmod" [a, b, c] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_byte_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "byte" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "byte" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_exp_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "exp" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "exp" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_sdiv_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "sdiv" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "sdiv" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_smod_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "smod" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "smod" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_sar_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "sar" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "sar" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_signextend_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "signextend" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "signextend" [a, b] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_sload_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "sload" [a] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "sload" [a] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_caller_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat) (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "caller" [] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "caller" [] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_address_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat) (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "address" [] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "address" [] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_callvalue_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat) (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "callvalue" [] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "callvalue" [] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_timestamp_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat) (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "timestamp" [] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "timestamp" [] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_number_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat) (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "number" [] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "number" [] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_blobbasefee_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat) (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "blobbasefee" [] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "blobbasefee" [] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_chainid_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat) (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "chainid" [] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "chainid" [] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_calldataload_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "calldataload" [a] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "calldataload" [a] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_calldatasize_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat) (calldata : List Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "calldatasize" [] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "calldatasize" [] := by rfl

@[simp] theorem evalBuiltinCallWithBackendContext_evmYulLean_mappingSlot_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (a b : Nat) :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "mappingSlot" [a, b] =
    evalBuiltinCallWithEvmYulLeanContext storage sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector calldata "mappingSlot" [a, b] := by rfl

private theorem evalBuiltinCallWithBackendContext_evmYulLean_pure_bridge
    (storage : IRStorageSlot → IRStorageWord) (sender msgValue thisAddress blockTimestamp blockNumber chainId blobBaseFee selector : Nat)
    (calldata : List Nat) (func : String) (argVals : List Nat)
    (hCaller : func ≠ "caller")
    (hAddress : func ≠ "address")
    (hCallvalue : func ≠ "callvalue")
    (hTimestamp : func ≠ "timestamp")
    (hNumber : func ≠ "number")
    (hChainid : func ≠ "chainid")
    (hBlobbasefee : func ≠ "blobbasefee")
    (hCalldatasize : func ≠ "calldatasize") :
    evalBuiltinCallWithBackendContext .evmYulLean storage sender msgValue thisAddress
      blockTimestamp blockNumber chainId blobBaseFee selector calldata func argVals =
    evalBuiltinCallViaEvmYulLean storage sender selector calldata func argVals := by
  simp [evalBuiltinCallWithBackendContext, evalBuiltinCallWithEvmYulLeanContext, hCaller,
    hAddress, hCallvalue, hTimestamp, hNumber, hChainid, hBlobbasefee, hCalldatasize]

end Compiler.Proofs.YulGeneration.Backends
