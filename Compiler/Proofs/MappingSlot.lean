import Compiler.Proofs.MappingEncoding
import EvmYul

namespace Compiler.Proofs

/-!
Mapping slot abstraction used by proof interpreters.

Today this delegates to the tagged encoding model in `MappingEncoding.lean`.
When issue #259 is implemented, only this module should need backend changes.
-/

/-- Mapping-slot backend chosen for proof semantics. -/
inductive MappingSlotBackend where
  | tagged
  | keccak
  deriving DecidableEq, Repr

/--
Active proof-model backend.

`tagged` is the current verification-level model. `keccak` is reserved for the
issue #259 backend migration.
-/
def activeMappingSlotBackend : MappingSlotBackend := .tagged

/-- Whether the active backend matches EVM keccak-derived slot layout exactly. -/
def activeMappingSlotBackendIsEvmFaithful : Bool :=
  match activeMappingSlotBackend with
  | .tagged => false
  | .keccak => true

/-- ABI-encode `(key, baseSlot)` as two 32-byte words (Solidity mapping convention). -/
def abiEncodeMappingSlot (baseSlot key : Nat) : ByteArray :=
  let keyWord : EvmYul.UInt256 := .ofNat key
  let baseSlotWord : EvmYul.UInt256 := .ofNat baseSlot
  keyWord.toByteArray ++ baseSlotWord.toByteArray

/-- Solidity mapping storage slot derivation: `keccak256(abi.encode(key, baseSlot))`. -/
def solidityMappingSlot (baseSlot key : Nat) : Nat :=
  EvmYul.fromByteArrayBigEndian (ffi.KEC (abiEncodeMappingSlot baseSlot key))

/-- Active proof-model mapping slot encoding backend. -/
def abstractMappingSlot (baseSlot key : Nat) : Nat :=
  match activeMappingSlotBackend with
  | .tagged => encodeMappingSlot baseSlot key
  | .keccak => solidityMappingSlot baseSlot key

/-- Active proof-model mapping slot tag sentinel (backend-specific). -/
def abstractMappingTag : Nat :=
  match activeMappingSlotBackend with
  | .tagged => mappingTag
  | .keccak => 0

/-- Active proof-model mapping slot decoder backend. -/
def abstractDecodeMappingSlot (slot : Nat) : Option (Nat × Nat) :=
  match activeMappingSlotBackend with
  | .tagged => decodeMappingSlot slot
  | .keccak => none

/-- Active proof-model nested mapping slot helper. -/
def abstractNestedMappingSlot (baseSlot key1 key2 : Nat) : Nat :=
  abstractMappingSlot (abstractMappingSlot baseSlot key1) key2

/-- Read a mapping entry directly from base slot and key. -/
def abstractLoadMappingEntry
    (mappings : Nat → Nat → Nat)
    (baseSlot key : Nat) : Nat :=
  mappings baseSlot key

/-- Write a mapping entry directly from base slot and key. -/
def abstractStoreMappingEntry
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (baseSlot key value : Nat) : (Nat → Nat) × (Nat → Nat → Nat) :=
  (storage, fun b k => if b = baseSlot ∧ k = key then value else mappings b k)

/-- Read through the active mapping-slot backend from split storage/mapping tables. -/
def abstractLoadStorageOrMapping
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (slot : Nat) : Nat :=
  match abstractDecodeMappingSlot slot with
  | some (baseSlot, key) => mappings baseSlot key
  | none => storage slot

/-- Write through the active mapping-slot backend to split storage/mapping tables. -/
def abstractStoreStorageOrMapping
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (slot value : Nat) : (Nat → Nat) × (Nat → Nat → Nat) :=
  match abstractDecodeMappingSlot slot with
  | some (baseSlot, key) =>
      (storage, fun b k => if b = baseSlot ∧ k = key then value else mappings b k)
  | none =>
      (fun s => if s = slot then value else storage s, mappings)

@[simp] theorem abstractMappingSlot_eq_encode (baseSlot key : Nat) :
    abstractMappingSlot baseSlot key = encodeMappingSlot baseSlot key := rfl

@[simp] theorem abstractMappingTag_eq_mappingTag :
    abstractMappingTag = mappingTag := rfl

@[simp] theorem abstractDecodeMappingSlot_eq_decode (slot : Nat) :
    abstractDecodeMappingSlot slot = decodeMappingSlot slot := rfl

@[simp] theorem activeMappingSlotBackend_eq_tagged :
    activeMappingSlotBackend = .tagged := rfl

@[simp] theorem activeMappingSlotBackendIsEvmFaithful_eq_false :
    activeMappingSlotBackendIsEvmFaithful = false := rfl

@[simp] theorem abstractNestedMappingSlot_eq_encodeNested (baseSlot key1 key2 : Nat) :
    abstractNestedMappingSlot baseSlot key1 key2 = encodeNestedMappingSlot baseSlot key1 key2 := by
  simp [abstractNestedMappingSlot, encodeNestedMappingSlot]

@[simp] theorem abstractLoadMappingEntry_eq
    (mappings : Nat → Nat → Nat)
    (baseSlot key : Nat) :
    abstractLoadMappingEntry mappings baseSlot key = mappings baseSlot key := rfl

@[simp] theorem abstractStoreMappingEntry_eq
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (baseSlot key value : Nat) :
    abstractStoreMappingEntry storage mappings baseSlot key value =
      (storage, fun b k => if b = baseSlot ∧ k = key then value else mappings b k) := rfl

@[simp] theorem abstractLoadStorageOrMapping_eq
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (slot : Nat) :
    abstractLoadStorageOrMapping storage mappings slot =
      match decodeMappingSlot slot with
      | some (baseSlot, key) => mappings baseSlot key
      | none => storage slot := by
  simp [abstractLoadStorageOrMapping]

@[simp] theorem abstractStoreStorageOrMapping_eq
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (slot value : Nat) :
    abstractStoreStorageOrMapping storage mappings slot value =
      match decodeMappingSlot slot with
      | some (baseSlot, key) =>
          (storage, fun b k => if b = baseSlot ∧ k = key then value else mappings b k)
      | none =>
          (fun s => if s = slot then value else storage s, mappings) := by
  simp [abstractStoreStorageOrMapping]

end Compiler.Proofs
