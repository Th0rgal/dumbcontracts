import Compiler.Proofs.MappingEncoding
import EvmYul

namespace Compiler.Proofs

/-!
Mapping slot abstraction used by proof interpreters.

The active backend is keccak-faithful (`solidityMappingSlot`), while the tagged
encoding model from `MappingEncoding.lean` is retained only for transitional
reference and compatibility scaffolding.
-/

/-- Mapping-slot backend chosen for proof semantics. -/
inductive MappingSlotBackend where
  | tagged
  | keccak
  deriving DecidableEq, Repr

/--
Active proof-model backend.

`keccak` is the active, EVM-faithful mapping-slot model.
-/
def activeMappingSlotBackend : MappingSlotBackend := .keccak

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
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (baseSlot key : Nat) : Nat :=
  match activeMappingSlotBackend with
  | .tagged => mappings baseSlot key
  | .keccak => storage (solidityMappingSlot baseSlot key)

/-- Write a mapping entry directly from base slot and key. -/
def abstractStoreMappingEntry
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (baseSlot key value : Nat) : (Nat → Nat) × (Nat → Nat → Nat) :=
  match activeMappingSlotBackend with
  | .tagged =>
      (storage, fun b k => if b = baseSlot ∧ k = key then value else mappings b k)
  | .keccak =>
      (fun s => if s = solidityMappingSlot baseSlot key then value else storage s, mappings)

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

@[simp] theorem abstractMappingSlot_eq_solidity (baseSlot key : Nat) :
    abstractMappingSlot baseSlot key = solidityMappingSlot baseSlot key := rfl

@[simp] theorem abstractMappingTag_eq_zero :
    abstractMappingTag = 0 := rfl

@[simp] theorem abstractDecodeMappingSlot_eq_none (slot : Nat) :
    abstractDecodeMappingSlot slot = none := rfl

@[simp] theorem activeMappingSlotBackend_eq_keccak :
    activeMappingSlotBackend = .keccak := rfl

@[simp] theorem activeMappingSlotBackendIsEvmFaithful_eq_true :
    activeMappingSlotBackendIsEvmFaithful = true := rfl

@[simp] theorem abstractNestedMappingSlot_eq_solidityNested (baseSlot key1 key2 : Nat) :
    abstractNestedMappingSlot baseSlot key1 key2 =
      solidityMappingSlot (solidityMappingSlot baseSlot key1) key2 := by
  simp [abstractNestedMappingSlot]

@[simp] theorem abstractLoadMappingEntry_eq
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (baseSlot key : Nat) :
    abstractLoadMappingEntry storage mappings baseSlot key = storage (solidityMappingSlot baseSlot key) := rfl

@[simp] theorem abstractStoreMappingEntry_eq
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (baseSlot key value : Nat) :
    abstractStoreMappingEntry storage mappings baseSlot key value =
      (fun s => if s = solidityMappingSlot baseSlot key then value else storage s, mappings) := rfl

@[simp] theorem abstractLoadStorageOrMapping_eq
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (slot : Nat) :
    abstractLoadStorageOrMapping storage mappings slot = storage slot := by
  simp [abstractLoadStorageOrMapping]

@[simp] theorem abstractStoreStorageOrMapping_eq
    (storage : Nat → Nat)
    (mappings : Nat → Nat → Nat)
    (slot value : Nat) :
    abstractStoreStorageOrMapping storage mappings slot value =
      (fun s => if s = slot then value else storage s, mappings) := by
  simp [abstractStoreStorageOrMapping]

end Compiler.Proofs
