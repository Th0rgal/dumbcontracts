/-
  SimpleStorage: Basic Correctness Proofs

  This file contains proofs of basic correctness properties for SimpleStorage.

  Status: Initial proofs with some axioms. These establish the foundation
  for more rigorous proofs as we develop proof tactics.
-/

import DumbContracts.Core
import DumbContracts.Examples.SimpleStorage
import DumbContracts.Specs.SimpleStorage.Spec
import DumbContracts.Specs.SimpleStorage.Invariants

namespace DumbContracts.Proofs.SimpleStorage

open DumbContracts
open DumbContracts.Examples
open DumbContracts.Specs.SimpleStorage

-- Lemma: setStorage updates the correct slot
theorem setStorage_updates_slot (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let s' := (setStorage slot value).run s |>.2
  s'.storage 0 = value := by
  -- Unfold definitions
  simp [setStorage]

-- Lemma: getStorage reads from the correct slot
theorem getStorage_reads_slot (s : ContractState) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let result := (getStorage slot).run s |>.1
  result = s.storage 0 := by
  simp [getStorage]

-- Lemma: setStorage preserves other slots
theorem setStorage_preserves_other_slots (s : ContractState) (value : Uint256) (n : Nat)
  (h : n ≠ 0) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let s' := (setStorage slot value).run s |>.2
  s'.storage n = s.storage n := by
  simp [setStorage, h]

-- Lemma: setStorage preserves context (sender, thisAddress)
theorem setStorage_preserves_sender (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let s' := (setStorage slot value).run s |>.2
  s'.sender = s.sender := by
  simp [setStorage]

theorem setStorage_preserves_address (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let s' := (setStorage slot value).run s |>.2
  s'.thisAddress = s.thisAddress := by
  simp [setStorage]

-- Lemma: setStorage preserves address storage
theorem setStorage_preserves_addr_storage (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let s' := (setStorage slot value).run s |>.2
  s'.storageAddr = s.storageAddr := by
  simp [setStorage]

-- Lemma: setStorage preserves mapping storage
theorem setStorage_preserves_map_storage (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let s' := (setStorage slot value).run s |>.2
  s'.storageMap = s.storageMap := by
  simp [setStorage]

-- Main theorem: store meets its specification
theorem store_meets_spec (s : ContractState) (value : Uint256) :
  let s' := (store value).run s |>.2
  store_spec value s s' := by
  simp [store, storedData, store_spec]
  constructor
  · -- s'.storage 0 = value
    exact setStorage_updates_slot s value
  constructor
  · -- Other slots unchanged
    intro slot h_neq
    exact setStorage_preserves_other_slots s value slot h_neq
  constructor
  · -- sender unchanged
    exact setStorage_preserves_sender s value
  constructor
  · -- thisAddress unchanged
    exact setStorage_preserves_address s value
  constructor
  · -- storageAddr unchanged
    exact setStorage_preserves_addr_storage s value
  · -- storageMap unchanged
    exact setStorage_preserves_map_storage s value

-- Main theorem: retrieve meets its specification
theorem retrieve_meets_spec (s : ContractState) :
  let result := retrieve.run s |>.1
  retrieve_spec result s := by
  simp [retrieve, storedData, retrieve_spec]
  exact getStorage_reads_slot s

-- Main theorem: store then retrieve returns the stored value
-- This is the key correctness property!
theorem store_retrieve_correct (s : ContractState) (value : Uint256) :
  let s' := (store value).run s |>.2
  let result := retrieve.run s' |>.1
  result = value := by
  -- Strategy: use store_meets_spec to show s'.storage 0 = value
  -- then use retrieve_meets_spec to show result = s'.storage 0
  have h_store : store_spec value s ((store value).run s |>.2) :=
    store_meets_spec s value
  have h_retrieve : retrieve_spec (retrieve.run ((store value).run s |>.2) |>.1) ((store value).run s |>.2) :=
    retrieve_meets_spec ((store value).run s |>.2)
  simp [store_spec] at h_store
  simp [retrieve_spec] at h_retrieve
  simp only [h_retrieve, h_store.1]

-- Theorem: store preserves well-formedness
theorem store_preserves_wellformedness (s : ContractState) (value : Uint256)
  (h : WellFormedState s) :
  let s' := (store value).run s |>.2
  WellFormedState s' := by
  constructor
  · -- sender nonempty
    simp [store, storedData]
    rw [setStorage_preserves_sender]
    exact h.sender_nonempty
  · -- contract address nonempty
    simp [store, storedData]
    rw [setStorage_preserves_address]
    exact h.contract_nonempty

-- Theorem: retrieve preserves state (read-only operation)
theorem retrieve_preserves_state (s : ContractState) :
  let s' := retrieve.run s |>.2
  s' = s := by
  simp [retrieve, storedData, getStorage]

end DumbContracts.Proofs.SimpleStorage
