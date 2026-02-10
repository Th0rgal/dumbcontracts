/-
  Basic correctness proofs for Counter contract.

  Proves that Counter operations satisfy their specifications.
-/

import DumbContracts.Core
import DumbContracts.Examples.Counter
import DumbContracts.Specs.Counter.Spec
import DumbContracts.Specs.Counter.Invariants

namespace DumbContracts.Proofs.Counter

open DumbContracts
open DumbContracts.Examples.Counter
open DumbContracts.Specs.Counter

/-! ## Basic Lemmas about setStorage and getStorage

These reuse patterns from SimpleStorage proofs.
-/

theorem setStorage_updates_count (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := count
  let s' := (setStorage slot value).run s |>.2
  s'.storage 0 = value := by
  simp [setStorage, count]

theorem getStorage_reads_count (s : ContractState) :
  let slot : StorageSlot Uint256 := count
  let result := (getStorage slot).run s |>.1
  result = s.storage 0 := by
  simp [getStorage, count]

theorem setStorage_preserves_other_slots (s : ContractState) (value : Uint256) (slot_num : Nat)
  (h : slot_num ≠ 0) :
  let slot : StorageSlot Uint256 := count
  let s' := (setStorage slot value).run s |>.2
  s'.storage slot_num = s.storage slot_num := by
  simp [setStorage, count, h]

theorem setStorage_preserves_context (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := count
  let s' := (setStorage slot value).run s |>.2
  s'.sender = s.sender ∧ s'.thisAddress = s.thisAddress := by
  simp [setStorage, count]

theorem setStorage_preserves_addr_storage (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := count
  let s' := (setStorage slot value).run s |>.2
  s'.storageAddr = s.storageAddr := by
  simp [setStorage, count]

theorem setStorage_preserves_map_storage (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := count
  let s' := (setStorage slot value).run s |>.2
  s'.storageMap = s.storageMap := by
  simp [setStorage, count]

/-! ## increment Correctness -/

theorem increment_meets_spec (s : ContractState) :
  let s' := increment.run s |>.2
  increment_spec s s' := by
  simp [increment, increment_spec]
  constructor
  · -- Prove: s'.storage 0 = s.storage 0 + 1
    have h1 := setStorage_updates_count s (s.storage 0 + 1)
    simp [count] at h1
    exact h1
  constructor
  · -- Prove: other slots unchanged
    intro slot h_neq
    have h2 := setStorage_preserves_other_slots s (s.storage 0 + 1) slot h_neq
    simp [count] at h2
    exact h2
  constructor
  · -- Prove: sender preserved
    have h3 := setStorage_preserves_context s (s.storage 0 + 1)
    simp [count] at h3
    exact h3.1
  constructor
  · -- Prove: thisAddress preserved
    have h3 := setStorage_preserves_context s (s.storage 0 + 1)
    simp [count] at h3
    exact h3.2
  constructor
  · -- Prove: storageAddr preserved
    exact setStorage_preserves_addr_storage s (s.storage 0 + 1)
  · -- Prove: storageMap preserved
    exact setStorage_preserves_map_storage s (s.storage 0 + 1)

theorem increment_adds_one (s : ContractState) :
  let s' := increment.run s |>.2
  s'.storage 0 = s.storage 0 + 1 := by
  have h := increment_meets_spec s
  simp [increment_spec] at h
  exact h.1

/-! ## decrement Correctness -/

theorem decrement_meets_spec (s : ContractState) :
  let s' := decrement.run s |>.2
  decrement_spec s s' := by
  simp [decrement, decrement_spec]
  constructor
  · -- Prove: s'.storage 0 = s.storage 0 - 1
    have h1 := setStorage_updates_count s (s.storage 0 - 1)
    simp [count] at h1
    exact h1
  constructor
  · -- Prove: other slots unchanged
    intro slot h_neq
    have h2 := setStorage_preserves_other_slots s (s.storage 0 - 1) slot h_neq
    simp [count] at h2
    exact h2
  constructor
  · -- Prove: sender preserved
    have h3 := setStorage_preserves_context s (s.storage 0 - 1)
    simp [count] at h3
    exact h3.1
  constructor
  · -- Prove: thisAddress preserved
    have h3 := setStorage_preserves_context s (s.storage 0 - 1)
    simp [count] at h3
    exact h3.2
  constructor
  · -- Prove: storageAddr preserved
    exact setStorage_preserves_addr_storage s (s.storage 0 - 1)
  · -- Prove: storageMap preserved
    exact setStorage_preserves_map_storage s (s.storage 0 - 1)

theorem decrement_subtracts_one (s : ContractState) :
  let s' := decrement.run s |>.2
  s'.storage 0 = s.storage 0 - 1 := by
  have h := decrement_meets_spec s
  simp [decrement_spec] at h
  exact h.1

/-! ## getCount Correctness -/

theorem getCount_meets_spec (s : ContractState) :
  let result := getCount.run s |>.1
  getCount_spec result s := by
  simp [getCount, getCount_spec]
  exact getStorage_reads_count s

theorem getCount_reads_count_value (s : ContractState) :
  let result := getCount.run s |>.1
  result = s.storage 0 := by
  have h := getCount_meets_spec s
  simp [getCount_spec] at h
  exact h

/-! ## Composition Properties -/

theorem increment_getCount_correct (s : ContractState) :
  let s' := increment.run s |>.2
  let result := getCount.run s' |>.1
  result = s.storage 0 + 1 := by
  have h_inc := increment_adds_one s
  have h_get := getCount_reads_count_value (increment.run s |>.2)
  simp only [h_inc] at h_get
  exact h_get

theorem decrement_getCount_correct (s : ContractState) :
  let s' := decrement.run s |>.2
  let result := getCount.run s' |>.1
  result = s.storage 0 - 1 := by
  have h_dec := decrement_subtracts_one s
  have h_get := getCount_reads_count_value (decrement.run s |>.2)
  simp only [h_dec] at h_get
  exact h_get

theorem increment_twice_adds_two (s : ContractState) :
  let s' := increment.run s |>.2
  let s'' := increment.run s' |>.2
  s''.storage 0 = s.storage 0 + 2 := by
  have h1 : (increment.run s |>.2).storage 0 = s.storage 0 + 1 := increment_adds_one s
  have h2 : (increment.run (increment.run s |>.2) |>.2).storage 0 = (increment.run s |>.2).storage 0 + 1 :=
    increment_adds_one (increment.run s |>.2)
  calc (increment.run (increment.run s |>.2) |>.2).storage 0
      = (increment.run s |>.2).storage 0 + 1 := h2
    _ = (s.storage 0 + 1) + 1 := by rw [h1]
    _ = s.storage 0 + 2 := by simp_arith

theorem increment_decrement_cancel (s : ContractState) :
  let s' := increment.run s |>.2
  let s'' := decrement.run s' |>.2
  s''.storage 0 = s.storage 0 := by
  have h1 : (increment.run s |>.2).storage 0 = s.storage 0 + 1 := increment_adds_one s
  have h2 : (decrement.run (increment.run s |>.2) |>.2).storage 0 = (increment.run s |>.2).storage 0 - 1 :=
    decrement_subtracts_one (increment.run s |>.2)
  calc (decrement.run (increment.run s |>.2) |>.2).storage 0
      = (increment.run s |>.2).storage 0 - 1 := h2
    _ = (s.storage 0 + 1) - 1 := by rw [h1]
    _ = s.storage 0 := by simp_arith

/-! ## State Preservation -/

theorem increment_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := increment.run s |>.2
  WellFormedState s' := by
  have h_spec := increment_meets_spec s
  simp [increment_spec] at h_spec
  exact ⟨h_spec.2.2.1 ▸ h.sender_nonempty, h_spec.2.2.2.1 ▸ h.contract_nonempty⟩

theorem decrement_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := decrement.run s |>.2
  WellFormedState s' := by
  have h_spec := decrement_meets_spec s
  simp [decrement_spec] at h_spec
  exact ⟨h_spec.2.2.1 ▸ h.sender_nonempty, h_spec.2.2.2.1 ▸ h.contract_nonempty⟩

theorem getCount_preserves_state (s : ContractState) :
  let s' := getCount.run s |>.2
  s' = s := by
  simp [getCount, getStorage]

end DumbContracts.Proofs.Counter
