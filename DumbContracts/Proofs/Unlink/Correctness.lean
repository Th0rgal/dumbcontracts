/-
  Unlink Privacy Protocol: deposit_meets_spec

  Proves that the deposit implementation in UnlinkPool.lean satisfies the
  formal deposit specification from Spec.lean. This is the first complete
  implementation-to-spec correctness proof for the Unlink protocol.

  Proof structure:
    1. Prove recursive helpers are pure (hashNote, computeCommitments, validateNotes)
    2. Show deposit reduces to insertLeaves when guards pass
    3. Apply insertLeaves building blocks from Basic.lean
    4. Compose into the full deposit_spec

  Preconditions:
    - Non-empty note list with positive amounts (validation)
    - No merkle root overflow (arithmetic safety)
    - No storage slot collision between nullifier and root-seen mappings
      (In Solidity this is ensured by keccak256; here we state it explicitly)
-/

import DumbContracts.Core
import DumbContracts.Examples.Unlink.UnlinkPool
import DumbContracts.Specs.Unlink.Spec
import DumbContracts.Proofs.Unlink.Basic

namespace DumbContracts.Proofs.Unlink

open DumbContracts
open DumbContracts.Specs.Unlink

/-! ## Recursive Helper Lemmas

The deposit function calls three helpers before insertLeaves:
  1. require (notes.length > 0)  — guard
  2. validateNotes notes          — recursive validation
  3. computeCommitments notes     — recursive commitment computation

We prove each helper preserves state (is "pure" w.r.t. storage).
-/

-- hashNote is pure: computes a value without modifying state
theorem hashNote_eq (note : Examples.Unlink.Note) (s : ContractState) :
    Examples.Unlink.hashNote note s =
    ContractResult.success (note.npk + note.token + note.amount) s := by
  unfold Examples.Unlink.hashNote
  simp [DumbContracts.bind, DumbContracts.pure, Bind.bind, Pure.pure, instMonadContract]

-- computeCommitments preserves state and returns a list of the same length
theorem computeCommitments_spec (notes : List Examples.Unlink.Note) (s : ContractState) :
    ∃ cs : List Uint256,
      Examples.Unlink.computeCommitments notes s = ContractResult.success cs s ∧
      cs.length = notes.length := by
  induction notes with
  | nil =>
    exact ⟨[], by unfold Examples.Unlink.computeCommitments; rfl, rfl⟩
  | cons note rest ih =>
    obtain ⟨cs_rest, h_run, h_len⟩ := ih
    refine ⟨(note.npk + note.token + note.amount) :: cs_rest, ?_, by simp [h_len]⟩
    unfold Examples.Unlink.computeCommitments
    simp only [DumbContracts.bind, Bind.bind, instMonadContract]
    rw [hashNote_eq]; simp only []; rw [h_run]
    simp [DumbContracts.pure, Pure.pure, instMonadContract]

-- validateNotes preserves state when all note amounts are positive
theorem validateNotes_spec (notes : List Examples.Unlink.Note) (s : ContractState)
    (h_valid : ∀ note ∈ notes, note.amount > 0) :
    Examples.Unlink.validateNotes notes s = ContractResult.success () s := by
  induction notes with
  | nil =>
    unfold Examples.Unlink.validateNotes
    simp [DumbContracts.pure, Pure.pure, instMonadContract]
  | cons note rest ih =>
    unfold Examples.Unlink.validateNotes
    simp only [DumbContracts.bind, Bind.bind, instMonadContract]
    simp [DumbContracts.require, h_valid note (List.mem_cons_self _ _)]
    exact ih (fun n hn => h_valid n (List.mem_cons_of_mem _ hn))

/-! ## Deposit Reduction

When all guards pass, deposit reduces to insertLeaves applied to a
commitment list of the same length as the input notes.
-/

theorem deposit_reduces (notes : List Examples.Unlink.Note) (s : ContractState)
    (h_nonempty : notes.length > 0)
    (h_valid : ∀ note ∈ notes, note.amount > 0) :
    ∃ cs : List Uint256,
      cs.length = notes.length ∧
      (Examples.Unlink.deposit notes).run s =
      (Examples.Unlink.insertLeaves cs).run s := by
  obtain ⟨cs, h_comp, h_len⟩ := computeCommitments_spec notes s
  refine ⟨cs, h_len, ?_⟩
  unfold Examples.Unlink.deposit
  simp only [DumbContracts.bind, Bind.bind, instMonadContract, Contract.run]
  simp [DumbContracts.require, h_nonempty]
  rw [validateNotes_spec notes s h_valid]
  simp only []
  rw [h_comp]

/-! ## deposit_meets_spec

The main correctness theorem. We use deposit_spec' which parametrizes
by list length to avoid the Note type mismatch between Specs.Unlink.Note
and Examples.Unlink.Note (both have identical fields, but are distinct types).

The no_slot_collision precondition models the fact that nullifier slots
(2 + hash.val) and root-seen slots (3 + root.val) don't overlap.
In Solidity, keccak256-based mapping slots guarantee this. In the EDSL
scaffold with flat offsets, we state it as an explicit assumption.
-/

-- No nullifier slot collides with the new root-seen slot
def no_slot_collision (s : ContractState) (n : Nat) : Prop :=
  ∀ nullifier : Uint256,
    2 + nullifier.val ≠ 3 + (s.storage 1 + (Core.Uint256.ofNat n)).val

-- deposit_spec parametrized by length (avoids Note type mismatch)
def deposit_spec' (n : Nat) (s s' : ContractState) : Prop :=
  currentMerkleRoot s' ≠ currentMerkleRoot s ∧
  rootSeen s' (currentMerkleRoot s') ∧
  nextLeafIndex s' = nextLeafIndex s + n ∧
  (∀ nullifier : Uint256, nullifierSpent s nullifier → nullifierSpent s' nullifier) ∧
  (∀ r : Uint256, rootSeen s r → rootSeen s' r) ∧
  Specs.sameContext s s'

-- deposit_spec is equivalent to deposit_spec' at notes.length
theorem deposit_spec_iff {notes : List Specs.Unlink.Note} {s s' : ContractState} :
    deposit_spec notes s s' ↔ deposit_spec' notes.length s s' := by
  simp [deposit_spec, deposit_spec']

-- deposit succeeds (doesn't revert) when preconditions hold
set_option maxRecDepth 2048 in
theorem deposit_succeeds (notes : List Examples.Unlink.Note) (s : ContractState)
    (h_nonempty : notes.length > 0)
    (h_valid : ∀ note ∈ notes, note.amount > 0) :
    ∃ s', (Examples.Unlink.deposit notes).run s = ContractResult.success () s' := by
  obtain ⟨cs, h_comp, _⟩ := computeCommitments_spec notes s
  unfold Examples.Unlink.deposit
  simp only [DumbContracts.bind, Bind.bind, instMonadContract, Contract.run]
  simp [DumbContracts.require, h_nonempty]
  rw [validateNotes_spec notes s h_valid]; simp only []
  rw [h_comp]; simp only []
  unfold Examples.Unlink.insertLeaves Examples.Unlink.markRootSeen
  simp only [getStorage, setStorage, DumbContracts.bind, DumbContracts.pure,
    Contract.run, Bind.bind, Pure.pure,
    Examples.Unlink.merkleRoot, Examples.Unlink.nextLeafIndex,
    Examples.Unlink.rootSeen, instMonadContract]
  exact ⟨_, rfl⟩

-- THE MAIN THEOREM: deposit implementation satisfies its specification
set_option maxRecDepth 2048 in
theorem deposit_meets_spec (notes : List Examples.Unlink.Note) (s : ContractState)
    (h_nonempty : notes.length > 0)
    (h_valid : ∀ note ∈ notes, note.amount > 0)
    (h_no_overflow : (s.storage 1).val + notes.length < Core.Uint256.modulus)
    (h_no_collision : no_slot_collision s notes.length) :
    let s' := ((Examples.Unlink.deposit notes).run s).snd
    deposit_spec' notes.length s s' := by
  obtain ⟨cs, h_len, h_eq⟩ := deposit_reduces notes s h_nonempty h_valid
  have h_snd : ((Examples.Unlink.deposit notes).run s).snd =
    ((Examples.Unlink.insertLeaves cs).run s).snd := by rw [h_eq]
  rw [h_snd]
  have h_overflow' : (s.storage 1).val + cs.length < Core.Uint256.modulus := h_len ▸ h_no_overflow
  have h_ofNat : Core.Uint256.ofNat cs.length = Core.Uint256.ofNat notes.length :=
    congrArg Core.Uint256.ofNat h_len
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Root changes
    exact insertLeaves_root_changes cs s (h_len ▸ h_nonempty) h_overflow'
  · -- New root is seen
    exact insertLeaves_new_root_seen cs s
  · -- Leaf index updated: nextLeafIndex s' = nextLeafIndex s + notes.length
    simp only [insertLeaves_leaf_index_updated cs s, h_ofNat]
  · -- Nullifier preservation
    intro n h_spent
    have h_col : 2 + n.val ≠ 3 + (s.storage 1 + (Core.Uint256.ofNat cs.length)).val := by
      rw [h_ofNat]; exact h_no_collision n
    exact insertLeaves_preserves_nullifiers cs s n h_col h_spent
  · -- Root preservation
    intro r h_seen
    exact insertLeaves_preserves_roots cs s r h_seen
  · -- Context preservation
    exact insertLeaves_preserves_context cs s

end DumbContracts.Proofs.Unlink
