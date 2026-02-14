/-
  Unlink Privacy Protocol: transact_meets_spec

  Proves that the transact implementation in UnlinkPool.lean satisfies the
  formal transact specification from Spec.lean.

  Proof structure:
    1. Prove recursive helpers (isRootSeen, checkNullifiersUnspent, etc.)
    2. Prove markNullifiersSpent state properties
    3. Compose into the full transact_spec
-/

import DumbContracts.Core
import DumbContracts.Examples.Unlink.UnlinkPool
import DumbContracts.Specs.Unlink.Spec
import DumbContracts.Proofs.Unlink.Basic
import DumbContracts.Proofs.Unlink.Correctness

namespace DumbContracts.Proofs.Unlink

open DumbContracts
open DumbContracts.Specs.Unlink

/-! ## Helper Lemmas -/

theorem isRootSeen_spec (root : Uint256) (s : ContractState) :
    Examples.Unlink.isRootSeen root s =
    ContractResult.success (decide (s.storage (3 + root.val) = 1)) s := by
  unfold Examples.Unlink.isRootSeen
  simp [DumbContracts.bind, DumbContracts.pure, Bind.bind, Pure.pure, instMonadContract,
    getStorage, Examples.Unlink.rootSeen]

theorem isRootSeen_true (root : Uint256) (s : ContractState)
    (h : s.storage (3 + root.val) = 1) :
    Examples.Unlink.isRootSeen root s =
    ContractResult.success true s := by
  rw [isRootSeen_spec]; congr 1; exact decide_eq_true h

theorem verifyProof_spec (txn : Examples.Unlink.Transaction) (s : ContractState) :
    Examples.Unlink.verifyProof txn s =
    ContractResult.success true s := by
  unfold Examples.Unlink.verifyProof
  simp [DumbContracts.bind, DumbContracts.pure, Bind.bind, Pure.pure, instMonadContract]

theorem isNullifierSpent_spec (n : Uint256) (s : ContractState) :
    Examples.Unlink.isNullifierSpent n s =
    ContractResult.success (decide (s.storage (2 + n.val) = 1)) s := by
  unfold Examples.Unlink.isNullifierSpent
  simp [DumbContracts.bind, DumbContracts.pure, Bind.bind, Pure.pure, instMonadContract,
    getStorage, Examples.Unlink.nullifierHashes]

theorem checkNullifiersUnspent_spec (nullifiers : List Uint256) (s : ContractState)
    (h_fresh : ∀ n ∈ nullifiers, s.storage (2 + n.val) ≠ 1) :
    Examples.Unlink.checkNullifiersUnspent nullifiers s =
    ContractResult.success () s := by
  induction nullifiers with
  | nil =>
    unfold Examples.Unlink.checkNullifiersUnspent
    simp [DumbContracts.pure, Pure.pure, instMonadContract]
  | cons n rest ih =>
    unfold Examples.Unlink.checkNullifiersUnspent
    simp only [DumbContracts.bind, Bind.bind, instMonadContract]
    rw [isNullifierSpent_spec]; simp only []
    have h_n := h_fresh n (List.mem_cons_self _ _)
    have h_decide : decide (s.storage (2 + n.val) = 1) = false :=
      decide_eq_false h_n
    simp [h_decide, DumbContracts.require]
    exact ih (fun m hm => h_fresh m (List.mem_cons_of_mem _ hm))

/-! ## markNullifiersSpent State Effects -/

theorem markNullifierSpent_spec (n : Uint256) (s : ContractState) :
    Examples.Unlink.markNullifierSpent n s =
    ContractResult.success ()
      { s with storage := fun slot =>
        if slot == 2 + n.val then 1 else s.storage slot } := by
  unfold Examples.Unlink.markNullifierSpent
  simp [setStorage, Examples.Unlink.nullifierHashes]

-- markNullifiersSpent succeeds
theorem markNullifiersSpent_succeeds (nullifiers : List Uint256) :
    ∀ s : ContractState, ∃ s', Examples.Unlink.markNullifiersSpent nullifiers s =
    ContractResult.success () s' := by
  induction nullifiers with
  | nil =>
    intro s
    unfold Examples.Unlink.markNullifiersSpent
    exact ⟨s, by simp [DumbContracts.pure, Pure.pure, instMonadContract]⟩
  | cons n rest ih =>
    intro s
    unfold Examples.Unlink.markNullifiersSpent
    simp only [DumbContracts.bind, Bind.bind, instMonadContract]
    rw [markNullifierSpent_spec]; simp only []
    exact ih _

-- Any slot whose value is 1 before markNullifiersSpent remains 1 after
-- (because markNullifiersSpent only writes 1, never changes 1 to something else)
theorem markNullifiersSpent_preserves_one
    (nullifiers : List Uint256) (slot : Nat) :
    ∀ (s : ContractState), s.storage slot = 1 →
    ∀ s', Examples.Unlink.markNullifiersSpent nullifiers s =
      ContractResult.success () s' →
    s'.storage slot = 1 := by
  induction nullifiers with
  | nil =>
    intro s h_val s' h_run
    unfold Examples.Unlink.markNullifiersSpent at h_run
    simp [DumbContracts.pure, Pure.pure, instMonadContract] at h_run
    rw [← h_run]; exact h_val
  | cons hd rest ih =>
    intro s h_val s' h_run
    unfold Examples.Unlink.markNullifiersSpent at h_run
    simp only [DumbContracts.bind, Bind.bind, instMonadContract] at h_run
    rw [markNullifierSpent_spec] at h_run; simp only [] at h_run
    -- Intermediate state has slot = 1 or unchanged
    apply ih _ _ s' h_run
    -- Show slot value in intermediate state
    show (if slot == 2 + hd.val then (1 : Uint256) else s.storage slot) = 1
    split
    · rfl
    · exact h_val

-- After markNullifiersSpent, each nullifier in the list has slot = 1
theorem markNullifiersSpent_sets_slots (nullifiers : List Uint256)
    (n : Uint256) (h_mem : n ∈ nullifiers) :
    ∀ (s : ContractState) (s' : ContractState),
    Examples.Unlink.markNullifiersSpent nullifiers s =
      ContractResult.success () s' →
    s'.storage (2 + n.val) = 1 := by
  induction nullifiers with
  | nil => exact absurd h_mem (List.not_mem_nil _)
  | cons hd rest ih =>
    intro s s' h_run
    unfold Examples.Unlink.markNullifiersSpent at h_run
    simp only [DumbContracts.bind, Bind.bind, instMonadContract] at h_run
    rw [markNullifierSpent_spec] at h_run; simp only [] at h_run
    rcases List.mem_cons.mp h_mem with rfl | h_rest
    · -- n = hd: slot set to 1, then preserved
      apply markNullifiersSpent_preserves_one rest (2 + n.val) _ _ s' h_run
      show (if (2 + n.val) == (2 + n.val) then (1 : Uint256) else s.storage (2 + n.val)) = 1
      simp
    · -- n ∈ rest: by induction
      exact ih h_rest _ _ h_run

-- markNullifiersSpent preserves slots not in the nullifier list
theorem markNullifiersSpent_preserves_other_slots
    (nullifiers : List Uint256)
    (slot : Nat) (h_not_null : ∀ n ∈ nullifiers, slot ≠ 2 + n.val) :
    ∀ (s : ContractState) (s' : ContractState),
    Examples.Unlink.markNullifiersSpent nullifiers s =
      ContractResult.success () s' →
    s'.storage slot = s.storage slot := by
  induction nullifiers with
  | nil =>
    intro s s' h_run
    unfold Examples.Unlink.markNullifiersSpent at h_run
    simp [DumbContracts.pure, Pure.pure, instMonadContract] at h_run
    rw [← h_run]
  | cons hd rest ih =>
    intro s s' h_run
    unfold Examples.Unlink.markNullifiersSpent at h_run
    simp only [DumbContracts.bind, Bind.bind, instMonadContract] at h_run
    rw [markNullifierSpent_spec] at h_run; simp only [] at h_run
    have h_ne : slot ≠ 2 + hd.val := h_not_null hd (List.mem_cons_self _ _)
    have h_rest : ∀ n ∈ rest, slot ≠ 2 + n.val :=
      fun n hn => h_not_null n (List.mem_cons_of_mem _ hn)
    -- ih gives s'.storage slot = intermediate.storage slot
    -- We then show intermediate.storage slot = s.storage slot
    have h_ih := ih h_rest _ s' h_run
    rw [h_ih]
    show (if slot == 2 + hd.val then (1 : Uint256) else s.storage slot) = s.storage slot
    have : (slot == 2 + hd.val) = false := by simp [beq_iff_eq, h_ne]
    simp [this]

-- markNullifiersSpent preserves context
theorem markNullifiersSpent_preserves_context
    (nullifiers : List Uint256) :
    ∀ (s : ContractState) (s' : ContractState),
    Examples.Unlink.markNullifiersSpent nullifiers s =
      ContractResult.success () s' →
    s'.sender = s.sender ∧ s'.thisAddress = s.thisAddress ∧
    s'.msgValue = s.msgValue ∧ s'.blockTimestamp = s.blockTimestamp := by
  induction nullifiers with
  | nil =>
    intro s s' h_run
    unfold Examples.Unlink.markNullifiersSpent at h_run
    simp [DumbContracts.pure, Pure.pure, instMonadContract] at h_run
    rw [← h_run]; exact ⟨rfl, rfl, rfl, rfl⟩
  | cons hd rest ih =>
    intro s s' h_run
    unfold Examples.Unlink.markNullifiersSpent at h_run
    simp only [DumbContracts.bind, Bind.bind, instMonadContract] at h_run
    rw [markNullifierSpent_spec] at h_run; simp only [] at h_run
    -- ih: s' has same context as intermediate state
    have h_ih := ih _ s' h_run
    -- intermediate state has same context as s (setStorage only changes storage)
    exact ⟨by rw [h_ih.1], by rw [h_ih.2.1], by rw [h_ih.2.2.1], by rw [h_ih.2.2.2]⟩

-- markNullifiersSpent preserves already-spent nullifiers
theorem markNullifiersSpent_preserves_spent
    (nullifiers : List Uint256) (n : Uint256) :
    ∀ (s : ContractState), s.storage (2 + n.val) = 1 →
    ∀ s', Examples.Unlink.markNullifiersSpent nullifiers s =
      ContractResult.success () s' →
    s'.storage (2 + n.val) = 1 :=
  markNullifiersSpent_preserves_one nullifiers (2 + n.val)

-- markNullifiersSpent preserves rootSeen slots (value 1 stays 1)
theorem markNullifiersSpent_preserves_rootSeen
    (nullifiers : List Uint256) (r : Uint256) :
    ∀ (s : ContractState), s.storage (3 + r.val) = 1 →
    ∀ s', Examples.Unlink.markNullifiersSpent nullifiers s =
      ContractResult.success () s' →
    s'.storage (3 + r.val) = 1 :=
  markNullifiersSpent_preserves_one nullifiers (3 + r.val)

/-! ## No-slot-collision for transact -/

def transact_no_slot_collision
    (s : ContractState) (nullifiers : List Uint256)
    (n_comms : Nat) : Prop :=
  ∀ nullifier ∈ nullifiers,
    2 + nullifier.val ≠ 3 + (s.storage 1 + (Core.Uint256.ofNat n_comms)).val

/-! ## transact_meets_spec -/

set_option maxRecDepth 2048 in
private theorem transact_spec_from_components
    (txn : Examples.Unlink.Transaction)
    (s s_marked s_final : ContractState)
    (h_root_seen : s.storage (3 + txn.merkleRoot.val) = 1)
    (h_fresh : ∀ n ∈ txn.nullifierHashes, s.storage (2 + n.val) ≠ 1)
    (h_withdrawal : txn.withdrawal.amount > 0 →
      txn.newCommitments.getLast? =
        some (txn.withdrawal.npk + txn.withdrawal.token + txn.withdrawal.amount))
    (h_no_overflow : (s.storage 1).val + txn.newCommitments.length < Core.Uint256.modulus)
    (h_no_collision : transact_no_slot_collision s txn.nullifierHashes txn.newCommitments.length)
    (h_comms_nonempty : txn.newCommitments.length > 0)
    (h_marked : Examples.Unlink.markNullifiersSpent txn.nullifierHashes s =
      ContractResult.success () s_marked)
    (h_insert : (Examples.Unlink.insertLeaves txn.newCommitments).run s_marked =
      ContractResult.success () s_final) :
    transact_spec
      txn.merkleRoot
      txn.nullifierHashes
      txn.newCommitments
      txn.withdrawal.amount
      (txn.withdrawal.npk + txn.withdrawal.token + txn.withdrawal.amount)
      s s_final := by
  have h_slot1 : s_marked.storage 1 = s.storage 1 :=
    markNullifiersSpent_preserves_other_slots txn.nullifierHashes 1
      (fun n _ => by omega) s s_marked h_marked
  have h_slot0 : s_marked.storage 0 = s.storage 0 :=
    markNullifiersSpent_preserves_other_slots txn.nullifierHashes 0
      (fun n _ => by omega) s s_marked h_marked
  have h_ctx := markNullifiersSpent_preserves_context txn.nullifierHashes s s_marked h_marked
  have h_snd : s_final = ((Examples.Unlink.insertLeaves txn.newCommitments).run s_marked).snd := by
    rw [h_insert]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_root_seen
  · intro n h_mem; exact h_fresh n h_mem
  · -- nullifiers spent in s_final
    intro n h_mem
    simp only [nullifierSpent]
    have h_set := markNullifiersSpent_sets_slots txn.nullifierHashes n h_mem s s_marked h_marked
    rw [h_snd, insertLeaves_preserves_slot txn.newCommitments s_marked _ (by omega) (by omega)
      (by rw [h_slot1]; exact h_no_collision n h_mem)]
    exact h_set
  · -- root changes
    simp only [currentMerkleRoot]
    rw [h_snd, insertLeaves_updates_root, h_slot1]
    exact gt_implies_ne (add_length_gt txn.newCommitments h_comms_nonempty h_no_overflow)
  · -- new root seen
    simp only [Specs.Unlink.rootSeen, currentMerkleRoot]
    rw [h_snd, insertLeaves_updates_root]
    exact insertLeaves_marks_root_seen txn.newCommitments s_marked
  · -- leaf index
    simp only [Specs.Unlink.nextLeafIndex]
    rw [h_snd, insertLeaves_updates_leaf_index, h_slot0]
  · -- root preservation
    intro r h_r_seen
    simp only [Specs.Unlink.rootSeen] at h_r_seen ⊢
    have h_mp := markNullifiersSpent_preserves_rootSeen txn.nullifierHashes r s h_r_seen s_marked h_marked
    rw [h_snd]
    exact insertLeaves_preserves_roots txn.newCommitments s_marked r h_mp
  · -- nullifier preservation
    intro n h_spent
    simp only [nullifierSpent] at h_spent ⊢
    have h_mp := markNullifiersSpent_preserves_spent txn.nullifierHashes n s h_spent s_marked h_marked
    rw [h_snd]
    by_cases h_eq : 2 + n.val = 3 + (s_marked.storage 1 +
        (Core.Uint256.ofNat txn.newCommitments.length)).val
    · rw [show 2 + n.val = 3 + (s_marked.storage 1 +
          (Core.Uint256.ofNat txn.newCommitments.length)).val from h_eq]
      exact insertLeaves_marks_root_seen txn.newCommitments s_marked
    · rw [insertLeaves_preserves_slot txn.newCommitments s_marked _ (by omega) (by omega) h_eq]
      exact h_mp
  · -- context
    unfold Specs.sameContext
    rw [h_snd]
    have h_il := insertLeaves_preserves_context txn.newCommitments s_marked
    unfold Specs.sameContext at h_il
    exact ⟨by rw [h_il.1, h_ctx.1],
           by rw [h_il.2.1, h_ctx.2.1],
           by rw [h_il.2.2.1, h_ctx.2.2.1],
           by rw [h_il.2.2.2, h_ctx.2.2.2]⟩
  · exact h_withdrawal

set_option maxRecDepth 4096 in
theorem transact_meets_spec
    (txn : Examples.Unlink.Transaction)
    (s : ContractState)
    (h_nulls_nonempty : txn.nullifierHashes.length > 0)
    (h_comms_nonempty : txn.newCommitments.length > 0)
    (h_nulls_bound : txn.nullifierHashes.length ≤ 16)
    (h_comms_bound : txn.newCommitments.length ≤ 16)
    (h_root_seen : s.storage (3 + txn.merkleRoot.val) = 1)
    (h_fresh : ∀ n ∈ txn.nullifierHashes, s.storage (2 + n.val) ≠ 1)
    (h_withdrawal : txn.withdrawal.amount > 0 →
      txn.newCommitments.getLast? =
        some (txn.withdrawal.npk + txn.withdrawal.token + txn.withdrawal.amount))
    (h_no_overflow : (s.storage 1).val + txn.newCommitments.length < Core.Uint256.modulus)
    (h_no_collision : transact_no_slot_collision s txn.nullifierHashes txn.newCommitments.length)
    :
    let result := (Examples.Unlink.transact txn).run s
    ∃ s', result = ContractResult.success () s' ∧
    transact_spec
      txn.merkleRoot
      txn.nullifierHashes
      txn.newCommitments
      txn.withdrawal.amount
      (txn.withdrawal.npk + txn.withdrawal.token + txn.withdrawal.amount)
      s s' := by
  -- Unfold transact and reduce through all guards
  unfold Examples.Unlink.transact
  simp only [DumbContracts.bind, Bind.bind, instMonadContract, Contract.run,
    DumbContracts.require]
  -- Reduce all 4 length guards
  have : decide (txn.nullifierHashes.length > 0) = true := decide_eq_true h_nulls_nonempty
  simp only [this, ↓reduceIte]
  have : decide (txn.newCommitments.length > 0) = true := decide_eq_true h_comms_nonempty
  simp only [this, ↓reduceIte]
  have : decide (txn.nullifierHashes.length ≤ 16) = true := decide_eq_true h_nulls_bound
  simp only [this, ↓reduceIte]
  have : decide (txn.newCommitments.length ≤ 16) = true := decide_eq_true h_comms_bound
  simp only [this, ↓reduceIte]
  -- isRootSeen check
  rw [isRootSeen_true _ _ h_root_seen]; simp only []
  simp only [DumbContracts.require, ↓reduceIte]
  -- Withdrawal coherence check
  by_cases h_wa : txn.withdrawal.amount > 0
  · -- withdrawal branch taken
    simp only [h_wa, ↓reduceIte, DumbContracts.bind, Bind.bind, instMonadContract]
    -- hashNote
    rw [hashNote_eq]; simp only []
    -- require withdrawal commitment match
    have h_wd := h_withdrawal h_wa
    have : decide (txn.newCommitments.getLast? =
      some (txn.withdrawal.npk + txn.withdrawal.token + txn.withdrawal.amount)) = true :=
      decide_eq_true h_wd
    simp only [DumbContracts.require, this, ↓reduceIte]
    -- checkNullifiersUnspent
    rw [checkNullifiersUnspent_spec _ _ h_fresh]; simp only []
    -- verifyProof
    rw [verifyProof_spec]; simp only []
    simp only [DumbContracts.require, ↓reduceIte]
    -- markNullifiersSpent + insertLeaves
    obtain ⟨s_marked, h_marked⟩ := markNullifiersSpent_succeeds txn.nullifierHashes s
    rw [h_marked]; simp only []
    -- Goal now has insertLeaves applied directly (not via .run)
    -- Contract.run c s = c s, so we can use h_insert after noting this
    obtain ⟨s_final, h_insert⟩ := insertLeaves_succeeds txn.newCommitments s_marked
    have h_insert' : Examples.Unlink.insertLeaves txn.newCommitments s_marked =
      ContractResult.success () s_final := h_insert
    rw [h_insert']
    exact ⟨s_final, rfl, transact_spec_from_components txn s s_marked s_final
      h_root_seen h_fresh h_withdrawal h_no_overflow h_no_collision
      h_comms_nonempty h_marked h_insert⟩
  · -- withdrawal branch not taken
    simp only [h_wa, ↓reduceIte, DumbContracts.pure, Pure.pure, instMonadContract,
      DumbContracts.bind, Bind.bind]
    -- checkNullifiersUnspent
    rw [checkNullifiersUnspent_spec _ _ h_fresh]; simp only []
    -- verifyProof
    rw [verifyProof_spec]; simp only []
    simp only [DumbContracts.require, ↓reduceIte]
    -- markNullifiersSpent + insertLeaves
    obtain ⟨s_marked, h_marked⟩ := markNullifiersSpent_succeeds txn.nullifierHashes s
    rw [h_marked]; simp only []
    obtain ⟨s_final, h_insert⟩ := insertLeaves_succeeds txn.newCommitments s_marked
    have h_insert' : Examples.Unlink.insertLeaves txn.newCommitments s_marked =
      ContractResult.success () s_final := h_insert
    rw [h_insert']
    exact ⟨s_final, rfl, transact_spec_from_components txn s s_marked s_final
      h_root_seen h_fresh h_withdrawal h_no_overflow h_no_collision
      h_comms_nonempty h_marked h_insert⟩

end DumbContracts.Proofs.Unlink
