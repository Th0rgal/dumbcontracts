import DumbContracts.Core
import DumbContracts.Semantics
import DumbContracts.Examples

namespace DumbContracts

structure State where
  balance : Address -> Int
  totalSupply : Int

abbrev Pred := State -> Prop
abbrev Rel := State -> State -> Prop

-- Transfer pre.
def preTransfer (from to : Address) (amount : Int) (s : State) : Prop :=
  amount >= 0 ∧ from ≠ to ∧ s.balance from >= amount

-- Transfer impl.
def transfer (from to : Address) (amount : Int) (s : State) : State :=
  { balance := update (update s.balance from (s.balance from - amount)) to (s.balance to + amount)
    totalSupply := s.totalSupply }

-- Transfer spec.
def transferSpec (from to : Address) (amount : Int) : Spec State :=
  { requires := preTransfer from to amount
    ensures := fun s s' =>
      s'.balance from = s.balance from - amount ∧
      s'.balance to = s.balance to + amount ∧
      (forall a, a ≠ from -> a ≠ to -> s'.balance a = s.balance a) ∧
      s'.totalSupply = s.totalSupply }

-- Transfer proof.
theorem transfer_sound (s : State) (from to : Address) (amount : Int) :
    preTransfer from to amount s ->
    (transferSpec from to amount).ensures s (transfer from to amount s) := by
  intro hpre
  have hft : from ≠ to := hpre.2.1
  constructor
  · simp [transfer, update, hft]
  constructor
  · simp [transfer, update]
  constructor
  · intro a ha_from ha_to
    simp [transfer, update, ha_from, ha_to]
  · simp [transfer]

-- Spec holds when requires holds.
theorem transfer_spec_holds (s : State) (from to : Address) (amount : Int) :
    (transferSpec from to amount).requires s ->
    (transferSpec from to amount).ensures s (transfer from to amount s) := by
  intro hreq
  exact transfer_sound s from to amount hreq

-- Mint pre.
def preMint (to : Address) (amount : Int) (s : State) : Prop :=
  amount >= 0

-- Mint impl.
def mint (to : Address) (amount : Int) (s : State) : State :=
  { balance := update s.balance to (s.balance to + amount)
    totalSupply := s.totalSupply + amount }

-- Mint spec.
def mintSpec (to : Address) (amount : Int) : Spec State :=
  { requires := preMint to amount
    ensures := fun s s' =>
      s'.balance to = s.balance to + amount ∧
      (forall a, a ≠ to -> s'.balance a = s.balance a) ∧
      s'.totalSupply = s.totalSupply + amount }

-- Mint proof.
theorem mint_sound (s : State) (to : Address) (amount : Int) :
    preMint to amount s ->
    (mintSpec to amount).ensures s (mint to amount s) := by
  intro _hpre
  constructor
  · simp [mint, update]
  constructor
  · intro a ha_to
    simp [mint, update, ha_to]
  · simp [mint]

-- Spec holds when requires holds.
theorem mint_spec_holds (s : State) (to : Address) (amount : Int) :
    (mintSpec to amount).requires s ->
    (mintSpec to amount).ensures s (mint to amount s) := by
  intro hreq
  exact mint_sound s to amount hreq

end DumbContracts

namespace DumbContracts.Lending

abbrev Address := DumbContracts.Address

structure LState where
  collateral : Address -> Nat
  debt : Address -> Nat
  minHealthFactor : Nat

abbrev Pred := LState -> Prop
abbrev Rel := LState -> LState -> Prop

structure Spec where
  requires : Pred
  ensures : Rel

-- Health factor invariant.
def hfOk (s : LState) (a : Address) : Prop :=
  s.collateral a >= s.debt a * s.minHealthFactor

def globalHF (s : LState) : Prop :=
  forall a, hfOk s a

-- Borrow pre.
def preBorrow (borrower : Address) (amount : Nat) (s : LState) : Prop :=
  s.collateral borrower >= (s.debt borrower + amount) * s.minHealthFactor

-- Borrow impl.
def borrow (borrower : Address) (amount : Nat) (s : LState) : LState :=
  { collateral := s.collateral
    debt := DumbContracts.update s.debt borrower (s.debt borrower + amount)
    minHealthFactor := s.minHealthFactor }

-- Borrow spec.
def borrowSpec (borrower : Address) (amount : Nat) : Spec :=
  { requires := preBorrow borrower amount
    ensures := fun s s' =>
      s'.debt borrower = s.debt borrower + amount ∧
      (forall a, a ≠ borrower -> s'.debt a = s.debt a) ∧
      (forall a, s'.collateral a = s.collateral a) ∧
      s'.minHealthFactor = s.minHealthFactor }

-- Borrow proof.
theorem borrow_sound (s : LState) (borrower : Address) (amount : Nat) :
    preBorrow borrower amount s ->
    (borrowSpec borrower amount).ensures s (borrow borrower amount s) := by
  intro _hpre
  constructor
  · simp [borrow, DumbContracts.update]
  constructor
  · intro a ha
    simp [borrow, DumbContracts.update, ha]
  constructor
  · intro a
    simp [borrow]
  · simp [borrow]

-- Borrow preserves HF.
theorem borrow_preserves_hf (s : LState) (borrower : Address) (amount : Nat) :
    globalHF s ->
    preBorrow borrower amount s ->
    globalHF (borrow borrower amount s) := by
  intro hglobal hpre a
  by_cases h : a = borrower
  · subst h
    dsimp [hfOk, borrow]
    simp [DumbContracts.update]
    exact hpre
  · dsimp [hfOk, borrow]
    have hprev := hglobal a
    simp [DumbContracts.update, h] at hprev ⊢
    exact hprev

-- Repay pre.
def preRepay (borrower : Address) (amount : Nat) (s : LState) : Prop :=
  s.debt borrower >= amount

-- Repay impl.
def repay (borrower : Address) (amount : Nat) (s : LState) : LState :=
  { collateral := s.collateral
    debt := DumbContracts.update s.debt borrower (s.debt borrower - amount)
    minHealthFactor := s.minHealthFactor }

-- Repay spec.
def repaySpec (borrower : Address) (amount : Nat) : Spec :=
  { requires := preRepay borrower amount
    ensures := fun s s' =>
      s'.debt borrower = s.debt borrower - amount ∧
      (forall a, a ≠ borrower -> s'.debt a = s.debt a) ∧
      (forall a, s'.collateral a = s.collateral a) ∧
      s'.minHealthFactor = s.minHealthFactor }

-- Repay proof.
theorem repay_sound (s : LState) (borrower : Address) (amount : Nat) :
    preRepay borrower amount s ->
    (repaySpec borrower amount).ensures s (repay borrower amount s) := by
  intro _hpre
  constructor
  · simp [repay, DumbContracts.update]
  constructor
  · intro a ha
    simp [repay, DumbContracts.update, ha]
  constructor
  · intro a
    simp [repay]
  · simp [repay]

-- Repay preserves HF.
theorem repay_preserves_hf (s : LState) (borrower : Address) (amount : Nat) :
    globalHF s ->
    preRepay borrower amount s ->
    globalHF (repay borrower amount s) := by
  intro hglobal hpre a
  by_cases h : a = borrower
  · subst h
    dsimp [hfOk, repay]
    simp [DumbContracts.update]
    have hprev := hglobal borrower
    have hmono : (s.debt borrower - amount) * s.minHealthFactor <=
        s.debt borrower * s.minHealthFactor := by
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    exact Nat.le_trans hmono hprev
  · dsimp [hfOk, repay]
    have hprev := hglobal a
    simp [DumbContracts.update, h] at hprev ⊢
    exact hprev

-- Withdraw pre.
def preWithdraw (borrower : Address) (amount : Nat) (s : LState) : Prop :=
  s.collateral borrower >= amount ∧
  s.collateral borrower - amount >= s.debt borrower * s.minHealthFactor

-- Withdraw impl.
def withdraw (borrower : Address) (amount : Nat) (s : LState) : LState :=
  { collateral := DumbContracts.update s.collateral borrower (s.collateral borrower - amount)
    debt := s.debt
    minHealthFactor := s.minHealthFactor }

-- Withdraw spec.
def withdrawSpec (borrower : Address) (amount : Nat) : Spec :=
  { requires := preWithdraw borrower amount
    ensures := fun s s' =>
      s'.collateral borrower = s.collateral borrower - amount ∧
      (forall a, a ≠ borrower -> s'.collateral a = s.collateral a) ∧
      (forall a, s'.debt a = s.debt a) ∧
      s'.minHealthFactor = s.minHealthFactor }

-- Withdraw proof.
theorem withdraw_sound (s : LState) (borrower : Address) (amount : Nat) :
    preWithdraw borrower amount s ->
    (withdrawSpec borrower amount).ensures s (withdraw borrower amount s) := by
  intro _hpre
  constructor
  · simp [withdraw, DumbContracts.update]
  constructor
  · intro a ha
    simp [withdraw, DumbContracts.update, ha]
  constructor
  · intro a
    simp [withdraw]
  · simp [withdraw]

-- Withdraw preserves HF.
theorem withdraw_preserves_hf (s : LState) (borrower : Address) (amount : Nat) :
    globalHF s ->
    preWithdraw borrower amount s ->
    globalHF (withdraw borrower amount s) := by
  intro hglobal hpre a
  by_cases h : a = borrower
  · subst h
    dsimp [hfOk, withdraw]
    simp [DumbContracts.update]
    exact hpre.2
  · dsimp [hfOk, withdraw]
    have hprev := hglobal a
    simp [DumbContracts.update, h] at hprev ⊢
    exact hprev

end DumbContracts.Lending
