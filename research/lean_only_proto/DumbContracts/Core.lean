import Std

namespace DumbContracts

abbrev Address := Nat
abbrev EWord := Nat

structure MsgCtx where
  sender : Address
  value : EWord
  blockNumber : EWord
  timestamp : EWord

structure Log where
  topics : List EWord
  data : List EWord

structure CState where
  storage : EWord -> EWord
  balances : Address -> EWord
  logs : List Log

abbrev Pred (S : Type) := S -> Prop
abbrev Rel (S : Type) := S -> S -> Prop

structure Spec (S : Type) where
  requires : Pred S
  ensures : Rel S

structure SpecR (S : Type) where
  requires : Pred S
  ensures : Rel S
  reverts : Pred S

-- Map update.
def update {A : Type} (f : Address -> A) (k : Address) (v : A) (a : Address) : A :=
  if a = k then v else f a

def updateNat {A : Type} (f : Nat -> A) (k : Nat) (v : A) (a : Nat) : A :=
  if a = k then v else f a

def updateStr {A : Type} (f : String -> A) (k : String) (v : A) (a : String) : A :=
  if a = k then v else f a

theorem update_eq {A : Type} (f : Address -> A) (k : Address) (v : A) :
  update f k v k = v := by
  simp [update]

theorem update_ne {A : Type} (f : Address -> A) (k : Address) (v : A) (a : Address)
    (h : a ≠ k) : update f k v a = f a := by
  simp [update, h]

theorem updateNat_eq {A : Type} (f : Nat -> A) (k : Nat) (v : A) :
  updateNat f k v k = v := by
  simp [updateNat]

theorem updateNat_ne {A : Type} (f : Nat -> A) (k : Nat) (v : A) (a : Nat)
    (h : a ≠ k) : updateNat f k v a = f a := by
  simp [updateNat, h]

theorem updateStr_eq {A : Type} (f : String -> A) (k : String) (v : A) :
  updateStr f k v k = v := by
  simp [updateStr]

theorem updateStr_ne {A : Type} (f : String -> A) (k : String) (v : A) (a : String)
    (h : a ≠ k) : updateStr f k v a = f a := by
  simp [updateStr, h]

end DumbContracts
