import DumbContracts.Lang
import DumbContracts.Semantics

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts

def getSlotFun : Fun :=
  { name := "getSlot"
    args := ["slot"]
    body := Stmt.return_ (Expr.sload (Expr.var "slot"))
    ret := none }

def setSlotFun : Fun :=
  { name := "setSlot"
    args := ["slot", "value"]
    body := Stmt.sstore (Expr.var "slot") (Expr.var "value")
    ret := none }

def addSlotFun : Fun :=
  { name := "addSlot"
    args := ["slot", "delta"]
    body := Stmt.sstore (Expr.var "slot") (Expr.add (Expr.sload (Expr.var "slot")) (Expr.var "delta"))
    ret := none }

def guardedAddSlotFun : Fun :=
  { name := "guardedAddSlot"
    args := ["slot", "delta"]
    body := Stmt.if_
      (Expr.gt (Expr.var "delta") (Expr.lit 0))
      (Stmt.sstore (Expr.var "slot")
        (Expr.add (Expr.sload (Expr.var "slot")) (Expr.var "delta")))
      Stmt.revert
    ret := none }

def storeOf (k v : Nat) : Store :=
  fun x => if x = k then v else 0

def riskStore (collateral debt minHF : Nat) : Store :=
  fun x =>
    if x = 0 then collateral
    else if x = 1 then debt
    else if x = 2 then minHF
    else 0

def setRiskFun : Fun :=
  { name := "setRisk"
    args := ["collateral", "debt", "minHF"]
    body :=
      Stmt.sstore (Expr.lit 0) (Expr.var "collateral") ;;
      Stmt.sstore (Expr.lit 1) (Expr.var "debt") ;;
      Stmt.sstore (Expr.lit 2) (Expr.var "minHF")
    ret := none }

def checkHealthFun : Fun :=
  { name := "checkHealth"
    args := []
    body := Stmt.if_
      (Expr.lt (Expr.sload (Expr.lit 0))
        (Expr.mul (Expr.sload (Expr.lit 1)) (Expr.sload (Expr.lit 2))))
      Stmt.revert
      Stmt.skip
    ret := none }

def balanceSlot (addr : Nat) : Nat :=
  1000 + addr

def totalSupplySlot : Nat :=
  0

def totalSupply (s : Store) : Nat :=
  s totalSupplySlot

def setBalance (s : Store) (addr val : Nat) : Store :=
  updateStore s (balanceSlot addr) val

def sum2 (s : Store) (a b : Nat) : Nat :=
  s (balanceSlot a) + s (balanceSlot b)

def sumBalances (s : Store) : List Nat -> Nat
  | [] => 0
  | a :: rest => s (balanceSlot a) + sumBalances rest

theorem updateStore_same (s : Store) (k : Nat) :
    updateStore s k (s k) = s := by
  funext a
  by_cases h : a = k
  · simp [updateStore, updateNat, h]
  · simp [updateStore, updateNat, h]

theorem updateStore_shadow (s : Store) (k v1 v2 : Nat) :
    updateStore (updateStore s k v1) k v2 = updateStore s k v2 := by
  funext a
  by_cases h : a = k
  · simp [updateStore, updateNat, h]
  · simp [updateStore, updateNat, h]

theorem balanceSlot_ne (a b : Nat) (h : a ≠ b) : balanceSlot a ≠ balanceSlot b := by
  intro h'
  apply h
  exact Nat.add_left_cancel h'

theorem balanceSlot_ne_total (addr : Nat) : balanceSlot addr ≠ totalSupplySlot := by
  simp [balanceSlot, totalSupplySlot]

def transferFun : Fun :=
  { name := "transfer"
    args := ["from", "to", "amount"]
    body := Stmt.if_
      (Expr.eq (Expr.var "to") (Expr.lit 0))
      Stmt.revert
      (Stmt.if_
        (Expr.lt (Expr.sload (Expr.add (Expr.lit 1000) (Expr.var "from"))) (Expr.var "amount"))
        Stmt.revert
        (Stmt.sstore
            (Expr.add (Expr.lit 1000) (Expr.var "from"))
            (Expr.sub
              (Expr.sload (Expr.add (Expr.lit 1000) (Expr.var "from")))
              (Expr.var "amount"))
          ;;
          Stmt.sstore
            (Expr.add (Expr.lit 1000) (Expr.var "to"))
            (Expr.add
              (Expr.sload (Expr.add (Expr.lit 1000) (Expr.var "to")))
              (Expr.var "amount"))))
    ret := none }

theorem getSlot_returns (slot value : Nat) :
    execFun getSlotFun [slot] (storeOf slot value) [] =
      ExecResult.returned [value] (bindArgs emptyEnv ["slot"] [slot]) (storeOf slot value) := by
  simp [getSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv, updateEnv]

theorem setSlot_updates (slot value : Nat) :
    execFun setSlotFun [slot, value] (storeOf slot 0) [] =
      ExecResult.ok (bindArgs emptyEnv ["slot", "value"] [slot, value]) (storeOf slot value) := by
  simp [setSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv, updateEnv, updateStore]

theorem addSlot_updates (slot base delta : Nat) :
    execFun addSlotFun [slot, delta] (storeOf slot base) [] =
      ExecResult.ok (bindArgs emptyEnv ["slot", "delta"] [slot, delta]) (storeOf slot (base + delta)) := by
  simp [addSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv, updateEnv, updateStore]

theorem set_then_get (slot value : Nat) :
    (match execFun setSlotFun [slot, value] (storeOf slot 0) [] with
      | ExecResult.ok _ store1 =>
          execFun getSlotFun [slot] store1 [] =
            ExecResult.returned [value] (bindArgs emptyEnv ["slot"] [slot]) (storeOf slot value)
      | _ => False) := by
  simp [setSlotFun, getSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv, updateEnv, updateStore]

theorem add_then_get (slot base delta : Nat) :
    (match execFun addSlotFun [slot, delta] (storeOf slot base) [] with
      | ExecResult.ok _ store1 =>
          execFun getSlotFun [slot] store1 [] =
            ExecResult.returned [base + delta] (bindArgs emptyEnv ["slot"] [slot]) (storeOf slot (base + delta))
      | _ => False) := by
  simp [addSlotFun, getSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv, updateEnv, updateStore]

theorem guarded_add_updates (slot base delta : Nat) (h : delta > 0) :
    execFun guardedAddSlotFun [slot, delta] (storeOf slot base) [] =
      ExecResult.ok (bindArgs emptyEnv ["slot", "delta"] [slot, delta]) (storeOf slot (base + delta)) := by
  simp [guardedAddSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv, updateEnv, updateStore, h]

theorem guarded_add_reverts (slot base delta : Nat) (h : delta = 0) :
    execFun guardedAddSlotFun [slot, delta] (storeOf slot base) [] =
      ExecResult.reverted := by
  simp [guardedAddSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv, updateEnv, updateStore, h]

-- Storage specs (Store-level).
def addSlotSpec (slot delta : Nat) : Spec Store :=
  { requires := fun _ => True
    ensures := fun s s' => s' = updateStore s slot (s slot + delta) }

def guardedAddSlotSpec (slot delta : Nat) : Spec Store :=
  { requires := fun _ => delta > 0
    ensures := fun s s' => s' = updateStore s slot (s slot + delta) }

def guardedAddSlotSpecR (slot delta : Nat) : SpecR Store :=
  { requires := fun _ => delta > 0
    ensures := fun s s' => s' = updateStore s slot (s slot + delta)
    reverts := fun _ => delta = 0 }

theorem addSlot_meets_spec (s : Store) (slot delta : Nat) :
    (addSlotSpec slot delta).requires s ->
    (match execFun addSlotFun [slot, delta] s [] with
      | ExecResult.ok _ s' => (addSlotSpec slot delta).ensures s s'
      | _ => False) := by
  intro _hreq
  simp [addSlotSpec, addSlotFun, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore]

theorem guardedAddSlot_meets_spec (s : Store) (slot delta : Nat) :
    (guardedAddSlotSpec slot delta).requires s ->
    (match execFun guardedAddSlotFun [slot, delta] s [] with
      | ExecResult.ok _ s' => (guardedAddSlotSpec slot delta).ensures s s'
      | _ => False) := by
  intro hreq
  have hpos : delta > 0 := by exact hreq
  simp [guardedAddSlotSpec, guardedAddSlotFun, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, hpos]

theorem guardedAddSlot_meets_specR_ok (s : Store) (slot delta : Nat) :
    (guardedAddSlotSpecR slot delta).requires s ->
    (match execFun guardedAddSlotFun [slot, delta] s [] with
      | ExecResult.ok _ s' => (guardedAddSlotSpecR slot delta).ensures s s'
      | _ => False) := by
  intro hreq
  have hpos : delta > 0 := by exact hreq
  simp [guardedAddSlotSpecR, guardedAddSlotFun, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, hpos]

theorem guardedAddSlot_meets_specR_reverts (s : Store) (slot delta : Nat) :
    (guardedAddSlotSpecR slot delta).reverts s ->
    execFun guardedAddSlotFun [slot, delta] s [] = ExecResult.reverted := by
  intro hrev
  simp [guardedAddSlotSpecR, guardedAddSlotFun, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, hrev]

theorem guardedAddSlot_reverts_when_not_requires (slot delta : Nat) (h : delta = 0) :
    (guardedAddSlotSpec slot delta).requires (storeOf slot 0) = False ∧
    execFun guardedAddSlotFun [slot, delta] (storeOf slot 0) [] = ExecResult.reverted := by
  constructor
  · simp [guardedAddSlotSpec, h]
  · simp [guardedAddSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv,
      updateEnv, updateStore, h]

theorem setRisk_updates (collateral debt minHF : Nat) :
    execFun setRiskFun [collateral, debt, minHF] (riskStore 0 0 0) [] =
      ExecResult.ok
        (bindArgs emptyEnv ["collateral", "debt", "minHF"] [collateral, debt, minHF])
        (riskStore collateral debt minHF) := by
  simp [setRiskFun, execFun, execStmt, evalExpr, riskStore, bindArgs, emptyEnv, updateEnv, updateStore]

theorem checkHealth_ok (collateral debt minHF : Nat) (h : debt * minHF <= collateral) :
    execFun checkHealthFun [] (riskStore collateral debt minHF) [] =
      ExecResult.ok (bindArgs emptyEnv [] []) (riskStore collateral debt minHF) := by
  simp [checkHealthFun, execFun, execStmt, evalExpr, riskStore, bindArgs, emptyEnv, updateEnv, updateStore,
    not_lt_of_ge h]

theorem checkHealth_reverts (collateral debt minHF : Nat) (h : collateral < debt * minHF) :
    execFun checkHealthFun [] (riskStore collateral debt minHF) [] =
      ExecResult.reverted := by
  simp [checkHealthFun, execFun, execStmt, evalExpr, riskStore, bindArgs, emptyEnv, updateEnv, updateStore, h]

-- Risk specs (Store-level).
def setRiskSpec (collateral debt minHF : Nat) : Spec Store :=
  { requires := fun _ => True
    ensures := fun s s' =>
      s' = updateStore (updateStore (updateStore s 0 collateral) 1 debt) 2 minHF }

def riskOk (store : Store) : Prop :=
  store 1 * store 2 <= store 0

def checkHealthSpec : Spec Store :=
  { requires := riskOk
    ensures := fun s s' => s' = s }

def checkHealthSpecR : SpecR Store :=
  { requires := riskOk
    ensures := fun s s' => s' = s
    reverts := fun s => s 0 < s 1 * s 2 }

theorem setRisk_meets_spec (s : Store) (collateral debt minHF : Nat) :
    (setRiskSpec collateral debt minHF).requires s ->
    (match execFun setRiskFun [collateral, debt, minHF] s [] with
      | ExecResult.ok _ s' => (setRiskSpec collateral debt minHF).ensures s s'
      | _ => False) := by
  intro _hreq
  simp [setRiskSpec, setRiskFun, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore]

theorem checkHealth_meets_spec (s : Store) :
    checkHealthSpec.requires s ->
    (match execFun checkHealthFun [] s [] with
      | ExecResult.ok _ s' => checkHealthSpec.ensures s s'
      | _ => False) := by
  intro hreq
  simp [checkHealthSpec, riskOk, checkHealthFun, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, not_lt_of_ge hreq]

theorem checkHealth_meets_specR_ok (s : Store) :
    checkHealthSpecR.requires s ->
    (match execFun checkHealthFun [] s [] with
      | ExecResult.ok _ s' => checkHealthSpecR.ensures s s'
      | _ => False) := by
  intro hreq
  simp [checkHealthSpecR, riskOk, checkHealthFun, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, not_lt_of_ge hreq]

theorem checkHealth_meets_specR_reverts (s : Store) :
    checkHealthSpecR.reverts s ->
    execFun checkHealthFun [] s [] = ExecResult.reverted := by
  intro hrev
  simp [checkHealthSpecR, checkHealthFun, execFun, execStmt, evalExpr, bindArgs,
    emptyEnv, updateEnv, updateStore, hrev]

-- Token-style specs (Store-level).
def transferSpecR (from to amount : Nat) : SpecR Store :=
  { requires := fun s => to ≠ 0 ∧ s (balanceSlot from) >= amount
    ensures := fun s s' =>
      s' =
        setBalance
          (setBalance s from (s (balanceSlot from) - amount))
          to (s (balanceSlot to) + amount)
    reverts := fun s => to = 0 ∨ s (balanceSlot from) < amount }

def transferSpecRNoSelf (from to amount : Nat) : SpecR Store :=
  { requires := fun s => to ≠ 0 ∧ from ≠ to ∧ s (balanceSlot from) >= amount
    ensures := (transferSpecR from to amount).ensures
    reverts := fun s => to = 0 ∨ from = to ∨ s (balanceSlot from) < amount }

def transferStoreSeq (s : Store) (from to amount : Nat) : Store :=
  let s1 := setBalance s from (s (balanceSlot from) - amount)
  setBalance s1 to (s1 (balanceSlot to) + amount)

def transferSpecRSeq (from to amount : Nat) : SpecR Store :=
  { requires := fun s => to ≠ 0 ∧ s (balanceSlot from) >= amount
    ensures := fun s s' => s' = transferStoreSeq s from to amount
    reverts := fun s => to = 0 ∨ s (balanceSlot from) < amount }

theorem transferStoreSeq_eq_transferSpecR_update (s : Store) (from to amount : Nat)
    (hneq : from ≠ to) :
    transferStoreSeq s from to amount =
      setBalance
        (setBalance s from (s (balanceSlot from) - amount))
        to (s (balanceSlot to) + amount) := by
  have hslot : balanceSlot from ≠ balanceSlot to := by
    exact balanceSlot_ne from to hneq
  have hs1 :
      (setBalance s from (s (balanceSlot from) - amount)) (balanceSlot to) =
        s (balanceSlot to) := by
    simp [setBalance, updateStore, updateNat, hslot]
  simp [transferStoreSeq, setBalance, updateStore, updateNat, hs1]

theorem transferSpecRSeq_ensures_eq_transferSpecR (s s' : Store) (from to amount : Nat)
    (hneq : from ≠ to) :
    (transferSpecRSeq from to amount).ensures s s' ↔
      (transferSpecR from to amount).ensures s s' := by
  constructor
  · intro hens
    have hs : s' = transferStoreSeq s from to amount := by
      simpa [transferSpecRSeq] using hens
    have hs' :
        s' =
          setBalance
            (setBalance s from (s (balanceSlot from) - amount))
            to (s (balanceSlot to) + amount) := by
      simpa [transferStoreSeq_eq_transferSpecR_update s from to amount hneq] using hs
    simpa [transferSpecR] using hs'
  · intro hens
    have hs :
        s' =
          setBalance
            (setBalance s from (s (balanceSlot from) - amount))
            to (s (balanceSlot to) + amount) := by
      simpa [transferSpecR] using hens
    have hs' : s' = transferStoreSeq s from to amount := by
      simpa [transferStoreSeq_eq_transferSpecR_update s from to amount hneq] using hs
    simpa [transferSpecRSeq] using hs'

theorem transfer_meets_specR_ok (s : Store) (from to amount : Nat) :
    (transferSpecR from to amount).requires s ->
    (match execFun transferFun [from, to, amount] s [] with
      | ExecResult.ok _ s' => (transferSpecR from to amount).ensures s s'
      | _ => False) := by
  intro hreq
  have hto : to ≠ 0 := hreq.left
  have hbal : s (balanceSlot from) >= amount := hreq.right
  have hnotlt : ¬ s (balanceSlot from) < amount := by
    exact not_lt_of_ge hbal
  simp [transferSpecR, transferFun, execFun, execStmt, evalExpr, bindArgs, emptyEnv,
    updateEnv, updateStore, balanceSlot, setBalance, hto, hnotlt]

theorem transfer_meets_specRNoSelf_ok (s : Store) (from to amount : Nat) :
    (transferSpecRNoSelf from to amount).requires s ->
    (match execFun transferFun [from, to, amount] s [] with
      | ExecResult.ok _ s' => (transferSpecRNoSelf from to amount).ensures s s'
      | _ => False) := by
  intro hreq
  have hreq' : (transferSpecR from to amount).requires s := by
    exact And.intro hreq.left hreq.right.right
  simpa [transferSpecRNoSelf] using (transfer_meets_specR_ok s from to amount hreq')

theorem transfer_meets_specRSeq_ok (s : Store) (from to amount : Nat) :
    (transferSpecRSeq from to amount).requires s ->
    (match execFun transferFun [from, to, amount] s [] with
      | ExecResult.ok _ s' => (transferSpecRSeq from to amount).ensures s s'
      | _ => False) := by
  intro hreq
  have hto : to ≠ 0 := hreq.left
  have hbal : s (balanceSlot from) >= amount := hreq.right
  have hnotlt : ¬ s (balanceSlot from) < amount := by
    exact not_lt_of_ge hbal
  simp [transferSpecRSeq, transferStoreSeq, transferFun, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, balanceSlot, setBalance, hto, hnotlt]

theorem transfer_meets_specR_reverts (s : Store) (from to amount : Nat) :
    (transferSpecR from to amount).reverts s ->
    execFun transferFun [from, to, amount] s [] = ExecResult.reverted := by
  intro hrev
  cases hrev with
  | inl hto =>
      simp [transferFun, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv,
        updateStore, balanceSlot, setBalance, hto]
  | inr hlt =>
      by_cases hto : to = 0
      · simp [transferFun, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv,
          updateStore, balanceSlot, setBalance, hto]
      · simp [transferFun, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv,
          updateStore, balanceSlot, setBalance, hto, hlt]

theorem transfer_self_noop (s : Store) (from amount : Nat)
    (hto : from ≠ 0) (hbal : s (balanceSlot from) >= amount) :
    execFun transferFun [from, from, amount] s [] =
      ExecResult.ok (bindArgs emptyEnv ["from", "to", "amount"] [from, from, amount]) s := by
  have hnotlt : ¬ s (balanceSlot from) < amount := by
    exact not_lt_of_ge hbal
  have hs :
      execFun transferFun [from, from, amount] s [] =
        ExecResult.ok
          (bindArgs emptyEnv ["from", "to", "amount"] [from, from, amount])
          (updateStore
            (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
            (balanceSlot from)
            (s (balanceSlot from) - amount + amount)) := by
    simp [transferFun, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv,
      updateStore, balanceSlot, hto, hnotlt]
  have hshadow :
      updateStore
        (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
        (balanceSlot from)
        (s (balanceSlot from) - amount + amount)
        =
        updateStore s (balanceSlot from) (s (balanceSlot from) - amount + amount) := by
    exact updateStore_shadow s (balanceSlot from)
      (s (balanceSlot from) - amount) (s (balanceSlot from) - amount + amount)
  have hval : s (balanceSlot from) - amount + amount = s (balanceSlot from) := by
    exact Nat.sub_add_cancel hbal
  have hs' :
      updateStore
        (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
        (balanceSlot from)
        (s (balanceSlot from) - amount + amount)
        = s := by
    calc
      updateStore
          (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
          (balanceSlot from)
          (s (balanceSlot from) - amount + amount)
          =
          updateStore s (balanceSlot from) (s (balanceSlot from) - amount + amount) := by
            exact hshadow
      _ = updateStore s (balanceSlot from) (s (balanceSlot from)) := by
            simp [hval]
      _ = s := by
            exact updateStore_same s (balanceSlot from)
  simpa [hs'] using hs

theorem transferSpecRSeq_self_ensures_noop (s s' : Store) (from amount : Nat)
    (hbal : s (balanceSlot from) >= amount)
    (hens : (transferSpecRSeq from from amount).ensures s s') :
    s' = s := by
  have hval : s (balanceSlot from) - amount + amount = s (balanceSlot from) := by
    exact Nat.sub_add_cancel hbal
  have hs :
      s' =
        updateStore
          (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
          (balanceSlot from)
          (s (balanceSlot from) - amount + amount) := by
    simpa [transferSpecRSeq, transferStoreSeq, setBalance, updateStore, updateNat] using hens
  have hshadow :
      updateStore
        (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
        (balanceSlot from)
        (s (balanceSlot from) - amount + amount)
        =
        updateStore s (balanceSlot from) (s (balanceSlot from) - amount + amount) := by
    exact updateStore_shadow s (balanceSlot from)
      (s (balanceSlot from) - amount) (s (balanceSlot from) - amount + amount)
  have hs' :
      s' = updateStore s (balanceSlot from) (s (balanceSlot from) - amount + amount) := by
    calc
      s' =
          updateStore
            (updateStore s (balanceSlot from) (s (balanceSlot from) - amount))
            (balanceSlot from)
            (s (balanceSlot from) - amount + amount) := by
              exact hs
      _ = updateStore s (balanceSlot from) (s (balanceSlot from) - amount + amount) := by
              exact hshadow
  calc
    s' = updateStore s (balanceSlot from) (s (balanceSlot from)) := by
          simpa [hval] using hs'
    _ = s := by
          exact updateStore_same s (balanceSlot from)

theorem transferSpecR_self_balance_increases (s s' : Store) (from amount : Nat)
    (hens : (transferSpecR from from amount).ensures s s') :
    s' (balanceSlot from) = s (balanceSlot from) + amount := by
  have hs :
      s' =
        setBalance
          (setBalance s from (s (balanceSlot from) - amount))
          from (s (balanceSlot from) + amount) := by
    simpa [transferSpecR] using hens
  have hshadow :
      setBalance
          (setBalance s from (s (balanceSlot from) - amount))
          from (s (balanceSlot from) + amount)
        =
        setBalance s from (s (balanceSlot from) + amount) := by
    simp [setBalance, updateStore_shadow]
  calc
    s' (balanceSlot from)
        = (setBalance s from (s (balanceSlot from) + amount)) (balanceSlot from) := by
            simpa [hs, hshadow]
    _ = s (balanceSlot from) + amount := by
            simp [setBalance, updateStore, updateNat]

theorem transferSpecR_self_ensures_not_s (s : Store) (from amount : Nat)
    (hpos : amount > 0) :
    ¬ (transferSpecR from from amount).ensures s s := by
  intro hens
  have hbal :
      s (balanceSlot from) = s (balanceSlot from) + amount := by
    simpa using (transferSpecR_self_balance_increases s s from amount hens)
  have h' : s (balanceSlot from) + amount = s (balanceSlot from) + 0 := by
    simpa using hbal.symm
  have hzero : amount = 0 := by
    exact Nat.add_left_cancel h'
  exact (ne_of_gt hpos) hzero

theorem transfer_preserves_sum2 (s s' : Store) (from to amount : Nat)
    (hreq : (transferSpecR from to amount).requires s) (hneq : from ≠ to) :
    (transferSpecR from to amount).ensures s s' ->
    sum2 s from to = sum2 s' from to := by
  intro h
  have hbal : amount <= s (balanceSlot from) := by
    exact hreq.right
  have hslot : balanceSlot from ≠ balanceSlot to := by
    exact balanceSlot_ne from to hneq
  have hs :
      s' =
        setBalance
          (setBalance s from (s (balanceSlot from) - amount))
          to (s (balanceSlot to) + amount) := by
    simpa [transferSpecR] using h
  calc
    sum2 s from to
        = s (balanceSlot from) + s (balanceSlot to) := by
            simp [sum2]
    _ = (s (balanceSlot from) - amount + amount) + s (balanceSlot to) := by
            simp [Nat.sub_add_cancel hbal, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = (s (balanceSlot from) - amount) + (s (balanceSlot to) + amount) := by
            simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    _ = sum2 s' from to := by
            simp [sum2, hs, setBalance, updateStore, updateNat, balanceSlot, hslot, Nat.add_assoc]

theorem transfer_preserves_other_balance (s s' : Store) (from to amount addr : Nat)
    (hfrom : addr ≠ from) (hto : addr ≠ to) :
    (transferSpecR from to amount).ensures s s' ->
    s' (balanceSlot addr) = s (balanceSlot addr) := by
  intro h
  have hs :
      s' =
        setBalance
          (setBalance s from (s (balanceSlot from) - amount))
          to (s (balanceSlot to) + amount) := by
    simpa [transferSpecR] using h
  have hslot_from : balanceSlot addr ≠ balanceSlot from := by
    exact balanceSlot_ne addr from hfrom
  have hslot_to : balanceSlot addr ≠ balanceSlot to := by
    exact balanceSlot_ne addr to hto
  simp [hs, setBalance, updateStore, updateNat, hslot_to, hslot_from]

theorem transfer_preserves_sum_list (s s' : Store) (from to amount : Nat) (addrs : List Nat)
    (hnotfrom : from ∉ addrs) (hnotto : to ∉ addrs)
    (hens : (transferSpecR from to amount).ensures s s') :
    sumBalances s addrs = sumBalances s' addrs := by
  induction addrs with
  | nil =>
      simp [sumBalances]
  | cons a rest ih =>
      have hnotfrom' : a ≠ from := by
        intro h
        apply hnotfrom
        simp [h]
      have hnotto' : a ≠ to := by
        intro h
        apply hnotto
        simp [h]
      have hnotfrom_tail : from ∉ rest := by
        intro hmem
        apply hnotfrom
        simp [hmem]
      have hnotto_tail : to ∉ rest := by
        intro hmem
        apply hnotto
        simp [hmem]
      have hbal :
          s' (balanceSlot a) = s (balanceSlot a) :=
        transfer_preserves_other_balance s s' from to amount hnotfrom' hnotto' hens
      have htail :
          sumBalances s rest = sumBalances s' rest :=
        ih hnotfrom_tail hnotto_tail hens
      simp [sumBalances, hbal, htail]

theorem transfer_preserves_sum_from_to_rest (s s' : Store) (from to amount : Nat) (rest : List Nat)
    (hreq : (transferSpecR from to amount).requires s) (hneq : from ≠ to)
    (hnotfrom : from ∉ rest) (hnotto : to ∉ rest)
    (hens : (transferSpecR from to amount).ensures s s') :
    sumBalances s (from :: to :: rest) = sumBalances s' (from :: to :: rest) := by
  have hsum2 : sum2 s from to = sum2 s' from to :=
    transfer_preserves_sum2 s s' from to amount hreq hneq hens
  have hrest : sumBalances s rest = sumBalances s' rest :=
    transfer_preserves_sum_list s s' from to amount rest hnotfrom hnotto hens
  calc
    sumBalances s (from :: to :: rest)
        = (s (balanceSlot from) + s (balanceSlot to)) + sumBalances s rest := by
            simp [sumBalances, Nat.add_assoc]
    _ = (s' (balanceSlot from) + s' (balanceSlot to)) + sumBalances s rest := by
            simpa [sum2] using hsum2
    _ = (s' (balanceSlot from) + s' (balanceSlot to)) + sumBalances s' rest := by
            simp [hrest]
    _ = sumBalances s' (from :: to :: rest) := by
            simp [sumBalances, Nat.add_assoc]

theorem transfer_preserves_totalSupply (s s' : Store) (from to amount : Nat)
    (hens : (transferSpecR from to amount).ensures s s') :
    totalSupply s' = totalSupply s := by
  have hs :
      s' =
        setBalance
          (setBalance s from (s (balanceSlot from) - amount))
          to (s (balanceSlot to) + amount) := by
    simpa [transferSpecR] using hens
  have hslot_from : balanceSlot from ≠ totalSupplySlot := by
    exact balanceSlot_ne_total from
  have hslot_to : balanceSlot to ≠ totalSupplySlot := by
    exact balanceSlot_ne_total to
  simp [totalSupply, hs, setBalance, updateStore, updateNat, hslot_to, hslot_from, totalSupplySlot]

theorem transfer_preserves_supply_list (s s' : Store) (from to amount : Nat) (rest : List Nat)
    (hreq : (transferSpecR from to amount).requires s) (hneq : from ≠ to)
    (hnotfrom : from ∉ rest) (hnotto : to ∉ rest)
    (hsupply : sumBalances s (from :: to :: rest) = totalSupply s)
    (hens : (transferSpecR from to amount).ensures s s') :
    sumBalances s' (from :: to :: rest) = totalSupply s' := by
  have hsum :
      sumBalances s (from :: to :: rest) = sumBalances s' (from :: to :: rest) :=
    transfer_preserves_sum_from_to_rest s s' from to amount rest hreq hneq hnotfrom hnotto hens
  have htot : totalSupply s' = totalSupply s :=
    transfer_preserves_totalSupply s s' from to amount hens
  calc
    sumBalances s' (from :: to :: rest)
        = sumBalances s (from :: to :: rest) := by
            symm
            exact hsum
    _ = totalSupply s := by
            exact hsupply
    _ = totalSupply s' := by
            symm
            exact htot

end DumbContracts.Examples
