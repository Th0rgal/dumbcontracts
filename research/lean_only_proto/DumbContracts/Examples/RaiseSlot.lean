import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Raise a slot to a minimum value without reverting. -/

def raiseSlotFun : Fun :=
  { name := "raiseSlot"
    args := ["slot", "floor"]
    body := sstoreIfGt (v "slot") (v "floor")
    ret := none }

def raiseSlotSpec (slot floor : Nat) : Spec Store :=
  { requires := fun _ => True
    ensures := fun s s' =>
      s' = updateStore s slot (if floor > s slot then floor else s slot) }

theorem raiseSlot_meets_spec (s : Store) (slot floor : Nat) :
    (raiseSlotSpec slot floor).requires s ->
    (match execFun raiseSlotFun [slot, floor] s [] with
      | ExecResult.ok _ s' => (raiseSlotSpec slot floor).ensures s s'
      | _ => False) := by
  intro _hreq
  by_cases h : floor > s slot
  · simp [raiseSlotFun, raiseSlotSpec, sstoreIfGt, letSload, v, execFun, execStmt, evalExpr,
      bindArgs, emptyEnv, updateEnv, updateStore, h]
  · simp [raiseSlotFun, raiseSlotSpec, sstoreIfGt, letSload, v, execFun, execStmt, evalExpr,
      bindArgs, emptyEnv, updateEnv, updateStore, h]

end DumbContracts.Examples
