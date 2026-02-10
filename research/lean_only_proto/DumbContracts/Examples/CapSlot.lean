import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Cap a slot to a maximum value without reverting. -/

def capSlotFun : Fun :=
  { name := "capSlot"
    args := ["slot", "cap"]
    body := sstoreIfLt (v "slot") (v "cap")
    ret := none }

def capSlotSpec (slot cap : Nat) : Spec Store :=
  { requires := fun _ => True
    ensures := fun s s' =>
      s' = updateStore s slot (if s slot > cap then cap else s slot) }

theorem capSlot_meets_spec (s : Store) (slot cap : Nat) :
    (capSlotSpec slot cap).requires s ->
    (match execFun capSlotFun [slot, cap] s [] with
      | ExecResult.ok _ s' => (capSlotSpec slot cap).ensures s s'
      | _ => False) := by
  intro _hreq
  by_cases h : cap < s slot
  · simp [capSlotFun, capSlotSpec, sstoreIfLt, letSload, v, execFun, execStmt, evalExpr,
      bindArgs, emptyEnv, updateEnv, updateStore, h]
  · simp [capSlotFun, capSlotSpec, sstoreIfLt, letSload, v, execFun, execStmt, evalExpr,
      bindArgs, emptyEnv, updateEnv, updateStore, h]

end DumbContracts.Examples
