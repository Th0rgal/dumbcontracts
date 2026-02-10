import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Update a slot to the min of its current value and a new input. -/

def updateMinFun : Fun :=
  { name := "updateMin"
    args := ["slot", "value"]
    body :=
      sstoreIfLt (v "slot") (v "value")
    ret := none }

def updateMinSpec (slot value : Nat) : Spec Store :=
  { requires := fun _ => True
    ensures := fun s s' => s' = updateStore s slot (if s slot < value then s slot else value) }

theorem updateMin_meets_spec (s : Store) (slot value : Nat) :
    (updateMinSpec slot value).requires s ->
    (match execFun updateMinFun [slot, value] s [] with
      | ExecResult.ok _ s' => (updateMinSpec slot value).ensures s s'
      | _ => False) := by
  intro _hreq
  by_cases h : value < s slot
  · simp [updateMinFun, updateMinSpec, sstoreIfLt, letSload, v, execFun, execStmt, evalExpr,
      bindArgs, emptyEnv, updateEnv, updateStore, h]
  · simp [updateMinFun, updateMinSpec, sstoreIfLt, letSload, v, execFun, execStmt, evalExpr,
      bindArgs, emptyEnv, updateEnv, updateStore, h]

end DumbContracts.Examples
