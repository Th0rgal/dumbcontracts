import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Update a slot to the max of its current value and a new input. -/

def updateMaxFun : Fun :=
  { name := "updateMax"
    args := ["slot", "value"]
    body :=
      letSload "current" (v "slot")
        (sstoreMax (v "slot") (v "current") (v "value"))
    ret := none }

def updateMaxSpec (slot value : Nat) : Spec Store :=
  { requires := fun _ => True
    ensures := fun s s' => s' = updateStore s slot (if s slot > value then s slot else value) }

theorem updateMax_meets_spec (s : Store) (slot value : Nat) :
    (updateMaxSpec slot value).requires s ->
    (match execFun updateMaxFun [slot, value] s [] with
      | ExecResult.ok _ s' => (updateMaxSpec slot value).ensures s s'
      | _ => False) := by
  intro _hreq
  by_cases h : s slot > value
  · simp [updateMaxFun, updateMaxSpec, letSload, sstoreMax, v, execFun, execStmt, evalExpr,
      bindArgs, emptyEnv, updateEnv, updateStore, h]
  · simp [updateMaxFun, updateMaxSpec, letSload, sstoreMax, v, execFun, execStmt, evalExpr,
      bindArgs, emptyEnv, updateEnv, updateStore, h]

end DumbContracts.Examples
