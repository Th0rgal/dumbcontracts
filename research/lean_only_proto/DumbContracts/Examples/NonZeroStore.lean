import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Store a value into a slot, but only if the value is non-zero. -/

def setNonZeroFun : Fun :=
  { name := "setNonZero"
    args := ["slot", "value"]
    body := requireNonZero (v "value") (sstoreVar "slot" (v "value"))
    ret := none }

def setNonZeroSpecR (slot value : Nat) : SpecR Store :=
  { requires := fun _ => value != 0
    ensures := fun s s' => s' = updateStore s slot value
    reverts := fun _ => value = 0 }

theorem setNonZero_meets_specR_ok (s : Store) (slot value : Nat) :
    (setNonZeroSpecR slot value).requires s ->
    (match execFun setNonZeroFun [slot, value] s [] with
      | ExecResult.ok _ s' => (setNonZeroSpecR slot value).ensures s s'
      | _ => False) := by
  intro hreq
  have hnonzero : value != 0 := by exact hreq
  simp [setNonZeroSpecR, setNonZeroFun, requireNonZero, require, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, hnonzero]

theorem setNonZero_meets_specR_reverts (s : Store) (slot value : Nat) :
    (setNonZeroSpecR slot value).reverts s ->
    execFun setNonZeroFun [slot, value] s [] = ExecResult.reverted := by
  intro hrev
  simp [setNonZeroSpecR, setNonZeroFun, requireNonZero, require, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, hrev]

end DumbContracts.Examples
