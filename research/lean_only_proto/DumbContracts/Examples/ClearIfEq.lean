import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Clear a slot (store 0) only if it matches an expected value. -/

def clearIfEqFun : Fun :=
  { name := "clearIfEq"
    args := ["slot", "expected"]
    body := sstoreIfEq (v "slot") (v "expected") (n 0)
    ret := none }

def clearIfEqSpecR (slot expected : Nat) : SpecR Store :=
  { requires := fun s => s slot = expected
    ensures := fun s s' => s' = updateStore s slot 0
    reverts := fun s => s slot != expected }

theorem clearIfEq_meets_specR_ok (s : Store) (slot expected : Nat) :
    (clearIfEqSpecR slot expected).requires s ->
    (match execFun clearIfEqFun [slot, expected] s [] with
      | ExecResult.ok _ s' => (clearIfEqSpecR slot expected).ensures s s'
      | _ => False) := by
  intro hreq
  have hmatch : s slot = expected := by exact hreq
  simp [clearIfEqSpecR, clearIfEqFun, sstoreIfEq, requireEq, eq, require, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, letSload, hmatch]

theorem clearIfEq_meets_specR_reverts (s : Store) (slot expected : Nat) :
    (clearIfEqSpecR slot expected).reverts s ->
    execFun clearIfEqFun [slot, expected] s [] = ExecResult.reverted := by
  intro hrev
  simp [clearIfEqSpecR, clearIfEqFun, sstoreIfEq, requireEq, eq, require, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, letSload, hrev]

end DumbContracts.Examples
