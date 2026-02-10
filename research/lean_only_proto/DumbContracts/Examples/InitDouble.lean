import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Initialize a slot to double the input if it is currently zero. -/

def initDoubleFun : Fun :=
  { name := "initDouble"
    args := ["slot", "value"]
    body := sstoreIfZero (v "slot") (Expr.mul (v "value") (n 2))
    ret := none }

def initDoubleSpecR (slot value : Nat) : SpecR Store :=
  { requires := fun s => s slot = 0
    ensures := fun s s' => s' = updateStore s slot (value * 2)
    reverts := fun s => s slot != 0 }

theorem initDouble_meets_specR_ok (s : Store) (slot value : Nat) :
    (initDoubleSpecR slot value).requires s ->
    (match execFun initDoubleFun [slot, value] s [] with
      | ExecResult.ok _ s' => (initDoubleSpecR slot value).ensures s s'
      | _ => False) := by
  intro hreq
  have hzero : s slot = 0 := by exact hreq
  simp [initDoubleSpecR, initDoubleFun, sstoreIfZero, letSload, requireZero, requireEq, eq, require,
    execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hzero]

theorem initDouble_meets_specR_reverts (s : Store) (slot value : Nat) :
    (initDoubleSpecR slot value).reverts s ->
    execFun initDoubleFun [slot, value] s [] = ExecResult.reverted := by
  intro hrev
  simp [initDoubleSpecR, initDoubleFun, sstoreIfZero, letSload, requireZero, requireEq, eq, require,
    execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hrev]

end DumbContracts.Examples
