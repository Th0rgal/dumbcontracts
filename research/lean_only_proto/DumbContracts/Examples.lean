import DumbContracts.Lang
import DumbContracts.Semantics

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics

def getSlotFun : Fun :=
  { name := "getSlot"
    args := ["slot"]
    body := Stmt.return_ (Expr.sload (Expr.var "slot"))
    ret := none }

def storeOf (k v : Nat) : Store :=
  fun x => if x = k then v else 0

theorem getSlot_returns (slot value : Nat) :
    execFun getSlotFun [slot] (storeOf slot value) [] =
      ExecResult.returned [value] (bindArgs emptyEnv ["slot"] [slot]) (storeOf slot value) := by
  simp [getSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv, updateEnv]

end DumbContracts.Examples
