import DumbContracts.Core
import DumbContracts.Lang

namespace DumbContracts.Semantics

open DumbContracts
open DumbContracts.Lang

abbrev Env := String -> Nat
abbrev Store := Nat -> Nat

abbrev updateEnv := DumbContracts.updateStr
abbrev updateStore := DumbContracts.updateNat

def boolToNat (b : Bool) : Nat :=
  if b then 1 else 0

def isTruthy (n : Nat) : Bool :=
  n != 0

partial def evalExpr (e : Expr) (env : Env) (store : Store) : Nat :=
  match e with
  | Expr.lit n => n
  | Expr.var v => env v
  | Expr.add a b => evalExpr a env store + evalExpr b env store
  | Expr.sub a b => evalExpr a env store - evalExpr b env store
  | Expr.mul a b => evalExpr a env store * evalExpr b env store
  | Expr.div a b => evalExpr a env store / evalExpr b env store
  | Expr.eq a b => boolToNat <| decide (evalExpr a env store = evalExpr b env store)
  | Expr.lt a b => boolToNat <| decide (evalExpr a env store < evalExpr b env store)
  | Expr.gt a b => boolToNat <| decide (evalExpr a env store > evalExpr b env store)
  | Expr.and a b =>
      let va := isTruthy (evalExpr a env store)
      let vb := isTruthy (evalExpr b env store)
      boolToNat (va && vb)
  | Expr.or a b =>
      let va := isTruthy (evalExpr a env store)
      let vb := isTruthy (evalExpr b env store)
      boolToNat (va || vb)
  | Expr.not a =>
      let va := isTruthy (evalExpr a env store)
      boolToNat (!va)
  | Expr.sload k => store (evalExpr k env store)

inductive ExecResult where
  | ok : Env -> Store -> ExecResult
  | returned : Nat -> Env -> Store -> ExecResult
  | reverted : ExecResult
  deriving Repr

partial def execStmt (s : Stmt) (env : Env) (store : Store) : ExecResult :=
  match s with
  | Stmt.skip => ExecResult.ok env store
  | Stmt.seq a b =>
      match execStmt a env store with
      | ExecResult.ok env' store' => execStmt b env' store'
      | res => res
  | Stmt.let_ v e body =>
      let val := evalExpr e env store
      execStmt body (updateEnv env v val) store
  | Stmt.assign v e =>
      let val := evalExpr e env store
      ExecResult.ok (updateEnv env v val) store
  | Stmt.if_ c t f =>
      let cond := evalExpr c env store
      if cond != 0 then execStmt t env store else execStmt f env store
  | Stmt.sstore k v =>
      let key := evalExpr k env store
      let val := evalExpr v env store
      ExecResult.ok env (updateStore store key val)
  | Stmt.revert => ExecResult.reverted
  | Stmt.return_ v =>
      let val := evalExpr v env store
      ExecResult.returned val env store

end DumbContracts.Semantics
