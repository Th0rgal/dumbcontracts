import DumbContracts.Core
import DumbContracts.Lang

namespace DumbContracts.Semantics

open DumbContracts
open DumbContracts.Lang

abbrev Env := String -> Nat
abbrev Store := Nat -> Nat
abbrev CallData := List Nat

abbrev updateEnv := DumbContracts.updateStr
abbrev updateStore := DumbContracts.updateNat

def boolToNat (b : Bool) : Nat :=
  if b then 1 else 0

def isTruthy (n : Nat) : Bool :=
  n != 0

def calldataload (cd : CallData) (offset : Nat) : Nat :=
  let idx := offset / 32
  cd.getD idx 0

partial def evalExpr (e : Expr) (env : Env) (store : Store) (cd : CallData) : Nat :=
  match e with
  | Expr.lit n => n
  | Expr.var v => env v
  | Expr.add a b => evalExpr a env store cd + evalExpr b env store cd
  | Expr.sub a b => evalExpr a env store cd - evalExpr b env store cd
  | Expr.mul a b => evalExpr a env store cd * evalExpr b env store cd
  | Expr.div a b => evalExpr a env store cd / evalExpr b env store cd
  | Expr.eq a b => boolToNat <| decide (evalExpr a env store cd = evalExpr b env store cd)
  | Expr.lt a b => boolToNat <| decide (evalExpr a env store cd < evalExpr b env store cd)
  | Expr.gt a b => boolToNat <| decide (evalExpr a env store cd > evalExpr b env store cd)
  | Expr.and a b =>
      let va := isTruthy (evalExpr a env store cd)
      let vb := isTruthy (evalExpr b env store cd)
      boolToNat (va && vb)
  | Expr.or a b =>
      let va := isTruthy (evalExpr a env store cd)
      let vb := isTruthy (evalExpr b env store cd)
      boolToNat (va || vb)
  | Expr.not a =>
      let va := isTruthy (evalExpr a env store cd)
      boolToNat (!va)
  | Expr.sload k => store (evalExpr k env store cd)
  | Expr.calldataload k => calldataload cd (evalExpr k env store cd)

inductive ExecResult where
  | ok : Env -> Store -> ExecResult
  | returned : List Nat -> Env -> Store -> ExecResult
  | reverted : ExecResult
  deriving Repr

partial def execStmt (s : Stmt) (env : Env) (store : Store) (cd : CallData) : ExecResult :=
  match s with
  | Stmt.skip => ExecResult.ok env store
  | Stmt.seq a b =>
      match execStmt a env store cd with
      | ExecResult.ok env' store' => execStmt b env' store' cd
      | res => res
  | Stmt.let_ v e body =>
      let val := evalExpr e env store cd
      execStmt body (updateEnv env v val) store cd
  | Stmt.assign v e =>
      let val := evalExpr e env store cd
      ExecResult.ok (updateEnv env v val) store
  | Stmt.if_ c t f =>
      let cond := evalExpr c env store cd
      if cond != 0 then execStmt t env store cd else execStmt f env store cd
  | Stmt.sstore k v =>
      let key := evalExpr k env store cd
      let val := evalExpr v env store cd
      ExecResult.ok env (updateStore store key val)
  | Stmt.revert => ExecResult.reverted
  | Stmt.return_ v =>
      let val := evalExpr v env store cd
      ExecResult.returned [val] env store

def emptyEnv : Env := fun _ => 0

def bindArgs (env : Env) (args : List String) (vals : List Nat) : Env :=
  match args, vals with
  | [], _ => env
  | _, [] => env
  | a :: as, v :: vs => bindArgs (updateEnv env a v) as vs

def execFun (f : Fun) (args : List Nat) (store : Store) (cd : CallData) : ExecResult :=
  let env0 := bindArgs emptyEnv f.args args
  execStmt f.body env0 store cd

end DumbContracts.Semantics
