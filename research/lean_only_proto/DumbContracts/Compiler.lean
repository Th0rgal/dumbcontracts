import DumbContracts.Lang
import DumbContracts.Yul

namespace DumbContracts.Compiler

open DumbContracts.Lang
open DumbContracts.Yul

def compileExpr : Lang.Expr -> Yul.Expr
  | Lang.Expr.lit n => Yul.Expr.lit n
  | Lang.Expr.var v => Yul.Expr.var v
  | Lang.Expr.add a b => Yul.Expr.call "add" [compileExpr a, compileExpr b]
  | Lang.Expr.sub a b => Yul.Expr.call "sub" [compileExpr a, compileExpr b]
  | Lang.Expr.mul a b => Yul.Expr.call "mul" [compileExpr a, compileExpr b]
  | Lang.Expr.div a b => Yul.Expr.call "div" [compileExpr a, compileExpr b]
  | Lang.Expr.eq a b => Yul.Expr.call "eq" [compileExpr a, compileExpr b]
  | Lang.Expr.lt a b => Yul.Expr.call "lt" [compileExpr a, compileExpr b]
  | Lang.Expr.gt a b => Yul.Expr.call "gt" [compileExpr a, compileExpr b]
  | Lang.Expr.and a b => Yul.Expr.call "and" [compileExpr a, compileExpr b]
  | Lang.Expr.or a b => Yul.Expr.call "or" [compileExpr a, compileExpr b]
  | Lang.Expr.not a => Yul.Expr.call "iszero" [compileExpr a]
  | Lang.Expr.sload k => Yul.Expr.call "sload" [compileExpr k]
  | Lang.Expr.calldataload k => Yul.Expr.call "calldataload" [compileExpr k]

def compileStmt : Lang.Stmt -> Yul.Stmt
  | Lang.Stmt.skip => Yul.Stmt.block []
  | Lang.Stmt.seq a b =>
      match compileStmt a, compileStmt b with
      | Yul.Stmt.block as, Yul.Stmt.block bs => Yul.Stmt.block (as ++ bs)
      | sa, sb => Yul.Stmt.block [sa, sb]
  | Lang.Stmt.let_ v e body =>
      Yul.Stmt.block [Yul.Stmt.let_ v (compileExpr e), compileStmt body]
  | Lang.Stmt.assign v e => Yul.Stmt.assign v (compileExpr e)
  | Lang.Stmt.if_ c t f =>
      Yul.Stmt.block [
        Yul.Stmt.if_ (compileExpr c) (compileStmt t),
        Yul.Stmt.if_ (Yul.Expr.call "iszero" [compileExpr c]) (compileStmt f)
      ]
  | Lang.Stmt.sstore k v => Yul.Stmt.expr (Yul.Expr.call "sstore" [compileExpr k, compileExpr v])
  | Lang.Stmt.revert => Yul.Stmt.expr (Yul.Expr.call "revert" [Yul.Expr.lit 0, Yul.Expr.lit 0])
  | Lang.Stmt.return_ v =>
      let storeRet := Yul.Stmt.expr (Yul.Expr.call "mstore" [Yul.Expr.lit 0, compileExpr v])
      let doRet := Yul.Stmt.expr (Yul.Expr.call "return" [Yul.Expr.lit 0, Yul.Expr.lit 32])
      Yul.Stmt.block [storeRet, doRet]

structure EntryPoint where
  name : String
  args : List String
  body : Lang.Stmt
  selector : Nat
  deriving Repr

-- Wrap a simple entry block into a Yul object with a dispatcher.
def compileEntry (e : EntryPoint) : Yul.Program :=
  let funBody := match compileStmt e.body with
    | Yul.Stmt.block ss => Yul.Stmt.block ss
    | s => Yul.Stmt.block [s]
  let funStmt := Yul.Stmt.func e.name e.args [] funBody
  let selector :=
    Yul.Expr.call "shr" [
      Yul.Expr.lit 224,
      Yul.Expr.call "calldataload" [Yul.Expr.lit 0]
    ]
  let mkArg (i : Nat) : Yul.Expr :=
    Yul.Expr.call "calldataload" [Yul.Expr.lit (4 + 32 * i)]
  let args := (List.range e.args.length).map mkArg
  let callEntry := Yul.Stmt.expr (Yul.Expr.call e.name args)
  let okCase := Yul.Stmt.block [callEntry, Yul.Stmt.expr (Yul.Expr.call "stop" [])]
  let badCase := Yul.Stmt.block [Yul.Stmt.expr (Yul.Expr.call "revert" [Yul.Expr.lit 0, Yul.Expr.lit 0])]
  let dispatcher := Yul.Stmt.switch selector [(e.selector, okCase)] badCase
  let code := Yul.Stmt.block [funStmt, dispatcher]
  { obj := { name := "DumbContract", code := code } }

-- Example: a minimal storage update entry.
def exampleEntry : EntryPoint :=
  { name := "getSlot"
    args := ["slot"]
    body := Lang.Stmt.return_ (Lang.Expr.sload (Lang.Expr.var "slot"))
    -- getSlot(uint256) -> 0x7eba7ba6
    selector := 0x7eba7ba6 }

end DumbContracts.Compiler
