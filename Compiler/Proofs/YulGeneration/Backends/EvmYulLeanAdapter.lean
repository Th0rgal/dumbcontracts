import Compiler.Yul.Ast
import Compiler.Constants
import Compiler.Proofs.IRGeneration.IRStorageWord
import Compiler.Proofs.MappingSlot
import Compiler.Proofs.YulGeneration.Calldata
import EvmYul.Yul.Ast
import EvmYul.UInt256
import Mathlib.Data.Finmap
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeLowering

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Yul
open Compiler.Proofs.IRGeneration (IRStorageWord IRStorageSlot)


def lowerExpr : YulExpr → EvmYul.Yul.Ast.Expr
  | .lit n => .Lit (EvmYul.UInt256.ofNat n)
  | .hex n => .Lit (EvmYul.UInt256.ofNat n)
  | .str s => .Var s
  | .ident name => .Var name
  | .call func args => .Call (.inr func) (args.map lowerExpr)

mutual
partial def lowerStmts : List YulStmt → Except AdapterError (List EvmYul.Yul.Ast.Stmt)
  | [] => pure []
  | stmt :: rest => do
      let stmts' ← lowerStmtGroup stmt
      let rest' ← lowerStmts rest
      pure (stmts' ++ rest')

/-- Lower a single Verity YulStmt to one or more EVMYulLean Stmts.
    Most cases produce exactly one statement; `for_` with init produces
    init stmts followed by the loop (EVMYulLean `For` has no init block). -/
partial def lowerStmtGroup : YulStmt → Except AdapterError (List EvmYul.Yul.Ast.Stmt)
  | .comment _ => pure [.Block []]
  | .let_ name value => pure [.Let [name] (some (lowerExpr value))]
  | .letMany names value => pure [.Let names (some (lowerExpr value))]
  | .assign name value =>
      -- EVMYulLean has no Assign; re-bind via Let (Yul semantics: assignment to
      -- existing variable is equivalent to re-declaration in the same scope).
      pure [.Let [name] (some (lowerExpr value))]
  | .expr e => pure [.ExprStmtCall (lowerExpr e)]
  | .leave => pure [.Leave]
  | .if_ cond body => do
      let body' ← lowerStmts body
      pure [.If (lowerExpr cond) body']
  | .for_ init cond post body => do
      let init' ← lowerStmts init
      let post' ← lowerStmts post
      let body' ← lowerStmts body
      -- EVMYulLean For has no init block; emit init stmts before the loop.
      pure (init' ++ [.For (lowerExpr cond) post' body'])
  | .switch expr cases defaultCase => do
      let lowerCase := fun ((tag, block) : Nat × List YulStmt) => do
        let block' ← lowerStmts block
        pure (EvmYul.UInt256.ofNat tag, block')
      let cases' ← cases.mapM lowerCase
      let default' ← lowerStmts (defaultCase.getD [])
      pure [.Switch (lowerExpr expr) cases' default']
  | .block stmts => do
      let stmts' ← lowerStmts stmts
      pure [.Block stmts']
  | .funcDef _name _params _rets body => do
      let body' ← lowerStmts body
      -- Lower to a Block containing the function body. EVMYulLean's
      -- FunctionDefinition is a separate type (not a Stmt constructor);
      -- for adapter coverage we emit the body as an inlined block.
      -- Full function-definition lowering requires YulContract.functions
      -- integration (tracked separately).
      pure [.Block body']

/-- Backward-compatible single-statement lowering (wraps lowerStmtGroup). -/
partial def lowerStmt : YulStmt → Except AdapterError EvmYul.Yul.Ast.Stmt
  | stmt => do
      let stmts ← lowerStmtGroup stmt
      pure (.Block stmts)

end

def lowerProgram (stmts : List YulStmt) : Except AdapterError EvmYul.Yul.Ast.Stmt := do
  let stmts' ← lowerStmts stmts
  pure (.Block stmts')

end Compiler.Proofs.YulGeneration.Backends
