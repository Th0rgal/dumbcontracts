import Compiler.Yul.Ast

namespace Compiler

inductive IRType
  | uint256
  | address
  | unit
  deriving Repr

structure IRParam where
  name : String
  ty : IRType
  deriving Repr

abbrev IRExpr := Yul.YulExpr
abbrev IRStmt := Yul.YulStmt

structure IRFunction where
  name : String
  selector : Nat
  params : List IRParam
  ret : IRType
  payable : Bool := false
  body : List IRStmt
  deriving Repr

structure IREntrypoint where
  payable : Bool := false
  body : List IRStmt
  deriving Repr

structure IRContract where
  name : String
  deploy : List IRStmt
  constructorPayable : Bool := false
  functions : List IRFunction
  /-- Optional Solidity-style fallback entrypoint for unmatched selectors. -/
  fallbackEntrypoint : Option IREntrypoint := none
  /-- Optional Solidity-style receive entrypoint for empty calldata. -/
  receiveEntrypoint : Option IREntrypoint := none
  usesMapping : Bool
  internalFunctions : List IRStmt := []  -- Yul function definitions for internal calls (#181)
  deriving Repr

end Compiler
