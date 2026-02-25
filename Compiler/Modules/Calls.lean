/-
  Compiler.Modules.Calls: Generic External Call Modules

  Standard ECM for ABI-encoded external calls with a single uint256 return:
  - `withReturn`: call/staticcall with selector + args, revert-forward on failure,
    validate return data, bind result variable

  Trust assumption: the target contract's function matches the declared
  selector and ABI encoding.
-/

import Compiler.ECM
import Compiler.ContractSpec

namespace Compiler.Modules.Calls

open Compiler.Yul
open Compiler.ECM
open Compiler.ContractSpec (Stmt Expr)

/-- Generic external call with single uint256 return.
    ABI-encodes `selector(args...)`, calls/staticcalls target, reverts on failure,
    validates returndatasize >= 32, and binds the result.

    The module is parameterized by:
    - `resultVar`: name for the bound result variable
    - `selector`: the 4-byte function selector
    - `numArgs`: number of ABI-encoded arguments (not counting target)
    - `isStatic`: true for staticcall, false for call

    Arguments passed to compile: [target] ++ argExprs -/
def withReturnModule (resultVar : String) (selector : Nat) (numArgs : Nat) (isStatic : Bool)
    : ExternalCallModule where
  name := "externalCallWithReturn"
  numArgs := 1 + numArgs  -- target + args
  resultVars := [resultVar]
  writesState := !isStatic
  readsState := true
  axioms := ["external_call_abi_interface"]
  compile := fun _ctx args => do
    let targetExpr ← match args.head? with
      | some t => pure t
      | none => throw "externalCallWithReturn expects at least 1 argument (target)"
    let argExprs := args.drop 1
    let selectorExpr := YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex selector]
    let storeSelector := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, selectorExpr])
    let storeArgs := argExprs.zipIdx.map fun (argExpr, i) =>
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit (4 + i * 32), argExpr])
    let calldataSize := 4 + numArgs * 32
    let callExpr :=
      if isStatic then
        YulExpr.call "staticcall" [
          YulExpr.call "gas" [],
          targetExpr,
          YulExpr.lit 0, YulExpr.lit calldataSize,
          YulExpr.lit 0, YulExpr.lit 32
        ]
      else
        YulExpr.call "call" [
          YulExpr.call "gas" [],
          targetExpr,
          YulExpr.lit 0,
          YulExpr.lit 0, YulExpr.lit calldataSize,
          YulExpr.lit 0, YulExpr.lit 32
        ]
    let letSuccess := YulStmt.let_ "__ecwr_success" callExpr
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__ecwr_success"]) [
      YulStmt.let_ "__ecwr_rds" (YulExpr.call "returndatasize" []),
      YulStmt.expr (YulExpr.call "returndatacopy" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__ecwr_rds"]),
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__ecwr_rds"])
    ]
    let sizeCheck := YulStmt.if_ (YulExpr.call "lt" [YulExpr.call "returndatasize" [], YulExpr.lit 32]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let callBlock := YulStmt.block ([storeSelector] ++ storeArgs ++ [letSuccess, revertBlock, sizeCheck])
    let bindResult := YulStmt.let_ resultVar (YulExpr.call "mload" [YulExpr.lit 0])
    pure [callBlock, bindResult]

/-- Convenience: create a `Stmt.ecm` for an external call with return.
    Replaces the former `Stmt.externalCallWithReturn` variant. -/
def withReturn (resultVar : String) (target : Expr) (selector : Nat)
    (args : List Expr) (isStatic : Bool := false) : Stmt :=
  .ecm (withReturnModule resultVar selector args.length isStatic) ([target] ++ args)

end Compiler.Modules.Calls
