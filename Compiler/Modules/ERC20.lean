/-
  Compiler.Modules.ERC20: ERC-20 Token Interaction Modules

  Standard ECMs for safe ERC-20 token operations:
  - `safeTransfer`:     transfer(address,uint256)       selector 0xa9059cbb
  - `safeTransferFrom`: transferFrom(address,address,uint256) selector 0x23b872dd
  - `safeApprove`:      approve(address,uint256)        selector 0x095ea7b3

  All modules handle the ERC-20 optional-bool-return pattern: if the call
  succeeds but returndatasize == 32 and the returned word is zero, the
  module reverts.  This correctly handles both standard (bool-returning)
  and non-standard (void-returning) ERC-20 tokens.

  Trust assumption: the target address implements the ERC-20 interface
  (or is a non-standard token that doesn't return a bool).
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.ERC20

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr)

/-- ERC-20 safeTransfer module.
    Calls `transfer(address to, uint256 amount)` with optional-bool-return handling.
    Arguments: [token, to, amount] -/
def safeTransferModule : ExternalCallModule where
  name := "safeTransfer"
  numArgs := 3
  writesState := true
  readsState := false
  axioms := ["erc20_transfer_interface"]
  compile := fun _ctx args => do
    let (tokenExpr, toExpr, amountExpr) ← match args with
      | [t, to, a] => pure (t, to, a)
      | _ => throw "safeTransfer expects 3 arguments (token, to, amount)"
    let selectorWord := 0xa9059cbb00000000000000000000000000000000000000000000000000000000
    pure [YulStmt.block ([
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex selectorWord]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 4, toExpr]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 36, amountExpr]),
      YulStmt.let_ "__st_success" (YulExpr.call "call" [
        YulExpr.call "gas" [], tokenExpr, YulExpr.lit 0,
        YulExpr.lit 0, YulExpr.lit 68, YulExpr.lit 0, YulExpr.lit 32
      ]),
      YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__st_success"])
        (revertWithMessage "transfer reverted"),
      YulStmt.if_ (YulExpr.call "eq" [YulExpr.call "returndatasize" [], YulExpr.lit 32]) [
        YulStmt.if_ (YulExpr.call "iszero" [YulExpr.call "mload" [YulExpr.lit 0]])
          (revertWithMessage "transfer returned false")
      ]
    ])]

/-- Convenience: create a `Stmt.ecm` for safeTransfer. -/
def safeTransfer (token to amount : Expr) : Stmt :=
  .ecm safeTransferModule [token, to, amount]

/-- ERC-20 safeTransferFrom module.
    Calls `transferFrom(address from, address to, uint256 amount)` with optional-bool-return handling.
    Arguments: [token, from, to, amount] -/
def safeTransferFromModule : ExternalCallModule where
  name := "safeTransferFrom"
  numArgs := 4
  writesState := true
  readsState := false
  axioms := ["erc20_transferFrom_interface"]
  compile := fun _ctx args => do
    let (tokenExpr, fromExpr, toExpr, amountExpr) ← match args with
      | [t, f, to, a] => pure (t, f, to, a)
      | _ => throw "safeTransferFrom expects 4 arguments (token, from, to, amount)"
    let selectorWord := 0x23b872dd00000000000000000000000000000000000000000000000000000000
    pure [YulStmt.block ([
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex selectorWord]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 4, fromExpr]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 36, toExpr]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 68, amountExpr]),
      YulStmt.let_ "__stf_success" (YulExpr.call "call" [
        YulExpr.call "gas" [], tokenExpr, YulExpr.lit 0,
        YulExpr.lit 0, YulExpr.lit 100, YulExpr.lit 0, YulExpr.lit 32
      ]),
      YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__stf_success"])
        (revertWithMessage "transferFrom reverted"),
      YulStmt.if_ (YulExpr.call "eq" [YulExpr.call "returndatasize" [], YulExpr.lit 32]) [
        YulStmt.if_ (YulExpr.call "iszero" [YulExpr.call "mload" [YulExpr.lit 0]])
          (revertWithMessage "transferFrom returned false")
      ]
    ])]

/-- Convenience: create a `Stmt.ecm` for safeTransferFrom. -/
def safeTransferFrom (token fromAddr to amount : Expr) : Stmt :=
  .ecm safeTransferFromModule [token, fromAddr, to, amount]

/-- ERC-20 safeApprove module (new — demonstrates ECM extensibility).
    Calls `approve(address spender, uint256 amount)` with optional-bool-return handling.
    Arguments: [token, spender, amount] -/
def safeApproveModule : ExternalCallModule where
  name := "safeApprove"
  numArgs := 3
  writesState := true
  readsState := false
  axioms := ["erc20_approve_interface"]
  compile := fun _ctx args => do
    let (tokenExpr, spenderExpr, amountExpr) ← match args with
      | [t, s, a] => pure (t, s, a)
      | _ => throw "safeApprove expects 3 arguments (token, spender, amount)"
    let selectorWord := 0x095ea7b300000000000000000000000000000000000000000000000000000000
    pure [YulStmt.block ([
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex selectorWord]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 4, spenderExpr]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 36, amountExpr]),
      YulStmt.let_ "__sa_success" (YulExpr.call "call" [
        YulExpr.call "gas" [], tokenExpr, YulExpr.lit 0,
        YulExpr.lit 0, YulExpr.lit 68, YulExpr.lit 0, YulExpr.lit 32
      ]),
      YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__sa_success"])
        (revertWithMessage "approve reverted"),
      YulStmt.if_ (YulExpr.call "eq" [YulExpr.call "returndatasize" [], YulExpr.lit 32]) [
        YulStmt.if_ (YulExpr.call "iszero" [YulExpr.call "mload" [YulExpr.lit 0]])
          (revertWithMessage "approve returned false")
      ]
    ])]

/-- Convenience: create a `Stmt.ecm` for safeApprove. -/
def safeApprove (token spender amount : Expr) : Stmt :=
  .ecm safeApproveModule [token, spender, amount]

end Compiler.Modules.ERC20
