/-
  Compiler.Modules.Precompiles: EVM Precompile Modules

  Standard ECMs for EVM precompile calls:
  - `ecrecover`: ECDSA signature recovery via precompile at address 0x01

  Trust assumption: EVM precompiles behave according to the Ethereum
  Yellow Paper specification.
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.Precompiles

open Compiler.Yul
open Compiler.ECM
open Compiler.Constants (addressMask)
open Compiler.CompilationModel (Stmt Expr)

/-- Ecrecover precompile module.
    Performs ECDSA recovery via staticcall to precompile address 0x01.
    Arguments: [hash, v, r, s]
    Binds one result variable (the recovered address, masked to 160 bits).
    Guards against stale hash when the precompile returns 0 bytes. -/
def ecrecoverModule (resultVar : String) : ExternalCallModule where
  name := "ecrecover"
  numArgs := 4
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := ["evm_ecrecover_precompile"]
  compile := fun _ctx args => do
    let (hashExpr, vExpr, rExpr, sExpr) ← match args with
      | [h, v, r, s] => pure (h, v, r, s)
      | _ => throw "ecrecover expects 4 arguments (hash, v, r, s)"
    let storeHash := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, hashExpr])
    let storeV := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, vExpr])
    let storeR := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 64, rExpr])
    let storeS := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 96, sExpr])
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      YulExpr.lit 1,
      YulExpr.lit 0, YulExpr.lit 128,
      YulExpr.lit 0, YulExpr.lit 32
    ]
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__ecr_success"]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let guardStale := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.call "returndatasize" []]) [
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let bindResult := YulStmt.let_ resultVar
      (YulExpr.call "and" [YulExpr.call "mload" [YulExpr.lit 0], YulExpr.hex addressMask])
    pure [YulStmt.block (
      [storeHash, storeV, storeR, storeS,
       YulStmt.let_ "__ecr_success" callExpr,
       revertBlock,
       guardStale]
    ), bindResult]

/-- Convenience: create a `Stmt.ecm` for ecrecover. -/
def ecrecover (resultVar : String) (hash v r s : Expr) : Stmt :=
  .ecm (ecrecoverModule resultVar) [hash, v, r, s]

end Compiler.Modules.Precompiles
