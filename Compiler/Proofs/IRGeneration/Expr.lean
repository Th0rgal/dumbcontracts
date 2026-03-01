/-
  Minimal IR artifacts consumed by end-to-end composition proofs.
-/

import Compiler.Specs

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.Specs
open Compiler.Yul

/-- Concrete IR contract for SimpleStorage used by EndToEnd composition proofs. -/
def simpleStorageIRContract : IRContract :=
  { name := "SimpleStorage"
    deploy := []
    functions := [
      { name := "store"
        selector := 0x6057361d
        params := [{ name := "value", ty := IRType.uint256 }]
        ret := IRType.unit
        body := [
          YulStmt.let_ "value" (YulExpr.call "calldataload" [YulExpr.lit 4]),
          YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.ident "value"]),
          YulStmt.expr (YulExpr.call "stop" [])
        ]
      },
      { name := "retrieve"
        selector := 0x2e64cec1
        params := []
        ret := IRType.uint256
        body := [
          YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.call "sload" [YulExpr.lit 0]]),
          YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
      }
    ]
    usesMapping := false }

@[simp] lemma compile_simpleStorageSpec :
    compile simpleStorageSpec [0x6057361d, 0x2e64cec1] = .ok simpleStorageIRContract := by
  rfl

end Compiler.Proofs.IRGeneration
