/-
  Compiler.Proofs.InterpreterFeatureTest: Interpreter feature-matrix smoke tests

  Machine-checked tests validating that the SpecInterpreter handles the
  feature categories documented in docs/INTERPRETER_FEATURE_MATRIX.md.

  Covers: basic path (execStmts), fuel path (execStmtsFuel), and
  boundary conditions (unsupported features correctly return none).

  Run: lake build Compiler.Proofs.InterpreterFeatureTest
-/

import Compiler.CompilationModel
import Verity.Proofs.Stdlib.SpecInterpreter

namespace Compiler.Proofs.InterpreterFeatureTest

open Compiler.CompilationModel
open Verity.Proofs.Stdlib.SpecInterpreter

/-! ## Test fixtures -/

private def testCtx : EvalContext := {
  sender := 42
  msgValue := 100
  blockTimestamp := 1000
  params := [10, 20]
  paramTypes := [.uint256, .uint256]
  constructorArgs := []
  constructorParamTypes := []
  localVars := []
  arrayParams := []
}

private def testFields : List Field := [
  { name := "balance", ty := .uint256 },
  { name := "owner", ty := .address }
]

private def testParamNames : List String := ["amount", "target"]

private def emptyState : ExecState := {
  storage := SpecStorage.empty
  returnValue := none
  halted := false
}

private def noExternalFns : List (String × (List Nat → Nat)) := []

/-- Helper: evaluate an expression in the test context. -/
private def testEval (e : Expr) : Nat :=
  evalExpr testCtx SpecStorage.empty testFields testParamNames noExternalFns e

/-- Helper: execute statements in basic path, return the result. -/
private def testExec (stmts : List Stmt) : Option (EvalContext × ExecState) :=
  execStmts testCtx testFields testParamNames noExternalFns emptyState stmts

/-- Helper: execute statements in fuel path, return the result. -/
private def testExecFuel (fuel : Nat) (stmts : List Stmt) : Option (EvalContext × ExecState) :=
  execStmtsFuel fuel testCtx testFields testParamNames noExternalFns [] emptyState stmts

private def iteInterpSpec : CompilationModel := {
  name := "IteInterpSpec"
  fields := []
  constructor := none
  functions := [
    { name := "choose"
      params := [{ name := "cond", ty := .uint256 }]
      returnType := some .uint256
      body := [
        Stmt.ite (Expr.param "cond")
          [Stmt.return (Expr.literal 11)]
          [Stmt.return (Expr.literal 22)]
      ]
    }
  ]
  events := []
}

private def mapping2InterpSpec : CompilationModel := {
  name := "Mapping2InterpSpec"
  fields := [
    { name := "allowances"
      ty := .mappingTyped (.nested .address .address)
      slot := some 5 }
  ]
  constructor := none
  functions := [
    { name := "setAllowance"
      params := [{ name := "owner", ty := .address }, { name := "spender", ty := .address }, { name := "amount", ty := .uint256 }]
      returnType := none
      body := [
        Stmt.setMapping2 "allowances" (Expr.param "owner") (Expr.param "spender") (Expr.param "amount"),
        Stmt.stop
      ]
    },
    { name := "allowance"
      params := [{ name := "owner", ty := .address }, { name := "spender", ty := .address }]
      returnType := some .uint256
      body := [Stmt.return (Expr.mapping2 "allowances" (Expr.param "owner") (Expr.param "spender"))]
    }
  ]
  events := []
}

/-! ## Category 1: Expressions — supported in basic path -/

/-- Literal evaluation. -/
example : testEval (Expr.literal 42) = 42 := by native_decide

/-- Parameter lookup (first param = 10). -/
example : testEval (Expr.param "amount") = 10 := by native_decide

/-- Caller access. -/
example : testEval Expr.caller = 42 := by native_decide

/-- msg.value access. -/
example : testEval Expr.msgValue = 100 := by native_decide

/-- block.timestamp access. -/
example : testEval Expr.blockTimestamp = 1000 := by native_decide

/-- Arithmetic: add(10, 20) = 30. -/
example : testEval (Expr.add (Expr.param "amount") (Expr.param "target")) = 30 := by native_decide

/-- Arithmetic: sub wraps (5 - 10 = 2^256 - 5). -/
example : testEval (Expr.sub (Expr.literal 5) (Expr.literal 10))
    = (2^256 - 5) := by native_decide

/-- Comparison: lt(10, 20) = 1. -/
example : testEval (Expr.lt (Expr.param "amount") (Expr.param "target")) = 1 := by native_decide

/-- Bitwise: and(0xFF, 0x0F) = 0x0F. -/
example : testEval (Expr.bitAnd (Expr.literal 0xFF) (Expr.literal 0x0F)) = 0x0F := by native_decide

/-! ## Category 2: Expressions — fallback_zero (not modeled) -/

/-- contractAddress returns 0 (not modeled). -/
example : testEval Expr.contractAddress = 0 := by native_decide

/-- chainid returns 0 (not modeled). -/
example : testEval Expr.chainid = 0 := by native_decide

/-! ## Category 3: Statements — basic path (execStmts) -/

/-- setStorage writes and return reads the value back. -/
example : (testExec [
    Stmt.setStorage "balance" (Expr.literal 500),
    Stmt.return (Expr.storage "balance")
  ]).bind (fun (_, s) => s.returnValue) = some 500 := by native_decide

/-- letVar + assignVar + return. -/
example : (testExec [
    Stmt.letVar "x" (Expr.literal 7),
    Stmt.assignVar "x" (Expr.add (Expr.localVar "x") (Expr.literal 3)),
    Stmt.return (Expr.localVar "x")
  ]).bind (fun (_, s) => s.returnValue) = some 10 := by native_decide

/-- require passes when condition is true. -/
example : (testExec [
    Stmt.require (Expr.literal 1) "must be true",
    Stmt.return (Expr.literal 42)
  ]).bind (fun (_, s) => s.returnValue) = some 42 := by native_decide

/-- require reverts when condition is false. -/
example : (testExec [
    Stmt.require (Expr.literal 0) "must be true",
    Stmt.return (Expr.literal 42)
  ]).isNone = true := by native_decide

/-- If/else branches correctly (then branch). -/
example : (testExec [
    Stmt.ite (Expr.literal 1)
      [Stmt.return (Expr.literal 1)]
      [Stmt.return (Expr.literal 2)]
  ]).bind (fun (_, s) => s.returnValue) = some 1 := by native_decide

/-- If/else branches correctly (else branch). -/
example : (testExec [
    Stmt.ite (Expr.literal 0)
      [Stmt.return (Expr.literal 1)]
      [Stmt.return (Expr.literal 2)]
  ]).bind (fun (_, s) => s.returnValue) = some 2 := by native_decide

/-- Event emission succeeds and stop halts. -/
example : (testExec [
    Stmt.emit "Transfer" [Expr.caller, Expr.param "target", Expr.param "amount"],
    Stmt.stop
  ]).isSome = true := by native_decide

/-! ## Category 4: Statements — basic path unsupported (correctly reverts) -/

/-- forEach reverts in basic path. -/
example : (testExec [
    Stmt.forEach "i" (Expr.literal 3) [Stmt.stop]
  ]).isNone = true := by native_decide

/-- internalCall reverts in basic path. -/
example : (testExec [
    Stmt.internalCall "helper" []
  ]).isNone = true := by native_decide

/-! ## Category 5: Statements — fuel path (execStmtsFuel) handles loops -/

/-- forEach succeeds with fuel. -/
example : (testExecFuel 100 [
    Stmt.forEach "i" (Expr.literal 3)
      [Stmt.setStorage "balance"
        (Expr.add (Expr.storage "balance") (Expr.literal 1))],
    Stmt.return (Expr.storage "balance")
  ]).bind (fun (_, s) => s.returnValue) = some 3 := by native_decide

/-! ## Category 6: Not-modeled features return none/revert -/

/-- mstore reverts in SpecInterpreter (memory not modeled). -/
example : (testExec [
    Stmt.mstore (Expr.literal 0) (Expr.literal 42)
  ]).isNone = true := by native_decide

/-- externalCallBind reverts in SpecInterpreter. -/
example : (testExec [
    Stmt.externalCallBind ["r"] "ext" []
  ]).isNone = true := by native_decide

/-! ## Category 7: interpretSpec smoke tests -/

/-- interpretSpec executes Stmt.ite with then/else branch semantics. -/
example :
    let thenTx : Compiler.DiffTestTypes.Transaction := { sender := 7, functionName := "choose", args := [1] }
    let elseTx : Compiler.DiffTestTypes.Transaction := { sender := 7, functionName := "choose", args := [0] }
    let thenResult := interpretSpec iteInterpSpec SpecStorage.empty thenTx
    let elseResult := interpretSpec iteInterpSpec SpecStorage.empty elseTx
    thenResult.success &&
      elseResult.success &&
      thenResult.returnValue == some 11 &&
      elseResult.returnValue == some 22 = true := by
  native_decide

/-- interpretSpec round-trips setMapping2/Expr.mapping2 read path. -/
example :
    let owner := 0xA11CE
    let spender := 0xB0B
    let amount := 777
    let writeTx : Compiler.DiffTestTypes.Transaction := {
      sender := owner
      functionName := "setAllowance"
      args := [owner, spender, amount]
    }
    let readTx : Compiler.DiffTestTypes.Transaction := {
      sender := owner
      functionName := "allowance"
      args := [owner, spender]
    }
    let writeResult := interpretSpec mapping2InterpSpec SpecStorage.empty writeTx
    let readResult := interpretSpec mapping2InterpSpec writeResult.finalStorage readTx
    writeResult.success &&
      readResult.success &&
      readResult.returnValue == some amount = true := by
  native_decide

/-! ## Summary

  26 native_decide proofs covering:
  - 9 expression evaluations (literals, params, caller, msgValue, blockTimestamp,
    arithmetic with wrapping, comparison, bitwise)
  - 2 fallback-zero boundary checks (contractAddress, chainid)
  - 7 basic-path statement tests (storage write+read, let/assign/return,
    require pass/fail, ite then/else, event emission + stop)
  - 2 basic-path unsupported boundary checks (forEach, internalCall)
  - 1 fuel-path forEach test
  - 2 not-modeled boundary checks (mstore, externalCallBind)
  - 2 interpretSpec smoke tests (Stmt.ite branches + Expr.mapping2 round-trip)
-/

end Compiler.Proofs.InterpreterFeatureTest
