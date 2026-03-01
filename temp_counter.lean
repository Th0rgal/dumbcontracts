import Compiler.Proofs.YulGeneration.Equivalence
import Compiler.Proofs.YulGeneration.Semantics
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.IR

open Compiler
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.IRGeneration
open Compiler.Yul

def fnCounter : IRFunction := {
  name := "f"
  selector := 0
  params := [{ name := "a", ty := IRType.uint256 }]
  ret := IRType.unit
  body := [YulStmt.let_ "x" (YulExpr.ident "a")]
}

def txCounter : IRTransaction := {
  sender := 7
  functionSelector := 0
  args := [42]
}

def stCounter : IRState := {
  vars := []
  storage := fun _ => 0
  memory := fun _ => 0
  calldata := txCounter.args
  returnValue := none
  sender := txCounter.sender
  selector := txCounter.functionSelector
}

noncomputable def lhsExec : YulExecResult :=
  let paramState := fnCounter.params.zip txCounter.args |>.foldl
      (fun s (pv : IRParam × Nat) => s.setVar pv.1.name pv.2) stCounter
  execYulStmts (yulStateOfIR 0 paramState) fnCounter.body

noncomputable def rhsExec : YulExecResult :=
  let yulTx : YulTransaction := {
    sender := txCounter.sender
    functionSelector := txCounter.functionSelector
    args := txCounter.args
  }
  execYulStmts (YulState.initial yulTx stCounter.storage) fnCounter.body

example : lhsExec = YulExecResult.continue ((yulStateOfIR 0 ((fnCounter.params.zip txCounter.args).foldl (fun s (pv : IRParam × Nat) => s.setVar pv.1.name pv.2) stCounter)).setVar "x" 42) := by
  simp [lhsExec, execYulStmts, execYulStmtsFuel, execYulStmtFuel, yulStateOfIR, fnCounter, txCounter, stCounter, YulState.getVar, YulState.setVar]

example : rhsExec = YulExecResult.revert (YulState.initial { sender := txCounter.sender, functionSelector := txCounter.functionSelector, args := txCounter.args } stCounter.storage) := by
  simp [rhsExec, execYulStmts, execYulStmtsFuel, execYulStmtFuel, fnCounter, txCounter, stCounter, YulState.initial, YulState.getVar]

example : lhsExec ≠ rhsExec := by
  intro h
  have h1 : lhsExec = YulExecResult.continue ((yulStateOfIR 0 ((fnCounter.params.zip txCounter.args).foldl (fun s (pv : IRParam × Nat) => s.setVar pv.1.name pv.2) stCounter)).setVar "x" 42) := by
    simp [lhsExec, execYulStmts, execYulStmtsFuel, execYulStmtFuel, yulStateOfIR, fnCounter, txCounter, stCounter, YulState.getVar, YulState.setVar]
  have h2 : rhsExec = YulExecResult.revert (YulState.initial { sender := txCounter.sender, functionSelector := txCounter.functionSelector, args := txCounter.args } stCounter.storage) := by
    simp [rhsExec, execYulStmts, execYulStmtsFuel, execYulStmtFuel, fnCounter, txCounter, stCounter, YulState.initial, YulState.getVar]
  rw [h1, h2] at h
  cases h
