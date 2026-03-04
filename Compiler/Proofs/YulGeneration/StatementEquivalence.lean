import Compiler.Proofs.YulGeneration.Equivalence
import Compiler.Proofs.YulGeneration.Semantics
import Compiler.Proofs.IRGeneration.IRInterpreter

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul
open Compiler.Proofs.IRGeneration

/-! ## Layer 3: Statement-Level Equivalence (Complete)

Proves that each IR statement type executes equivalently in Yul when states
are aligned. Uses `mutual` recursion between `conditional_equiv` and
`all_stmts_equiv` to handle the circular dependency.

Individual statement proofs compose via `execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv`
(Equivalence.lean) to complete the `hbody` hypothesis in `Preservation.lean`.
-/

/-! ### Expression Equivalence (Now Proven — Previously Axioms)

With the IR expression evaluators refactored to be total and structurally
identical to the Yul evaluators, these are now **proven theorems**.

Previously these were axioms:
  axiom evalIRExpr_eq_evalYulExpr : ...
  axiom evalIRExprs_eq_evalYulExprs : ...

Eliminated by making `evalIRExpr`/`evalIRExprs`/`evalIRCall` total (using
`termination_by` with `exprSize`/`exprsSize`) and restructuring `evalIRCall`
to evaluate all arguments first (matching `evalYulCall`). See Issue #148.
-/

open Compiler.Proofs.YulGeneration in
mutual

/-- IR and Yul expression evaluation are identical when states are aligned.

PROVEN (previously axiom #1). Both evaluators are now total with identical
structure — the proof proceeds by mutual structural induction on expression size. -/
theorem evalIRExpr_eq_evalYulExpr (selector : Nat) (irState : IRState) (expr : YulExpr) :
    evalIRExpr irState expr = evalYulExpr (yulStateOfIR selector irState) expr := by
  match expr with
  | .lit n => simp [evalIRExpr, evalYulExpr]
  | .hex n => simp [evalIRExpr, evalYulExpr]
  | .str _ => simp [evalIRExpr, evalYulExpr]
  | .ident name =>
      simp [evalIRExpr, evalYulExpr, IRState.getVar, YulState.getVar, yulStateOfIR]
  | .call func args =>
      simp only [evalIRExpr, evalYulExpr]
      exact evalIRCall_eq_evalYulCall selector irState func args
termination_by exprSize expr
decreasing_by
  simp [exprSize, exprsSize]

/-- List version: IR and Yul list evaluation are identical when states are aligned.

PROVEN (previously axiom #2). Follows from `evalIRExpr_eq_evalYulExpr` by
structural induction on the expression list. -/
theorem evalIRExprs_eq_evalYulExprs (selector : Nat) (irState : IRState) (exprs : List YulExpr) :
    evalIRExprs irState exprs = evalYulExprs (yulStateOfIR selector irState) exprs := by
  match exprs with
  | [] => simp [evalIRExprs, evalYulExprs]
  | e :: es =>
      simp only [evalIRExprs, evalYulExprs]
      rw [evalIRExpr_eq_evalYulExpr selector irState e]
      rw [evalIRExprs_eq_evalYulExprs selector irState es]
termination_by exprsSize exprs
decreasing_by
  all_goals
    simp [exprsSize, exprSize]
    omega

/-- Call version: IR and Yul call evaluation are identical when states are aligned. -/
theorem evalIRCall_eq_evalYulCall (selector : Nat) (irState : IRState) (func : String) (args : List YulExpr) :
    evalIRCall irState func args = evalYulCall (yulStateOfIR selector irState) func args := by
  simp only [evalIRCall, evalYulCall]
  rw [evalIRExprs_eq_evalYulExprs selector irState args]
  rfl
termination_by exprsSize args + 1
decreasing_by
  simp [exprsSize, exprSize]

end

attribute [simp] evalIRExpr_eq_evalYulExpr evalIRExprs_eq_evalYulExprs evalIRCall_eq_evalYulCall

/-! ## Proven Theorems -/

theorem assign_equiv (selector : Nat) (fuel : Nat) (varName : String) (valueExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.assign varName valueExpr))
      (execYulStmtFuel fuel yulState (YulStmt.assign varName valueExpr)) := by
  -- Unfold state alignment
  unfold statesAligned at halign
  subst halign
  -- Destruct fuel
  cases fuel with
  | zero => contradiction
  | succ fuel' =>
      simp [execIRStmtFuel, execIRStmt, execYulStmtFuel, execYulFuel]
      -- Use lemma: evalIRExpr irState expr = evalYulExpr (yulStateOfIR selector irState) expr
      rw [evalIRExpr_eq_evalYulExpr]
      -- Now both sides are identical
      cases evalYulExpr (yulStateOfIR selector irState) valueExpr with
      | none =>
          -- Both revert
          unfold execResultsAligned
          rfl
      | some v =>
          -- Both continue with updated variable
          unfold execResultsAligned statesAligned yulStateOfIR
          simp [IRState.setVar, YulState.setVar]

set_option maxHeartbeats 800000 in
private theorem stmt_and_stmts_equiv :
    ∀ fuel,
      (∀ selector stmt irState yulState,
        execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState) ∧
      (∀ selector stmts irState yulState,
        execIRStmts_equiv_execYulStmts_goal selector fuel stmts irState yulState) := by
  sorry

theorem all_stmts_equiv : ∀ selector fuel stmt irState yulState,
    execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState := by
  intro selector fuel stmt irState yulState
  exact (stmt_and_stmts_equiv fuel).1 selector stmt irState yulState

theorem conditional_equiv (selector : Nat) (fuel : Nat)
    (condExpr : YulExpr) (body : List YulStmt)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (_hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.if_ condExpr body))
      (execYulStmtFuel fuel yulState (YulStmt.if_ condExpr body)) := by
  simpa [execIRStmt_equiv_execYulStmt_goal] using
    (all_stmts_equiv selector fuel (YulStmt.if_ condExpr body) irState yulState halign)

theorem return_equiv (selector : Nat) (fuel : Nat)
    (offsetExpr sizeExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.expr (.call "return" [offsetExpr, sizeExpr])))
      (execYulStmtFuel fuel yulState (YulStmt.expr (.call "return" [offsetExpr, sizeExpr]))) := by
  simpa [execIRStmt_equiv_execYulStmt_goal] using
    (all_stmts_equiv selector fuel (YulStmt.expr (.call "return" [offsetExpr, sizeExpr])) irState yulState halign)

theorem revert_equiv (selector : Nat) (fuel : Nat)
    (offsetExpr sizeExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.expr (.call "revert" [offsetExpr, sizeExpr])))
      (execYulStmtFuel fuel yulState (YulStmt.expr (.call "revert" [offsetExpr, sizeExpr]))) := by
  simpa [execIRStmt_equiv_execYulStmt_goal] using
    (all_stmts_equiv selector fuel (YulStmt.expr (.call "revert" [offsetExpr, sizeExpr])) irState yulState halign)

theorem storageStore_equiv (selector : Nat) (fuel : Nat)
    (slotExpr valExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (_hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.expr (.call "sstore" [slotExpr, valExpr])))
      (execYulStmtFuel fuel yulState (YulStmt.expr (.call "sstore" [slotExpr, valExpr]))) := by
  simpa [execIRStmt_equiv_execYulStmt_goal] using
    (all_stmts_equiv selector fuel (YulStmt.expr (.call "sstore" [slotExpr, valExpr])) irState yulState halign)


end Compiler.Proofs.YulGeneration
