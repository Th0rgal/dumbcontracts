import Compiler.Yul.Ast

namespace Compiler.Yul

/-- Phase at which a patch rule runs. -/
inductive PatchPhase
  | postCodegen
  deriving Repr, DecidableEq

/-- Audit metadata + executable rewrite for one expression patch rule. -/
structure ExprPatchRule where
  patchName : String
  pattern : String
  rewrite : String
  sideConditions : List String
  proofId : String
  passPhase : PatchPhase
  priority : Nat
  applyExpr : YulExpr → Option YulExpr

/-- Fail-closed metadata guard: a runnable rule must carry audit/proof linkage. -/
def ExprPatchRule.isAuditable (rule : ExprPatchRule) : Bool :=
  !rule.patchName.isEmpty && !rule.proofId.isEmpty && !rule.sideConditions.isEmpty

/-- Audit metadata + executable rewrite for one statement patch rule. -/
structure StmtPatchRule where
  patchName : String
  pattern : String
  rewrite : String
  sideConditions : List String
  proofId : String
  passPhase : PatchPhase
  priority : Nat
  applyStmt : YulStmt → Option YulStmt

/-- Fail-closed metadata guard: a runnable statement rule must carry audit/proof linkage. -/
def StmtPatchRule.isAuditable (rule : StmtPatchRule) : Bool :=
  !rule.patchName.isEmpty && !rule.proofId.isEmpty && !rule.sideConditions.isEmpty

/-- Audit metadata + executable rewrite for one block patch rule. -/
structure BlockPatchRule where
  patchName : String
  pattern : String
  rewrite : String
  sideConditions : List String
  proofId : String
  passPhase : PatchPhase
  priority : Nat
  applyBlock : List YulStmt → Option (List YulStmt)

/-- Fail-closed metadata guard: a runnable block rule must carry audit/proof linkage. -/
def BlockPatchRule.isAuditable (rule : BlockPatchRule) : Bool :=
  !rule.patchName.isEmpty && !rule.proofId.isEmpty && !rule.sideConditions.isEmpty

/-- Deterministic patch pass settings. -/
structure PatchPassConfig where
  enabled : Bool := true
  maxIterations : Nat := 2
  passPhase : PatchPhase := .postCodegen

/-- Per-rule usage entry emitted by the patch pass. -/
structure PatchManifestEntry where
  patchName : String
  matchCount : Nat
  changedNodes : Nat
  proofRef : String
  deriving Repr

/-- Result of running a patch pass over Yul statements. -/
structure PatchPassReport where
  patched : List YulStmt
  iterations : Nat
  manifest : List PatchManifestEntry
  deriving Repr

private structure PatchRuleMeta where
  patchName : String
  proofRef : String

private def insertRuleByPriority (rule : ExprPatchRule) : List ExprPatchRule → List ExprPatchRule
  | [] => [rule]
  | head :: tail =>
      if rule.priority > head.priority then
        rule :: head :: tail
      else
        head :: insertRuleByPriority rule tail

/-- Stable, deterministic ordering: priority descending, declaration order as tie-break. -/
def orderRulesByPriority (rules : List ExprPatchRule) : List ExprPatchRule :=
  rules.foldl (fun acc rule => insertRuleByPriority rule acc) []

private def insertStmtRuleByPriority (rule : StmtPatchRule) : List StmtPatchRule → List StmtPatchRule
  | [] => [rule]
  | head :: tail =>
      if rule.priority > head.priority then
        rule :: head :: tail
      else
        head :: insertStmtRuleByPriority rule tail

/-- Stable, deterministic ordering for statement rules. -/
def orderStmtRulesByPriority (rules : List StmtPatchRule) : List StmtPatchRule :=
  rules.foldl (fun acc rule => insertStmtRuleByPriority rule acc) []

private def insertBlockRuleByPriority (rule : BlockPatchRule) : List BlockPatchRule → List BlockPatchRule
  | [] => [rule]
  | head :: tail =>
      if rule.priority > head.priority then
        rule :: head :: tail
      else
        head :: insertBlockRuleByPriority rule tail

/-- Stable, deterministic ordering for block rules. -/
def orderBlockRulesByPriority (rules : List BlockPatchRule) : List BlockPatchRule :=
  rules.foldl (fun acc rule => insertBlockRuleByPriority rule acc) []

private def applyFirstRule (orderedRules : List ExprPatchRule) (expr : YulExpr) : Option (YulExpr × String) :=
  let rec go : List ExprPatchRule → Option (YulExpr × String)
    | [] => none
    | rule :: rest =>
        match rule.applyExpr expr with
        | some rewritten => some (rewritten, rule.patchName)
        | none => go rest
  go orderedRules

private def applyFirstStmtRule (orderedRules : List StmtPatchRule) (stmt : YulStmt) : Option (YulStmt × String) :=
  let rec go : List StmtPatchRule → Option (YulStmt × String)
    | [] => none
    | rule :: rest =>
        match rule.applyStmt stmt with
        | some rewritten => some (rewritten, rule.patchName)
        | none => go rest
  go orderedRules

private def applyFirstBlockRule
    (orderedRules : List BlockPatchRule)
    (block : List YulStmt) : Option (List YulStmt × String) :=
  let rec go : List BlockPatchRule → Option (List YulStmt × String)
    | [] => none
    | rule :: rest =>
        match rule.applyBlock block with
        | some rewritten => some (rewritten, rule.patchName)
        | none => go rest
  go orderedRules

mutual

private def rewriteExprOnce (orderedRules : List ExprPatchRule) : YulExpr → (YulExpr × List String)
  | .call func args =>
      let (rewrittenArgs, argHits) := rewriteExprListOnce orderedRules args
      let candidate := YulExpr.call func rewrittenArgs
      match applyFirstRule orderedRules candidate with
      | some (rewritten, patchName) => (rewritten, patchName :: argHits)
      | none => (candidate, argHits)
  | expr =>
      match applyFirstRule orderedRules expr with
      | some (rewritten, patchName) => (rewritten, [patchName])
      | none => (expr, [])

private def rewriteExprListOnce (orderedRules : List ExprPatchRule) : List YulExpr → (List YulExpr × List String)
  | [] => ([], [])
  | expr :: rest =>
      let (expr', hitsHead) := rewriteExprOnce orderedRules expr
      let (rest', hitsTail) := rewriteExprListOnce orderedRules rest
      (expr' :: rest', hitsHead ++ hitsTail)

end

private def applyStmtRulesToCandidate
    (orderedStmtRules : List StmtPatchRule)
    (candidate : YulStmt)
    (hits : List String) : YulStmt × List String :=
  match applyFirstStmtRule orderedStmtRules candidate with
  | some (rewritten, patchName) => (rewritten, hits ++ [patchName])
  | none => (candidate, hits)

mutual

private def rewriteStmtOnce
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule) : YulStmt → (YulStmt × List String)
  | .comment txt =>
      applyStmtRulesToCandidate orderedStmtRules (.comment txt) []
  | .let_ name value =>
      let (value', hits) := rewriteExprOnce orderedExprRules value
      applyStmtRulesToCandidate orderedStmtRules (.let_ name value') hits
  | .letMany names value =>
      let (value', hits) := rewriteExprOnce orderedExprRules value
      applyStmtRulesToCandidate orderedStmtRules (.letMany names value') hits
  | .assign name value =>
      let (value', hits) := rewriteExprOnce orderedExprRules value
      applyStmtRulesToCandidate orderedStmtRules (.assign name value') hits
  | .expr expr =>
      let (expr', hits) := rewriteExprOnce orderedExprRules expr
      applyStmtRulesToCandidate orderedStmtRules (.expr expr') hits
  | .leave =>
      applyStmtRulesToCandidate orderedStmtRules .leave []
  | .if_ cond body =>
      let (cond', condHits) := rewriteExprOnce orderedExprRules cond
      let (body', bodyHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules body
      applyStmtRulesToCandidate orderedStmtRules (.if_ cond' body') (condHits ++ bodyHits)
  | .for_ init cond post body =>
      let (init', initHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules init
      let (cond', condHits) := rewriteExprOnce orderedExprRules cond
      let (post', postHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules post
      let (body', bodyHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules body
      applyStmtRulesToCandidate
        orderedStmtRules
        (.for_ init' cond' post' body')
        (initHits ++ condHits ++ postHits ++ bodyHits)
  | .switch expr cases default =>
      let (expr', exprHits) := rewriteExprOnce orderedExprRules expr
      let (cases', caseHits) := rewriteSwitchCasesOnce orderedExprRules orderedStmtRules orderedBlockRules cases
      let (default', defaultHits) := rewriteOptionalStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules default
      applyStmtRulesToCandidate orderedStmtRules (.switch expr' cases' default') (exprHits ++ caseHits ++ defaultHits)
  | .block stmts =>
      let (stmts', hits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules stmts
      applyStmtRulesToCandidate orderedStmtRules (.block stmts') hits
  | .funcDef name params rets body =>
      let (body', hits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules body
      applyStmtRulesToCandidate orderedStmtRules (.funcDef name params rets body') hits

private def rewriteStmtListOnce
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule) : List YulStmt → (List YulStmt × List String)
  | [] => ([], [])
  | stmt :: rest =>
      let (stmt', headHits) := rewriteStmtOnce orderedExprRules orderedStmtRules orderedBlockRules stmt
      let (rest', tailHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules rest
      let candidate := stmt' :: rest'
      let hits := headHits ++ tailHits
      match applyFirstBlockRule orderedBlockRules candidate with
      | some (rewritten, patchName) => (rewritten, hits ++ [patchName])
      | none => (candidate, hits)

private def rewriteOptionalStmtListOnce
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule) : Option (List YulStmt) → (Option (List YulStmt) × List String)
  | none => (none, [])
  | some stmts =>
      let (stmts', hits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules stmts
      (some stmts', hits)

private def rewriteSwitchCasesOnce
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule) : List (Nat × List YulStmt) → (List (Nat × List YulStmt) × List String)
  | [] => ([], [])
  | (tag, body) :: rest =>
      let (body', bodyHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules body
      let (rest', restHits) := rewriteSwitchCasesOnce orderedExprRules orderedStmtRules orderedBlockRules rest
      ((tag, body') :: rest', bodyHits ++ restHits)

end

private def countHitsForPatch (patchName : String) (hits : List String) : Nat :=
  hits.foldl (fun acc hit => if hit = patchName then acc + 1 else acc) 0

private def metaListFromRules
    (exprRules : List ExprPatchRule)
    (stmtRules : List StmtPatchRule)
    (blockRules : List BlockPatchRule) : List PatchRuleMeta :=
  let exprMeta := exprRules.map (fun rule => { patchName := rule.patchName, proofRef := rule.proofId })
  let stmtMeta := stmtRules.map (fun rule => { patchName := rule.patchName, proofRef := rule.proofId })
  let blockMeta := blockRules.map (fun rule => { patchName := rule.patchName, proofRef := rule.proofId })
  let allMeta := exprMeta ++ stmtMeta ++ blockMeta
  allMeta.foldl
    (fun acc m =>
      if acc.any (fun seen => seen.patchName = m.patchName) then acc else acc ++ [m])
    []

private def manifestFromHits (ruleMeta : List PatchRuleMeta) (hits : List String) : List PatchManifestEntry :=
  (ruleMeta.foldr (fun m acc =>
    let hitCount := countHitsForPatch m.patchName hits
    if hitCount = 0 then
      acc
    else
      { patchName := m.patchName
        matchCount := hitCount
        changedNodes := hitCount
        proofRef := m.proofRef } :: acc) [])

private def runPatchPassLoop
    (fuel : Nat)
    (orderedExprRules : List ExprPatchRule)
    (orderedStmtRules : List StmtPatchRule)
    (orderedBlockRules : List BlockPatchRule)
    (current : List YulStmt)
    (iterations : Nat)
    (allHits : List String) : List YulStmt × Nat × List String :=
  match fuel with
  | 0 => (current, iterations, allHits)
  | Nat.succ fuel' =>
      let (next, stepHits) := rewriteStmtListOnce orderedExprRules orderedStmtRules orderedBlockRules current
      if stepHits.isEmpty then
        (current, iterations, allHits)
      else
        runPatchPassLoop fuel' orderedExprRules orderedStmtRules orderedBlockRules next (iterations + 1) (allHits ++ stepHits)

/-- Run one deterministic patch pass over expression and statement rules with bounded fixpoint iterations. -/
def runPatchPassWithBlocks
    (config : PatchPassConfig)
    (exprRules : List ExprPatchRule)
    (stmtRules : List StmtPatchRule)
    (blockRules : List BlockPatchRule)
    (stmts : List YulStmt) : PatchPassReport :=
  if ¬config.enabled then
    { patched := stmts, iterations := 0, manifest := [] }
  else
    let orderedExprRules :=
      orderRulesByPriority (exprRules.filter (fun rule =>
        rule.passPhase == config.passPhase && rule.isAuditable))
    let orderedStmtRules :=
      orderStmtRulesByPriority (stmtRules.filter (fun rule =>
        rule.passPhase == config.passPhase && rule.isAuditable))
    let orderedBlockRules :=
      orderBlockRulesByPriority (blockRules.filter (fun rule =>
        rule.passPhase == config.passPhase && rule.isAuditable))
    let ruleMeta := metaListFromRules orderedExprRules orderedStmtRules orderedBlockRules
    let (patched, iterations, hits) :=
      runPatchPassLoop config.maxIterations orderedExprRules orderedStmtRules orderedBlockRules stmts 0 []
    { patched := patched
      iterations := iterations
      manifest := manifestFromHits ruleMeta hits }

/-- Run one deterministic patch pass over expression and statement rules with bounded fixpoint iterations. -/
def runPatchPass
    (config : PatchPassConfig)
    (exprRules : List ExprPatchRule)
    (stmtRules : List StmtPatchRule)
    (stmts : List YulStmt) : PatchPassReport :=
  runPatchPassWithBlocks config exprRules stmtRules [] stmts

/-- Run one deterministic patch pass on statements with bounded fixpoint iterations. -/
def runExprPatchPass
    (config : PatchPassConfig)
    (rules : List ExprPatchRule)
    (stmts : List YulStmt) : PatchPassReport :=
  runPatchPassWithBlocks config rules [] [] stmts

end Compiler.Yul
