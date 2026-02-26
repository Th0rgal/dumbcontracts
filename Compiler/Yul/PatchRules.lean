import Compiler.Yul.PatchFramework

namespace Compiler.Yul

/-- `or(x, 0) -> x` -/
def orZeroRightRule : ExprPatchRule :=
  { patchName := "or-zero-right"
    pattern := "or(x, 0)"
    rewrite := "x"
    sideConditions := ["second argument is literal zero"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.or_zero_right_preserves"
    passPhase := .postCodegen
    priority := 100
    applyExpr := fun expr =>
      match expr with
      | .call "or" [lhs, .lit 0] => some lhs
      | _ => none }

/-- `or(0, x) -> x` -/
def orZeroLeftRule : ExprPatchRule :=
  { patchName := "or-zero-left"
    pattern := "or(0, x)"
    rewrite := "x"
    sideConditions := ["first argument is literal zero"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.or_zero_left_preserves"
    passPhase := .postCodegen
    priority := 95
    applyExpr := fun expr =>
      match expr with
      | .call "or" [.lit 0, rhs] => some rhs
      | _ => none }

/-- `xor(x, 0) -> x` -/
def xorZeroRightRule : ExprPatchRule :=
  { patchName := "xor-zero-right"
    pattern := "xor(x, 0)"
    rewrite := "x"
    sideConditions := ["second argument is literal zero"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.xor_zero_right_preserves"
    passPhase := .postCodegen
    priority := 90
    applyExpr := fun expr =>
      match expr with
      | .call "xor" [lhs, .lit 0] => some lhs
      | _ => none }

/-- `xor(0, x) -> x` -/
def xorZeroLeftRule : ExprPatchRule :=
  { patchName := "xor-zero-left"
    pattern := "xor(0, x)"
    rewrite := "x"
    sideConditions := ["first argument is literal zero"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.xor_zero_left_preserves"
    passPhase := .postCodegen
    priority := 85
    applyExpr := fun expr =>
      match expr with
      | .call "xor" [.lit 0, rhs] => some rhs
      | _ => none }

/-- `and(x, 0) -> 0` -/
def andZeroRightRule : ExprPatchRule :=
  { patchName := "and-zero-right"
    pattern := "and(x, 0)"
    rewrite := "0"
    sideConditions := ["second argument is literal zero"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.and_zero_right_preserves"
    passPhase := .postCodegen
    priority := 80
    applyExpr := fun expr =>
      match expr with
      | .call "and" [_lhs, .lit 0] => some (.lit 0)
      | _ => none }

/-- `add(x, 0) -> x` -/
def addZeroRightRule : ExprPatchRule :=
  { patchName := "add-zero-right"
    pattern := "add(x, 0)"
    rewrite := "x"
    sideConditions := ["second argument is literal zero"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.add_zero_right_preserves"
    passPhase := .postCodegen
    priority := 75
    applyExpr := fun expr =>
      match expr with
      | .call "add" [lhs, .lit 0] => some lhs
      | _ => none }

/-- `add(0, x) -> x` -/
def addZeroLeftRule : ExprPatchRule :=
  { patchName := "add-zero-left"
    pattern := "add(0, x)"
    rewrite := "x"
    sideConditions := ["first argument is literal zero"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.add_zero_left_preserves"
    passPhase := .postCodegen
    priority := 74
    applyExpr := fun expr =>
      match expr with
      | .call "add" [.lit 0, rhs] => some rhs
      | _ => none }

/-- `sub(x, 0) -> x` -/
def subZeroRightRule : ExprPatchRule :=
  { patchName := "sub-zero-right"
    pattern := "sub(x, 0)"
    rewrite := "x"
    sideConditions := ["second argument is literal zero"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.sub_zero_right_preserves"
    passPhase := .postCodegen
    priority := 73
    applyExpr := fun expr =>
      match expr with
      | .call "sub" [lhs, .lit 0] => some lhs
      | _ => none }

/-- `mul(x, 1) -> x` -/
def mulOneRightRule : ExprPatchRule :=
  { patchName := "mul-one-right"
    pattern := "mul(x, 1)"
    rewrite := "x"
    sideConditions := ["second argument is literal one"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.mul_one_right_preserves"
    passPhase := .postCodegen
    priority := 72
    applyExpr := fun expr =>
      match expr with
      | .call "mul" [lhs, .lit 1] => some lhs
      | _ => none }

/-- `mul(1, x) -> x` -/
def mulOneLeftRule : ExprPatchRule :=
  { patchName := "mul-one-left"
    pattern := "mul(1, x)"
    rewrite := "x"
    sideConditions := ["first argument is literal one"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.mul_one_left_preserves"
    passPhase := .postCodegen
    priority := 71
    applyExpr := fun expr =>
      match expr with
      | .call "mul" [.lit 1, rhs] => some rhs
      | _ => none }

/-- `div(x, 1) -> x` -/
def divOneRightRule : ExprPatchRule :=
  { patchName := "div-one-right"
    pattern := "div(x, 1)"
    rewrite := "x"
    sideConditions := ["second argument is literal one"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.div_one_right_preserves"
    passPhase := .postCodegen
    priority := 70
    applyExpr := fun expr =>
      match expr with
      | .call "div" [lhs, .lit 1] => some lhs
      | _ => none }

/-- `mod(x, 1) -> 0` -/
def modOneRightRule : ExprPatchRule :=
  { patchName := "mod-one-right"
    pattern := "mod(x, 1)"
    rewrite := "0"
    sideConditions := ["second argument is literal one"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.mod_one_right_preserves"
    passPhase := .postCodegen
    priority := 69
    applyExpr := fun expr =>
      match expr with
      | .call "mod" [_lhs, .lit 1] => some (.lit 0)
      | _ => none }

/-- Initial deterministic, proven-safe expression patch pack (Issue #583 expansion). -/
def foundationExprPatchPack : List ExprPatchRule :=
  [ orZeroRightRule
  , orZeroLeftRule
  , xorZeroRightRule
  , xorZeroLeftRule
  , andZeroRightRule
  , addZeroRightRule
  , addZeroLeftRule
  , subZeroRightRule
  , mulOneRightRule
  , mulOneLeftRule
  , divOneRightRule
  , modOneRightRule
  ]

/-- Smoke test: higher-priority rule wins deterministically. -/
example :
    (let rules := orderRulesByPriority
      [ modOneRightRule
      , addZeroLeftRule
      , andZeroRightRule
      , xorZeroLeftRule
      , mulOneRightRule
      , xorZeroRightRule
      , orZeroRightRule
      , divOneRightRule
      , addZeroRightRule
      , mulOneLeftRule
      , subZeroRightRule
      , orZeroLeftRule
      ]
     rules.map (fun r => r.patchName)) =
    [ "or-zero-right"
    , "or-zero-left"
    , "xor-zero-right"
    , "xor-zero-left"
    , "and-zero-right"
    , "add-zero-right"
    , "add-zero-left"
    , "sub-zero-right"
    , "mul-one-right"
    , "mul-one-left"
    , "div-one-right"
    , "mod-one-right"
    ] := by
  native_decide

/-- Smoke test: one rewrite pass catches nested expression occurrences. -/
example :
    let stmt : YulStmt :=
      .expr (.call "or" [.call "xor" [.ident "x", .lit 0], .lit 0])
    let report := runExprPatchPass { enabled := true, maxIterations := 1 } foundationExprPatchPack [stmt]
    (match report.patched with
    | [.expr (.ident "x")] => true
    | _ => false) = true := by
  native_decide

/-- Smoke test: manifest emits rule usage with proof refs. -/
example :
    let stmt : YulStmt := .expr (.call "or" [.ident "x", .lit 0])
    let report := runExprPatchPass { enabled := true, maxIterations := 1 } foundationExprPatchPack [stmt]
    report.manifest.map (fun m => (m.patchName, m.matchCount, m.proofRef)) =
      [("or-zero-right", 1,
        "Compiler.Proofs.YulGeneration.PatchRulesProofs.or_zero_right_preserves")] := by
  native_decide

/-- Smoke test: `xor(0, x)` rewrites to `x`. -/
example :
    let stmt : YulStmt := .expr (.call "xor" [.lit 0, .ident "x"])
    let report := runExprPatchPass { enabled := true, maxIterations := 1 } foundationExprPatchPack [stmt]
    (match report.patched with
    | [.expr (.ident "x")] => true
    | _ => false) = true := by
  native_decide

/-- Smoke test: `and(x, 0)` rewrites to `0`. -/
example :
    let stmt : YulStmt := .expr (.call "and" [.ident "x", .lit 0])
    let report := runExprPatchPass { enabled := true, maxIterations := 1 } foundationExprPatchPack [stmt]
    (match report.patched with
    | [.expr (.lit 0)] => true
    | _ => false) = true := by
  native_decide

/-- Smoke test: `sub(x, 0)` rewrites to `x`. -/
example :
    let stmt : YulStmt := .expr (.call "sub" [.ident "x", .lit 0])
    let report := runExprPatchPass { enabled := true, maxIterations := 1 } foundationExprPatchPack [stmt]
    (match report.patched with
    | [.expr (.ident "x")] => true
    | _ => false) = true := by
  native_decide

/-- Smoke test: `mul(1, x)` rewrites to `x`. -/
example :
    let stmt : YulStmt := .expr (.call "mul" [.lit 1, .ident "x"])
    let report := runExprPatchPass { enabled := true, maxIterations := 1 } foundationExprPatchPack [stmt]
    (match report.patched with
    | [.expr (.ident "x")] => true
    | _ => false) = true := by
  native_decide

/-- Smoke test: `mod(x, 1)` rewrites to `0`. -/
example :
    let stmt : YulStmt := .expr (.call "mod" [.ident "x", .lit 1])
    let report := runExprPatchPass { enabled := true, maxIterations := 1 } foundationExprPatchPack [stmt]
    (match report.patched with
    | [.expr (.lit 0)] => true
    | _ => false) = true := by
  native_decide

/-- Smoke test: fail-closed metadata gate skips non-auditable rules. -/
example :
    let unsafeRule : ExprPatchRule :=
      { patchName := "unsafe-without-proof"
        pattern := "or(x, 0)"
        rewrite := "x"
        sideConditions := []
        proofId := ""
        passPhase := .postCodegen
        priority := 999
        applyExpr := fun expr =>
          match expr with
          | .call "or" [lhs, .lit 0] => some lhs
          | _ => none }
    let stmt : YulStmt := .expr (.call "or" [.ident "x", .lit 0])
    let report := runExprPatchPass { enabled := true, maxIterations := 1 } [unsafeRule] [stmt]
    (match report.patched, report.iterations, report.manifest with
    | [.expr (.call "or" [.ident "x", .lit 0])], 0, [] => true
    | _, _, _ => false) = true := by
  native_decide

/-- Smoke test: statement rules run after expression rewrites in one pass. -/
example :
    let commentFlip : StmtPatchRule :=
      { patchName := "comment-flip"
        pattern := "// from"
        rewrite := "// to"
        sideConditions := ["statement is comment // from"]
        proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.comment_flip_preserves"
        passPhase := .postCodegen
        priority := 50
        applyStmt := fun stmt =>
          match stmt with
          | .comment "from" => some (.comment "to")
          | _ => none }
    let stmt : YulStmt := .comment "from"
    let report := runPatchPass { enabled := true, maxIterations := 1 } foundationExprPatchPack [commentFlip] [stmt]
    (match report.patched, report.manifest.map (fun m => m.patchName) with
    | [.comment "to"], ["comment-flip"] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: non-auditable statement rules are fail-closed. -/
example :
    let unsafeStmtRule : StmtPatchRule :=
      { patchName := "unsafe-stmt-without-proof"
        pattern := "// from"
        rewrite := "// to"
        sideConditions := []
        proofId := ""
        passPhase := .postCodegen
        priority := 999
        applyStmt := fun stmt =>
          match stmt with
          | .comment "from" => some (.comment "to")
          | _ => none }
    let stmt : YulStmt := .comment "from"
    let report := runPatchPass { enabled := true, maxIterations := 1 } [] [unsafeStmtRule] [stmt]
    (match report.patched, report.iterations, report.manifest with
    | [.comment "from"], 0, [] => true
    | _, _, _ => false) = true := by
  native_decide

/-- Smoke test: block rules can rewrite whole statement blocks after child rewrites. -/
example :
    let collapseToNop : BlockPatchRule :=
      { patchName := "collapse-to-nop"
        pattern := "{ leave }"
        rewrite := "{ /* nop */ }"
        sideConditions := ["block contains exactly one leave statement"]
        proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.collapse_to_nop_preserves"
        passPhase := .postCodegen
        priority := 40
        applyBlock := fun block =>
          match block with
          | [.leave] => some [.comment "nop"]
          | _ => none }
    let report := runPatchPassWithBlocks
      { enabled := true, maxIterations := 1 }
      []
      []
      [collapseToNop]
      [.leave]
    (match report.patched, report.manifest.map (fun m => m.patchName) with
    | [.comment "nop"], ["collapse-to-nop"] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: non-auditable block rules are fail-closed. -/
example :
    let unsafeBlockRule : BlockPatchRule :=
      { patchName := "unsafe-block-without-proof"
        pattern := "{ leave }"
        rewrite := "{ /* nop */ }"
        sideConditions := []
        proofId := ""
        passPhase := .postCodegen
        priority := 999
        applyBlock := fun block =>
          match block with
          | [.leave] => some [.comment "nop"]
          | _ => none }
    let report := runPatchPassWithBlocks
      { enabled := true, maxIterations := 1 }
      []
      []
      [unsafeBlockRule]
      [.leave]
    (match report.patched, report.iterations, report.manifest with
    | [.leave], 0, [] => true
    | _, _, _ => false) = true := by
  native_decide

end Compiler.Yul
