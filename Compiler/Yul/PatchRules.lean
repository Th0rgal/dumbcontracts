import Compiler.Yul.PatchFramework

namespace Compiler.Yul

/-- `or(x, 0) -> x` -/
def orZeroRightRule : ExprPatchRule :=
  { patchName := "or-zero-right"
    pattern := "or(x, 0)"
    rewrite := "x"
    sideConditions := ["second argument is literal zero"]
    proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.or_zero_right_preserves"
    scope := .runtime
    passPhase := .postCodegen
    priority := 100
    applyExpr := fun _ expr =>
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
    scope := .runtime
    passPhase := .postCodegen
    priority := 95
    applyExpr := fun _ expr =>
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
    scope := .runtime
    passPhase := .postCodegen
    priority := 90
    applyExpr := fun _ expr =>
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
    scope := .runtime
    passPhase := .postCodegen
    priority := 85
    applyExpr := fun _ expr =>
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
    scope := .runtime
    passPhase := .postCodegen
    priority := 80
    applyExpr := fun _ expr =>
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
    scope := .runtime
    passPhase := .postCodegen
    priority := 75
    applyExpr := fun _ expr =>
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
    scope := .runtime
    passPhase := .postCodegen
    priority := 74
    applyExpr := fun _ expr =>
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
    scope := .runtime
    passPhase := .postCodegen
    priority := 73
    applyExpr := fun _ expr =>
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
    scope := .runtime
    passPhase := .postCodegen
    priority := 72
    applyExpr := fun _ expr =>
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
    scope := .runtime
    passPhase := .postCodegen
    priority := 71
    applyExpr := fun _ expr =>
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
    scope := .runtime
    passPhase := .postCodegen
    priority := 70
    applyExpr := fun _ expr =>
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
    scope := .runtime
    passPhase := .postCodegen
    priority := 69
    applyExpr := fun _ expr =>
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

/-- Initial deterministic statement patch pack.
    Intentionally empty until the first proof-carrying statement rewrites land. -/
def foundationStmtPatchPack : List StmtPatchRule :=
  []

/-- Initial deterministic block patch pack.
    Intentionally empty until the first proof-carrying block rewrites land. -/
def foundationBlockPatchPack : List BlockPatchRule :=
  []

/-- Initial deterministic object patch pack.
    Intentionally empty until the first proof-carrying object rewrites land. -/
def foundationObjectPatchPack : List ObjectPatchRule :=
  []

private def appendUniqueString (xs : List String) (item : String) : List String :=
  if xs.any (fun seen => seen = item) then xs else xs ++ [item]

private def unionUniqueStrings (xs ys : List String) : List String :=
  ys.foldl (fun acc item => appendUniqueString acc item) xs

mutual

private partial def callNamesInExpr : YulExpr → List String
  | .call func args =>
      let argCalls := callNamesInExprs args
      appendUniqueString argCalls func
  | _ => []

private partial def callNamesInExprs : List YulExpr → List String
  | [] => []
  | expr :: rest =>
      unionUniqueStrings (callNamesInExpr expr) (callNamesInExprs rest)

private partial def callNamesInStmt : YulStmt → List String
  | .comment _ => []
  | .let_ _ value => callNamesInExpr value
  | .letMany _ value => callNamesInExpr value
  | .assign _ value => callNamesInExpr value
  | .expr value => callNamesInExpr value
  | .leave => []
  | .if_ cond body =>
      unionUniqueStrings (callNamesInExpr cond) (callNamesInStmts body)
  | .for_ init cond post body =>
      unionUniqueStrings
        (callNamesInStmts init)
        (unionUniqueStrings (callNamesInExpr cond) (unionUniqueStrings (callNamesInStmts post) (callNamesInStmts body)))
  | .switch expr cases default =>
      let caseCalls :=
        cases.foldl (fun acc (_, body) => unionUniqueStrings acc (callNamesInStmts body)) []
      let defaultCalls :=
        match default with
        | some body => callNamesInStmts body
        | none => []
      unionUniqueStrings (callNamesInExpr expr) (unionUniqueStrings caseCalls defaultCalls)
  | .block stmts => callNamesInStmts stmts
  | .funcDef _ _ _ body => callNamesInStmts body

private partial def callNamesInStmts : List YulStmt → List String
  | [] => []
  | stmt :: rest =>
      unionUniqueStrings (callNamesInStmt stmt) (callNamesInStmts rest)

end

private def topLevelFunctionDefs (stmts : List YulStmt) : List (String × List YulStmt) :=
  stmts.foldr
    (fun stmt acc =>
      match stmt with
      | .funcDef name _ _ body => (name, body) :: acc
      | _ => acc)
    []

private def topLevelNonFunctionStmts (stmts : List YulStmt) : List YulStmt :=
  stmts.foldr
    (fun stmt acc =>
      match stmt with
      | .funcDef _ _ _ _ => acc
      | _ => stmt :: acc)
    []

private def filterDefinedNames (definedNames : List String) (candidates : List String) : List String :=
  candidates.foldl
    (fun acc name =>
      if definedNames.any (fun defined => defined = name) then
        appendUniqueString acc name
      else
        acc)
    []

private partial def reachableHelperNamesFrom
    (defs : List (String × List YulStmt))
    (definedNames : List String)
    (fuel : Nat)
    (reachable : List String) : List String :=
  match fuel with
  | 0 => reachable
  | fuel + 1 =>
      let expanded :=
        reachable.foldl
          (fun acc name =>
            match defs.find? (fun defn => defn.fst = name) with
            | some (_, body) =>
                unionUniqueStrings acc (filterDefinedNames definedNames (callNamesInStmts body))
            | none => acc)
          reachable
      if expanded.length = reachable.length then
        reachable
      else
        reachableHelperNamesFrom defs definedNames fuel expanded

private def reachableTopLevelHelperNames (stmts : List YulStmt) : List String :=
  let defs := topLevelFunctionDefs stmts
  let definedNames := defs.map Prod.fst
  let seed := filterDefinedNames definedNames (callNamesInStmts (topLevelNonFunctionStmts stmts))
  reachableHelperNamesFrom defs definedNames (defs.length + 1) seed

private def pruneUnreachableTopLevelHelpers (stmts : List YulStmt) : List YulStmt × Nat :=
  let reachable := reachableTopLevelHelperNames stmts
  stmts.foldr
    (fun stmt (accStmts, removed) =>
      match stmt with
      | .funcDef name params rets body =>
          if reachable.any (fun seen => seen = name) then
            (.funcDef name params rets body :: accStmts, removed)
          else
            (accStmts, removed + 1)
      | _ =>
          (stmt :: accStmts, removed))
    ([], 0)

private def solcCompatFunAliasTarget? (name : String) : Option String :=
  if name.startsWith "internal__" then
    some s!"fun_{name.drop 10}"
  else
    none

private def renameTargetFor (renames : List (String × String)) (name : String) : String :=
  match renames.find? (fun entry => entry.fst = name) with
  | some entry => entry.snd
  | none => name

private def solcCompatInternalFunRenameMap (stmts : List YulStmt) : List (String × String) :=
  let definedNames := topLevelFunctionDefs stmts |>.map Prod.fst
  definedNames.foldl
    (fun acc name =>
      match solcCompatFunAliasTarget? name with
      | none => acc
      | some target =>
          let targetAlreadyDefined := definedNames.any (fun seen => seen = target)
          let targetAlreadyAssigned := acc.any (fun entry => entry.snd = target)
          if targetAlreadyDefined || targetAlreadyAssigned then
            acc
          else
            acc ++ [(name, target)])
    []

mutual

private partial def renameCallsInExpr (renames : List (String × String)) : YulExpr → YulExpr
  | .lit n => .lit n
  | .hex n => .hex n
  | .str s => .str s
  | .ident name => .ident name
  | .call func args =>
      .call (renameTargetFor renames func) (renameCallsInExprs renames args)

private partial def renameCallsInExprs (renames : List (String × String)) : List YulExpr → List YulExpr
  | [] => []
  | expr :: rest => renameCallsInExpr renames expr :: renameCallsInExprs renames rest

private partial def renameCallsInStmt (renames : List (String × String)) : YulStmt → YulStmt
  | .comment text => .comment text
  | .let_ name value => .let_ name (renameCallsInExpr renames value)
  | .letMany names value => .letMany names (renameCallsInExpr renames value)
  | .assign name value => .assign name (renameCallsInExpr renames value)
  | .expr value => .expr (renameCallsInExpr renames value)
  | .leave => .leave
  | .if_ cond body =>
      .if_ (renameCallsInExpr renames cond) (renameCallsInStmts renames body)
  | .for_ init cond post body =>
      .for_
        (renameCallsInStmts renames init)
        (renameCallsInExpr renames cond)
        (renameCallsInStmts renames post)
        (renameCallsInStmts renames body)
  | .switch expr cases default =>
      .switch
        (renameCallsInExpr renames expr)
        (cases.map (fun (tag, body) => (tag, renameCallsInStmts renames body)))
        (default.map (renameCallsInStmts renames))
  | .block stmts => .block (renameCallsInStmts renames stmts)
  | .funcDef name params rets body =>
      .funcDef (renameTargetFor renames name) params rets (renameCallsInStmts renames body)

private partial def renameCallsInStmts (renames : List (String × String)) : List YulStmt → List YulStmt
  | [] => []
  | stmt :: rest => renameCallsInStmt renames stmt :: renameCallsInStmts renames rest

end

private def canonicalizeInternalFunNames (stmts : List YulStmt) : List YulStmt × Nat :=
  let renames := solcCompatInternalFunRenameMap stmts
  if renames.isEmpty then
    (stmts, 0)
  else
    (renameCallsInStmts renames stmts, renames.length)

def solcCompatPruneUnreachableHelpersProofRef : String :=
  "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_prune_unreachable_helpers_preserves"

/-- Canonicalize Verity internal helper naming to `solc`-style `fun_*` names when collision-free. -/
def solcCompatCanonicalizeInternalFunNamesProofRef : String :=
  "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_canonicalize_internal_fun_names_preserves"

/-- Deduplicate top-level helper definitions that are structurally equivalent. -/
def solcCompatDedupeEquivalentHelpersProofRef : String :=
  "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_dedupe_equivalent_helpers_preserves"

private def findEquivalentTopLevelHelper?
    (seen : List (String × List String × List String × String))
    (params rets : List String)
    (body : List YulStmt) : Option String :=
  let bodyKey : String := reprStr body
  match seen.find? (fun entry =>
      decide (entry.2.1 = params) && decide (entry.2.2.1 = rets) && decide (entry.2.2.2 = bodyKey)) with
  | some entry => some entry.1
  | none => none

private def dedupeEquivalentTopLevelHelpers (stmts : List YulStmt) : List YulStmt × Nat :=
  let step := fun (acc : (List YulStmt × List (String × List String × List String × String) ×
      List (String × String) × Nat)) (stmt : YulStmt) =>
    let (keptRev, seen, renames, removed) := acc
    match stmt with
    | .funcDef name params rets body =>
        match findEquivalentTopLevelHelper? seen params rets body with
        | some canonical =>
            let renames' :=
              if canonical = name || renames.any (fun pair => pair.fst = name && pair.snd = canonical) then
                renames
              else
                renames ++ [(name, canonical)]
            (keptRev, seen, renames', removed + 1)
        | none =>
            (.funcDef name params rets body :: keptRev, (name, params, rets, reprStr body) :: seen, renames, removed)
    | _ =>
        (stmt :: keptRev, seen, renames, removed)
  let (keptRev, _, renames, removed) := stmts.foldl step ([], [], [], 0)
  let kept := keptRev.reverse
  if removed = 0 then
    (stmts, 0)
  else if renames.isEmpty then
    (kept, removed)
  else
    (renameCallsInStmts renames kept, removed)

/-- Canonicalize `internal__*` helper names to `fun_*` and rewrite in-object call sites.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatCanonicalizeInternalFunNamesRule : ObjectPatchRule :=
  { patchName := "solc-compat-canonicalize-internal-fun-names"
    pattern := "function internal__X(...) with in-object call sites"
    rewrite := "function fun_X(...) with updated in-object call sites"
    sideConditions :=
      [ "only top-level function names with prefix internal__ are considered"
      , "target fun_* name must not already be defined in the same object code list"
      , "if two internal__ names map to the same target, only the first is renamed" ]
    proofId := solcCompatCanonicalizeInternalFunNamesProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 210
    applyObject := fun _ obj =>
      let (deployCode', deployRenamed) := canonicalizeInternalFunNames obj.deployCode
      let (runtimeCode', runtimeRenamed) := canonicalizeInternalFunNames obj.runtimeCode
      if deployRenamed + runtimeRenamed = 0 then
        none
      else
        some { obj with deployCode := deployCode', runtimeCode := runtimeCode' } }

/-- Deduplicate top-level helper function defs that are structurally equivalent.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatDedupeEquivalentHelpersRule : ObjectPatchRule :=
  { patchName := "solc-compat-dedupe-equivalent-helpers"
    pattern := "duplicate top-level helper defs with equivalent params/returns/body"
    rewrite := "retain first helper def, rewrite call sites to retained helper"
    sideConditions :=
      [ "only top-level function definitions are considered"
      , "equivalence requires exact params/returns/body structural equality"
      , "the first encountered equivalent helper is canonical" ]
    proofId := solcCompatDedupeEquivalentHelpersProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 205
    applyObject := fun _ obj =>
      let (deployCode', deployRemoved) := dedupeEquivalentTopLevelHelpers obj.deployCode
      let (runtimeCode', runtimeRemoved) := dedupeEquivalentTopLevelHelpers obj.runtimeCode
      if deployRemoved + runtimeRemoved = 0 then
        none
      else
        some { obj with deployCode := deployCode', runtimeCode := runtimeCode' } }

/-- Remove unreachable top-level helper function definitions in deploy/runtime code.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatPruneUnreachableHelpersRule : ObjectPatchRule :=
  { patchName := "solc-compat-prune-unreachable-helpers"
    pattern := "object-level top-level helper function defs"
    rewrite := "remove helpers not reachable from non-function statements"
    sideConditions :=
      [ "only top-level function definitions are considered"
      , "reachability is computed transitively from non-function statements"
      , "helpers called by reachable helpers are retained" ]
    proofId := solcCompatPruneUnreachableHelpersProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 200
    applyObject := fun _ obj =>
      let (deployCode', deployRemoved) := pruneUnreachableTopLevelHelpers obj.deployCode
      let (runtimeCode', runtimeRemoved) := pruneUnreachableTopLevelHelpers obj.runtimeCode
      if deployRemoved + runtimeRemoved = 0 then
        none
      else
        some { obj with deployCode := deployCode', runtimeCode := runtimeCode' } }

structure RewriteRuleBundle where
  id : String
  exprRules : List ExprPatchRule
  stmtRules : List StmtPatchRule
  blockRules : List BlockPatchRule
  objectRules : List ObjectPatchRule

private def rewriteBundleProofAllowlist (bundle : RewriteRuleBundle) : List String :=
  let exprProofs := bundle.exprRules.map (fun rule => rule.proofId)
  let stmtProofs := bundle.stmtRules.map (fun rule => rule.proofId)
  let blockProofs := bundle.blockRules.map (fun rule => rule.proofId)
  let objectProofs := bundle.objectRules.map (fun rule => rule.proofId)
  let allProofs := exprProofs ++ stmtProofs ++ blockProofs ++ objectProofs
  allProofs.foldl
    (fun acc proofRef => if acc.any (fun seen => seen = proofRef) then acc else acc ++ [proofRef])
    []

def foundationRewriteBundleId : String := "foundation"

def solcCompatRewriteBundleId : String := "solc-compat-v0"

/-- Baseline, non-compat rewrite bundle. -/
def foundationRewriteBundle : RewriteRuleBundle :=
  { id := foundationRewriteBundleId
    exprRules := foundationExprPatchPack
    stmtRules := foundationStmtPatchPack
    blockRules := foundationBlockPatchPack
    objectRules := foundationObjectPatchPack }

/-- Opt-in `solc` compatibility rewrite bundle.
    Initially aliases foundation rules until dedicated compatibility rewrites land. -/
def solcCompatRewriteBundle : RewriteRuleBundle :=
  { id := solcCompatRewriteBundleId
    exprRules := foundationExprPatchPack
    stmtRules := foundationStmtPatchPack
    blockRules := foundationBlockPatchPack
    objectRules := foundationObjectPatchPack ++
      [ solcCompatCanonicalizeInternalFunNamesRule
      , solcCompatDedupeEquivalentHelpersRule
      , solcCompatPruneUnreachableHelpersRule ] }

def allRewriteBundles : List RewriteRuleBundle :=
  [foundationRewriteBundle, solcCompatRewriteBundle]

def supportedRewriteBundleIds : List String :=
  allRewriteBundles.map (·.id)

def findRewriteBundle? (bundleId : String) : Option RewriteRuleBundle :=
  allRewriteBundles.find? (fun bundle => bundle.id = bundleId)

def rewriteBundleForId (bundleId : String) : RewriteRuleBundle :=
  match findRewriteBundle? bundleId with
  | some bundle => bundle
  | none => foundationRewriteBundle

def rewriteProofAllowlistForId (bundleId : String) : List String :=
  rewriteBundleProofAllowlist (rewriteBundleForId bundleId)

/-- Activation-time proof allowlist for the shipped foundation patch packs. -/
def foundationProofAllowlist : List String :=
  rewriteBundleProofAllowlist foundationRewriteBundle

/-- Activation-time proof allowlist for the shipped `solc` compatibility patch bundle. -/
def solcCompatProofAllowlist : List String :=
  rewriteBundleProofAllowlist solcCompatRewriteBundle

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
        scope := .runtime
        passPhase := .postCodegen
        priority := 999
        applyExpr := fun _ expr =>
          match expr with
          | .call "or" [lhs, .lit 0] => some lhs
          | _ => none }
    let stmt : YulStmt := .expr (.call "or" [.ident "x", .lit 0])
    let report := runExprPatchPass { enabled := true, maxIterations := 1 } [unsafeRule] [stmt]
    (match report.patched, report.iterations, report.manifest with
    | [.expr (.call "or" [.ident "x", .lit 0])], 0, [] => true
    | _, _, _ => false) = true := by
  native_decide

/-- Smoke test: rules with unregistered proof refs are fail-closed when proof registry enforcement is enabled. -/
example :
    let mismatchedProofRule : ExprPatchRule :=
      { patchName := "unregistered-proof-id"
        pattern := "or(x, 0)"
        rewrite := "x"
        sideConditions := ["second argument is literal zero"]
        proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.not_registered"
        scope := .runtime
        passPhase := .postCodegen
        priority := 999
        applyExpr := fun _ expr =>
          match expr with
          | .call "or" [lhs, .lit 0] => some lhs
          | _ => none }
    let stmt : YulStmt := .expr (.call "or" [.ident "x", .lit 0])
    let report := runExprPatchPass
      { enabled := true
        maxIterations := 1
        requiredProofRefs := foundationProofAllowlist }
      [mismatchedProofRule]
      [stmt]
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
        scope := .runtime
        passPhase := .postCodegen
        priority := 50
        applyStmt := fun _ stmt =>
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
        scope := .runtime
        passPhase := .postCodegen
        priority := 999
        applyStmt := fun _ stmt =>
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
        scope := .runtime
        passPhase := .postCodegen
        priority := 40
        applyBlock := fun _ block =>
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
        scope := .runtime
        passPhase := .postCodegen
        priority := 999
        applyBlock := fun _ block =>
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

/-- Smoke test: object rules can rewrite full-object fields after deploy/runtime subtree rewrites. -/
example :
    let renameObject : ObjectPatchRule :=
      { patchName := "rename-object"
        pattern := "object Main"
        rewrite := "object MainParity"
        sideConditions := ["object name is Main"]
        proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.rename_object_preserves"
        scope := .object
        passPhase := .postCodegen
        priority := 30
        applyObject := fun _ obj =>
          if obj.name = "Main" then
            some { obj with name := "MainParity" }
          else
            none }
    let input : YulObject :=
      { name := "Main", deployCode := [.comment "deploy"], runtimeCode := [.comment "runtime"] }
    let report := runPatchPassWithObjects
      { enabled := true, maxIterations := 1 }
      []
      []
      []
      [renameObject]
      input
    (match report.patched.name, report.manifest.map (fun m => m.patchName) with
    | "MainParity", ["rename-object"] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: compatibility wrapper `runPatchPassOnObject` rewrites deploy/runtime
    subtrees with scope-aware rule enforcement. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := [.expr (.call "or" [.ident "x", .lit 0])]
        runtimeCode := [.expr (.call "add" [.ident "y", .lit 0])] }
    let report := runPatchPassOnObject
      { enabled := true, maxIterations := 1 }
      foundationExprPatchPack
      []
      []
      input
    (match report.patched.deployCode, report.patched.runtimeCode, report.manifest.map (fun m => m.patchName) with
    | [.expr (.call "or" [.ident "x", .lit 0])], [.expr (.ident "y")], ["add-zero-right"] => true
    | _, _, _ => false) = true := by
  native_decide

/-- Smoke test: deploy-scoped expression rules do not run on runtime code. -/
example :
    let deployOnly : ExprPatchRule :=
      { patchName := "deploy-only-add-zero-right"
        pattern := "add(x, 0)"
        rewrite := "x"
        sideConditions := ["second argument is literal zero"]
        proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.add_zero_right_preserves"
        scope := .deploy
        passPhase := .postCodegen
        priority := 1000
        applyExpr := fun _ expr =>
          match expr with
          | .call "add" [lhs, .lit 0] => some lhs
          | _ => none }
    let input : YulObject :=
      { name := "Main"
        deployCode := [.expr (.call "add" [.ident "x", .lit 0])]
        runtimeCode := [.expr (.call "add" [.ident "y", .lit 0])] }
    let report := runPatchPassOnObject
      { enabled := true, maxIterations := 1 }
      [deployOnly]
      []
      []
      input
    (match report.patched.deployCode, report.patched.runtimeCode, report.manifest.map (fun m => m.patchName) with
    | [.expr (.ident "x")], [.expr (.call "add" [.ident "y", .lit 0])], ["deploy-only-add-zero-right"] => true
    | _, _, _ => false) = true := by
  native_decide

/-- Smoke test: pack-allowlisted expression rules only activate for matching `RewriteCtx.packId`. -/
example :
    let packScoped : ExprPatchRule :=
      { patchName := "pack-scoped-add-zero-right"
        pattern := "add(x, 0)"
        rewrite := "x"
        sideConditions := ["second argument is literal zero"]
        proofId := "Compiler.Proofs.YulGeneration.PatchRulesProofs.add_zero_right_preserves"
        packAllowlist := ["solc-0.8.28-o999999-viair-true-evm-paris"]
        scope := .runtime
        passPhase := .postCodegen
        priority := 1000
        applyExpr := fun _ expr =>
          match expr with
          | .call "add" [lhs, .lit 0] => some lhs
          | _ => none }
    let stmt : YulStmt := .expr (.call "add" [.ident "x", .lit 0])
    let reportMatched := runExprPatchPass
      { enabled := true, maxIterations := 1, packId := "solc-0.8.28-o999999-viair-true-evm-paris" }
      [packScoped]
      [stmt]
    let reportMissed := runExprPatchPass
      { enabled := true, maxIterations := 1, packId := "solc-0.8.28-o200-viair-false-evm-shanghai" }
      [packScoped]
      [stmt]
    (match reportMatched.patched, reportMissed.patched with
    | [.expr (.ident "x")], [.expr (.call "add" [.ident "x", .lit 0])] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: shipped rewrite bundles include an explicit `solc` compatibility bundle. -/
example :
    supportedRewriteBundleIds = [foundationRewriteBundleId, solcCompatRewriteBundleId] := by
  native_decide

/-- Smoke test: unknown rewrite bundle IDs fail closed to foundation. -/
example :
    (rewriteBundleForId "missing-bundle").id = foundationRewriteBundleId := by
  native_decide

/-- Smoke test: compatibility bundle currently inherits foundation proof allowlist. -/
example :
    rewriteProofAllowlistForId solcCompatRewriteBundleId = solcCompatProofAllowlist := by
  native_decide

/-- Smoke test: `solc-compat` bundle extends foundation with compatibility-only proofs. -/
example :
    foundationProofAllowlist.any (fun proofRef => proofRef = solcCompatPruneUnreachableHelpersProofRef) = false := by
  native_decide

/-- Smoke test: `solc-compat` bundle contains compatibility-only proof refs. -/
example :
    solcCompatProofAllowlist.any (fun proofRef => proofRef = solcCompatPruneUnreachableHelpersProofRef) = true := by
  native_decide

/-- Smoke test: `solc-compat` bundle contains canonical internal-fun rename proof refs. -/
example :
    solcCompatProofAllowlist.any
      (fun proofRef => proofRef = solcCompatCanonicalizeInternalFunNamesProofRef) = true := by
  native_decide

/-- Smoke test: `solc-compat` bundle contains equivalent helper dedupe proof refs. -/
example :
    solcCompatProofAllowlist.any
      (fun proofRef => proofRef = solcCompatDedupeEquivalentHelpersProofRef) = true := by
  native_decide

/-- Smoke test: object rule canonicalizes internal helper names and rewrites call sites. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode :=
          [ .funcDef "internal__foo" [] [] [.leave]
          , .funcDef "bar" [] [] [.expr (.call "internal__foo" [])]
          , .expr (.call "bar" [])
          ] }
    let report := runPatchPassWithObjects
      { enabled := true
        maxIterations := 2
        rewriteBundleId := solcCompatRewriteBundleId
        requiredProofRefs := solcCompatProofAllowlist }
      []
      []
      []
      [solcCompatCanonicalizeInternalFunNamesRule]
      input
    (match report.patched.runtimeCode, report.manifest.map (fun m => m.patchName) with
    | [ .funcDef "fun_foo" [] [] [.leave]
      , .funcDef "bar" [] [] [.expr (.call "fun_foo" [])]
      , .expr (.call "bar" [])
      ],
      ["solc-compat-canonicalize-internal-fun-names"] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: canonicalization is fail-safe when target name already exists. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode :=
          [ .funcDef "internal__foo" [] [] [.leave]
          , .funcDef "fun_foo" [] [] [.leave]
          , .funcDef "bar" [] [] [.expr (.call "internal__foo" [])]
          ] }
    let report := runPatchPassWithObjects
      { enabled := true
        maxIterations := 2
        rewriteBundleId := solcCompatRewriteBundleId
        requiredProofRefs := solcCompatProofAllowlist }
      []
      []
      []
      [solcCompatCanonicalizeInternalFunNamesRule]
      input
    (match report.patched.runtimeCode, report.manifest with
    | [ .funcDef "internal__foo" [] [] [.leave]
      , .funcDef "fun_foo" [] [] [.leave]
      , .funcDef "bar" [] [] [.expr (.call "internal__foo" [])]
      ], [] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: object rule prunes unreachable helpers and keeps reachable transitive callees. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode :=
          [ .funcDef "deployUnused" [] [] [.leave]
          , .expr (.call "return" [.lit 0, .lit 0])
          ]
        runtimeCode :=
          [ .funcDef "helperB" [] [] [.leave]
          , .funcDef "helperA" [] [] [.expr (.call "helperB" [])]
          , .funcDef "dead" [] [] [.leave]
          , .switch (.call "shr" [.lit 224, .call "calldataload" [.lit 0]])
              [(0, [.expr (.call "helperA" [])])]
              (some [.expr (.call "revert" [.lit 0, .lit 0])])
          ] }
    let report := runPatchPassWithObjects
      { enabled := true
        maxIterations := 2
        rewriteBundleId := solcCompatRewriteBundleId
        requiredProofRefs := solcCompatProofAllowlist }
      []
      []
      []
      [solcCompatPruneUnreachableHelpersRule]
      input
    (match report.patched.deployCode, report.patched.runtimeCode, report.manifest.map (fun m => m.patchName) with
    | [.expr (.call "return" [.lit 0, .lit 0])],
      [.funcDef "helperB" [] [] [.leave],
       .funcDef "helperA" [] [] [.expr (.call "helperB" [])],
       .switch (.call "shr" [.lit 224, .call "calldataload" [.lit 0]])
         [(0, [.expr (.call "helperA" [])])]
         (some [.expr (.call "revert" [.lit 0, .lit 0])])],
      ["solc-compat-prune-unreachable-helpers"] => true
    | _, _, _ => false) = true := by
  native_decide

/-- Smoke test: object rule dedupes equivalent helpers and rewrites call sites to canonical helper. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode :=
          [ .funcDef "helperCanonical" [] [] [.leave]
          , .funcDef "helperAlias" [] [] [.leave]
          , .funcDef "entry" [] [] [.expr (.call "helperAlias" [])]
          , .expr (.call "entry" [])
          ] }
    let report := runPatchPassWithObjects
      { enabled := true
        maxIterations := 2
        rewriteBundleId := solcCompatRewriteBundleId
        requiredProofRefs := solcCompatProofAllowlist }
      []
      []
      []
      [solcCompatDedupeEquivalentHelpersRule]
      input
    (match report.patched.runtimeCode, report.manifest.map (fun m => m.patchName) with
    | [ .funcDef "helperCanonical" [] [] [.leave]
      , .funcDef "entry" [] [] [.expr (.call "helperCanonical" [])]
      , .expr (.call "entry" [])
      ],
      ["solc-compat-dedupe-equivalent-helpers"] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: exact duplicate helper defs with identical names are deduped. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode :=
          [ .funcDef "dup" [] [] [.leave]
          , .funcDef "dup" [] [] [.leave]
          , .expr (.call "dup" [])
          ] }
    let report := runPatchPassWithObjects
      { enabled := true
        maxIterations := 2
        rewriteBundleId := solcCompatRewriteBundleId
        requiredProofRefs := solcCompatProofAllowlist }
      []
      []
      []
      [solcCompatDedupeEquivalentHelpersRule]
      input
    (match report.patched.runtimeCode, report.manifest.map (fun m => m.patchName) with
    | [ .funcDef "dup" [] [] [.leave]
      , .expr (.call "dup" [])
      ],
      ["solc-compat-dedupe-equivalent-helpers"] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: non-auditable object rules are fail-closed. -/
example :
    let unsafeObjectRule : ObjectPatchRule :=
      { patchName := "unsafe-object-without-proof"
        pattern := "object Main"
        rewrite := "object MainParity"
        sideConditions := []
        proofId := ""
        scope := .object
        passPhase := .postCodegen
        priority := 999
        applyObject := fun _ obj =>
          if obj.name = "Main" then
            some { obj with name := "MainParity" }
          else
            none }
    let input : YulObject :=
      { name := "Main", deployCode := [.comment "deploy"], runtimeCode := [.comment "runtime"] }
    let report := runPatchPassWithObjects
      { enabled := true, maxIterations := 1 }
      []
      []
      []
      [unsafeObjectRule]
      input
    (match report.patched.name, report.iterations, report.manifest with
    | "Main", 0, [] => true
    | _, _, _ => false) = true := by
  native_decide

end Compiler.Yul
