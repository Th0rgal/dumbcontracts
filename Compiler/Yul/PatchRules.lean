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

private partial def callNamesInStmtNoFuncDefs : YulStmt → List String
  | .comment _ => []
  | .expr expr => callNamesInExpr expr
  | .let_ _ expr => callNamesInExpr expr
  | .letMany _ expr => callNamesInExpr expr
  | .assign _ expr => callNamesInExpr expr
  | .leave => []
  | .if_ cond body =>
      unionUniqueStrings (callNamesInExpr cond) (callNamesInStmtsNoFuncDefs body)
  | .for_ init cond post body =>
      unionUniqueStrings
        (callNamesInStmtsNoFuncDefs init)
        (unionUniqueStrings
          (callNamesInExpr cond)
          (unionUniqueStrings
            (callNamesInStmtsNoFuncDefs post)
            (callNamesInStmtsNoFuncDefs body)))
  | .switch expr cases default =>
      let caseCalls :=
        cases.foldl (fun acc (_, body) => unionUniqueStrings acc (callNamesInStmtsNoFuncDefs body)) []
      let defaultCalls :=
        match default with
        | some body => callNamesInStmtsNoFuncDefs body
        | none => []
      unionUniqueStrings (callNamesInExpr expr) (unionUniqueStrings caseCalls defaultCalls)
  | .block stmts => callNamesInStmtsNoFuncDefs stmts
  | .funcDef _ _ _ _ => []

private partial def callNamesInStmtsNoFuncDefs : List YulStmt → List String
  | [] => []
  | stmt :: rest =>
      unionUniqueStrings (callNamesInStmtNoFuncDefs stmt) (callNamesInStmtsNoFuncDefs rest)

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
  let seed := filterDefinedNames definedNames (callNamesInStmtsNoFuncDefs (topLevelNonFunctionStmts stmts))
  reachableHelperNamesFrom defs definedNames (defs.length + 1) seed

private def pruneUnreachableTopLevelHelpers (stmts : List YulStmt) : List YulStmt × Nat :=
  let (wrapped, topStmts) :=
    match stmts with
    | [.block inner] => (true, inner)
    | _ => (false, stmts)
  let reachable := reachableTopLevelHelperNames topStmts
  let (prunedTopStmts, removed) :=
    topStmts.foldr
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
  if wrapped then
    ([.block prunedTopStmts], removed)
  else
    (prunedTopStmts, removed)

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

private def dispatchLabelFunctionName? (label : String) : Option String :=
  if label = "fallback()" || label = "receive()" then
    none
  else if label.endsWith "()" then
    let raw := label.dropRight 2
    if raw.isEmpty then none else some raw
  else
    none

private def topLevelFunctionNames (stmts : List YulStmt) : List String :=
  (topLevelFunctionDefs stmts).map Prod.fst

private def appendUniqueHelperDef
    (defs : List (String × List YulStmt))
    (name : String)
    (body : List YulStmt) : List (String × List YulStmt) :=
  if defs.any (fun entry => entry.1 = name) then
    defs
  else
    defs ++ [(name, body)]

private def helperDefsToStmts (defs : List (String × List YulStmt)) : List YulStmt :=
  defs.map (fun entry => .funcDef entry.1 [] [] entry.2)

private def insertTopLevelHelpersAfterPrefix
    (stmts : List YulStmt)
    (defs : List (String × List YulStmt)) : List YulStmt :=
  let rec splitPrefix : List YulStmt → List YulStmt × List YulStmt
    | [] => ([], [])
    | stmt :: rest =>
        match stmt with
        | .funcDef _ _ _ _ =>
            let (pref, suff) := splitPrefix rest
            (stmt :: pref, suff)
        | _ => ([], stmt :: rest)
  let (pref, suff) := splitPrefix stmts
  pref ++ helperDefsToStmts defs ++ suff

mutual

private partial def outlineDispatchCasesInStmt
    (knownDefs : List String)
    (stmt : YulStmt) : YulStmt × List (String × List YulStmt) × List String
  := match stmt with
    | .comment text => (.comment text, [], knownDefs)
    | .let_ name value => (.let_ name value, [], knownDefs)
    | .letMany names value => (.letMany names value, [], knownDefs)
    | .assign name value => (.assign name value, [], knownDefs)
    | .expr value => (.expr value, [], knownDefs)
    | .leave => (.leave, [], knownDefs)
    | .if_ cond body =>
        let (body', defs, knownDefs') := outlineDispatchCasesInStmts knownDefs body
        (.if_ cond body', defs, knownDefs')
    | .for_ init cond post body =>
        let (init', initDefs, knownAfterInit) := outlineDispatchCasesInStmts knownDefs init
        let (post', postDefs, knownAfterPost) := outlineDispatchCasesInStmts knownAfterInit post
        let (body', bodyDefs, knownAfterBody) := outlineDispatchCasesInStmts knownAfterPost body
        (.for_ init' cond post' body',
          initDefs ++ postDefs ++ bodyDefs,
          knownAfterBody)
    | .switch expr cases default =>
        let rec rewriteCases
            (remaining : List (Nat × List YulStmt))
            (known : List String)
            (accCases : List (Nat × List YulStmt))
            (accDefs : List (String × List YulStmt))
            : List (Nat × List YulStmt) × List (String × List YulStmt) × List String :=
          match remaining with
          | [] => (accCases.reverse, accDefs, known)
          | (tag, body) :: rest =>
              let (body', nestedDefs, knownAfterBody) := outlineDispatchCasesInStmts known body
              let knownWithNested :=
                nestedDefs.foldl (fun acc entry => appendUniqueString acc entry.1) knownAfterBody
              let nestedMerged :=
                nestedDefs.foldl (fun acc entry => appendUniqueHelperDef acc entry.1 entry.2) accDefs
              match body' with
              | .comment label :: restBody =>
                  match dispatchLabelFunctionName? label with
                  | some baseName =>
                      let helperName := s!"fun_{baseName}"
                      if knownWithNested.any (fun seen => seen = helperName) then
                        rewriteCases rest knownWithNested ((tag, body') :: accCases) nestedMerged
                      else
                        let defs' := appendUniqueHelperDef nestedMerged helperName restBody
                        let known' := appendUniqueString knownWithNested helperName
                        rewriteCases rest known' ((tag, [.expr (.call helperName [])]) :: accCases) defs'
                  | none =>
                      rewriteCases rest knownWithNested ((tag, body') :: accCases) nestedMerged
              | _ =>
                  rewriteCases rest knownWithNested ((tag, body') :: accCases) nestedMerged
        let (cases', defsFromCases, knownAfterCases) := rewriteCases cases knownDefs [] []
        let (default', defsFromDefault, knownAfterDefault) :=
          match default with
          | some body =>
              let (body', defs, known') := outlineDispatchCasesInStmts knownAfterCases body
              (some body', defs, known')
          | none => (none, [], knownAfterCases)
        let defsAll :=
          defsFromDefault.foldl (fun acc entry => appendUniqueHelperDef acc entry.1 entry.2) defsFromCases
        (.switch expr cases' default', defsAll, knownAfterDefault)
    | .block stmts =>
        let (stmts', defs, knownDefs') := outlineDispatchCasesInStmts knownDefs stmts
        (.block stmts', defs, knownDefs')
    | .funcDef name params rets body =>
        let (body', defs, knownDefs') := outlineDispatchCasesInStmts knownDefs body
        (.funcDef name params rets body', defs, knownDefs')

private partial def outlineDispatchCasesInStmts
    (knownDefs : List String)
    (stmts : List YulStmt) : List YulStmt × List (String × List YulStmt) × List String
  := match stmts with
    | [] => ([], [], knownDefs)
    | stmt :: rest =>
        let (stmt', defsHead, knownAfterHead) := outlineDispatchCasesInStmt knownDefs stmt
        let (rest', defsTail, knownAfterTail) := outlineDispatchCasesInStmts knownAfterHead rest
        let defs :=
          defsTail.foldl (fun acc entry => appendUniqueHelperDef acc entry.1 entry.2) defsHead
        (stmt' :: rest', defs, knownAfterTail)

end

private def outlineRuntimeDispatchHelpers (stmts : List YulStmt) : List YulStmt × Nat :=
  let known := topLevelFunctionNames stmts
  let (rewritten, helperDefs, _) := outlineDispatchCasesInStmts known stmts
  if helperDefs.isEmpty then
    (stmts, 0)
  else
    (insertTopLevelHelpersAfterPrefix rewritten helperDefs, helperDefs.length)

private def topLevelZeroArityFunctionBodies (stmts : List YulStmt) : List (String × List YulStmt) :=
  stmts.foldr
    (fun stmt acc =>
      match stmt with
      | .funcDef name [] [] body => (name, body) :: acc
      | _ => acc)
    []

private def helperBodyForName? (defs : List (String × List YulStmt)) (name : String) : Option (List YulStmt) :=
  match defs.find? (fun entry => entry.1 = name) with
  | some entry => some entry.2
  | none => none

mutual

private partial def inlineDispatchWrapperCallsInStmt
    (helpers : List (String × List YulStmt))
    (stmt : YulStmt) : YulStmt × Nat
  := match stmt with
    | .comment text => (.comment text, 0)
    | .let_ name value => (.let_ name value, 0)
    | .letMany names value => (.letMany names value, 0)
    | .assign name value => (.assign name value, 0)
    | .expr value => (.expr value, 0)
    | .leave => (.leave, 0)
    | .if_ cond body =>
        let (body', rewritten) := inlineDispatchWrapperCallsInStmts helpers body
        (.if_ cond body', rewritten)
    | .for_ init cond post body =>
        let (init', initRewrites) := inlineDispatchWrapperCallsInStmts helpers init
        let (post', postRewrites) := inlineDispatchWrapperCallsInStmts helpers post
        let (body', bodyRewrites) := inlineDispatchWrapperCallsInStmts helpers body
        (.for_ init' cond post' body', initRewrites + postRewrites + bodyRewrites)
    | .switch expr cases default =>
        let rewriteCase := fun (entry : Nat × List YulStmt) =>
          let (tag, body) := entry
          match body with
          | [.expr (.call helperName [])] =>
              if helperName.startsWith "fun_" then
                match helperBodyForName? helpers helperName with
                | some helperBody => ((tag, helperBody), 1)
                | none => ((tag, body), 0)
              else
                ((tag, body), 0)
          | _ =>
              let (body', rewritten) := inlineDispatchWrapperCallsInStmts helpers body
              ((tag, body'), rewritten)
        let rewrittenCases := cases.map rewriteCase
        let cases' := rewrittenCases.map Prod.fst
        let caseRewriteCount := rewrittenCases.foldl (fun acc entry => acc + entry.snd) 0
        let (default', defaultRewriteCount) :=
          match default with
          | some body =>
              let (body', rewritten) := inlineDispatchWrapperCallsInStmts helpers body
              (some body', rewritten)
          | none => (none, 0)
        (.switch expr cases' default', caseRewriteCount + defaultRewriteCount)
    | .block stmts =>
        let (stmts', rewritten) := inlineDispatchWrapperCallsInStmts helpers stmts
        (.block stmts', rewritten)
    | .funcDef name params rets body =>
        let (body', rewritten) := inlineDispatchWrapperCallsInStmts helpers body
        (.funcDef name params rets body', rewritten)

private partial def inlineDispatchWrapperCallsInStmts
    (helpers : List (String × List YulStmt))
    (stmts : List YulStmt) : List YulStmt × Nat
  := match stmts with
    | [] => ([], 0)
    | stmt :: rest =>
        let (stmt', rewrittenHead) := inlineDispatchWrapperCallsInStmt helpers stmt
        let (rest', rewrittenTail) := inlineDispatchWrapperCallsInStmts helpers rest
        (stmt' :: rest', rewrittenHead + rewrittenTail)

end

private def inlineRuntimeDispatchWrapperCalls (stmts : List YulStmt) : List YulStmt × Nat :=
  let helpers := topLevelZeroArityFunctionBodies stmts
  inlineDispatchWrapperCallsInStmts helpers stmts

private def freshMappingSlotTemp (nextId : Nat) : String × Nat :=
  (s!"__compat_mapping_slot_{nextId}", nextId + 1)

mutual

private partial def inlineMappingSlotCallsInExpr
    (nextId : Nat)
    (expr : YulExpr) : List YulStmt × YulExpr × Nat × Nat
  := match expr with
    | .lit n => ([], .lit n, nextId, 0)
    | .hex n => ([], .hex n, nextId, 0)
    | .str s => ([], .str s, nextId, 0)
    | .ident name => ([], .ident name, nextId, 0)
    | .call "mappingSlot" [baseSlot, key] =>
        let (basePrefix, baseSlot', nextAfterBase, baseRewrites) := inlineMappingSlotCallsInExpr nextId baseSlot
        let (keyPrefix, key', nextAfterKey, keyRewrites) := inlineMappingSlotCallsInExpr nextAfterBase key
        let (tmpName, nextAfterTmp) := freshMappingSlotTemp nextAfterKey
        let preStmts :=
          basePrefix ++
            keyPrefix ++
              [ .expr (.call "mstore" [.lit 512, key'])
              , .expr (.call "mstore" [.lit 544, baseSlot'])
              , .let_ tmpName (.call "keccak256" [.lit 512, .lit 64])
              ]
        (preStmts, .ident tmpName, nextAfterTmp, baseRewrites + keyRewrites + 1)
    | .call func args =>
        let (preStmts, args', nextId', rewrites) := inlineMappingSlotCallsInExprs nextId args
        (preStmts, .call func args', nextId', rewrites)

private partial def inlineMappingSlotCallsInExprs
    (nextId : Nat)
    (exprs : List YulExpr) : List YulStmt × List YulExpr × Nat × Nat
  := match exprs with
    | [] => ([], [], nextId, 0)
    | expr :: rest =>
        let (prefixHead, exprHead, nextAfterHead, rewritesHead) := inlineMappingSlotCallsInExpr nextId expr
        let (prefixTail, exprTail, nextAfterTail, rewritesTail) := inlineMappingSlotCallsInExprs nextAfterHead rest
        (prefixHead ++ prefixTail, exprHead :: exprTail, nextAfterTail, rewritesHead + rewritesTail)

private partial def inlineMappingSlotCallsInStmt
    (nextId : Nat)
    (stmt : YulStmt) : List YulStmt × Nat × Nat
  := match stmt with
    | .comment text => ([.comment text], nextId, 0)
    | .let_ name value =>
        let (preStmts, value', nextId', rewrites) := inlineMappingSlotCallsInExpr nextId value
        (preStmts ++ [.let_ name value'], nextId', rewrites)
    | .letMany names value =>
        let (preStmts, value', nextId', rewrites) := inlineMappingSlotCallsInExpr nextId value
        (preStmts ++ [.letMany names value'], nextId', rewrites)
    | .assign name value =>
        let (preStmts, value', nextId', rewrites) := inlineMappingSlotCallsInExpr nextId value
        (preStmts ++ [.assign name value'], nextId', rewrites)
    | .expr value =>
        let (preStmts, value', nextId', rewrites) := inlineMappingSlotCallsInExpr nextId value
        (preStmts ++ [.expr value'], nextId', rewrites)
    | .leave => ([.leave], nextId, 0)
    | .if_ cond body =>
        let (condPrefix, cond', nextAfterCond, condRewrites) := inlineMappingSlotCallsInExpr nextId cond
        let (body', nextAfterBody, bodyRewrites) := inlineMappingSlotCallsInStmts nextAfterCond body
        (condPrefix ++ [.if_ cond' body'], nextAfterBody, condRewrites + bodyRewrites)
    | .for_ init cond post body =>
        let (init', nextAfterInit, initRewrites) := inlineMappingSlotCallsInStmts nextId init
        let (post', nextAfterPost, postRewrites) := inlineMappingSlotCallsInStmts nextAfterInit post
        let (body', nextAfterBody, bodyRewrites) := inlineMappingSlotCallsInStmts nextAfterPost body
        ([.for_ init' cond post' body'], nextAfterBody, initRewrites + postRewrites + bodyRewrites)
    | .switch expr cases default =>
        let (exprPrefix, expr', nextAfterExpr, exprRewrites) := inlineMappingSlotCallsInExpr nextId expr
        let rec rewriteCases
            (remaining : List (Nat × List YulStmt))
            (nextIdCases : Nat)
            (accCases : List (Nat × List YulStmt))
            (accRewrites : Nat)
            : List (Nat × List YulStmt) × Nat × Nat :=
          match remaining with
          | [] => (accCases.reverse, nextIdCases, accRewrites)
          | (tag, body) :: rest =>
              let (body', nextAfterBody, bodyRewrites) := inlineMappingSlotCallsInStmts nextIdCases body
              rewriteCases rest nextAfterBody ((tag, body') :: accCases) (accRewrites + bodyRewrites)
        let (cases', nextAfterCases, caseRewrites) := rewriteCases cases nextAfterExpr [] 0
        let (default', nextAfterDefault, defaultRewrites) :=
          match default with
          | some body =>
              let (body', nextBody, rewritten) := inlineMappingSlotCallsInStmts nextAfterCases body
              (some body', nextBody, rewritten)
          | none => (none, nextAfterCases, 0)
        (exprPrefix ++ [.switch expr' cases' default'], nextAfterDefault, exprRewrites + caseRewrites + defaultRewrites)
    | .block stmts =>
        let (stmts', nextId', rewrites) := inlineMappingSlotCallsInStmts nextId stmts
        ([.block stmts'], nextId', rewrites)
    | .funcDef name params rets body =>
        let (body', nextId', rewrites) := inlineMappingSlotCallsInStmts nextId body
        ([.funcDef name params rets body'], nextId', rewrites)

private partial def inlineMappingSlotCallsInStmts
    (nextId : Nat)
    (stmts : List YulStmt) : List YulStmt × Nat × Nat
  := match stmts with
    | [] => ([], nextId, 0)
    | stmt :: rest =>
        let (stmt', nextAfterStmt, rewritesHead) := inlineMappingSlotCallsInStmt nextId stmt
        let (rest', nextAfterRest, rewritesTail) := inlineMappingSlotCallsInStmts nextAfterStmt rest
        (stmt' ++ rest', nextAfterRest, rewritesHead + rewritesTail)

end

private def inlineRuntimeMappingSlotCalls (stmts : List YulStmt) : List YulStmt × Nat :=
  let (stmts', _, rewritten) := inlineMappingSlotCallsInStmts 0 stmts
  (stmts', rewritten)

private def inlineKeccakMarketParamsLet?
    (name : String)
    (args : List YulExpr) : Option (List YulStmt) :=
  match args with
  | [loanToken, collateralToken, oracle, irm, lltv] =>
      some
        [ .expr (.call "mstore" [.lit 0, loanToken])
        , .expr (.call "mstore" [.lit 32, collateralToken])
        , .expr (.call "mstore" [.lit 64, oracle])
        , .expr (.call "mstore" [.lit 96, irm])
        , .expr (.call "mstore" [.lit 128, lltv])
        , .let_ name (.call "keccak256" [.lit 0, .lit 160])
        ]
  | _ => none

private def inlineKeccakMarketParamsAssign?
    (name : String)
    (args : List YulExpr) : Option (List YulStmt) :=
  match args with
  | [loanToken, collateralToken, oracle, irm, lltv] =>
      some
        [ .expr (.call "mstore" [.lit 0, loanToken])
        , .expr (.call "mstore" [.lit 32, collateralToken])
        , .expr (.call "mstore" [.lit 64, oracle])
        , .expr (.call "mstore" [.lit 96, irm])
        , .expr (.call "mstore" [.lit 128, lltv])
        , .assign name (.call "keccak256" [.lit 0, .lit 160])
        ]
  | _ => none

mutual

private partial def inlineKeccakMarketParamsCallsInStmt
    (stmt : YulStmt) : List YulStmt × Nat
  := match stmt with
    | .comment text => ([.comment text], 0)
    | .let_ name (.call "keccakMarketParams" args) =>
        match inlineKeccakMarketParamsLet? name args with
        | some stmts => (stmts, 1)
        | none => ([stmt], 0)
    | .let_ _ _ => ([stmt], 0)
    | .letMany _ _ => ([stmt], 0)
    | .assign name (.call "keccakMarketParams" args) =>
        match inlineKeccakMarketParamsAssign? name args with
        | some stmts => (stmts, 1)
        | none => ([stmt], 0)
    | .assign _ _ => ([stmt], 0)
    | .expr _ => ([stmt], 0)
    | .leave => ([stmt], 0)
    | .if_ cond body =>
        let (body', rewritten) := inlineKeccakMarketParamsCallsInStmts body
        ([.if_ cond body'], rewritten)
    | .for_ init cond post body =>
        let (init', initRewrites) := inlineKeccakMarketParamsCallsInStmts init
        let (post', postRewrites) := inlineKeccakMarketParamsCallsInStmts post
        let (body', bodyRewrites) := inlineKeccakMarketParamsCallsInStmts body
        ([.for_ init' cond post' body'], initRewrites + postRewrites + bodyRewrites)
    | .switch expr cases default =>
        let rewriteCase := fun (entry : Nat × List YulStmt) =>
          let (tag, body) := entry
          let (body', rewritten) := inlineKeccakMarketParamsCallsInStmts body
          ((tag, body'), rewritten)
        let rewrittenCases := cases.map rewriteCase
        let cases' := rewrittenCases.map Prod.fst
        let caseRewriteCount := rewrittenCases.foldl (fun acc entry => acc + entry.snd) 0
        let (default', defaultRewriteCount) :=
          match default with
          | some body =>
              let (body', rewritten) := inlineKeccakMarketParamsCallsInStmts body
              (some body', rewritten)
          | none => (none, 0)
        ([.switch expr cases' default'], caseRewriteCount + defaultRewriteCount)
    | .block stmts =>
        let (stmts', rewritten) := inlineKeccakMarketParamsCallsInStmts stmts
        ([.block stmts'], rewritten)
    | .funcDef name params rets body =>
        let (body', rewritten) := inlineKeccakMarketParamsCallsInStmts body
        ([.funcDef name params rets body'], rewritten)

private partial def inlineKeccakMarketParamsCallsInStmts
    (stmts : List YulStmt) : List YulStmt × Nat
  := match stmts with
    | [] => ([], 0)
    | stmt :: rest =>
        let (stmt', rewrittenHead) := inlineKeccakMarketParamsCallsInStmt stmt
        let (rest', rewrittenTail) := inlineKeccakMarketParamsCallsInStmts rest
        (stmt' ++ rest', rewrittenHead + rewrittenTail)

end

private def inlineRuntimeKeccakMarketParamsCalls (stmts : List YulStmt) : List YulStmt × Nat :=
  inlineKeccakMarketParamsCallsInStmts stmts

def solcCompatPruneUnreachableHelpersProofRef : String :=
  "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_prune_unreachable_helpers_preserves"

/-- Canonicalize Verity internal helper naming to `solc`-style `fun_*` names when collision-free. -/
def solcCompatCanonicalizeInternalFunNamesProofRef : String :=
  "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_canonicalize_internal_fun_names_preserves"

/-- Deduplicate top-level helper definitions that are structurally equivalent. -/
def solcCompatDedupeEquivalentHelpersProofRef : String :=
  "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_dedupe_equivalent_helpers_preserves"

/-- Inline dispatch wrapper case calls to top-level zero-arity `fun_*` helper definitions. -/
def solcCompatInlineDispatchWrapperCallsProofRef : String :=
  "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_inline_dispatch_wrapper_calls_preserves"

/-- Outline switch dispatch case bodies into explicit top-level `fun_*` helpers. -/
def solcCompatOutlineDispatchHelpersProofRef : String :=
  "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_outline_dispatch_helpers_preserves"

/-- Inline direct `keccakMarketParams(...)` helper calls into explicit memory writes + `keccak256`. -/
def solcCompatInlineKeccakMarketParamsCallsProofRef : String :=
  "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_inline_keccak_market_params_calls_preserves"

/-- Inline `mappingSlot(baseSlot, key)` helper calls into explicit scratch writes + `keccak256`. -/
def solcCompatInlineMappingSlotCallsProofRef : String :=
  "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_inline_mapping_slot_calls_preserves"

def solcCompatDropUnusedKeccakMarketParamsHelperProofRef : String :=
  "Compiler.Proofs.YulGeneration.PatchRulesProofs.solc_compat_drop_unused_keccak_market_params_helper_preserves"

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

private def dropUnusedTopLevelFunctionByName (stmts : List YulStmt) (name : String) : List YulStmt × Nat :=
  let (wrapped, topStmts) :=
    match stmts with
    | [.block inner] => (true, inner)
    | _ => (false, stmts)
  let (withoutTarget, removed) :=
    topStmts.foldr
      (fun stmt (accStmts, accRemoved) =>
        match stmt with
        | .funcDef defName params rets body =>
            if defName = name then
              (accStmts, accRemoved + 1)
            else
              (.funcDef defName params rets body :: accStmts, accRemoved)
        | _ => (stmt :: accStmts, accRemoved))
      ([], 0)
  if removed = 0 then
    (stmts, 0)
  else if (callNamesInStmts withoutTarget).any (fun called => called = name) then
    (stmts, 0)
  else if wrapped then
    ([.block withoutTarget], removed)
  else
    (withoutTarget, removed)

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

/-- Outline labeled runtime switch cases as explicit `fun_*` helper defs and dispatch via calls.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatOutlineDispatchHelpersRule : ObjectPatchRule :=
  { patchName := "solc-compat-outline-dispatch-helpers"
    pattern := "runtime switch case body prefixed with comment `<name>()`"
    rewrite := "insert top-level `fun_<name>` helper and replace case body with helper call"
    sideConditions :=
      [ "only runtime code is transformed"
      , "labels `fallback()` and `receive()` are excluded"
      , "existing `fun_*` names are collision-safe and never overwritten"
      , "outlined helper parameters/returns are empty (dispatch shape only)" ]
    proofId := solcCompatOutlineDispatchHelpersProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 215
    applyObject := fun _ obj =>
      let (runtimeCode', outlined) := outlineRuntimeDispatchHelpers obj.runtimeCode
      if outlined = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

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

/-- Inline runtime switch case bodies of the form `fun_X()` to the corresponding zero-arity helper body.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatInlineDispatchWrapperCallsRule : ObjectPatchRule :=
  { patchName := "solc-compat-inline-dispatch-wrapper-calls"
    pattern := "runtime switch case body with a single call to `fun_*`"
    rewrite := "replace case body with the referenced top-level zero-arity helper body"
    sideConditions :=
      [ "only runtime code is transformed"
      , "case body must be exactly one statement: `fun_*()` call"
      , "target helper must be a top-level zero-arity definition in the same object" ]
    proofId := solcCompatInlineDispatchWrapperCallsProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 212
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := inlineRuntimeDispatchWrapperCalls obj.runtimeCode
      if rewritten = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Inline runtime direct `keccakMarketParams(...)` helper calls to `mstore`/`keccak256` sequence.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatInlineKeccakMarketParamsCallsRule : ObjectPatchRule :=
  { patchName := "solc-compat-inline-keccak-market-params-calls"
    pattern := "let/assign using direct call `keccakMarketParams(a,b,c,d,e)`"
    rewrite := "replace with explicit memory writes at [0,32,64,96,128] then `keccak256(0,160)`"
    sideConditions :=
      [ "only runtime code is transformed"
      , "only direct `.let_`/`.assign` calls are rewritten"
      , "exactly five arguments are required"
      , "scratch memory clobbering follows existing helper semantics" ]
    proofId := solcCompatInlineKeccakMarketParamsCallsProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := inlineRuntimeKeccakMarketParamsCalls obj.runtimeCode
      if rewritten = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Inline runtime `mappingSlot(baseSlot, key)` helper calls into explicit `mstore`/`keccak256`.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatInlineMappingSlotCallsRule : ObjectPatchRule :=
  { patchName := "solc-compat-inline-mapping-slot-calls"
    pattern := "expression call `mappingSlot(baseSlot, key)`"
    rewrite := "introduce scratch writes to [512,544] and replace call with a fresh slot temporary"
    sideConditions :=
      [ "only runtime code is transformed"
      , "only calls with exactly two arguments are rewritten"
      , "loop-condition expressions are intentionally not rewritten"
      , "fresh temporary names use reserved prefix `__compat_mapping_slot_`"
      , "scratch memory clobbering follows existing `mappingSlot` helper semantics (base 512)" ]
    proofId := solcCompatInlineMappingSlotCallsProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 211
    applyObject := fun _ obj =>
      let (runtimeCode', rewritten) := inlineRuntimeMappingSlotCalls obj.runtimeCode
      if rewritten = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

/-- Drop top-level runtime `keccakMarketParams` helper when no call sites remain.
    This is enabled only in the opt-in `solc-compat` bundle. -/
def solcCompatDropUnusedKeccakMarketParamsHelperRule : ObjectPatchRule :=
  { patchName := "solc-compat-drop-unused-keccak-market-params-helper"
    pattern := "top-level helper definition `keccakMarketParams` with no remaining call sites"
    rewrite := "remove helper definition"
    sideConditions :=
      [ "only runtime code is transformed"
      , "only top-level definitions named `keccakMarketParams` are considered"
      , "helper is removed only when no call site remains in runtime code" ]
    proofId := solcCompatDropUnusedKeccakMarketParamsHelperProofRef
    scope := .object
    passPhase := .postCodegen
    priority := 210
    applyObject := fun _ obj =>
      let (runtimeCode', removed) := dropUnusedTopLevelFunctionByName obj.runtimeCode "keccakMarketParams"
      if removed = 0 then
        none
      else
        some { obj with runtimeCode := runtimeCode' } }

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
      , solcCompatInlineDispatchWrapperCallsRule
      , solcCompatInlineMappingSlotCallsRule
      , solcCompatInlineKeccakMarketParamsCallsRule
      , solcCompatDropUnusedKeccakMarketParamsHelperRule
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

/-- Smoke test: `solc-compat` bundle contains dispatch-wrapper inlining proof refs. -/
example :
    solcCompatProofAllowlist.any
      (fun proofRef => proofRef = solcCompatInlineDispatchWrapperCallsProofRef) = true := by
  native_decide

/-- Smoke test: `solc-compat` bundle contains keccak-market-params inlining proof refs. -/
example :
    solcCompatProofAllowlist.any
      (fun proofRef => proofRef = solcCompatInlineKeccakMarketParamsCallsProofRef) = true := by
  native_decide

/-- Smoke test: `solc-compat` bundle contains mapping-slot inlining proof refs. -/
example :
    solcCompatProofAllowlist.any
      (fun proofRef => proofRef = solcCompatInlineMappingSlotCallsProofRef) = true := by
  native_decide

/-- Smoke test: `solc-compat` bundle contains drop-unused-keccak-helper proof refs. -/
example :
    solcCompatProofAllowlist.any
      (fun proofRef => proofRef = solcCompatDropUnusedKeccakMarketParamsHelperProofRef) = true := by
  native_decide

/-- Smoke test: `solc-compat` bundle contains dispatch helper outlining proof refs. -/
example :
    solcCompatProofAllowlist.any
      (fun proofRef => proofRef = solcCompatOutlineDispatchHelpersProofRef) = false := by
  native_decide

/-- Smoke test: dispatch cases are outlined into top-level `fun_*` helper defs. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode :=
          [ .funcDef "existing" [] [] [.leave]
          , .block
              [ .let_ "__has_selector" (.lit 1)
              , .if_ (.ident "__has_selector")
                  [ .switch (.ident "__selector")
                      [(1, [.comment "accrueInterest()", .leave])]
                      (some [.comment "fallback()", .leave])
                  ]
              ]
          ] }
    let report := runPatchPassWithObjects
      { enabled := true
        maxIterations := 2
        rewriteBundleId := solcCompatRewriteBundleId
        requiredProofRefs := solcCompatProofAllowlist ++ [solcCompatOutlineDispatchHelpersProofRef] }
      []
      []
      []
      [solcCompatOutlineDispatchHelpersRule]
      input
    (match report.patched.runtimeCode, report.manifest.map (fun m => m.patchName) with
    | [ .funcDef "existing" [] [] [.leave]
      , .funcDef "fun_accrueInterest" [] [] [.leave]
      , .block
          [ .let_ "__has_selector" (.lit 1)
          , .if_ (.ident "__has_selector")
              [ .switch (.ident "__selector")
                  [(1, [.expr (.call "fun_accrueInterest" [])])]
                  (some [.comment "fallback()", .leave])
              ]
          ]
      ],
      ["solc-compat-outline-dispatch-helpers"] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: dispatch helper outlining is collision-safe when helper already exists. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode :=
          [ .funcDef "fun_accrueInterest" [] [] [.leave]
          , .block
              [ .if_ (.lit 1)
                  [ .switch (.ident "__selector")
                      [(1, [.comment "accrueInterest()", .leave])]
                      none
                  ]
              ]
          ] }
    let report := runPatchPassWithObjects
      { enabled := true
        maxIterations := 2
        rewriteBundleId := solcCompatRewriteBundleId
        requiredProofRefs := solcCompatProofAllowlist ++ [solcCompatOutlineDispatchHelpersProofRef] }
      []
      []
      []
      [solcCompatOutlineDispatchHelpersRule]
      input
    (match report.patched.runtimeCode, report.manifest with
    | [ .funcDef "fun_accrueInterest" [] [] [.leave]
      , .block
          [ .if_ (.lit 1)
              [ .switch (.ident "__selector")
                  [(1, [.comment "accrueInterest()", .leave])]
                  none
              ]
          ]
      ], [] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: dispatch wrapper calls are inlined and wrapper helper becomes pruneable. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode :=
          [ .funcDef "fun_ping" [] [] [.leave]
          , .block
              [ .if_ (.lit 1)
                  [ .switch (.ident "__selector")
                      [(1, [.expr (.call "fun_ping" [])])]
                      none
                  ]
              ]
          ] }
    let report := runPatchPassWithObjects
      { enabled := true
        maxIterations := 1
        rewriteBundleId := solcCompatRewriteBundleId
        requiredProofRefs := solcCompatProofAllowlist }
      []
      []
      []
      [solcCompatInlineDispatchWrapperCallsRule, solcCompatPruneUnreachableHelpersRule]
      input
    (match report.patched.runtimeCode, report.manifest.map (fun m => m.patchName) with
    | [ .block
          [ .if_ (.lit 1)
              [ .switch (.ident "__selector")
                  [(1, [.leave])]
                  none
              ]
          ]
      ],
      ["solc-compat-inline-dispatch-wrapper-calls", "solc-compat-prune-unreachable-helpers"] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: dispatch wrapper inlining skips non-zero-arity helpers. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode :=
          [ .funcDef "fun_ping" ["arg0"] [] [.leave]
          , .block
              [ .if_ (.lit 1)
                  [ .switch (.ident "__selector")
                      [(1, [.expr (.call "fun_ping" [])])]
                      none
                  ]
              ]
          ] }
    let report := runPatchPassWithObjects
      { enabled := true
        maxIterations := 2
        rewriteBundleId := solcCompatRewriteBundleId
        requiredProofRefs := solcCompatProofAllowlist }
      []
      []
      []
      [solcCompatInlineDispatchWrapperCallsRule]
      input
    (match report.patched.runtimeCode, report.manifest with
    | [ .funcDef "fun_ping" ["arg0"] [] [.leave]
      , .block
          [ .if_ (.lit 1)
              [ .switch (.ident "__selector")
                  [(1, [.expr (.call "fun_ping" [])])]
                  none
              ]
          ]
      ], [] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: direct `keccakMarketParams(...)` calls are inlined and helper becomes pruneable. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode :=
          [ .funcDef "keccakMarketParams"
              ["loanToken", "collateralToken", "oracle", "irm", "lltv"]
              ["id"]
              [ .expr (.call "mstore" [.lit 0, .ident "loanToken"])
              , .expr (.call "mstore" [.lit 32, .ident "collateralToken"])
              , .expr (.call "mstore" [.lit 64, .ident "oracle"])
              , .expr (.call "mstore" [.lit 96, .ident "irm"])
              , .expr (.call "mstore" [.lit 128, .ident "lltv"])
              , .assign "id" (.call "keccak256" [.lit 0, .lit 160])
              ]
          , .block
              [ .let_ "id0"
                  (.call "keccakMarketParams"
                    [.ident "loanToken", .ident "collateralToken", .ident "oracle", .ident "irm", .ident "lltv"])
              ]
          ] }
    let report := runPatchPassWithObjects
      { enabled := true
        maxIterations := 1
        rewriteBundleId := solcCompatRewriteBundleId
        requiredProofRefs := solcCompatProofAllowlist }
      []
      []
      []
      [solcCompatInlineKeccakMarketParamsCallsRule, solcCompatPruneUnreachableHelpersRule]
      input
    (match report.patched.runtimeCode, report.manifest.map (fun m => m.patchName) with
    | [ .block
          [ .expr (.call "mstore" [.lit 0, .ident "loanToken"])
          , .expr (.call "mstore" [.lit 32, .ident "collateralToken"])
          , .expr (.call "mstore" [.lit 64, .ident "oracle"])
          , .expr (.call "mstore" [.lit 96, .ident "irm"])
          , .expr (.call "mstore" [.lit 128, .ident "lltv"])
          , .let_ "id0" (.call "keccak256" [.lit 0, .lit 160])
          ]
      ],
      ["solc-compat-inline-keccak-market-params-calls", "solc-compat-prune-unreachable-helpers"] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: nested `mappingSlot(...)` calls are inlined and helper becomes pruneable. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode :=
          [ .funcDef "mappingSlot" ["baseSlot", "key"] ["slot"]
              [ .expr (.call "mstore" [.lit 512, .ident "key"])
              , .expr (.call "mstore" [.lit 544, .ident "baseSlot"])
              , .assign "slot" (.call "keccak256" [.lit 512, .lit 64])
              ]
          , .block
              [ .let_ "value"
                  (.call "sload"
                    [ .call "add"
                        [ .call "mappingSlot"
                            [ .lit 3
                            , .call "mappingSlot" [.lit 2, .ident "id"]
                            ]
                        , .lit 1
                        ]
                    ])
              ]
          ] }
    let report := runPatchPassWithObjects
      { enabled := true
        maxIterations := 1
        rewriteBundleId := solcCompatRewriteBundleId
        requiredProofRefs := solcCompatProofAllowlist }
      []
      []
      []
      [solcCompatInlineMappingSlotCallsRule, solcCompatPruneUnreachableHelpersRule]
      input
    (match report.patched.runtimeCode, report.manifest.map (fun m => m.patchName) with
    | [ .block
          [ .expr (.call "mstore" [.lit 512, .ident "id"])
          , .expr (.call "mstore" [.lit 544, .lit 2])
          , .let_ "__compat_mapping_slot_0" (.call "keccak256" [.lit 512, .lit 64])
          , .expr (.call "mstore" [.lit 512, .ident "__compat_mapping_slot_0"])
          , .expr (.call "mstore" [.lit 544, .lit 3])
          , .let_ "__compat_mapping_slot_1" (.call "keccak256" [.lit 512, .lit 64])
          , .let_ "value" (.call "sload" [.call "add" [.ident "__compat_mapping_slot_1", .lit 1]])
          ]
      ],
      ["solc-compat-inline-mapping-slot-calls", "solc-compat-prune-unreachable-helpers"] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: unused top-level `keccakMarketParams` helper is dropped. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode :=
          [ .funcDef "keccakMarketParams"
              ["loanToken", "collateralToken", "oracle", "irm", "lltv"]
              ["id"]
              [ .assign "id" (.call "keccak256" [.lit 0, .lit 160]) ]
          , .funcDef "fun_accrueInterest" ["id"] [] [.leave]
          , .block [ .expr (.call "fun_accrueInterest" [.lit 1]) ]
          ] }
    let report := runPatchPassWithObjects
      { enabled := true
        maxIterations := 1
        rewriteBundleId := solcCompatRewriteBundleId
        requiredProofRefs := solcCompatProofAllowlist }
      []
      []
      []
      [solcCompatDropUnusedKeccakMarketParamsHelperRule]
      input
    (match report.patched.runtimeCode, report.manifest.map (fun m => m.patchName) with
    | [ .funcDef "fun_accrueInterest" ["id"] [] [.leave]
      , .block [ .expr (.call "fun_accrueInterest" [.lit 1]) ]
      ],
      ["solc-compat-drop-unused-keccak-market-params-helper"] => true
    | _, _ => false) = true := by
  native_decide

/-- Smoke test: `keccakMarketParams` helper is kept when call sites remain. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode :=
          [ .funcDef "keccakMarketParams"
              ["loanToken", "collateralToken", "oracle", "irm", "lltv"]
              ["id"]
              [ .assign "id" (.call "keccak256" [.lit 0, .lit 160]) ]
          , .funcDef "fun_accrueInterest" ["id"] []
              [ .let_ "slot" (.call "keccakMarketParams"
                  [.ident "loanToken", .ident "collateralToken", .ident "oracle", .ident "irm", .ident "lltv"])
              ]
          , .block [ .expr (.call "fun_accrueInterest" [.lit 1]) ]
          ] }
    let report := runPatchPassWithObjects
      { enabled := true
        maxIterations := 1
        rewriteBundleId := solcCompatRewriteBundleId
        requiredProofRefs := solcCompatProofAllowlist }
      []
      []
      []
      [solcCompatDropUnusedKeccakMarketParamsHelperRule]
      input
    (match report.patched.runtimeCode, report.manifest with
    | [ .funcDef "keccakMarketParams"
          ["loanToken", "collateralToken", "oracle", "irm", "lltv"]
          ["id"]
          [ .assign "id" (.call "keccak256" [.lit 0, .lit 160]) ]
      , .funcDef "fun_accrueInterest" ["id"] []
          [ .let_ "slot" (.call "keccakMarketParams"
              [.ident "loanToken", .ident "collateralToken", .ident "oracle", .ident "irm", .ident "lltv"])
          ]
      , .block [ .expr (.call "fun_accrueInterest" [.lit 1]) ]
      ], [] => true
    | _, _ => false) = true := by
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

/-- Smoke test: prune handles single top-level block wrappers and ignores nested func-def calls in seed. -/
example :
    let input : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode :=
          [ .block
            [ .funcDef "helperB" [] [] [.leave]
            , .funcDef "helperA" [] [] [.expr (.call "helperB" [])]
            , .funcDef "dead" [] [] [.leave]
            , .switch (.call "shr" [.lit 224, .call "calldataload" [.lit 0]])
                [(0, [.expr (.call "helperA" [])])]
                (some [.expr (.call "revert" [.lit 0, .lit 0])])
            ]
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
    (match report.patched.runtimeCode, report.manifest.map (fun m => m.patchName) with
    | [ .block
        [ .funcDef "helperB" [] [] [.leave]
        , .funcDef "helperA" [] [] [.expr (.call "helperB" [])]
        , .switch (.call "shr" [.lit 224, .call "calldataload" [.lit 0]])
            [(0, [.expr (.call "helperA" [])])]
            (some [.expr (.call "revert" [.lit 0, .lit 0])])
        ] ],
      ["solc-compat-prune-unreachable-helpers"] => true
    | _, _ => false) = true := by
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
