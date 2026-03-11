import Compiler.CompilationModel.Compile
import Compiler.Proofs.IRGeneration.FunctionBody

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-- Scope seen by the tail after compiling a single statement. This matches the
statement-list compiler's `collectStmtNames` update. -/
def stmtNextScope (scope : List String) (stmt : Stmt) : List String :=
  collectStmtNames stmt ++ scope

/-- Single-step result relation used by the generic statement induction library.
Unlike `stmtResultMatchesIRExecExact`, this tracks the tail scope instead of
requiring exact bindings for every name in the runtime map. -/
def stmtStepMatchesIRExec
    (fields : List Field)
    (nextScope : List String) :
    SourceSemantics.StmtResult → IRExecResult → Prop
  | .continue runtime, .continue state =>
      FunctionBody.runtimeStateMatchesIR fields runtime state ∧
      FunctionBody.bindingsExactlyMatchIRVarsOnScope nextScope runtime.bindings state ∧
      FunctionBody.bindingsBounded runtime.bindings ∧
      FunctionBody.scopeNamesPresent nextScope runtime.bindings
  | .stop runtime, .stop state =>
      FunctionBody.runtimeStateMatchesIR fields runtime state
  | .return value runtime, .return value' state =>
      value = value' ∧
      FunctionBody.runtimeStateMatchesIR fields runtime state
  | .revert, .revert _ => True
  | _, _ => False

/-- A compiled statement head that preserves the exact-state invariant needed to
continue generic statement-list induction on the remaining tail. -/
structure CompiledStmtStep
    (fields : List Field)
    (scope : List String)
    (stmt : Stmt)
    (compiledIR : List YulStmt) : Prop where
  compileOk :
    CompilationModel.compileStmt fields [] [] .calldata [] false scope stmt =
      Except.ok compiledIR
  preserves :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf compiledIR - compiledIR.length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime stmt = sourceResult ∧
        execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR = irExec ∧
        stmtStepMatchesIRExec fields (stmtNextScope scope stmt) sourceResult irExec

/-- Statement lists whose heads all admit a generic compiled-step proof. -/
inductive StmtListGenericCore (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListGenericCore fields scope []
  | cons {scope : List String} {stmt : Stmt} {compiledIR : List YulStmt} {rest : List Stmt} :
      CompiledStmtStep fields scope stmt compiledIR →
      StmtListGenericCore fields (stmtNextScope scope stmt) rest →
      StmtListGenericCore fields scope (stmt :: rest)

theorem compiledStmtStep_letVar
    {fields : List Field}
    {scope : List String}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.letVar name value) [YulStmt.let_ name valueIR] where
  compileOk := by
    simp [CompilationModel.compileStmt, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let slack := sizeOf [YulStmt.let_ name valueIR] - [YulStmt.let_ name valueIR].length
    let wholeExtraFuel := extraFuel - slack
    have hwholeFuel :
        sizeOf [YulStmt.let_ name valueIR] + wholeExtraFuel + 1 =
          [YulStmt.let_ name valueIR].length + extraFuel + 1 := by
      dsimp [wholeExtraFuel, slack]
      have : slack ≤ extraFuel := by
        simpa [slack] using hslack
      omega
    rcases FunctionBody.execIRStmts_compiled_let_core_append_wholeFuel_of_scope
        (fields := fields)
        (runtime := runtime)
        (state := state)
        (scope := scope)
        (name := name)
        (value := value)
        (tailIR := [])
        (extraFuel := wholeExtraFuel)
        hcore hexact hinScope hscope hbounded hruntime with
      ⟨valueIR', hvalueIR', hwhole, hruntime', hexact', hbounded', hscope'⟩
    rw [hvalueIR] at hvalueIR'
    injection hvalueIR' with hEq
    subst hEq
    refine ⟨_, _, ?_⟩
    · simp [SourceSemantics.execStmt]
    · simpa [hwholeFuel] using hwhole
    · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using
        And.intro hruntime' <| And.intro hexact' <| And.intro hbounded' hscope'

theorem compiledStmtStep_assignVar
    {fields : List Field}
    {scope : List String}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.assignVar name value) [YulStmt.assign name valueIR] where
  compileOk := by
    simp [CompilationModel.compileStmt, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let slack := sizeOf [YulStmt.assign name valueIR] - [YulStmt.assign name valueIR].length
    let wholeExtraFuel := extraFuel - slack
    have hwholeFuel :
        sizeOf [YulStmt.assign name valueIR] + wholeExtraFuel + 1 =
          [YulStmt.assign name valueIR].length + extraFuel + 1 := by
      dsimp [wholeExtraFuel, slack]
      have : slack ≤ extraFuel := by
        simpa [slack] using hslack
      omega
    rcases FunctionBody.execIRStmts_compiled_assign_core_append_wholeFuel_of_scope
        (fields := fields)
        (runtime := runtime)
        (state := state)
        (scope := scope)
        (name := name)
        (value := value)
        (tailIR := [])
        (extraFuel := wholeExtraFuel)
        hcore hexact hinScope hscope hbounded hruntime with
      ⟨valueIR', hvalueIR', hwhole, hruntime', hexact', hbounded', hscope'⟩
    rw [hvalueIR] at hvalueIR'
    injection hvalueIR' with hEq
    subst hEq
    refine ⟨_, _, ?_⟩
    · simp [SourceSemantics.execStmt]
    · simpa [hwholeFuel] using hwhole
    · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using
        And.intro hruntime' <| And.intro hexact' <| And.intro hbounded' hscope'

theorem compiledStmtStep_require
    {fields : List Field}
    {scope : List String}
    {cond : Expr}
    {message : String}
    {failCond : YulExpr}
    (hcore : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hfailCompile : CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond) :
    CompiledStmtStep fields scope (.require cond message)
      [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] where
  compileOk := by
    simp [CompilationModel.compileStmt, hfailCompile]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let slack :=
      sizeOf [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] -
        [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)].length
    let wholeExtraFuel := extraFuel - slack
    have hwholeFuel :
        sizeOf [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] + wholeExtraFuel + 1 =
          [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)].length + extraFuel + 1 := by
      dsimp [wholeExtraFuel, slack]
      have : slack ≤ extraFuel := by
        simpa [slack] using hslack
      omega
    by_cases hcondZero : SourceSemantics.evalExpr fields runtime cond = 0
    · rcases FunctionBody.execIRStmts_compiled_require_core_fail_append_wholeFuel_of_scope
          (fields := fields)
          (runtime := runtime)
          (state := state)
          (scope := scope)
          (cond := cond)
          (message := message)
          (tailIR := [])
          (extraFuel := wholeExtraFuel)
          hcore hexact hinScope hscope hbounded hruntime hcondZero with
        ⟨failCond', revState, hfailCompile', hwhole⟩
      rw [hfailCompile] at hfailCompile'
      injection hfailCompile' with hEq
      subst hEq
      refine ⟨_, _, ?_⟩
      · simp [SourceSemantics.execStmt, hcondZero]
      · simpa [hwholeFuel] using hwhole
      · simp [stmtStepMatchesIRExec]
    · have hcondNeZero : SourceSemantics.evalExpr fields runtime cond ≠ 0 := hcondZero
      have hwhole :=
        FunctionBody.execIRStmts_compiled_require_core_pass_append_wholeFuel_of_scope
          (fields := fields)
          (runtime := runtime)
          (state := state)
          (scope := scope)
          (cond := cond)
          (message := message)
          (tailIR := [])
          (extraFuel := wholeExtraFuel)
          hcore hexact hinScope hscope hbounded hruntime hcondNeZero
      refine ⟨_, _, ?_⟩
      · simp [SourceSemantics.execStmt, hcondNeZero]
      · simpa [hwholeFuel] using hwhole
      · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using
          And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope

theorem compiledStmtStep_return
    {fields : List Field}
    {scope : List String}
    {value : Expr}
    {valueIR : YulExpr}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.return value)
      [ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
      , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] where
  compileOk := by
    simp [CompilationModel.compileStmt, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let compiledIR :=
      [ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
      , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ]
    let slack := sizeOf compiledIR - compiledIR.length
    let wholeExtraFuel := extraFuel - slack
    have hwholeFuel :
        sizeOf compiledIR + wholeExtraFuel + 1 =
          compiledIR.length + extraFuel + 1 := by
      dsimp [wholeExtraFuel, slack, compiledIR]
      have : slack ≤ extraFuel := by
        simpa [slack, compiledIR] using hslack
      omega
    rcases FunctionBody.execIRStmts_compiled_return_core_append_wholeFuel_of_scope
        (fields := fields)
        (runtime := runtime)
        (state := state)
        (scope := scope)
        (value := value)
        (tailIR := [])
        (extraFuel := wholeExtraFuel)
        hcore hexact hinScope hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
        hruntime with
      ⟨valueIR', hvalueIR', hwhole⟩
    rw [hvalueIR] at hvalueIR'
    injection hvalueIR' with hEq
    subst hEq
    let retVal := SourceSemantics.evalExpr fields runtime value
    let retState := { state with memory := fun o => if o = 0 then retVal else state.memory o }
    refine ⟨_, _, ?_⟩
    · simp [SourceSemantics.execStmt]
    · simpa [hwholeFuel, compiledIR, retVal, retState] using hwhole
    · refine ⟨rfl, ?_⟩
      exact FunctionBody.runtimeStateMatchesIR_setMemory hruntime 0 retVal

theorem compiledStmtStep_stop
    {fields : List Field}
    {scope : List String} :
    CompiledStmtStep fields scope .stop [YulStmt.expr (YulExpr.call "stop" [])] where
  compileOk := by
    simp [CompilationModel.compileStmt]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let compiledIR := [YulStmt.expr (YulExpr.call "stop" [])]
    let slack := sizeOf compiledIR - compiledIR.length
    let wholeExtraFuel := extraFuel - slack
    have hwholeFuel :
        sizeOf compiledIR + wholeExtraFuel + 1 =
          compiledIR.length + extraFuel + 1 := by
      dsimp [wholeExtraFuel, slack, compiledIR]
      have : slack ≤ extraFuel := by
        simpa [slack, compiledIR] using hslack
      omega
    refine ⟨_, _, ?_⟩
    · simp [SourceSemantics.execStmt]
    · simpa [compiledIR, hwholeFuel] using
        (FunctionBody.execIRStmts_compiled_stop_core_append_wholeFuel
          (state := state) (tailIR := []) (extraFuel := wholeExtraFuel))
    · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using hruntime

private theorem encodeStorageAt_writeUintSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot query value : Nat}
    (hneq : query ≠ slot) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintSlots world [slot] value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  simp [SourceSemantics.encodeStorageAt, SourceSemantics.writeUintSlots, hneq]

private theorem encodeStorageAt_writeUintSlots_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slots : List Nat}
    {query value : Nat}
    (hnotMem : query ∉ slots) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintSlots world slots value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  simp [SourceSemantics.encodeStorageAt, SourceSemantics.writeUintSlots,
    List.contains_eq_false.mpr hnotMem]

private def findResolvedFieldAtSlotCopy (fields : List Field) (slot : Nat) : Option Field :=
  let rec go (remaining : List Field) (idx : Nat) : Option Field :=
    match remaining with
    | [] => none
    | field :: rest =>
        let resolvedSlot := field.slot.getD idx
        if resolvedSlot = slot || field.aliasSlots.contains slot then
          some field
        else
          go rest (idx + 1)
  go fields 0

private def findFieldWithResolvedSlotCopyFrom
    (fields : List Field) (idx : Nat) (name : String) : Option (Field × Nat) :=
  match fields with
  | [] => none
  | field :: rest =>
      if field.name == name then
        some (field, field.slot.getD idx)
      else
        findFieldWithResolvedSlotCopyFrom rest (idx + 1) name

private def findFieldWriteSlotsCopyFrom
    (fields : List Field) (idx : Nat) (name : String) : Option (List Nat) :=
  match fields with
  | [] => none
  | field :: rest =>
      if field.name == name then
        some (field.slot.getD idx :: field.aliasSlots)
      else
        findFieldWriteSlotsCopyFrom rest (idx + 1) name

private def findResolvedFieldAtSlotCopyFrom
    (fields : List Field) (idx : Nat) (slot : Nat) : Option Field :=
  match fields with
  | [] => none
  | field :: rest =>
      let resolvedSlot := field.slot.getD idx
      if resolvedSlot = slot || field.aliasSlots.contains slot then
        some field
      else
        findResolvedFieldAtSlotCopyFrom rest (idx + 1) slot

private def fieldWriteEntriesAt
    (idx : Nat) (field : Field) : List (Nat × String × Option PackedBits) :=
  (field.slot.getD idx, field.name, field.packedBits) ::
    (field.aliasSlots.zipIdx.map (fun (slot, aliasIdx) =>
      (slot, s!"{field.name}.aliasSlots[{aliasIdx}]", field.packedBits)))

private def firstInFieldConflictCopy
    (seen : List (Nat × String × Option PackedBits))
    (current : List (Nat × String × Option PackedBits)) :
    Option (Nat × String × String) :=
  match current with
  | [] => none
  | (slot, ownerName, packed) :: tail =>
      match seen.find? (fun entry => entry.1 == slot && packedSlotsConflict entry.2.2 packed) with
      | some (_, prevName, _) => some (slot, prevName, ownerName)
      | none => firstInFieldConflictCopy ((slot, ownerName, packed) :: seen) tail

private def firstFieldWriteSlotConflictCopyFrom
    (seen : List (Nat × String × Option PackedBits))
    (idx : Nat) (fields : List Field) : Option (Nat × String × String) :=
  match fields with
  | [] => none
  | field :: rest =>
      let writeSlots := fieldWriteEntriesAt idx field
      match firstInFieldConflictCopy seen writeSlots with
      | some conflict => some conflict
      | none => firstFieldWriteSlotConflictCopyFrom (writeSlots.reverse ++ seen) (idx + 1) rest

private theorem list_findSlotPackedNone_ne_none
    {seen : List (Nat × String × Option PackedBits)}
    {slot : Nat}
    (hmem : slot ∈ seen.map (fun entry => entry.1)) :
    (seen.find? (fun entry => entry.1 == slot && packedSlotsConflict entry.2.2 none)) ≠ none := by
  induction seen with
  | nil =>
      cases hmem
  | cons entry rest ih =>
      simp at hmem ⊢
      by_cases hEq : entry.1 = slot
      · subst hEq
        simp [packedSlotsConflict]
      · simp [hEq, ih hmem]

private theorem firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_singleton
    {seen : List (Nat × String × Option PackedBits)}
    {fields : List Field}
    {idx : Nat}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hseen : slot ∈ seen.map (fun entry => entry.1))
    (hfind :
      findFieldWithResolvedSlotCopyFrom fields idx fieldName = some (f, slot))
    (hwrite :
      findFieldWriteSlotsCopyFrom fields idx fieldName = some [slot])
    (hunpacked : f.packedBits = none) :
    firstFieldWriteSlotConflictCopyFrom seen idx fields ≠ none := by
  induction fields generalizing seen idx with
  | nil =>
      cases hfind
  | cons field rest ih =>
      by_cases hname : field.name == fieldName
      · simp [findFieldWithResolvedSlotCopyFrom, findFieldWriteSlotsCopyFrom, hname] at hfind hwrite
        injection hfind with hf hslot
        subst hf
        subst hslot
        have hfindSeen :
            (seen.find? (fun entry => entry.1 == field.slot.getD idx &&
              packedSlotsConflict entry.2.2 none)) ≠ none :=
          list_findSlotPackedNone_ne_none hseen
        intro hnone
        simp [firstFieldWriteSlotConflictCopyFrom, firstInFieldConflictCopy,
          fieldWriteEntriesAt, hunpacked, hfindSeen] at hnone
      · simp [findFieldWithResolvedSlotCopyFrom, findFieldWriteSlotsCopyFrom, hname] at hfind hwrite
        intro hnone
        cases hfirst : firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field)
        · have htailNone :
              firstFieldWriteSlotConflictCopyFrom
                ((fieldWriteEntriesAt idx field).reverse ++ seen)
                (idx + 1)
                rest = none := by
            simpa [firstFieldWriteSlotConflictCopyFrom, hfirst] using hnone
          have hseen' :
              slot ∈
                (((fieldWriteEntriesAt idx field).reverse ++ seen).map
                  (fun entry => entry.1)) := by
            simp [hseen]
          exact (ih hseen' hfind hwrite hunpacked) htailNone
        · simp [firstFieldWriteSlotConflictCopyFrom, hfirst] at hnone

private theorem findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hwrite : findFieldWriteSlots fields fieldName = some [slot])
    (hunpacked : f.packedBits = none) :
    findResolvedFieldAtSlotCopy fields slot = some f := by
  have hnoConflictCopy :
      firstFieldWriteSlotConflictCopyFrom [] 0 fields = none := by
    simpa [firstFieldWriteSlotConflict, firstFieldWriteSlotConflictCopyFrom,
      fieldWriteEntriesAt, firstInFieldConflictCopy] using hnoConflict
  have hfindCopy :
      findFieldWithResolvedSlotCopyFrom fields 0 fieldName = some (f, slot) := by
    simpa [findFieldWithResolvedSlot, findFieldWithResolvedSlotCopyFrom] using hfind
  have hwriteCopy :
      findFieldWriteSlotsCopyFrom fields 0 fieldName = some [slot] := by
    simpa [findFieldWriteSlots, findFieldWriteSlotsCopyFrom] using hwrite
  have hresolved :
      findResolvedFieldAtSlotCopyFrom fields 0 slot = some f := by
    induction fields generalizing slot with
    | nil =>
        cases hfindCopy
    | cons field rest ih =>
        by_cases hname : field.name == fieldName
        · simp [findFieldWithResolvedSlotCopyFrom, findFieldWriteSlotsCopyFrom, hname] at
            hfindCopy hwriteCopy
          injection hfindCopy with hf hslot
          subst hf
          subst hslot
          simp [findResolvedFieldAtSlotCopyFrom]
        · simp [findFieldWithResolvedSlotCopyFrom, findFieldWriteSlotsCopyFrom, hname] at
            hfindCopy hwriteCopy
          cases hfirst : firstInFieldConflictCopy [] (fieldWriteEntriesAt 0 field)
          · have htailNoConflict :
                firstFieldWriteSlotConflictCopyFrom
                  (fieldWriteEntriesAt 0 field).reverse
                  1
                  rest = none := by
              simpa [firstFieldWriteSlotConflictCopyFrom, hfirst] using hnoConflictCopy
            have hheadNotOwn :
                slot ∉ (fieldWriteEntriesAt 0 field).map (fun entry => entry.1) := by
              intro hmem
              have hmemRev :
                  slot ∈ ((fieldWriteEntriesAt 0 field).reverse.map (fun entry => entry.1)) := by
                simpa [List.map_reverse] using (List.mem_reverse.mpr hmem)
              exact
                (firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_singleton
                  hmemRev hfindCopy hwriteCopy hunpacked) htailNoConflict
            have hresolvedNe : field.slot.getD 0 ≠ slot := by
              have hheadNotOwn' := hheadNotOwn
              simp [fieldWriteEntriesAt] at hheadNotOwn'
              exact hheadNotOwn'.1
            have haliasNotMem : slot ∉ field.aliasSlots := by
              have hheadNotOwn' := hheadNotOwn
              simp [fieldWriteEntriesAt] at hheadNotOwn'
              exact hheadNotOwn'.2
            have haliasNe : field.aliasSlots.contains slot = false :=
              List.contains_eq_false.mpr haliasNotMem
            simpa [findResolvedFieldAtSlotCopyFrom, hresolvedNe, haliasNe] using
              ih (slot := slot) htailNoConflict hfindCopy hwriteCopy hunpacked
          · simp [firstFieldWriteSlotConflictCopyFrom, hfirst] at hnoConflictCopy
  simpa [findResolvedFieldAtSlotCopy, findResolvedFieldAtSlotCopyFrom] using hresolved

private def findDynamicArrayElementAtSlotCopy
    (fields : List Field) (world : Verity.ContractState) (targetSlot : Nat) : Option Nat :=
  let rec scanElements (baseSlot : Nat) : List Verity.Core.Uint256 → Nat → Option Nat
    | [], _ => none
    | value :: rest, idx =>
        if Compiler.Proofs.solidityMappingSlot baseSlot idx = targetSlot then
          some value.val
        else
          scanElements baseSlot rest (idx + 1)
  let rec go (remaining : List Field) (idx : Nat) : Option Nat :=
    match remaining with
    | [] => none
    | field :: rest =>
        let resolvedSlot := field.slot.getD idx
        match field.ty with
        | .dynamicArray _ =>
            match scanElements resolvedSlot (world.storageArray resolvedSlot) 0 with
            | some value => some value
            | none => go rest (idx + 1)
        | _ => go rest (idx + 1)
  go fields 0

private def encodeStorageAtCopy
    (fields : List Field) (world : Verity.ContractState) (slot : Nat) : Nat :=
  match findResolvedFieldAtSlotCopy fields slot with
  | some field =>
      if SourceSemantics.fieldUsesAddressStorage field then
        (world.storageAddr slot).val
      else if SourceSemantics.fieldUsesDynamicArrayStorage field then
        (world.storageArray slot).length
      else
        (world.storage slot).val
  | none =>
      match findDynamicArrayElementAtSlotCopy fields world slot with
      | some value => value
      | none => (world.storage slot).val

private theorem encodeStorageAt_eq_copy
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat} :
    SourceSemantics.encodeStorageAt fields world slot =
      encodeStorageAtCopy fields world slot := by
  simp [SourceSemantics.encodeStorageAt, encodeStorageAtCopy,
    findResolvedFieldAtSlotCopy, findDynamicArrayElementAtSlotCopy]

private theorem encodeStorageAt_eq_storage_of_resolvedSlot
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    SourceSemantics.encodeStorageAt fields world slot = (world.storage slot).val := by
  rw [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, hnotAddr, hnotDyn]

private def abstractStoreStorageOrMappingMany
    (storage : Nat → Nat) (slots : List Nat) (value : Nat) : Nat → Nat :=
  match slots with
  | [] => storage
  | slot :: rest =>
      abstractStoreStorageOrMappingMany
        (Compiler.Proofs.abstractStoreStorageOrMapping storage slot value)
        rest
        value

private theorem abstractStoreStorageOrMappingMany_eq
    {storage : Nat → Nat}
    {slots : List Nat}
    {value query : Nat} :
    abstractStoreStorageOrMappingMany storage slots value query =
      if slots.contains query then value else storage query := by
  induction slots generalizing storage with
  | nil =>
      simp [abstractStoreStorageOrMappingMany]
  | cons slot rest ih =>
      by_cases hEq : query = slot
      · subst hEq
        simp [abstractStoreStorageOrMappingMany, Compiler.Proofs.abstractStoreStorageOrMapping_eq]
      · simp [abstractStoreStorageOrMappingMany, ih,
          Compiler.Proofs.abstractStoreStorageOrMapping_eq, hEq]

private theorem runtimeStateMatchesIR_writeUintSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeUintSlots runtime.world [slot] value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value } := by
  rcases hruntime with
    ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hEq : query = slot
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hstorage,
      encodeStorageAt_eq_storage_of_resolvedSlot hresolved hnotAddr hnotDyn]
    simp [SourceSemantics.writeUintSlots]
  · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hstorage]
    simp [hEq, encodeStorageAt_writeUintSlots_singleton_other]

private theorem runtimeStateMatchesIR_writeUintSlots
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slots : List Nat}
    {value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    {f : Field}
    (hresolved : ∀ slot ∈ slots, findResolvedFieldAtSlotCopy fields slot = some f)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeUintSlots runtime.world slots value }
      { state with
          storage := abstractStoreStorageOrMappingMany state.storage slots value } := by
  rcases hruntime with
    ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hmem : query ∈ slots
  · rw [abstractStoreStorageOrMappingMany_eq, hstorage,
      encodeStorageAt_eq_storage_of_resolvedSlot (hresolved query hmem) hnotAddr hnotDyn]
    simp [SourceSemantics.writeUintSlots, List.contains_eq_true.mpr hmem]
  · rw [abstractStoreStorageOrMappingMany_eq, hstorage]
    simp [List.contains_eq_false.mpr hmem, encodeStorageAt_writeUintSlots_other hmem]

private theorem bindingsExactlyMatchIRVarsOnScope_writeUintSlot
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {slot value : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings state) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value } := by
  intro name hname
  simpa [IRState.getVar, Compiler.Proofs.abstractStoreStorageOrMapping_eq] using
    hexact name hname

private theorem bindingsExactlyMatchIRVarsOnScope_writeUintSlots
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {slots : List Nat}
    {value : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings state) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
      { state with
          storage := abstractStoreStorageOrMappingMany state.storage slots value } := by
  intro name hname
  simpa [IRState.getVar, abstractStoreStorageOrMappingMany_eq] using
    hexact name hname

private theorem execIRStmts_sstore_lit_ident_slots_continue
    (fuel : Nat)
    (state : IRState)
    (slots : List Nat)
    (name : String)
    (value : Nat)
    (hvalue : IRState.getVar state name = value) :
    execIRStmts (slots.length + fuel + 1) state
      (slots.map (fun slot =>
        YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident name]))) =
      .continue
        { state with
            storage := abstractStoreStorageOrMappingMany state.storage slots value } := by
  induction slots generalizing state fuel with
  | nil =>
      simp [execIRStmts, abstractStoreStorageOrMappingMany]
  | cons slot rest ih =>
      let nextState :=
        { state with
            storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value }
      have hstmt :
          execIRStmt (rest.length + fuel + 1) state
            (YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident name])) =
              .continue nextState := by
        apply execIRStmt_sstore_lit_expr_succ_of_eval
        simpa [evalIRExpr, IRState.getVar, hvalue]
      have hvalueNext : IRState.getVar nextState name = value := by
        simpa [nextState, IRState.getVar] using hvalue
      have htail :=
        ih (fuel := fuel) (state := nextState) (name := name) (value := value) hvalueNext
      simpa [execIRStmts, abstractStoreStorageOrMappingMany, nextState] using htail

private theorem execIRStmts_let_then_sstore_lit_ident_slots_continue
    (fuel : Nat)
    (state : IRState)
    (slots : List Nat)
    (tempName : String)
    (valueIR : YulExpr)
    (value : Nat)
    (hvalue : evalIRExpr state valueIR = some value) :
    execIRStmts (slots.length + fuel + 2) state
      (YulStmt.let_ tempName valueIR ::
        slots.map (fun slot =>
          YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident tempName]))) =
      .continue
        { state.setVar tempName value with
            storage :=
              abstractStoreStorageOrMappingMany
                (state.setVar tempName value).storage
                slots
                value } := by
  have hlet :
      execIRStmt (slots.length + fuel + 1) state
        (YulStmt.let_ tempName valueIR) =
          .continue (state.setVar tempName value) := by
    simp [execIRStmt, hvalue]
  have hslots :=
    execIRStmts_sstore_lit_ident_slots_continue
      fuel
      (state.setVar tempName value)
      slots
      tempName
      value
      (by simp [IRState.getVar])
  simpa [execIRStmts, hlet] using hslots

theorem compiledStmtStep_setStorage_singleSlot
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (halias : f.aliasSlots = [])
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStorage fieldName value)
      [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])] where
  compileOk := by
    simp [CompilationModel.compileStmt, CompilationModel.compileSetStorage,
      hfind, halias, hunpacked, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let compiledIR := [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])]
    let valueNat := SourceSemantics.evalExpr fields runtime value
    have hresolvedSlot :
        findResolvedFieldAtSlotCopy fields slot = some f :=
      findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
        hnoConflict hfind hwriteSlots hunpacked
    have heval :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcore hexact hinScope hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
        hruntime
    rw [hvalueIR] at heval
    have hvalueEval : evalIRExpr state valueIR = some valueNat := by
      simpa [valueNat] using heval
    have hslack' : sizeOf compiledIR - compiledIR.length ≤ extraFuel := by
      simpa [compiledIR] using hslack
    refine ⟨_, _, ?_⟩
    · simp [SourceSemantics.execStmt, hwriteSlots, valueNat]
    · have hExecStmt :
          execIRStmt (extraFuel + 1) state
            (YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])) =
              .continue
                { state with
                    storage :=
                      Compiler.Proofs.abstractStoreStorageOrMapping
                        state.storage slot valueNat } :=
        execIRStmt_sstore_lit_expr_succ_of_eval
          extraFuel state slot valueIR valueNat hvalueEval
      simpa [compiledIR, execIRStmts, hExecStmt]
    · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
      · exact runtimeStateMatchesIR_writeUintSlot hruntime hresolvedSlot hnotAddr hnotDyn
      · exact bindingsExactlyMatchIRVarsOnScope_writeUintSlot hexact

private theorem terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
    {fields : List Field}
    {scope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec)
    (hnotContinue : ∀ next, sourceResult ≠ .continue next) :
    stmtStepMatchesIRExec fields scope sourceResult irExec := by
  cases sourceResult <;> cases irExec <;> simp [stmtStepMatchesIRExec] at hmatch ⊢
  case continue runtime =>
    exact False.elim (hnotContinue runtime rfl)

theorem compiledStmtStep_ite
    {fields : List Field}
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hcond : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hthen : FunctionBody.StmtListTerminalCore scope thenBranch)
    (helse : FunctionBody.StmtListTerminalCore scope elseBranch) :
    ∃ compiledIR, CompiledStmtStep fields scope (.ite cond thenBranch elseBranch) compiledIR := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcond with ⟨condIR, hcondIR⟩
  rcases FunctionBody.compileStmtList_terminal_core_ok
      (fields := fields)
      (scope := scope)
      (inScopeNames := scope)
      (stmts := thenBranch)
      hthen with
    ⟨thenIR, hthenIR⟩
  rcases FunctionBody.compileStmtList_terminal_core_ok
      (fields := fields)
      (scope := scope)
      (inScopeNames := scope)
      (stmts := elseBranch)
      helse with
    ⟨elseIR, helseIR⟩
  have helseNonempty : elseBranch.isEmpty = false := by
    cases elseBranch with
    | nil =>
        exfalso
        exact FunctionBody.stmtListTerminalCore_ne_nil helse rfl
    | cons =>
        simp
  let tempName :=
    CompilationModel.pickFreshName "__ite_cond"
      (scope ++ collectExprNames cond ++
        collectStmtListNames thenBranch ++ collectStmtListNames elseBranch)
  let compiledIR :=
    [YulStmt.block
      [ YulStmt.let_ tempName condIR
      , YulStmt.if_ (YulExpr.ident tempName) thenIR
      , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]]
  refine ⟨compiledIR, ?_⟩
  refine
    { compileOk := ?_
      preserves := ?_ }
  · unfold compiledIR tempName
    unfold CompilationModel.compileStmt
    rw [hcondIR, hthenIR, helseIR]
    simp [helseNonempty]
  · intro runtime state extraFuel hexact hscope hbounded hruntime hslack
    let slack := sizeOf compiledIR - compiledIR.length
    let wholeExtraFuel := extraFuel - slack
    have hwholeFuel :
        sizeOf compiledIR + wholeExtraFuel + 1 =
          compiledIR.length + extraFuel + 1 := by
      dsimp [wholeExtraFuel, slack, compiledIR]
      have : slack ≤ extraFuel := by
        simpa [slack, compiledIR] using hslack
      omega
    have hpresent : FunctionBody.exprBoundNamesPresent cond runtime.bindings :=
      FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope
    let condValue := SourceSemantics.evalExpr fields runtime cond
    have hcondEval :
        evalIRExpr state condIR = some condValue := by
      have heval :=
        FunctionBody.eval_compileExpr_core_of_scope
          hcond hexact hinScope hbounded hpresent hruntime
      rw [hcondIR] at heval
      simpa [condValue] using heval
    by_cases hcondZero : condValue = 0
    · let branchExtraFuel :=
        sizeOf compiledIR - (sizeOf elseIR + 5) + wholeExtraFuel
      rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
          (fields := fields)
          (runtime := runtime)
          (state := state.setVar tempName condValue)
          (scope := scope)
          (inScopeNames := scope)
          (stmts := elseBranch)
          (extraFuel := branchExtraFuel)
          helse
          FunctionBody.scopeNamesIncluded_refl
          hscope
          (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
            (scope := scope)
            (inScopeNames := scope)
            (cond := cond)
            (thenBranch := thenBranch)
            (elseBranch := elseBranch)
            (value := condValue)
            hexact
            FunctionBody.scopeNamesIncluded_refl)
          hbounded
          (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime) with
        ⟨elseIR', helseIR', helseSem⟩
      rw [helseIR] at helseIR'
      injection helseIR' with helseEq
      subst helseEq
      have hsourceEq :
          SourceSemantics.execStmtList fields runtime
            (.ite cond thenBranch elseBranch :: []) =
            SourceSemantics.execStmtList fields runtime elseBranch :=
        FunctionBody.execStmtList_terminal_core_ite_else_eq
          (fields := fields)
          (runtime := runtime)
          (scope := scope)
          (cond := cond)
          (thenBranch := thenBranch)
          (elseBranch := elseBranch)
          (rest := [])
          helse
          (by simp [condValue, hcondZero])
      have hbodyMatch :
          FunctionBody.stmtResultMatchesIRExec
            fields
            (SourceSemantics.execStmtList fields runtime elseBranch)
            (execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR) := by
        have hmatch :=
          FunctionBody.stmtResultMatchesIRExec_compiled_terminal_ite_else
            (fields := fields)
            (runtime := runtime)
            (state := state)
            (scope := scope)
            (cond := cond)
            (thenBranch := thenBranch)
            (elseBranch := elseBranch)
            (rest := [])
            (extraFuel := wholeExtraFuel)
            (tempName := tempName)
            (condIR := condIR)
            (thenIR := thenIR)
            (elseIR := elseIR)
            (tailIR := [])
            (condValue := condValue)
            (irExec := execIRStmts
              (sizeOf elseIR + branchExtraFuel)
              (state.setVar tempName condValue)
              elseIR)
            helse
            helseSem
            (by simp [condValue, hcondZero])
            hcondEval
            hcondZero
            (by
              simpa [compiledIR, branchExtraFuel, tempName, condValue] using rfl)
        rw [hsourceEq] at hmatch
        simpa [hwholeFuel, compiledIR] using hmatch
      refine ⟨_, _, ?_⟩
      · simp [SourceSemantics.execStmt, condValue, hcondZero]
      · rfl
      · exact terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
          hbodyMatch
          (FunctionBody.execStmtList_terminal_core_not_continue
            (fields := fields)
            (runtime := runtime)
            (scope := scope)
            (stmts := elseBranch)
            helse)
    · let branchExtraFuel :=
        sizeOf compiledIR - (sizeOf thenIR + 5) + wholeExtraFuel
      rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
          (fields := fields)
          (runtime := runtime)
          (state := state.setVar tempName condValue)
          (scope := scope)
          (inScopeNames := scope)
          (stmts := thenBranch)
          (extraFuel := branchExtraFuel)
          hthen
          FunctionBody.scopeNamesIncluded_refl
          hscope
          (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
            (scope := scope)
            (inScopeNames := scope)
            (cond := cond)
            (thenBranch := thenBranch)
            (elseBranch := elseBranch)
            (value := condValue)
            hexact
            FunctionBody.scopeNamesIncluded_refl)
          hbounded
          (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime) with
        ⟨thenIR', hthenIR', hthenSem⟩
      rw [hthenIR] at hthenIR'
      injection hthenIR' with hthenEq
      subst hthenEq
      have hsourceEq :
          SourceSemantics.execStmtList fields runtime
            (.ite cond thenBranch elseBranch :: []) =
            SourceSemantics.execStmtList fields runtime thenBranch :=
        FunctionBody.execStmtList_terminal_core_ite_then_eq
          (fields := fields)
          (runtime := runtime)
          (scope := scope)
          (cond := cond)
          (thenBranch := thenBranch)
          (elseBranch := elseBranch)
          (rest := [])
          hthen
          (by simp [condValue, hcondZero])
      have hbodyMatch :
          FunctionBody.stmtResultMatchesIRExec
            fields
            (SourceSemantics.execStmtList fields runtime thenBranch)
            (execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR) := by
        have hmatch :=
          FunctionBody.stmtResultMatchesIRExec_compiled_terminal_ite_then
            (fields := fields)
            (runtime := runtime)
            (state := state)
            (scope := scope)
            (cond := cond)
            (thenBranch := thenBranch)
            (elseBranch := elseBranch)
            (rest := [])
            (extraFuel := wholeExtraFuel)
            (tempName := tempName)
            (condIR := condIR)
            (thenIR := thenIR)
            (elseIR := elseIR)
            (tailIR := [])
            (condValue := condValue)
            (irExec := execIRStmts
              (sizeOf thenIR + branchExtraFuel + 1)
              (state.setVar tempName condValue)
              thenIR)
            hthen
            hthenSem
            (by simp [condValue, hcondZero])
            hcondEval
            (by
              intro hzero
              exact hcondZero hzero)
            (by
              simpa [compiledIR, branchExtraFuel, tempName, condValue, Nat.add_assoc,
                Nat.add_left_comm, Nat.add_comm] using rfl)
        rw [hsourceEq] at hmatch
        simpa [hwholeFuel, compiledIR] using hmatch
      refine ⟨_, _, ?_⟩
      · simp [SourceSemantics.execStmt, condValue, hcondZero]
      · rfl
      · exact terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
          hbodyMatch
          (FunctionBody.execStmtList_terminal_core_not_continue
            (fields := fields)
            (runtime := runtime)
            (scope := scope)
            (stmts := thenBranch)
            hthen)

theorem stmtStepMatchesIRExec_implies_stmtResultMatchesIRExec
    {fields : List Field}
    {scope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : stmtStepMatchesIRExec fields scope sourceResult irExec) :
    FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec := by
  cases sourceResult <;> cases irExec <;> simp [stmtStepMatchesIRExec] at hmatch <;>
    simp [FunctionBody.stmtResultMatchesIRExec, hmatch]

private theorem yulStmtList_sizeOf_append_left_le
    (head tail : List YulStmt) :
    sizeOf head ≤ sizeOf (head ++ tail) := by
  induction head with
  | nil =>
      simp
  | cons stmt rest ih =>
      simp [List.cons_append]
      omega

private theorem scopeNamesIncluded_stmtNextScope
    {scope inScopeNames : List String}
    {stmt : Stmt}
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    FunctionBody.scopeNamesIncluded
      (stmtNextScope scope stmt)
      (collectStmtNames stmt ++ inScopeNames) := by
  intro name hname
  rcases List.mem_append.mp hname with hhead | htail
  · exact List.mem_append.mpr <| Or.inl hhead
  · exact List.mem_append.mpr <| Or.inr <| hincluded name htail

private theorem execIRStmts_append_of_continue
    (fuel : Nat)
    (state next : IRState)
    (head tail : List YulStmt)
    (hhead : execIRStmts fuel state head = .continue next) :
    execIRStmts fuel state (head ++ tail) =
      execIRStmts (fuel - head.length) next tail := by
  induction head generalizing fuel state with
  | nil =>
      simp at hhead
      subst hhead
      simp
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simp [execIRStmts] at hhead
      | succ fuel =>
          simp [execIRStmts] at hhead ⊢
          cases hstmt : execIRStmt fuel state stmt <;> simp [hstmt] at hhead
          case continue next' =>
            simpa using ih fuel next' hhead

private theorem execIRStmts_append_of_not_continue
    (fuel : Nat)
    (state : IRState)
    (head tail : List YulStmt)
    (irExec : IRExecResult)
    (hhead : execIRStmts fuel state head = irExec)
    (hnot : ∀ next, irExec ≠ .continue next) :
    execIRStmts fuel state (head ++ tail) = irExec := by
  induction head generalizing fuel state with
  | nil =>
      simp at hhead
      subst hhead
      exact False.elim (hnot state rfl)
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simp [execIRStmts] at hhead ⊢
      | succ fuel =>
          simp [execIRStmts] at hhead ⊢
          cases hstmt : execIRStmt fuel state stmt <;> simp [hstmt] at hhead ⊢
          case continue next' =>
            exact ih fuel next' hhead hnot
          case return value state' =>
            cases hhead
            simp [execIRStmts, hstmt]
          case stop state' =>
            cases hhead
            simp [execIRStmts, hstmt]
          case revert state' =>
            cases hhead
            simp [execIRStmts, hstmt]

theorem exec_compileStmtList_generic_sizeOf_extraFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (extraFuel : Nat)
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec := by
  induction hgeneric generalizing runtime state inScopeNames extraFuel with
  | nil =>
      refine ⟨[], by simp [CompilationModel.compileStmtList], ?_⟩
      simp [SourceSemantics.execStmtList, FunctionBody.stmtResultMatchesIRExec, hruntime]
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      have hnextIncluded :
          FunctionBody.scopeNamesIncluded
            (stmtNextScope scope stmt)
            (collectStmtNames stmt ++ inScopeNames) :=
        scopeNamesIncluded_stmtNextScope hincluded
      rcases ih
          (runtime := runtime)
          (state := state)
          (inScopeNames := collectStmtNames stmt ++ inScopeNames)
          (extraFuel := 0)
          hnextIncluded hscope hexact hbounded hruntime with
        ⟨tailIR, htailCompile, htailSem⟩
      let bodyIR := compiledIR ++ tailIR
      have hbodyCompile :
          CompilationModel.compileStmtList
            fields [] [] .calldata [] false inScopeNames (stmt :: rest) =
              Except.ok bodyIR := by
        exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
          hstep.compileOk htailCompile
      let headExtraFuel := sizeOf bodyIR - compiledIR.length + extraFuel
      have hheadSlack :
          sizeOf compiledIR - compiledIR.length ≤ headExtraFuel := by
        have hsize : sizeOf compiledIR ≤ sizeOf bodyIR := by
          simpa [bodyIR] using yulStmtList_sizeOf_append_left_le compiledIR tailIR
        dsimp [headExtraFuel]
        omega
      rcases hstep.preserves runtime state headExtraFuel
          hexact hscope hbounded hruntime hheadSlack with
        ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
      refine ⟨bodyIR, hbodyCompile, ?_⟩
      cases sourceHead <;> cases irHead <;> simp [stmtStepMatchesIRExec] at hheadMatch
      ·
        rcases hheadMatch with ⟨hruntime', hexact', hbounded', hscope'⟩
        let tailExtraFuel' :=
          sizeOf bodyIR - compiledIR.length - sizeOf tailIR + extraFuel
        have htailSem' :=
          ih
            (runtime := _)
            (state := _)
            (inScopeNames := collectStmtNames stmt ++ inScopeNames)
            (extraFuel := tailExtraFuel')
            hnextIncluded hscope' hexact' hbounded' hruntime'
        rcases htailSem' with ⟨tailIR', htailCompile', htailSem''⟩
        rw [htailCompile] at htailCompile'
        injection htailCompile' with htailEq
        subst htailEq
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .continue ‹IRState› := by
          simpa [headExtraFuel, bodyIR] using hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              execIRStmts (sizeOf tailIR + tailExtraFuel' + 1) ‹IRState› tailIR := by
          rw [execIRStmts_append_of_continue
              (fuel := sizeOf bodyIR + extraFuel + 1)
              (state := state)
              (next := ‹IRState›)
              (head := compiledIR)
              (tail := tailIR)
              hheadExec']
          dsimp [tailExtraFuel']
          omega
        rw [show SourceSemantics.execStmtList fields runtime (stmt :: rest) =
            SourceSemantics.execStmtList fields ‹SourceSemantics.RuntimeState› rest by
              simp [SourceSemantics.execStmtList, hsourceHead]]
        rw [hfullExec]
        simpa [tailExtraFuel', bodyIR] using htailSem''
      ·
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .stop ‹IRState› := by
          simpa [headExtraFuel, bodyIR] using hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .stop ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .stop ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtList, hsourceHead]
        rw [hfullExec]
        exact stmtStepMatchesIRExec_implies_stmtResultMatchesIRExec hheadMatch
      ·
        rcases hheadMatch with ⟨rfl, hruntime'⟩
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .return ‹Nat› ‹IRState› := by
          simpa [headExtraFuel, bodyIR] using hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .return ‹Nat› ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .return ‹Nat› ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtList, hsourceHead]
        rw [hfullExec]
        exact ⟨rfl, hruntime'⟩
      ·
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .revert ‹IRState› := by
          simpa [headExtraFuel, bodyIR] using hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .revert ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .revert ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtList, hsourceHead]
        rw [hfullExec]
        simp [FunctionBody.stmtResultMatchesIRExec]

theorem supported_function_body_correct_from_exact_state_generic
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hgeneric :
      StmtListGenericCore
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        fn.body = sourceResult ∧
      execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
  have hstateRuntime' :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
  have hscopeExact :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (fn.params.map (·.name)) bindings state :=
    FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings
  let sizeSlack := extraFuel - (sizeOf bodyStmts - bodyStmts.length)
  rcases exec_compileStmtList_generic_sizeOf_extraFuel
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings })
      (state := state)
      (scope := fn.params.map (·.name))
      (inScopeNames := fn.params.map (·.name))
      (stmts := fn.body)
      (extraFuel := sizeSlack)
      hgeneric
      FunctionBody.scopeNamesIncluded_refl
      hscope
      hscopeExact
      hbounded
      hstateRuntime' with
    ⟨bodyIR, hbodyGenericCompile, hgenericSem⟩
  have hbodyEq : bodyIR = bodyStmts := by
    rw [hbodyCompile'] at hbodyGenericCompile
    injection hbodyGenericCompile with hEq
    exact hEq.symm
  subst bodyIR
  have hfuel :
      sizeOf bodyStmts + sizeSlack + 1 =
        bodyStmts.length + extraFuel + 1 := by
    dsimp [sizeSlack]
    omega
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simpa [hfuel] using rfl
  · simpa [hfuel, sizeSlack] using hgenericSem

end Compiler.Proofs.IRGeneration
