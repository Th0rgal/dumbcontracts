import Verity.Core.Free.TypedIR
import Compiler.CompilationModel

namespace Verity.Core.Free
open Compiler.CompilationModel

/-- Existential wrapper for typed IR expressions returned by compilation. -/
structure SomeTExpr where
  ty : Ty
  expr : TExpr ty

/-- Compiler state threaded through `CompileM`. -/
structure CompileState where
  nextId : Nat := 0
  vars : List (String × TVar) := []
  params : Array TVar := #[]
  locals : Array TVar := #[]
  body : Array TStmt := #[]

abbrev CompileM := StateT CompileState (Except String)

private def lookupVar (name : String) : CompileM TVar := do
  match (← get).vars.find? (fun (entry : String × TVar) => entry.1 == name) with
  | some (_, v) =>
      return v
  | none =>
      throw s!"Typed IR compile error: unknown variable '{name}'"

private def bindVar (name : String) (v : TVar) : CompileM Unit :=
  modify fun st => { st with vars := (name, v) :: st.vars }

/-- Allocate a fresh typed SSA variable. -/
def freshVar (ty : Ty) : CompileM { v : TVar // v.ty = ty } := do
  let st ← get
  let v : TVar := { id := st.nextId, ty := ty }
  set { st with nextId := st.nextId + 1 }
  return ⟨v, rfl⟩

private def pushParam (v : TVar) : CompileM Unit :=
  modify fun st => { st with params := st.params.push v }

private def pushLocal (v : TVar) : CompileM Unit :=
  modify fun st => { st with locals := st.locals.push v }

private def emit (stmt : TStmt) : CompileM Unit :=
  modify fun st => { st with body := st.body.push stmt }

private def paramTypeToTy : ParamType → Except String Ty
  | .uint256 => Except.ok Ty.uint256
  | .uint8 => Except.ok Ty.uint256
  | .address => Except.ok Ty.address
  | .bool => Except.ok Ty.bool
  | .bytes32 => Except.ok Ty.uint256
  | .tuple _ => Except.error "Typed IR compile error: tuple params are not yet supported"
  | .array _ => Except.error "Typed IR compile error: dynamic array params are not yet supported"
  | .fixedArray _ _ => Except.error "Typed IR compile error: fixed array params are not yet supported"
  | .bytes => Except.error "Typed IR compile error: bytes params are not yet supported"

private def fieldTypeToTy : FieldType → Except String Ty
  | .uint256 => Except.ok Ty.uint256
  | .address => Except.ok Ty.address
  | .mappingTyped _ => Except.ok Ty.uint256
  | .mappingStruct _ _ => Except.ok Ty.uint256
  | .mappingStruct2 _ _ _ => Except.ok Ty.uint256

private def asUInt256 (e : SomeTExpr) : Except String (TExpr Ty.uint256) :=
  match e with
  | ⟨Ty.uint256, expr⟩ => Except.ok expr
  | ⟨ty, _⟩ => Except.error s!"Typed IR compile error: expected uint256 expression, got {repr ty}"

private def asAddress (e : SomeTExpr) : Except String (TExpr Ty.address) :=
  match e with
  | ⟨Ty.address, expr⟩ => Except.ok expr
  | ⟨ty, _⟩ => Except.error s!"Typed IR compile error: expected address expression, got {repr ty}"

private def asBool (e : SomeTExpr) : Except String (TExpr Ty.bool) :=
  match e with
  | ⟨Ty.bool, expr⟩ => Except.ok expr
  | ⟨ty, _⟩ => Except.error s!"Typed IR compile error: expected bool expression, got {repr ty}"

private def compileStorageRead (fields : List Field) (fieldName : String) : Except String SomeTExpr := do
  match findFieldWithResolvedSlot fields fieldName with
  | none =>
      throw s!"Typed IR compile error: unknown storage field '{fieldName}'"
  | some (field, slot) =>
      match (← fieldTypeToTy field.ty) with
      | Ty.uint256 =>
          return ⟨Ty.uint256, TExpr.getStorage slot⟩
      | Ty.address =>
          return ⟨Ty.address, TExpr.getStorageAddr slot⟩
      | Ty.bool =>
          throw s!"Typed IR compile error: storage bool field '{fieldName}' unsupported in phase 2.1"
      | Ty.unit =>
          throw s!"Typed IR compile error: storage unit field '{fieldName}' unsupported"

mutual

private def compileExpr (fields : List Field) : Expr → CompileM SomeTExpr
  | .literal n =>
      return ⟨Ty.uint256, TExpr.uintLit n⟩
  | .param name => do
      let v ← lookupVar name
      return ⟨v.ty, TExpr.var v⟩
  | .localVar name => do
      let v ← lookupVar name
      return ⟨v.ty, TExpr.var v⟩
  | .storage fieldName =>
      liftExcept <| compileStorageRead fields fieldName
  | .mapping field key => do
      let keyExpr ← compileExpr fields key
      let keyAddr ← liftExcept <| asAddress keyExpr
      match findFieldSlot fields field with
      | some slot =>
          return ⟨Ty.uint256, TExpr.getMapping slot keyAddr⟩
      | none =>
          throw s!"Typed IR compile error: unknown mapping field '{field}'"
  | .mappingUint field key => do
      let keyExpr ← compileExpr fields key
      let keyUint ← liftExcept <| asUInt256 keyExpr
      match findFieldSlot fields field with
      | some slot =>
          return ⟨Ty.uint256, TExpr.getMappingUint slot keyUint⟩
      | none =>
          throw s!"Typed IR compile error: unknown mapping field '{field}'"
  | .caller => return ⟨Ty.address, TExpr.sender⟩
  | .contractAddress => return ⟨Ty.address, TExpr.this⟩
  | .msgValue => return ⟨Ty.uint256, TExpr.msgValue⟩
  | .blockTimestamp => return ⟨Ty.uint256, TExpr.blockTimestamp⟩
  | .add a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.uint256, TExpr.add a' b'⟩
  | .sub a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.uint256, TExpr.sub a' b'⟩
  | .mul a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.uint256, TExpr.mul a' b'⟩
  | .lt a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.bool, TExpr.lt a' b'⟩
  | .ge a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.bool, TExpr.not (TExpr.lt a' b')⟩
  | .gt a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.bool, TExpr.lt b' a'⟩
  | .le a b => do
      let a' ← liftExcept <| asUInt256 (← compileExpr fields a)
      let b' ← liftExcept <| asUInt256 (← compileExpr fields b)
      return ⟨Ty.bool, TExpr.not (TExpr.lt b' a')⟩
  | .logicalAnd a b => do
      let a' ← liftExcept <| asBool (← compileExpr fields a)
      let b' ← liftExcept <| asBool (← compileExpr fields b)
      return ⟨Ty.bool, TExpr.and a' b'⟩
  | .logicalOr a b => do
      let a' ← liftExcept <| asBool (← compileExpr fields a)
      let b' ← liftExcept <| asBool (← compileExpr fields b)
      return ⟨Ty.bool, TExpr.or a' b'⟩
  | .logicalNot a => do
      let a' ← liftExcept <| asBool (← compileExpr fields a)
      return ⟨Ty.bool, TExpr.not a'⟩
  | .ite cond thenVal elseVal => do
      let c ← liftExcept <| asBool (← compileExpr fields cond)
      let t ← compileExpr fields thenVal
      let e ← compileExpr fields elseVal
      match t, e with
      | ⟨Ty.uint256, tExpr⟩, ⟨Ty.uint256, eExpr⟩ => return ⟨Ty.uint256, TExpr.ite c tExpr eExpr⟩
      | ⟨Ty.address, tExpr⟩, ⟨Ty.address, eExpr⟩ => return ⟨Ty.address, TExpr.ite c tExpr eExpr⟩
      | ⟨Ty.bool, tExpr⟩, ⟨Ty.bool, eExpr⟩ => return ⟨Ty.bool, TExpr.ite c tExpr eExpr⟩
      | ⟨Ty.unit, tExpr⟩, ⟨Ty.unit, eExpr⟩ => return ⟨Ty.unit, TExpr.ite c tExpr eExpr⟩
      | ⟨tTy, _⟩, ⟨eTy, _⟩ =>
          throw s!"Typed IR compile error: ite branch type mismatch ({repr tTy} vs {repr eTy})"
  | expr =>
      throw s!"Typed IR compile error: unsupported expression form in phase 2.1: {repr expr}"

private def emitSSABind (name : String) (rhs : SomeTExpr) : CompileM Unit :=
  match rhs with
  | ⟨ty, expr⟩ => do
      let ⟨dst, hty⟩ ← freshVar ty
      let rhs' : TExpr dst.ty := by
        simpa [hty] using expr
      bindVar name dst
      pushLocal dst
      emit (.let_ dst rhs')

private def compileStmt (fields : List Field) : Stmt → CompileM Unit
  | .letVar name value => do
      emitSSABind name (← compileExpr fields value)
  | .assignVar name value => do
      let old ← lookupVar name
      let rhs ← compileExpr fields value
      if rhs.ty != old.ty then
        throw s!"Typed IR compile error: assignment type mismatch for '{name}'"
      emitSSABind name rhs
  | .setStorage fieldName value => do
      let rhs ← compileExpr fields value
      match findFieldWithResolvedSlot fields fieldName with
      | none =>
          throw s!"Typed IR compile error: unknown storage field '{fieldName}'"
      | some (field, slot) =>
          match (← fieldTypeToTy field.ty), rhs with
          | Ty.uint256, ⟨Ty.uint256, expr⟩ => emit (.setStorage slot expr)
          | Ty.address, ⟨Ty.address, expr⟩ => emit (.setStorageAddr slot expr)
          | expectedTy, ⟨actualTy, _⟩ =>
              throw s!"Typed IR compile error: setStorage type mismatch for '{fieldName}' (expected {repr expectedTy}, got {repr actualTy})"
  | .setMapping fieldName key value => do
      let keyExpr ← liftExcept <| asAddress (← compileExpr fields key)
      let valueExpr ← liftExcept <| asUInt256 (← compileExpr fields value)
      match findFieldSlot fields fieldName with
      | some slot => emit (.setMapping slot keyExpr valueExpr)
      | none => throw s!"Typed IR compile error: unknown mapping field '{fieldName}'"
  | .setMappingUint fieldName key value => do
      let keyExpr ← liftExcept <| asUInt256 (← compileExpr fields key)
      let valueExpr ← liftExcept <| asUInt256 (← compileExpr fields value)
      match findFieldSlot fields fieldName with
      | some slot => emit (.setMappingUint slot keyExpr valueExpr)
      | none => throw s!"Typed IR compile error: unknown mapping field '{fieldName}'"
  | .require cond message => do
      let condExpr ← liftExcept <| asBool (← compileExpr fields cond)
      emit (.if_ condExpr [] [.revert message])
  | .ite cond thenBranch elseBranch => do
      let condExpr ← liftExcept <| asBool (← compileExpr fields cond)
      let thenStmts ← compileBranch fields thenBranch
      let elseStmts ← compileBranch fields elseBranch
      emit (.if_ condExpr thenStmts elseStmts)
  | .stop =>
      emit (.expr TExpr.unitLit)
  | .return _ =>
      emit (.expr TExpr.unitLit)
  | .returnValues _ =>
      emit (.expr TExpr.unitLit)
  | stmt =>
      throw s!"Typed IR compile error: unsupported statement form in phase 2.1: {repr stmt}"

private def compileBranch (fields : List Field) (stmts : List Stmt) : CompileM (List TStmt) := do
  let startState ← get
  set { startState with body := #[] }
  for stmt in stmts do
    compileStmt fields stmt
  let branchState ← get
  set { startState with nextId := branchState.nextId }
  return branchState.body.toList

end

private def registerParam (param : Param) : CompileM Unit := do
  let ty ← liftExcept <| paramTypeToTy param.ty
  let ⟨v, _⟩ ← freshVar ty
  bindVar param.name v
  pushParam v

/-- Compile a single `CompilationModel` function into typed IR. -/
def compileFunctionToTBlock (spec : CompilationModel) (fn : FunctionSpec) : Except String TBlock := do
  let (_, st) ← ((do
      for p in fn.params do
        registerParam p
      for stmt in fn.body do
        compileStmt spec.fields stmt
      return ()) : CompileM Unit).run {}
  return { params := st.params.toList
           locals := st.locals.toList
           body := st.body.toList }

/-- Compile a named function from a `CompilationModel` to typed IR. -/
def compileFunctionNamed (spec : CompilationModel) (functionName : String) : Except String TBlock := do
  match spec.functions.find? (fun fn => fn.name == functionName) with
  | some fn => compileFunctionToTBlock spec fn
  | none => throw s!"Typed IR compile error: function '{functionName}' not found in spec '{spec.name}'"

end Verity.Core.Free
