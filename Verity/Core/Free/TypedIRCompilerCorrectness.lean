import Verity.Core.Free.TypedIRCompiler

namespace Verity.Core.Free
open Compiler.CompilationModel

/-- Generic structural-induction theorem: compiling concatenated statement lists
is equivalent to compiling the prefix then the suffix. -/
theorem compileStmts_append (fields : List Field) (pre post : List Stmt) :
    compileStmts fields (pre ++ post) = (do
      compileStmts fields pre
      compileStmts fields post) := by
  induction pre with
  | nil =>
      simp [compileStmts]
  | cons stmt rest ih =>
      simp [compileStmts, ih]

/-- `compileStmts_append` specialized to any initial compiler state. -/
theorem compileStmts_append_from (fields : List Field) (pre post : List Stmt)
    (st : CompileState) :
    (compileStmts fields (pre ++ post)).run st =
      ((do
          compileStmts fields pre
          compileStmts fields post).run st) := by
  simpa using congrArg (fun m => m.run st) (compileStmts_append fields pre post)

/-- Source semantics for the supported 2.2 subset:
`setStorage fieldName (literal n)` updates the resolved storage slot. -/
def execSourceSetStorageLiteral (world : Verity.ContractState) (slot : Nat) (n : Verity.Core.Uint256) :
    Verity.ContractState :=
  { world with storage := fun i => if i == slot then n else world.storage i }

/-- Compile + execute the same supported subset statement through typed IR. -/
def execCompiledSetStorageLiteral
    (fields : List Field) (fieldName : String) (init : TExecState) (n : Nat) :
    TExecResult :=
  match (compileStmts fields [Stmt.setStorage fieldName (Expr.literal n)]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Compile + execute a broader supported subset statement sequence:
`letVar tmp (literal n); setStorage fieldName (localVar tmp)`. -/
def execCompiledLetSetStorageLocalLiteral
    (fields : List Field) (fieldName tmp : String) (init : TExecState) (n : Nat) :
    TExecResult :=
  match (compileStmts fields
      [Stmt.letVar tmp (Expr.literal n), Stmt.setStorage fieldName (Expr.localVar tmp)]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Semantic-preservation theorem for the supported 2.2 subset:
compiling and running `setStorage fieldName (literal n)` matches direct source execution,
under explicit field-resolution assumptions. -/
theorem compile_setStorage_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (n : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledSetStorageLiteral fields fieldName init n =
      .ok { init with world := execSourceSetStorageLiteral init.world slot n } := by
  simp [execCompiledSetStorageLiteral, execSourceSetStorageLiteral,
    compileStmts_single_setStorage_literal_run, hfind, evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel]

/-- Semantic-preservation theorem for the supported two-statement subset:
compiling and running `letVar tmp (literal n); setStorage fieldName (localVar tmp)`
matches direct source storage update semantics under explicit field-resolution assumptions. -/
theorem compile_let_setStorage_local_literal_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState) (n : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledLetSetStorageLocalLiteral fields fieldName tmp init n =
      .ok
        ({ init with
            world := execSourceSetStorageLiteral init.world slot n
            vars := init.vars.set { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256) }) := by
  simp [execCompiledLetSetStorageLocalLiteral, execSourceSetStorageLiteral,
    compileStmts_let_literal_setStorage_local_run, hfind, evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel]

end Verity.Core.Free
