import Compiler.TypedIRCompilerCorrectness

/-!
Scoped proof-layer support witness for statement lists.

`SupportedStmtList` is now a compositional public grammar: it can expose either
the existing generic compile-core / terminal-core statement grammars directly,
or splice in one of the still-legacy `require`-family tail programs while the
remaining storage-write shapes are being migrated off the hardcoded inventory.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Verity.Core.Free

/-- Proof-layer compositional witness for supported statement lists.

The witness is scoped because the generic compile-core grammars track local name
availability explicitly. Legacy tail-program leaves remain available as a
transitional constructor so existing non-core storage/write shapes continue to
fit under the same body interface while the old fragment inventory is
dismantled. -/
inductive SupportedStmtList (fields : List Field) : List String → List Stmt → Prop where
  | compileCore
      {scope : List String}
      {stmts : List Stmt} :
      FunctionBody.StmtListCompileCore scope stmts →
      SupportedStmtList fields scope stmts
  | terminalCore
      {scope : List String}
      {stmts : List Stmt} :
      FunctionBody.StmtListTerminalCore scope stmts →
      SupportedStmtList fields scope stmts
  | legacyProgram
      {scope : List String}
      (program : RequireFamilyClausesTailProgram fields)
      {rest : List Stmt} :
      SupportedStmtList fields (List.foldl stmtNextScope scope program.toStmts) rest →
      SupportedStmtList fields scope (program.toStmts ++ rest)

end Compiler.Proofs.IRGeneration
