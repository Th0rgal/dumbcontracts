/-
  Compiler.ECM: External Call Module Framework

  External Call Modules (ECMs) package reusable external call patterns
  (ERC-20 transfers, precompile calls, callbacks, etc.) as typed, auditable
  Lean structures that the compiler can plug in without modification.

  Standard modules ship in `Compiler/Modules/`. Third parties can publish
  their own as separate Lean packages.

  See: #964
-/

import Compiler.Yul.Ast

namespace Compiler.ECM

open Compiler.Yul

/-- Context provided to ECM compile functions beyond the argument expressions.
    This gives modules access to compiler services without coupling them to
    the full ContractSpec compilation pipeline. -/
structure CompilationContext where
  /-- Whether dynamic data comes from calldata (external functions) or memory (internal). -/
  isDynamicFromCalldata : Bool := true

/-- An External Call Module packages a reusable external call pattern.
    Module authors provide the compilation logic; the compiler provides
    the generic framework for validation, compilation, and verification. -/
structure ExternalCallModule where
  /-- Human-readable name, used in error messages and audit reports. -/
  name : String

  /-- Number of Expr arguments this module expects.
      The compiler validates argument count before calling `compile`. -/
  numArgs : Nat

  /-- Local variables this module binds (e.g., ecrecover binds a result address).
      Empty for fire-and-forget patterns like safeTransfer. -/
  resultVars : List String := []

  /-- Does this pattern write to storage or make state-changing calls?
      If true, it cannot appear in view or pure functions. -/
  writesState : Bool

  /-- Does this pattern read storage or environment variables?
      If true, it cannot appear in pure functions. -/
  readsState : Bool

  /-- Compilation function. Takes a compilation context and compiled argument
      expressions (YulExpr) and produces the Yul statement sequence implementing
      this pattern. Returns Except so modules can report argument errors. -/
  compile : CompilationContext → List YulExpr → Except String (List YulStmt)

  /-- Trust assumptions. Surfaced in compilation reports and aggregated
      across all modules used by a contract. -/
  axioms : List String := []

instance : BEq ExternalCallModule where
  beq a b := a.name == b.name && a.numArgs == b.numArgs

instance : Repr ExternalCallModule where
  reprPrec m _ := s!"ECM[{m.name}]"

instance : ToString ExternalCallModule where
  toString m := s!"ECM[{m.name}]"

end Compiler.ECM
