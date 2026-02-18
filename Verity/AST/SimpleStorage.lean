/-
  Verity.AST.SimpleStorage: Unified AST for SimpleStorage

  Defines the AST representation and proves `denote ast = edsl_fn` by `rfl`
  for each SimpleStorage function. This demonstrates Phase 2 of issue #364:
  a single source that is both compilable and provably equivalent to the EDSL.
-/

import Verity.Denote
import Verity.Examples.SimpleStorage

namespace Verity.AST.SimpleStorage

open Verity
open Verity.AST
open Verity.Denote
open Verity.Examples (storedData store retrieve)

/-- AST for `store(value)`: setStorage 0 value; stop -/
def storeAST : Stmt :=
  .sstore 0 (.var "value") .stop

/-- AST for `retrieve()`: return getStorage 0 -/
def retrieveAST : Stmt :=
  .bindUint "x" (.storage 0)
    (.ret (.var "x"))

/-!
## Equivalence Proofs

Each theorem proves that the AST denotation is definitionally equal to
the handwritten EDSL function. The `rfl` tactic succeeds because both
sides unfold to the same normal form through transparent `def`s.
-/

/-- `store` AST denotes to the EDSL `store` function. -/
theorem store_equiv (value : Uint256) :
    denoteUnit (fun s => if s == "value" then value else 0) emptyEnvAddr storeAST
    = store value := by
  rfl

/-- `retrieve` AST denotes to the EDSL `retrieve` function. -/
theorem retrieve_equiv :
    denoteUint emptyEnv emptyEnvAddr retrieveAST
    = retrieve := by
  rfl

end Verity.AST.SimpleStorage
