/-
  Verity.AST.Counter: Unified AST for Counter

  Defines the AST representation and proves `denote ast = edsl_fn` by `rfl`
  for each Counter function. Demonstrates that modular arithmetic (add/sub)
  works correctly through the denotation.
-/

import Verity.Denote
import Verity.Examples.Counter

namespace Verity.AST.Counter

open Verity
open Verity.AST
open Verity.Denote
open Verity.Examples.Counter (count increment decrement getCount)

/-- AST for `increment()`: let current ← getStorage 0; setStorage 0 (add current 1) -/
def incrementAST : Stmt :=
  .bindUint "current" (.storage 0)
    (.sstore 0 (.add (.var "current") (.lit 1)) .stop)

/-- AST for `decrement()`: let current ← getStorage 0; setStorage 0 (sub current 1) -/
def decrementAST : Stmt :=
  .bindUint "current" (.storage 0)
    (.sstore 0 (.sub (.var "current") (.lit 1)) .stop)

/-- AST for `getCount()`: getStorage 0 -/
def getCountAST : Stmt :=
  .bindUint "x" (.storage 0)
    (.ret (.var "x"))

/-!
## Equivalence Proofs
-/

theorem increment_equiv :
    denoteUnit emptyEnv emptyEnvAddr incrementAST = increment := by
  rfl

theorem decrement_equiv :
    denoteUnit emptyEnv emptyEnvAddr decrementAST = decrement := by
  rfl

theorem getCount_equiv :
    denoteUint emptyEnv emptyEnvAddr getCountAST = getCount := by
  rfl

end Verity.AST.Counter
