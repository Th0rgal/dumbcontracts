/-
  Verity.AST.SafeCounter: Unified AST for SafeCounter

  Demonstrates `requireSomeUint` / `safeAdd` / `safeSub` through the
  unified AST with `rfl` equivalence proofs.
-/

import Verity.Denote
import Verity.Examples.SafeCounter

namespace Verity.AST.SafeCounter

open Verity
open Verity.AST
open Verity.Denote
open Verity.Examples.SafeCounter (count increment decrement getCount)

/-- AST for `increment()`:
    let current ← getStorage 0
    let newCount ← requireSomeUint (safeAdd current 1) "Overflow in increment"
    setStorage 0 newCount -/
def incrementAST : Stmt :=
  .bindUint "current" (.storage 0)
    (.requireSome "newCount" (.safeAdd (.var "current") (.lit 1)) "Overflow in increment"
      (.sstore 0 (.var "newCount") .stop))

/-- AST for `decrement()`:
    let current ← getStorage 0
    let newCount ← requireSomeUint (safeSub current 1) "Underflow in decrement"
    setStorage 0 newCount -/
def decrementAST : Stmt :=
  .bindUint "current" (.storage 0)
    (.requireSome "newCount" (.safeSub (.var "current") (.lit 1)) "Underflow in decrement"
      (.sstore 0 (.var "newCount") .stop))

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

end Verity.AST.SafeCounter
