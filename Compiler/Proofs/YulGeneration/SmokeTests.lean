import Compiler.Proofs.YulGeneration.Semantics

namespace Compiler.Proofs.YulGeneration

open Compiler.Yul

private def emptyStorage : Nat → Nat := fun _ => 0
private def emptyMappings : Nat → Nat → Nat := fun _ _ => 0

private def mkState (selector : Nat) (args : List Nat) : YulState :=
  YulState.initial { sender := 0, functionSelector := selector, args := args } emptyStorage emptyMappings

#eval evalYulExpr (mkState 7 []) (YulExpr.call "calldataload" [YulExpr.lit 0])

#eval evalYulExpr (mkState 7 [42]) (YulExpr.call "calldataload" [YulExpr.lit 4])

#eval evalYulExpr (mkState 7 [])
  (YulExpr.call "shr" [YulExpr.lit selectorShift, YulExpr.call "calldataload" [YulExpr.lit 0]])

end Compiler.Proofs.YulGeneration
