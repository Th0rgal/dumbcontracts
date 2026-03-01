import Verity.Core.Free.TypedIR

namespace Verity.Core.Free

def x : TVar := { id := 0, ty := .uint256 }
def y : TVar := { id := 1, ty := .uint256 }
def flag : TVar := { id := 2, ty := .bool }

/-- Expression typing sanity check: uint arithmetic stays in `Ty.uint256`. -/
example : TExpr .uint256 := TExpr.add (TExpr.var x) (TExpr.var y)

/-- Statement typing sanity check: destination and rhs types must match. -/
example : TStmt := TStmt.assign x (TExpr.add (TExpr.var x) (TExpr.uintLit 1))

/-- Branching sanity check: condition must be statically boolean. -/
example : TStmt := TStmt.if_
  (TExpr.var flag)
  [TStmt.setStorage 0 (TExpr.var x)]
  [TStmt.revert "bad condition"]

/-- Block construction sanity check with typed declarations and statements. -/
example : TBlock where
  params := [x]
  locals := [y, flag]
  body :=
    [ TStmt.let_ y (TExpr.add (TExpr.var x) (TExpr.uintLit 1))
    , TStmt.assign x (TExpr.var y)
    , TStmt.if_ (TExpr.var flag)
        [TStmt.setStorage 0 (TExpr.var x)]
        [TStmt.revert "flag=false"]
    ]

end Verity.Core.Free
