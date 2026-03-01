import Verity.Core.Address
import Verity.Core.Uint256

namespace Verity.Core.Free

/-- Type universe for typed IR values. -/
inductive Ty where
  | uint256
  | address
  | bool
  | unit
  deriving DecidableEq, Repr, Inhabited

/-- SSA variable with a globally unique numeric identifier and static type. -/
structure TVar where
  id : Nat
  ty : Ty
  deriving DecidableEq, Repr, Inhabited

/-- Typed expression GADT. Ill-typed expressions are unrepresentable. -/
inductive TExpr : Ty → Type where
  | var (v : TVar) : TExpr v.ty
  | uintLit (value : Verity.Core.Uint256) : TExpr .uint256
  | addressLit (value : Verity.Core.Address) : TExpr .address
  | boolLit (value : Bool) : TExpr .bool
  | unitLit : TExpr .unit
  | add (lhs rhs : TExpr .uint256) : TExpr .uint256
  | sub (lhs rhs : TExpr .uint256) : TExpr .uint256
  | mul (lhs rhs : TExpr .uint256) : TExpr .uint256
  | eq {ty : Ty} (lhs rhs : TExpr ty) : TExpr .bool
  | lt (lhs rhs : TExpr .uint256) : TExpr .bool
  | and (lhs rhs : TExpr .bool) : TExpr .bool
  | or (lhs rhs : TExpr .bool) : TExpr .bool
  | not (value : TExpr .bool) : TExpr .bool
  | ite {ty : Ty} (cond : TExpr .bool) (thenExpr elseExpr : TExpr ty) : TExpr ty
  | sender : TExpr .address
  | this : TExpr .address
  | msgValue : TExpr .uint256
  | blockTimestamp : TExpr .uint256
  | getStorage (slot : Nat) : TExpr .uint256
  | getStorageAddr (slot : Nat) : TExpr .address
  | getMapping (slot : Nat) (key : TExpr .address) : TExpr .uint256
  | getMappingUint (slot : Nat) (key : TExpr .uint256) : TExpr .uint256
  deriving Repr

/-- Typed statements. Each assignment is type-correct by construction. -/
inductive TStmt where
  | let_ (dst : TVar) (rhs : TExpr dst.ty)
  | assign (dst : TVar) (rhs : TExpr dst.ty)
  | setStorage (slot : Nat) (value : TExpr .uint256)
  | setStorageAddr (slot : Nat) (value : TExpr .address)
  | setMapping (slot : Nat) (key : TExpr .address) (value : TExpr .uint256)
  | setMappingUint (slot : Nat) (key : TExpr .uint256) (value : TExpr .uint256)
  | if_ (cond : TExpr .bool) (thenBranch elseBranch : List TStmt)
  | expr (value : TExpr .unit)
  | revert (reason : String)
  deriving Repr

/-- Typed IR block: declared parameters, local variables, and body statements. -/
structure TBlock where
  params : List TVar
  locals : List TVar
  body : List TStmt
  deriving Repr

end Verity.Core.Free
