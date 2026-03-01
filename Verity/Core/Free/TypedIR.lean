import Verity.Core
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

/-- Runtime interpretation of type-level typed IR tags. -/
def Ty.denote : Ty → Type
  | .uint256 => Verity.Core.Uint256
  | .address => Verity.Core.Address
  | .bool => Bool
  | .unit => PUnit

/-- Typed IR variable environment, partitioned by runtime type. -/
structure TVars where
  uint256 : Nat → Verity.Core.Uint256 := fun _ => 0
  address : Nat → Verity.Core.Address := fun _ => 0
  bool : Nat → Bool := fun _ => false
  unit : Nat → PUnit := fun _ => ⟨⟩
  deriving Inhabited

def TVars.get (vars : TVars) (v : TVar) : Ty.denote v.ty := by
  cases v with
  | mk id ty =>
      cases ty with
      | uint256 => exact vars.uint256 id
      | address => exact vars.address id
      | bool => exact vars.bool id
      | unit => exact vars.unit id

def TVars.set (vars : TVars) (v : TVar) (value : Ty.denote v.ty) : TVars := by
  cases v with
  | mk id ty =>
      cases ty with
      | uint256 =>
          exact { vars with uint256 := fun i => if i = id then value else vars.uint256 i }
      | address =>
          exact { vars with address := fun i => if i = id then value else vars.address i }
      | bool =>
          exact { vars with bool := fun i => if i = id then value else vars.bool i }
      | unit =>
          exact { vars with unit := fun i => if i = id then value else vars.unit i }

/-- Interpreter state for typed IR execution. -/
structure TExecState where
  world : Verity.ContractState
  vars : TVars := {}

instance : Inhabited TExecState := ⟨{ world := Verity.defaultState }⟩

/-- Statement/block evaluation result. -/
inductive TExecResult where
  | ok (state : TExecState)
  | revert (reason : String)
  deriving Inhabited

/-- Evaluate a typed expression in the current execution state. -/
def evalTExpr (s : TExecState) : TExpr ty → Ty.denote ty
  | .var v => s.vars.get v
  | .uintLit value => value
  | .addressLit value => value
  | .boolLit value => value
  | .unitLit => ⟨⟩
  | .add lhs rhs =>
      let l : Verity.Core.Uint256 := evalTExpr s lhs
      let r : Verity.Core.Uint256 := evalTExpr s rhs
      Verity.Core.Uint256.add l r
  | .sub lhs rhs =>
      let l : Verity.Core.Uint256 := evalTExpr s lhs
      let r : Verity.Core.Uint256 := evalTExpr s rhs
      Verity.Core.Uint256.sub l r
  | .mul lhs rhs =>
      let l : Verity.Core.Uint256 := evalTExpr s lhs
      let r : Verity.Core.Uint256 := evalTExpr s rhs
      Verity.Core.Uint256.mul l r
  | .eq (ty := .uint256) lhs rhs =>
      let l : Verity.Core.Uint256 := evalTExpr s lhs
      let r : Verity.Core.Uint256 := evalTExpr s rhs
      decide (l = r)
  | .eq (ty := .address) lhs rhs =>
      let l : Verity.Core.Address := evalTExpr s lhs
      let r : Verity.Core.Address := evalTExpr s rhs
      decide (l = r)
  | .eq (ty := .bool) lhs rhs =>
      let l : Bool := evalTExpr s lhs
      let r : Bool := evalTExpr s rhs
      decide (l = r)
  | .eq (ty := .unit) _ _ => true
  | .lt lhs rhs =>
      let l : Verity.Core.Uint256 := evalTExpr s lhs
      let r : Verity.Core.Uint256 := evalTExpr s rhs
      decide (l < r)
  | .and lhs rhs => evalTExpr s lhs && evalTExpr s rhs
  | .or lhs rhs => evalTExpr s lhs || evalTExpr s rhs
  | .not value => !(evalTExpr s value)
  | .ite cond thenExpr elseExpr =>
      match evalTExpr s cond with
      | true => evalTExpr s thenExpr
      | false => evalTExpr s elseExpr
  | .sender => s.world.sender
  | .this => s.world.thisAddress
  | .msgValue => s.world.msgValue
  | .blockTimestamp => s.world.blockTimestamp
  | .getStorage slot => s.world.storage slot
  | .getStorageAddr slot => s.world.storageAddr slot
  | .getMapping slot key => s.world.storageMap slot (evalTExpr s key)
  | .getMappingUint slot key => s.world.storageMapUint slot (evalTExpr s key)

mutual

/-- Fuel-bounded evaluator for a single typed IR statement. -/
def evalTStmtFuel : Nat → TExecState → TStmt → TExecResult
  | 0, _, _ => .revert "out of fuel"
  | Nat.succ _, s, .let_ dst rhs =>
      .ok { s with vars := s.vars.set dst (evalTExpr s rhs) }
  | Nat.succ _, s, .assign dst rhs =>
      .ok { s with vars := s.vars.set dst (evalTExpr s rhs) }
  | Nat.succ _, s, .setStorage slot value =>
      let v := evalTExpr s value
      .ok { s with world := { s.world with
        storage := fun i => if i == slot then v else s.world.storage i } }
  | Nat.succ _, s, .setStorageAddr slot value =>
      let v := evalTExpr s value
      .ok { s with world := { s.world with
        storageAddr := fun i => if i == slot then v else s.world.storageAddr i } }
  | Nat.succ _, s, .setMapping slot key value =>
      let k := evalTExpr s key
      let v := evalTExpr s value
      .ok { s with world := { s.world with
        storageMap := fun i addr => if i == slot && addr == k then v else s.world.storageMap i addr } }
  | Nat.succ _, s, .setMappingUint slot key value =>
      let k := evalTExpr s key
      let v := evalTExpr s value
      .ok { s with world := { s.world with
        storageMapUint := fun i key' => if i == slot && key' == k then v else s.world.storageMapUint i key' } }
  | Nat.succ fuel, s, .if_ cond thenBranch elseBranch =>
      match evalTExpr s cond with
      | true => evalTStmtsFuel fuel s thenBranch
      | false => evalTStmtsFuel fuel s elseBranch
  | Nat.succ _, s, .expr value =>
      let _ := evalTExpr s value
      .ok s
  | Nat.succ _, _, .revert reason => .revert reason

/-- Fuel-bounded evaluator for a sequence of typed IR statements. -/
def evalTStmtsFuel : Nat → TExecState → List TStmt → TExecResult
  | _, s, [] => .ok s
  | 0, _, _ :: _ => .revert "out of fuel"
  | Nat.succ fuel, s, stmt :: rest =>
      match evalTStmtFuel fuel s stmt with
      | .ok s' => evalTStmtsFuel fuel s' rest
      | .revert reason => .revert reason

end

/-- Default execution budget for wrapper evaluators. -/
def defaultEvalFuel : Nat := 1024

/-- Evaluate one typed IR statement. -/
def evalTStmt (s : TExecState) (stmt : TStmt) : TExecResult :=
  evalTStmtFuel defaultEvalFuel s stmt

/-- Evaluate a sequence of typed IR statements. -/
def evalTStmts (s : TExecState) (stmts : List TStmt) : TExecResult :=
  evalTStmtsFuel defaultEvalFuel s stmts

/-- Evaluate a full typed IR block body from an initial execution state. -/
def evalTBlock (s : TExecState) (block : TBlock) : TExecResult :=
  evalTStmts s block.body

@[simp] theorem evalTExpr_var (s : TExecState) (v : TVar) :
    evalTExpr s (TExpr.var v) = s.vars.get v := rfl

@[simp] theorem evalTExpr_uintLit (s : TExecState) (value : Verity.Core.Uint256) :
    evalTExpr s (TExpr.uintLit value) = value := rfl

@[simp] theorem evalTExpr_boolLit (s : TExecState) (value : Bool) :
    evalTExpr s (TExpr.boolLit value) = value := rfl

@[simp] theorem evalTExpr_add (s : TExecState) (lhs rhs : TExpr .uint256) :
    evalTExpr s (TExpr.add lhs rhs) =
      Verity.Core.Uint256.add (evalTExpr s lhs) (evalTExpr s rhs) := rfl

@[simp] theorem evalTExpr_ite (s : TExecState) {ty : Ty}
    (cond : TExpr .bool) (thenExpr elseExpr : TExpr ty) :
    evalTExpr s (TExpr.ite cond thenExpr elseExpr) =
      match evalTExpr s cond with
      | true => evalTExpr s thenExpr
      | false => evalTExpr s elseExpr := rfl

@[simp] theorem evalTStmt_revert (s : TExecState) (reason : String) :
    evalTStmt s (.revert reason) = .revert reason := by
  simp [evalTStmt, defaultEvalFuel, evalTStmtFuel]

@[simp] theorem evalTStmts_nil (s : TExecState) :
    evalTStmts s [] = .ok s := by
  simp [evalTStmts, evalTStmtsFuel]

@[simp] theorem evalTBlock_body (s : TExecState) (block : TBlock) :
    evalTBlock s block = evalTStmts s block.body := rfl

@[simp] theorem TVars.get_set_same (vars : TVars) (v : TVar) (value : Ty.denote v.ty) :
    (vars.set v value).get v = value := by
  cases v with
  | mk id ty =>
      cases ty <;> simp [TVars.set, TVars.get]

end Verity.Core.Free
