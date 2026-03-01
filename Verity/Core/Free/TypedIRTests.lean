import Verity.Core.Free.TypedIR
import Compiler.Proofs.IRGeneration.IRInterpreter

namespace Verity.Core.Free

def x : TVar := { id := 0, ty := .uint256 }
def y : TVar := { id := 1, ty := .uint256 }
def flag : TVar := { id := 2, ty := .bool }
def owner : TVar := { id := 3, ty := .address }

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

def baseWorld : Verity.ContractState :=
  { Verity.defaultState with
    sender := 7
    thisAddress := 9
    msgValue := 11
    blockTimestamp := 13
  }

def baseState : TExecState :=
  { world := baseWorld
    vars :=
      { uint256 := fun
          | 0 => 5
          | 1 => 8
          | _ => 0
        bool := fun
          | 2 => true
          | _ => false
        address := fun
          | 3 => 42
          | _ => 0
      } }

/-- `evalTExpr` reads variables and preserves typed arithmetic. -/
example :
    evalTExpr baseState (TExpr.add (TExpr.var x) (TExpr.var y)) =
      Verity.Core.Uint256.add 5 8 := by
  simp [baseState, x, y, evalTExpr, TVars.get]

/-- Context expressions read from world/environment. -/
example :
    evalTExpr baseState TExpr.sender = (7 : Verity.Core.Address) := by
  simp [baseState, evalTExpr, baseWorld]

/-- Assignment updates the typed variable environment. -/
example :
    match evalTStmt baseState (TStmt.assign x (TExpr.uintLit 99)) with
    | .ok s' => s'.vars.get x = (99 : Verity.Core.Uint256)
    | .revert _ => True := by
  simp [evalTStmt, evalTStmtFuel, defaultEvalFuel]

/-- Storage updates are reflected in the output execution world. -/
example :
    match evalTStmt baseState (TStmt.setStorage 4 (TExpr.uintLit 123)) with
    | .ok s' => s'.world.storage 4 = (123 : Verity.Core.Uint256)
    | .revert _ => True := by
  simp [evalTStmt, evalTStmtFuel, defaultEvalFuel]

/-- Branching and block execution compose through `evalTBlock`. -/
example :
    match evalTStmt baseState
      (TStmt.if_ (TExpr.boolLit true)
        []
        [TStmt.revert "no"]) with
    | .ok _ => True
    | .revert _ => False := by
  simp [evalTStmt, evalTStmtFuel, evalTStmtsFuel, defaultEvalFuel]

/-- Explicit revert in the block propagates as `Except.error`. -/
example :
    evalTBlock baseState
      { params := []
        locals := []
        body := [TStmt.revert "halt"] } = .revert "halt" := by
  simp [evalTBlock, evalTStmts, evalTStmtsFuel, evalTStmtFuel, defaultEvalFuel]

open Compiler.Yul
open Compiler.Proofs.IRGeneration

def counterTmp : TVar := { id := 10, ty := .uint256 }

/-- Typed IR block equivalent to Counter.increment (`count := count + 1`). -/
def counterIncrementTBlock : TBlock where
  params := []
  locals := [counterTmp]
  body :=
    [ TStmt.let_ counterTmp (TExpr.getStorage 0)
    , TStmt.assign counterTmp (TExpr.add (TExpr.var counterTmp) (TExpr.uintLit 1))
    , TStmt.setStorage 0 (TExpr.var counterTmp)
    ]

/-- Existing untyped IR program equivalent to `counterIncrementTBlock`. -/
def counterIncrementIR : List YulStmt :=
  [ .let_ "tmp" (.call "sload" [.lit 0])
  , .assign "tmp" (.call "add" [.ident "tmp", .lit 1])
  , .expr (.call "sstore" [.lit 0, .ident "tmp"])
  ]

def counterTypedInit : TExecState :=
  { world := { Verity.defaultState with
      storage := fun i => if i = 0 then 41 else 0 } }

def counterIRInit : IRState :=
  { (IRState.initial 0) with
      storage := fun i => if i = 0 then 41 else 0 }

def counterTypedFinalSlot : Option Nat :=
  match evalTBlock counterTypedInit counterIncrementTBlock with
  | .ok s => some ((s.world.storage 0 : Verity.Core.Uint256) : Nat)
  | .revert _ => none

def counterIRFinalSlot : Option Nat :=
  match execIRStmts 32 counterIRInit counterIncrementIR with
  | .continue s => some (s.storage 0)
  | _ => none

/-- Golden test: typed Counter increment matches existing IR evaluation. -/
example : counterTypedFinalSlot = counterIRFinalSlot := by
  native_decide

def simpleStorageValue : TVar := { id := 20, ty := .uint256 }

/-- Typed IR block equivalent to SimpleStorage.store(v). -/
def simpleStorageStoreTBlock : TBlock where
  params := [simpleStorageValue]
  locals := []
  body := [TStmt.setStorage 0 (TExpr.var simpleStorageValue)]

/-- Existing untyped IR program equivalent to `simpleStorageStoreTBlock`. -/
def simpleStorageStoreIR : List YulStmt :=
  [ .expr (.call "sstore" [.lit 0, .ident "value"]) ]

def simpleStorageTypedInit : TExecState :=
  { world := { Verity.defaultState with
      storage := fun i => if i = 0 then 5 else 0 }
    vars := { uint256 := fun
      | 20 => 77
      | _ => 0 } }

def simpleStorageIRInit : IRState :=
  (IRState.initial 0).setVar "value" 77

def simpleStorageIRInitWithStorage : IRState :=
  { simpleStorageIRInit with
      storage := fun i => if i = 0 then 5 else 0 }

def simpleStorageTypedFinalSlot : Option Nat :=
  match evalTBlock simpleStorageTypedInit simpleStorageStoreTBlock with
  | .ok s => some ((s.world.storage 0 : Verity.Core.Uint256) : Nat)
  | .revert _ => none

def simpleStorageIRFinalSlot : Option Nat :=
  match execIRStmts 16 simpleStorageIRInitWithStorage simpleStorageStoreIR with
  | .continue s => some (s.storage 0)
  | _ => none

/-- Golden test: typed SimpleStorage store matches existing IR evaluation. -/
example : simpleStorageTypedFinalSlot = simpleStorageIRFinalSlot := by
  native_decide

end Verity.Core.Free
