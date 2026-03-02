import Verity.Core.Free.TypedIR
import Verity.Core.Free.TypedIRCompiler
import Verity.Core.Free.TypedIRCompilerCorrectness
import Verity.Core.Free.TypedIRLowering
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Specs

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
  simp [baseState, evalTExpr, baseWorld, Verity.Env.ofWorld]

def envOverrideState : TExecState :=
  { world := baseWorld
    env := { sender := 99, thisAddress := 100, msgValue := 101, blockTimestamp := 102 }
    vars := baseState.vars }

/-- Context expressions read from explicit `TExecState.env`, not from world fields. -/
example :
    evalTExpr envOverrideState TExpr.sender = (99 : Verity.Core.Address) := by
  simp [envOverrideState, evalTExpr]

/-- Storage updates do not mutate explicit execution environment fields. -/
example :
    match evalTStmt envOverrideState (TStmt.setStorage 8 (TExpr.uintLit 55)) with
    | .ok s' => s'.env.sender = (99 : Verity.Core.Address)
    | .revert _ => False := by
  simp [envOverrideState, evalTStmt, evalTStmtFuel, defaultEvalFuel]

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

def counterTypedInitWorld : Verity.ContractState :=
  { «storage» := fun i => if i = 0 then 41 else 0
    storageAddr := fun _ => 0
    storageMap := fun _ _ => 0
    storageMapUint := fun _ _ => 0
    storageMap2 := fun _ _ _ => 0
    sender := 0
    thisAddress := 0
    msgValue := 0
    blockTimestamp := 0
    knownAddresses := fun _ => Verity.Core.FiniteAddressSet.empty
    events := [] }

def counterTypedInit : TExecState :=
  { world := counterTypedInitWorld }

def counterIRInit : IRState :=
  { vars := []
    «storage» := fun i => if i = 0 then 41 else 0
    memory := fun _ => 0
    calldata := []
    returnValue := none
    sender := 0
    selector := 0 }

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

def simpleStorageTypedInitWorld : Verity.ContractState :=
  { «storage» := fun i => if i = 0 then 5 else 0
    storageAddr := fun _ => 0
    storageMap := fun _ _ => 0
    storageMapUint := fun _ _ => 0
    storageMap2 := fun _ _ _ => 0
    sender := 0
    thisAddress := 0
    msgValue := 0
    blockTimestamp := 0
    knownAddresses := fun _ => Verity.Core.FiniteAddressSet.empty
    events := [] }

def simpleStorageTypedInit : TExecState :=
  { world := simpleStorageTypedInitWorld
    vars := { uint256 := fun
      | 20 => 77
      | _ => 0 } }

def simpleStorageIRInit : IRState :=
  (IRState.initial 0).setVar "value" 77

def simpleStorageIRInitWithStorage : IRState :=
  { vars := simpleStorageIRInit.vars
    «storage» := fun i => if i = 0 then 5 else 0
    memory := simpleStorageIRInit.memory
    calldata := simpleStorageIRInit.calldata
    returnValue := simpleStorageIRInit.returnValue
    sender := simpleStorageIRInit.sender
    selector := simpleStorageIRInit.selector }

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

private def tVarValueNat (state : Verity.Core.Free.TExecState.{0}) (v : TVar) : Nat :=
  match v with
  | ⟨id, .uint256⟩ => state.vars.uint256 id
  | ⟨id, .address⟩ => state.vars.address id
  | ⟨id, .bool⟩ => if state.vars.bool id then 1 else 0
  | ⟨_, .unit⟩ => 0

private def mkIRStateFromTyped (state : Verity.Core.Free.TExecState.{0}) (block : TBlock) : IRState :=
  let initVars : List (String × Nat) :=
    (block.params ++ block.locals).map (fun v => (tVarName v, tVarValueNat state v))
  IRState.mk
    initVars
    (fun i => (state.world.storage i : Nat))
    (fun _ => 0)
    []
    none
    state.env.sender
    0

private def execLoweredSlot0 (fuel : Nat) (state : IRState) (block : TBlock) : Option Nat :=
  match execIRStmts fuel state (lowerTBlock block) with
  | .continue s => some (s.storage 0)
  | .stop s => some (s.storage 0)
  | .return _ s => some (s.storage 0)
  | .revert _ => none

private def execLoweredReturn (fuel : Nat) (state : IRState) (block : TBlock) : Option Nat :=
  match execIRStmts fuel state (lowerTBlock block) with
  | .return ret _ => some ret
  | _ => none

private def execLoweredState (fuel : Nat) (state : IRState) (block : TBlock) : Option IRState :=
  match execIRStmts fuel state (lowerTBlock block) with
  | .continue s => some s
  | .stop s => some s
  | .return _ s => some s
  | .revert _ => none

/-- Golden test: lowering typed Counter block to Yul preserves storage-slot result. -/
example :
    execLoweredSlot0 64 (mkIRStateFromTyped counterTypedInit counterIncrementTBlock) counterIncrementTBlock =
      counterTypedFinalSlot := by
  native_decide

/-- Golden test: lowering typed SimpleStorage block to Yul preserves storage-slot result. -/
example :
    execLoweredSlot0 64 (mkIRStateFromTyped simpleStorageTypedInit simpleStorageStoreTBlock) simpleStorageStoreTBlock =
      simpleStorageTypedFinalSlot := by
  native_decide

def compiledCounterIncrementFinalSlot : Option Nat :=
  match compileFunctionNamed Compiler.Specs.counterSpec "increment" with
  | .error _ => none
  | .ok block =>
      match evalTBlock counterTypedInit block with
      | .ok s => some ((s.world.storage 0 : Verity.Core.Uint256) : Nat)
      | .revert _ => none

/-- Golden test: CompilationModel->typed-IR compiler preserves Counter.increment storage effect. -/
example : compiledCounterIncrementFinalSlot = counterIRFinalSlot := by
  native_decide

def compiledSimpleStorageStoreFinalSlot : Option Nat :=
  match compileFunctionNamed Compiler.Specs.simpleStorageSpec "store" with
  | .error _ => none
  | .ok block =>
      match block.params with
      | [] => none
      | valueParam :: _ =>
          let init : TExecState :=
            { world := simpleStorageTypedInitWorld
              vars := { uint256 := fun
                | i => if i = valueParam.id then 77 else 0 } }
          match evalTBlock init block with
          | .ok s => some ((s.world.storage 0 : Verity.Core.Uint256) : Nat)
          | .revert _ => none

/-- Golden test: CompilationModel->typed-IR compiler preserves SimpleStorage.store storage effect. -/
example : compiledSimpleStorageStoreFinalSlot = simpleStorageIRFinalSlot := by
  native_decide

def compiledCounterLoweredFinalSlot : Option Nat :=
  match compileFunctionNamed Compiler.Specs.counterSpec "increment" with
  | .error _ => none
  | .ok block =>
      execLoweredSlot0 256 (mkIRStateFromTyped counterTypedInit block) block

/-- Golden test: compiled typed Counter block lowers to Yul with matching final storage. -/
example : compiledCounterLoweredFinalSlot = compiledCounterIncrementFinalSlot := by
  native_decide

def compiledCounterDecrementFinalSlot : Option Nat :=
  let initWorld : Verity.ContractState :=
    { counterTypedInitWorld with «storage» := fun i => if i = 0 then 41 else 0 }
  let initTyped : TExecState := { world := initWorld }
  match compileFunctionNamed Compiler.Specs.counterSpec "decrement" with
  | .error _ => none
  | .ok block =>
      match evalTBlock initTyped block with
      | .ok s => some ((s.world.storage 0 : Verity.Core.Uint256) : Nat)
      | .revert _ => none

def compiledCounterDecrementLoweredFinalSlot : Option Nat :=
  let initWorld : Verity.ContractState :=
    { counterTypedInitWorld with «storage» := fun i => if i = 0 then 41 else 0 }
  let initTyped : TExecState := { world := initWorld }
  match compileFunctionNamed Compiler.Specs.counterSpec "decrement" with
  | .error _ => none
  | .ok block =>
      execLoweredSlot0 256 (mkIRStateFromTyped initTyped block) block

/-- End-to-end Counter decrement: typed IR lowering preserves storage effect. -/
example : compiledCounterDecrementLoweredFinalSlot = compiledCounterDecrementFinalSlot := by
  native_decide

def compiledCounterGetCountReturn : Option Nat :=
  let initWorld : Verity.ContractState :=
    { counterTypedInitWorld with «storage» := fun i => if i = 0 then 41 else 0 }
  let initTyped : TExecState := { world := initWorld }
  match compileFunctionNamed Compiler.Specs.counterSpec "getCount" with
  | .error _ => none
  | .ok block =>
      execLoweredReturn 256 (mkIRStateFromTyped initTyped block) block

/-- End-to-end Counter getCount: typed IR pipeline returns slot-0 value. -/
example : compiledCounterGetCountReturn = some 41 := by
  native_decide

def compiledSimpleStorageLoweredFinalSlot : Option Nat :=
  match compileFunctionNamed Compiler.Specs.simpleStorageSpec "store" with
  | .error _ => none
  | .ok block =>
      match block.params with
      | [] => none
      | valueParam :: _ =>
          let init : Verity.Core.Free.TExecState.{0} :=
            { world := simpleStorageTypedInitWorld
              vars := { uint256 := fun
                | i => if i = valueParam.id then 77 else 0 } }
          execLoweredSlot0 256 (mkIRStateFromTyped init block) block

/-- Golden test: compiled typed SimpleStorage block lowers to Yul with matching final storage. -/
example : compiledSimpleStorageLoweredFinalSlot = compiledSimpleStorageStoreFinalSlot := by
  native_decide

def compiledSimpleStorageRetrieveReturn : Option Nat :=
  let initWorld : Verity.ContractState :=
    { simpleStorageTypedInitWorld with «storage» := fun i => if i = 0 then 77 else 0 }
  let initTyped : TExecState := { world := initWorld }
  match compileFunctionNamed Compiler.Specs.simpleStorageSpec "retrieve" with
  | .error _ => none
  | .ok block =>
      execLoweredReturn 256 (mkIRStateFromTyped initTyped block) block

/-- End-to-end SimpleStorage retrieve: typed IR pipeline returns slot-0 value. -/
example : compiledSimpleStorageRetrieveReturn = some 77 := by
  native_decide

def compiledSimpleStorageStoreRetrieveRoundtrip : Option Nat :=
  match compileFunctionNamed Compiler.Specs.simpleStorageSpec "store",
        compileFunctionNamed Compiler.Specs.simpleStorageSpec "retrieve" with
  | .ok storeBlock, .ok retrieveBlock =>
      match storeBlock.params with
      | [] => none
      | valueParam :: _ =>
          let init : Verity.Core.Free.TExecState.{0} :=
            { world := simpleStorageTypedInitWorld
              vars := { uint256 := fun
                | i => if i = valueParam.id then 99 else 0 } }
          match execLoweredState 256 (mkIRStateFromTyped init storeBlock) storeBlock with
          | none => none
          | some postStore =>
              execLoweredReturn 256 postStore retrieveBlock
  | _, _ => none

/-- End-to-end SimpleStorage store→retrieve roundtrip through typed IR pipeline. -/
example : compiledSimpleStorageStoreRetrieveRoundtrip = some 99 := by
  native_decide

/-- Smoke test: Ledger.transfer compiles successfully (exercises bool→uint256 coercion). -/
def compiledLedgerTransferBlock : Option TBlock :=
  match compileFunctionNamed Compiler.Specs.ledgerSpec "transfer" with
  | .ok block => some block
  | .error _ => none

example : compiledLedgerTransferBlock.isSome = true := by
  native_decide

/-- End-to-end Ledger.transfer: non-self transfer updates both balances correctly. -/
def compiledLedgerTransferResult : Option (Nat × Nat) :=
  match compileFunctionNamed Compiler.Specs.ledgerSpec "transfer" with
  | .error _ => none
  | .ok block =>
      match block.params with
      | [toParam, amountParam] =>
          let initWorld : Verity.ContractState :=
            { Verity.defaultState with
              -- sender (address 1) has balance 100 in mapping slot 0
              storageMap := fun slot addr =>
                if slot == 0 && addr == 1 then 100
                else if slot == 0 && addr == 2 then 50
                else 0
              sender := 1 }
          let init : TExecState :=
            { world := initWorld
              vars := { address := fun i =>
                          if i = toParam.id then 2 else 0
                        uint256 := fun i =>
                          if i = amountParam.id then 30 else 0 } }
          match evalTBlock init block with
          | .ok s => some (s.world.storageMap 0 1, s.world.storageMap 0 2)
          | .revert _ => none
      | _ => none

/-- Ledger.transfer(to=2, amount=30): sender balance 100→70, recipient balance 50→80. -/
example : compiledLedgerTransferResult = some (70, 80) := by
  native_decide

/-- Compiler correctness base lemma: list compilation composes by append. -/
example (fields : List Compiler.CompilationModel.Field)
    (pre post : List Compiler.CompilationModel.Stmt) :
    compileStmts fields (pre ++ post) = (do
      compileStmts fields pre
      compileStmts fields post) :=
  compileStmts_append fields pre post

end Verity.Core.Free
