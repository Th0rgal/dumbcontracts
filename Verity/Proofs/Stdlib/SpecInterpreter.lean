/-
  Verity.Proofs.Stdlib.SpecInterpreter: Semantics for ContractSpec DSL

  This module defines what it *means* to execute a ContractSpec.
  It provides a reference implementation that can be proven equivalent to
  both the EDSL semantics (Layer 1) and the IR/Yul semantics (Layers 2-3).

  Philosophy:
  - Simple, direct interpretation of the ContractSpec DSL
  - No optimizations - correctness over performance
  - Easy to understand and verify

  Supports:
  - If/else branching (#179)
  - forEach loops via loop expansion (#179)
  - Internal function calls via fuel-based execution (#181)
  - Double mappings and uint256-keyed mappings (#154)
  - Event emission recording (#153)
  - External function calls via externalFunctions parameter (#172)

  Two execution paths:
  - Basic (`execStmts`/`execStmt`): handles most constructs. `Stmt.forEach`
    and `Stmt.internalCall` revert (return none) instead of silently producing
    wrong results. Used by `execFunction`/`execConstructor`/`interpretSpec`.
  - Fuel-based (`execStmtsFuel`): handles all constructs including forEach
    and internal function calls. Used by `execFunctionFuel` and
    `execConstructorFuel`.

  Known limitation:
  - First-class low-level call / returndata primitives are intentionally
    fail-fast in the scalar interpreter (`execStmt`/`execStmts` and fuel path)
    because full EVM callframe+returndata semantics are not modeled yet.
  - `Expr.internalCall` always returns 0 in `evalExpr` — the expression evaluator
    does not carry the functions list. Use Stmt.internalCall (which assigns to a
    local variable) instead of Expr.internalCall in contract specs. (#181)
  - arrayParams is never populated from Transaction — array element access
    returns 0 (#180)
-/

import Compiler.ContractSpec
import Compiler.DiffTestTypes
import Verity.Core

namespace Verity.Proofs.Stdlib.SpecInterpreter

open Compiler.ContractSpec
open Compiler.DiffTestTypes
open Verity
open Verity.Core.Uint256 (modulus)

def addressModulus : Nat := 2^160

/-!
## Evaluation Context

Context needed to evaluate ContractSpec expressions and statements.
-/

structure EvalContext where
  -- Execution environment
  sender : Address
  msgValue : Nat
  blockTimestamp : Nat
  -- Function parameters (by index)
  params : List Nat
  paramTypes : List ParamType
  -- Constructor parameters (by index, if in constructor)
  constructorArgs : List Nat
  constructorParamTypes : List ParamType
  -- Local variables (from letVar)
  localVars : List (String × Nat)
  -- Array parameters: name → (length, elements) (#180)
  arrayParams : List (String × (Nat × List Nat))
  deriving Repr

/-!
## Storage State

Abstract representation of contract storage.
Extended with double-mapping support (#154) and events (#153).
-/

structure SpecStorage where
  -- Simple storage slots (resolved slot → value)
  slots : List (Nat × Nat)
  -- Mapping storage (resolved base slot → key → value)
  mappings : List (Nat × List (Nat × Nat))
  -- Double mapping storage (resolved base slot → (key1, key2) → value) (#154)
  mappings2 : List (Nat × List ((Nat × Nat) × Nat))
  -- Emitted events (#153)
  events : List (String × List Nat)
  deriving Repr

-- Create empty storage
def SpecStorage.empty : SpecStorage :=
  { slots := [], mappings := [], mappings2 := [], events := [] }

-- Read from simple storage slot
def SpecStorage.getSlot (s : SpecStorage) (slot : Nat) : Nat :=
  s.slots.lookup slot |>.getD 0

-- Write to simple storage slot
def SpecStorage.setSlot (s : SpecStorage) (slot : Nat) (value : Nat) : SpecStorage :=
  { s with slots := (slot, value) :: s.slots.filter (·.1 ≠ slot) }

-- Read from mapping
def SpecStorage.getMapping (s : SpecStorage) (baseSlot : Nat) (key : Nat) : Nat :=
  match s.mappings.lookup baseSlot with
  | none => 0
  | some m => m.lookup key |>.getD 0

-- Write to mapping
def SpecStorage.setMapping (s : SpecStorage) (baseSlot : Nat) (key : Nat) (value : Nat) : SpecStorage :=
  let oldMapping := s.mappings.lookup baseSlot |>.getD []
  let newMapping := (key, value) :: oldMapping.filter (·.1 ≠ key)
  let filteredMappings := s.mappings.filter (·.1 ≠ baseSlot)
  { s with mappings := (baseSlot, newMapping) :: filteredMappings }

-- Read from double mapping (#154)
def SpecStorage.getMapping2 (s : SpecStorage) (baseSlot : Nat) (key1 key2 : Nat) : Nat :=
  match s.mappings2.lookup baseSlot with
  | none => 0
  | some m =>
    match m.find? (fun ((k1, k2), _) => k1 == key1 && k2 == key2) with
    | none => 0
    | some (_, v) => v

-- Write to double mapping (#154)
def SpecStorage.setMapping2 (s : SpecStorage) (baseSlot : Nat) (key1 key2 : Nat) (value : Nat) : SpecStorage :=
  let oldMapping := s.mappings2.lookup baseSlot |>.getD []
  let newMapping := ((key1, key2), value) :: oldMapping.filter (fun ((k1, k2), _) => !(k1 == key1 && k2 == key2))
  let filteredMappings := s.mappings2.filter (·.1 ≠ baseSlot)
  { s with mappings2 := (baseSlot, newMapping) :: filteredMappings }

-- Add event to log (#153)
def SpecStorage.addEvent (s : SpecStorage) (name : String) (args : List Nat) : SpecStorage :=
  { s with events := s.events ++ [(name, args)] }

private def wordMask : Nat := modulus - 1

@[simp] def dedupNatPreserve (xs : List Nat) : List Nat :=
  let rec go (seen : List Nat) : List Nat → List Nat
    | [] => []
    | x :: rest =>
        if seen.contains x then
          go seen rest
        else
          x :: go (x :: seen) rest
  go [] xs

@[simp] theorem dedupNatPreserve_go_nil_single (x : Nat) :
    dedupNatPreserve.go [] [x] = [x] := by
  simp [dedupNatPreserve.go]

@[simp] def slotAliasForSource (sourceSlot : Nat) (range : SlotAliasRange) : Option Nat :=
  if range.sourceStart <= sourceSlot && sourceSlot <= range.sourceEnd then
    some (range.targetStart + (sourceSlot - range.sourceStart))
  else
    none

@[simp] def derivedAliasSlotsForSource (sourceSlot : Nat) (ranges : List SlotAliasRange) : List Nat :=
  dedupNatPreserve (ranges.filterMap (slotAliasForSource sourceSlot))

@[simp] def applySlotAliasRanges (fields : List Field) (ranges : List SlotAliasRange) : List Field :=
  fields.zipIdx.map fun (f, idx) =>
    let sourceSlot := f.slot.getD idx
    let derivedAliases := derivedAliasSlotsForSource sourceSlot ranges
    let mergedAliases := dedupNatPreserve (f.aliasSlots ++ derivedAliases)
    { f with aliasSlots := mergedAliases }

@[simp] def resolveFields (spec : ContractSpec) : List Field :=
  if spec.slotAliasRanges.isEmpty then
    spec.fields
  else
    applySlotAliasRanges spec.fields spec.slotAliasRanges

private def packedMaskNat (packed : PackedBits) : Nat :=
  if packed.width >= 256 then
    modulus - 1
  else
    (2 ^ packed.width) - 1

private def packedShiftedMaskNat (packed : PackedBits) : Nat :=
  packedMaskNat packed * (2 ^ packed.offset)

private def packedBitsValid (packed : PackedBits) : Bool :=
  packed.width > 0 &&
  packed.width <= 256 &&
  packed.offset < 256 &&
  packed.offset + packed.width <= 256

def readStorageField (storage : SpecStorage) (fields : List Field) (fieldName : String) : Nat :=
  match findFieldWithResolvedSlot fields fieldName with
  | some (field, slot) =>
      let word := storage.getSlot slot
      match field.packedBits with
      | none => word
      | some packed =>
          Nat.land (word >>> packed.offset) (packedMaskNat packed)
  | none => 0

def writeStorageField (storage : SpecStorage) (fields : List Field) (fieldName : String) (rawValue : Nat) :
    Option SpecStorage :=
  if isMapping fields fieldName then
    none
  else
    match findFieldWithResolvedSlot fields fieldName with
    | none => none
    | some (field, slot) =>
        let writeSlots := dedupNatPreserve (slot :: field.aliasSlots)
        let value := rawValue
        match field.packedBits with
        | none =>
            let next := writeSlots.foldl (fun acc writeSlot => acc.setSlot writeSlot value) storage
            some next
        | some packed =>
            let packedValue := Nat.land value (packedMaskNat packed)
            let shiftedMask := packedShiftedMaskNat packed
            let clearedMask := wordMask - shiftedMask
            let next := writeSlots.foldl (fun acc writeSlot =>
              let slotWord := acc.getSlot writeSlot
              let slotCleared := Nat.land slotWord clearedMask
              let packedWord := packedValue <<< packed.offset
              acc.setSlot writeSlot (Nat.lor slotCleared packedWord)
            ) storage
            some next

@[simp] theorem readStorageField_unpacked
    (storage : SpecStorage) (fields : List Field) (fieldName : String)
    (field : Field) (slot : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (field, slot))
    (hpacked : field.packedBits = none) :
    readStorageField storage fields fieldName = storage.getSlot slot := by
  simp [readStorageField, hfind, hpacked]

@[simp] theorem readStorageField_missing
    (storage : SpecStorage) (fields : List Field) (fieldName : String)
    (hfind : findFieldWithResolvedSlot fields fieldName = none) :
    readStorageField storage fields fieldName = 0 := by
  simp [readStorageField, hfind]

@[simp] theorem writeStorageField_unpacked_noAlias
    (storage : SpecStorage) (fields : List Field) (fieldName : String) (rawValue : Nat)
    (field : Field) (slot : Nat)
    (hMap : isMapping fields fieldName = false)
    (hFind : findFieldWithResolvedSlot fields fieldName = some (field, slot))
    (hAlias : field.aliasSlots = [])
    (hPacked : field.packedBits = none) :
    writeStorageField storage fields fieldName rawValue = some (storage.setSlot slot rawValue) := by
  simp [writeStorageField, hMap, hFind, hAlias, hPacked, dedupNatPreserve]

/-!
## External call model checks

To avoid silently proving against placeholder zeros, function/constructor
execution fails fast when `spec.externals` declares targets that are missing
from `externalFns`.
-/

@[simp] private def hasExternalModel (externalFns : List (String × (List Nat → Nat))) (name : String) : Bool :=
  externalFns.any (·.1 == name)

@[simp] private def specHasUnmodeledExternals (spec : ContractSpec) (externalFns : List (String × (List Nat → Nat))) : Bool :=
  spec.externals.any (fun ext => !(hasExternalModel externalFns ext.name))

/-!
## Expression Evaluation

Evaluate ContractSpec expressions to natural numbers.
All arithmetic is modular (mod 2^256) to match EVM semantics.
-/

mutual
def evalExprs (ctx : EvalContext) (storage : SpecStorage) (fields : List Field) (paramNames : List String) (externalFns : List (String × (List Nat → Nat))) : List Expr → List Nat
  | [] => []
  | e :: es => evalExpr ctx storage fields paramNames externalFns e :: evalExprs ctx storage fields paramNames externalFns es

def evalExpr (ctx : EvalContext) (storage : SpecStorage) (fields : List Field) (paramNames : List String) (externalFns : List (String × (List Nat → Nat))) : Expr → Nat
  | Expr.literal n => n % modulus
  | Expr.param name =>
      match paramNames.findIdx? (· == name) with
      | some idx =>
          let raw := ctx.params.getD idx 0
          match ctx.paramTypes[idx]? with
          | some ParamType.address => raw % addressModulus
          | some ParamType.bool => if raw % modulus == 0 then 0 else 1
          | _ => raw % modulus
      | none => 0
  | Expr.constructorArg idx =>
      let raw := ctx.constructorArgs.getD idx 0
      match ctx.constructorParamTypes[idx]? with
      | some ParamType.address => raw % addressModulus
      | some ParamType.bool => if raw % modulus == 0 then 0 else 1
      | _ => raw % modulus
  | Expr.storage fieldName =>
      match fields.findIdx? (·.name == fieldName) with
      | some idx =>
          let slot := (fields[idx]?.map (fun f => f.slot.getD idx)).getD idx
          match fields[idx]? with
          | some f =>
              let word := storage.getSlot slot
              match f.packedBits with
              | none => word
              | some packed => Nat.land (word >>> packed.offset) (packedMaskNat packed)
          | none => 0
      | none => 0
  | Expr.mapping fieldName key | Expr.mappingUint fieldName key =>
      match fields.findIdx? (·.name == fieldName) with
      | some idx =>
          let baseSlot := (fields[idx]?.map (fun f => f.slot.getD idx)).getD idx
          let keyVal := evalExpr ctx storage fields paramNames externalFns key
          storage.getMapping baseSlot keyVal
      | none => 0
  | Expr.mappingWord fieldName key wordOffset =>
      match fields.findIdx? (·.name == fieldName) with
      | some idx =>
          let baseSlot := (fields[idx]?.map (fun f => f.slot.getD idx)).getD idx
          let keyVal := evalExpr ctx storage fields paramNames externalFns key
          storage.getMapping baseSlot ((keyVal + wordOffset) % modulus)
      | none => 0
  | Expr.mappingPackedWord fieldName key wordOffset packed =>
      if !(packedBitsValid packed) then
        0
      else
        match fields.findIdx? (·.name == fieldName) with
        | some idx =>
            let baseSlot := (fields[idx]?.map (fun f => f.slot.getD idx)).getD idx
            let keyVal := evalExpr ctx storage fields paramNames externalFns key
            let word := storage.getMapping baseSlot ((keyVal + wordOffset) % modulus)
            Nat.land (word >>> packed.offset) (packedMaskNat packed)
        | none => 0
  | Expr.mapping2 fieldName key1 key2 =>
      match fields.findIdx? (·.name == fieldName) with
      | some idx =>
          let baseSlot := (fields[idx]?.map (fun f => f.slot.getD idx)).getD idx
          let key1Val := evalExpr ctx storage fields paramNames externalFns key1
          let key2Val := evalExpr ctx storage fields paramNames externalFns key2
          storage.getMapping2 baseSlot key1Val key2Val
      | none => 0
  | Expr.caller => ctx.sender.val
  | Expr.contractAddress =>
      -- Contract address is not modeled in the scalar interpreter.
      0
  | Expr.chainid =>
      -- chainid is not modeled in the scalar interpreter.
      0
  | Expr.msgValue => ctx.msgValue % modulus
  | Expr.blockTimestamp => ctx.blockTimestamp % modulus
  | Expr.mload _offset =>
      -- Linear memory is not modeled in the scalar interpreter.
      0
  | Expr.keccak256 _offset _size =>
      -- Keccak over linear memory is not modeled in the scalar interpreter.
      0
  | Expr.call _gas _target _value _inOffset _inSize _outOffset _outSize =>
      -- Low-level call semantics are not modeled in the scalar SpecInterpreter yet.
      0
  | Expr.staticcall _gas _target _inOffset _inSize _outOffset _outSize =>
      -- Low-level call semantics are not modeled in the scalar SpecInterpreter yet.
      0
  | Expr.delegatecall _gas _target _inOffset _inSize _outOffset _outSize =>
      -- Low-level call semantics are not modeled in the scalar SpecInterpreter yet.
      0
  | Expr.returndataSize =>
      -- Returndata buffers are not modeled in the scalar SpecInterpreter yet.
      0
  | Expr.returndataOptionalBoolAt _outOffset =>
      -- Returndata buffers are not modeled in the scalar SpecInterpreter yet.
      0
  | Expr.localVar name =>
      ctx.localVars.lookup name |>.getD 0
  | Expr.externalCall name args =>
      let argVals := evalExprs ctx storage fields paramNames externalFns args
      match externalFns.lookup name with
      | some fn => fn argVals % modulus
      | none => 0
  | Expr.internalCall _functionName _args => 0
  | Expr.arrayLength name =>
      match ctx.arrayParams.lookup name with
      | some (len, _) => len
      | none => 0
  | Expr.arrayElement name index =>
      let idx := evalExpr ctx storage fields paramNames externalFns index
      match ctx.arrayParams.lookup name with
      | some (_, elems) => elems.getD idx 0
      | none => 0
  | Expr.add a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      (va + vb) % modulus
  | Expr.sub a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      if va >= vb then va - vb
      else modulus - (vb - va)
  | Expr.mul a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      (va * vb) % modulus
  | Expr.div a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      if vb == 0 then 0 else va / vb
  | Expr.mod a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      if vb == 0 then 0 else va % vb
  | Expr.bitAnd a b =>
      Nat.land (evalExpr ctx storage fields paramNames externalFns a) (evalExpr ctx storage fields paramNames externalFns b)
  | Expr.bitOr a b =>
      Nat.lor (evalExpr ctx storage fields paramNames externalFns a) (evalExpr ctx storage fields paramNames externalFns b)
  | Expr.bitXor a b =>
      Nat.xor (evalExpr ctx storage fields paramNames externalFns a) (evalExpr ctx storage fields paramNames externalFns b)
  | Expr.bitNot a =>
      (modulus - 1 - evalExpr ctx storage fields paramNames externalFns a) % modulus
  | Expr.shl shift value =>
      (evalExpr ctx storage fields paramNames externalFns value <<< evalExpr ctx storage fields paramNames externalFns shift) % modulus
  | Expr.shr shift value =>
      evalExpr ctx storage fields paramNames externalFns value >>> evalExpr ctx storage fields paramNames externalFns shift
  | Expr.eq a b =>
      if evalExpr ctx storage fields paramNames externalFns a == evalExpr ctx storage fields paramNames externalFns b then 1 else 0
  | Expr.ge a b =>
      if evalExpr ctx storage fields paramNames externalFns a >= evalExpr ctx storage fields paramNames externalFns b then 1 else 0
  | Expr.gt a b =>
      if evalExpr ctx storage fields paramNames externalFns a > evalExpr ctx storage fields paramNames externalFns b then 1 else 0
  | Expr.lt a b =>
      if evalExpr ctx storage fields paramNames externalFns a < evalExpr ctx storage fields paramNames externalFns b then 1 else 0
  | Expr.le a b =>
      if evalExpr ctx storage fields paramNames externalFns a <= evalExpr ctx storage fields paramNames externalFns b then 1 else 0
  | Expr.logicalAnd a b =>
      if evalExpr ctx storage fields paramNames externalFns a ≠ 0 && evalExpr ctx storage fields paramNames externalFns b ≠ 0 then 1 else 0
  | Expr.logicalOr a b =>
      if evalExpr ctx storage fields paramNames externalFns a ≠ 0 || evalExpr ctx storage fields paramNames externalFns b ≠ 0 then 1 else 0
  | Expr.logicalNot a =>
      if evalExpr ctx storage fields paramNames externalFns a == 0 then 1 else 0
  | Expr.mulDivDown a b c =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      let vc := evalExpr ctx storage fields paramNames externalFns c
      if vc == 0 then 0 else ((va * vb) % modulus) / vc
  | Expr.mulDivUp a b c =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      let vc := evalExpr ctx storage fields paramNames externalFns c
      if vc == 0 then 0
      else
        let product := (va * vb) % modulus
        let subtracted := if vc >= 1 then vc - 1 else modulus - (1 - vc)
        ((product + subtracted) % modulus) / vc
  | Expr.wMulDown a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      ((va * vb) % modulus) / 1000000000000000000
  | Expr.wDivUp a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      if vb == 0 then 0
      else
        let product := (va * 1000000000000000000) % modulus
        let subtracted := if vb >= 1 then vb - 1 else modulus - (1 - vb)
        ((product + subtracted) % modulus) / vb
  | Expr.min a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      if va ≤ vb then va else vb
  | Expr.max a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      if va ≥ vb then va else vb
end

mutual
def exprUsesUnsupportedLowLevel : Expr → Bool
  | Expr.contractAddress | Expr.chainid => true
  | Expr.mload _ | Expr.keccak256 _ _ => true
  | Expr.call _ _ _ _ _ _ _ => true
  | Expr.staticcall _ _ _ _ _ _ => true
  | Expr.delegatecall _ _ _ _ _ _ => true
  | Expr.returndataSize => true
  | Expr.returndataOptionalBoolAt _ => true
  | Expr.mapping _ key | Expr.mappingWord _ key _ | Expr.mappingPackedWord _ key _ _ | Expr.mappingUint _ key =>
      exprUsesUnsupportedLowLevel key
  | Expr.mapping2 _ key1 key2 =>
      exprUsesUnsupportedLowLevel key1 || exprUsesUnsupportedLowLevel key2
  | Expr.externalCall _ args | Expr.internalCall _ args =>
      exprListUsesUnsupportedLowLevel args
  | Expr.arrayElement _ index =>
      exprUsesUnsupportedLowLevel index
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.mod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.lt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b |
    Expr.wMulDown a b | Expr.wDivUp a b | Expr.min a b | Expr.max a b =>
      exprUsesUnsupportedLowLevel a || exprUsesUnsupportedLowLevel b
  | Expr.mulDivDown a b c | Expr.mulDivUp a b c =>
      exprUsesUnsupportedLowLevel a || exprUsesUnsupportedLowLevel b || exprUsesUnsupportedLowLevel c
  | Expr.bitNot a | Expr.logicalNot a =>
      exprUsesUnsupportedLowLevel a
  | _ =>
      false

def exprListUsesUnsupportedLowLevel : List Expr → Bool
  | [] => false
  | e :: es =>
      exprUsesUnsupportedLowLevel e || exprListUsesUnsupportedLowLevel es

def stmtUsesUnsupportedLowLevel : Stmt → Bool
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value |
    Stmt.return value | Stmt.require value _ =>
      exprUsesUnsupportedLowLevel value
  | Stmt.setMapping _ key value | Stmt.setMappingWord _ key _ value | Stmt.setMappingPackedWord _ key _ _ value | Stmt.setMappingUint _ key value =>
      exprUsesUnsupportedLowLevel key || exprUsesUnsupportedLowLevel value
  | Stmt.setMapping2 _ key1 key2 value =>
      exprUsesUnsupportedLowLevel key1 || exprUsesUnsupportedLowLevel key2 || exprUsesUnsupportedLowLevel value
  | Stmt.requireError cond _ args =>
      exprUsesUnsupportedLowLevel cond || exprListUsesUnsupportedLowLevel args
  | Stmt.revertError _ args | Stmt.emit _ args | Stmt.returnValues args =>
      exprListUsesUnsupportedLowLevel args
  | Stmt.mstore _ _ =>
      true
  | Stmt.returndataCopy _ _ _ | Stmt.revertReturndata =>
      true
  | Stmt.ite cond thenBranch elseBranch =>
      exprUsesUnsupportedLowLevel cond ||
      stmtListUsesUnsupportedLowLevel thenBranch ||
      stmtListUsesUnsupportedLowLevel elseBranch
  | Stmt.forEach _ count body =>
      exprUsesUnsupportedLowLevel count || stmtListUsesUnsupportedLowLevel body
  | Stmt.internalCall _ args =>
      exprListUsesUnsupportedLowLevel args
  | Stmt.internalCallAssign _ _ args =>
      exprListUsesUnsupportedLowLevel args
  | Stmt.rawLog _ _ _ =>
      true
  | Stmt.externalCallBind _ _ args _ value =>
      exprListUsesUnsupportedLowLevel args || exprUsesUnsupportedLowLevel value
  | Stmt.returnArray _ | Stmt.returnBytes _ | Stmt.returnStorageWords _ | Stmt.stop =>
      false

def stmtListUsesUnsupportedLowLevel : List Stmt → Bool
  | [] => false
  | s :: ss =>
      stmtUsesUnsupportedLowLevel s || stmtListUsesUnsupportedLowLevel ss
end

attribute [simp] exprUsesUnsupportedLowLevel exprListUsesUnsupportedLowLevel
attribute [simp] stmtUsesUnsupportedLowLevel stmtListUsesUnsupportedLowLevel

/-!
## Statement Execution

Execute ContractSpec statements, updating storage and context.
Returns None if execution reverts.

The basic `execStmt` / `execStmts` handle most constructs. `Stmt.forEach` and
`Stmt.internalCall` return `none` (revert) in this path — `forEach` because
loop expansion is not structurally decreasing, and `internalCall` because
function lookup requires the `functions` parameter. For contracts that use
these features, use `execStmtsFuel` / `execFunctionFuel`.
-/

-- Execution state
structure ExecState where
  storage : SpecStorage
  returnValue : Option Nat
  halted : Bool
  deriving Repr

-- Execute a single statement
-- Returns updated context and state
-- Note: execStmt and execStmts are mutually recursive because ite branches
-- need to execute a list of statements.
mutual
def execStmt (ctx : EvalContext) (fields : List Field) (paramNames : List String) (externalFns : List (String × (List Nat → Nat))) (state : ExecState) (stmt : Stmt) :
    Option (EvalContext × ExecState) :=
  if stmtUsesUnsupportedLowLevel stmt then
    none
  else match stmt with
  | Stmt.letVar name expr =>
      let value := evalExpr ctx state.storage fields paramNames externalFns expr
      let newVars := (name, value) :: ctx.localVars.filter (·.1 ≠ name)
      some ({ ctx with localVars := newVars }, state)

  | Stmt.assignVar name expr =>
      let value := evalExpr ctx state.storage fields paramNames externalFns expr
      let newVars := (name, value) :: ctx.localVars.filter (·.1 ≠ name)
      some ({ ctx with localVars := newVars }, state)

  | Stmt.setStorage fieldName expr =>
      let value := evalExpr ctx state.storage fields paramNames externalFns expr
      match fields.findIdx? (·.name == fieldName) with
      | some idx =>
          match fields[idx]? with
          | none => none
          | some f =>
              let slot := f.slot.getD idx
              let writeSlots := dedupNatPreserve (slot :: f.aliasSlots)
              let value := value
              match f.packedBits with
              | none =>
                  let storage' := writeSlots.foldl (fun acc writeSlot => acc.setSlot writeSlot value) state.storage
                  some (ctx, { state with storage := storage' })
              | some packed =>
                  let packedValue := Nat.land value (packedMaskNat packed)
                  let shiftedMask := packedShiftedMaskNat packed
                  let clearedMask := wordMask - shiftedMask
                  let storage' := writeSlots.foldl (fun acc writeSlot =>
                    let slotWord := acc.getSlot writeSlot
                    let slotCleared := Nat.land slotWord clearedMask
                    let packedWord := packedValue <<< packed.offset
                    acc.setSlot writeSlot (Nat.lor slotCleared packedWord)
                  ) state.storage
                  some (ctx, { state with storage := storage' })
      | none => none

  | Stmt.setMapping fieldName keyExpr valueExpr
  | Stmt.setMappingUint fieldName keyExpr valueExpr =>
      match fields.findIdx? (·.name == fieldName) with
      | some idx =>
          match fields[idx]? with
          | none => none
          | some f =>
              let baseSlot := f.slot.getD idx
              let writeSlots := dedupNatPreserve (baseSlot :: f.aliasSlots)
              let key := evalExpr ctx state.storage fields paramNames externalFns keyExpr
              let value := evalExpr ctx state.storage fields paramNames externalFns valueExpr
              let storage' := writeSlots.foldl (fun acc writeSlot => acc.setMapping writeSlot key value) state.storage
              some (ctx, { state with storage := storage' })
      | none => none

  | Stmt.setMappingWord fieldName keyExpr wordOffset valueExpr =>
      match fields.findIdx? (·.name == fieldName) with
      | some idx =>
          match fields[idx]? with
          | none => none
          | some f =>
              let baseSlot := f.slot.getD idx
              let writeSlots := dedupNatPreserve (baseSlot :: f.aliasSlots)
              let keyRaw := evalExpr ctx state.storage fields paramNames externalFns keyExpr
              let key := (keyRaw + wordOffset) % modulus
              let value := evalExpr ctx state.storage fields paramNames externalFns valueExpr
              let storage' := writeSlots.foldl (fun acc writeSlot => acc.setMapping writeSlot key value) state.storage
              some (ctx, { state with storage := storage' })
      | none => none

  | Stmt.setMappingPackedWord fieldName keyExpr wordOffset packed valueExpr =>
      if !(packedBitsValid packed) then
        none
      else
        match fields.findIdx? (·.name == fieldName) with
        | some idx =>
            match fields[idx]? with
            | none => none
            | some f =>
                let baseSlot := f.slot.getD idx
                let writeSlots := dedupNatPreserve (baseSlot :: f.aliasSlots)
                let keyRaw := evalExpr ctx state.storage fields paramNames externalFns keyExpr
                let key := (keyRaw + wordOffset) % modulus
                let value := evalExpr ctx state.storage fields paramNames externalFns valueExpr
                let packedValue := Nat.land value (packedMaskNat packed)
                let shiftedMask := packedShiftedMaskNat packed
                let clearedMask := wordMask - shiftedMask
                let storage' := writeSlots.foldl (fun acc writeSlot =>
                  let slotWord := acc.getMapping writeSlot key
                  let slotCleared := Nat.land slotWord clearedMask
                  let packedWord := packedValue <<< packed.offset
                  acc.setMapping writeSlot key (Nat.lor slotCleared packedWord)
                ) state.storage
                some (ctx, { state with storage := storage' })
        | none => none

  | Stmt.setMapping2 fieldName key1Expr key2Expr valueExpr =>
      match fields.findIdx? (·.name == fieldName) with
      | some idx =>
          match fields[idx]? with
          | none => none
          | some f =>
              let baseSlot := f.slot.getD idx
              let writeSlots := dedupNatPreserve (baseSlot :: f.aliasSlots)
              let key1 := evalExpr ctx state.storage fields paramNames externalFns key1Expr
              let key2 := evalExpr ctx state.storage fields paramNames externalFns key2Expr
              let value := evalExpr ctx state.storage fields paramNames externalFns valueExpr
              let storage' :=
                writeSlots.foldl (fun acc writeSlot => acc.setMapping2 writeSlot key1 key2 value) state.storage
              some (ctx, { state with storage := storage' })
      | none => none

  | Stmt.require condExpr _message =>
      let cond := evalExpr ctx state.storage fields paramNames externalFns condExpr
      if cond ≠ 0 then some (ctx, state) else none

  | Stmt.requireError condExpr _errorName _args =>
      let cond := evalExpr ctx state.storage fields paramNames externalFns condExpr
      if cond ≠ 0 then some (ctx, state) else none

  | Stmt.revertError _errorName _args =>
      none

  | Stmt.return expr =>
      let value := evalExpr ctx state.storage fields paramNames externalFns expr
      some (ctx, { state with returnValue := some value, halted := true })

  | Stmt.returnValues values =>
      let first := (evalExprs ctx state.storage fields paramNames externalFns values).head?
      some (ctx, { state with returnValue := first, halted := true })

  | Stmt.returnArray _name =>
      -- The spec interpreter models scalar returnValue only.
      -- Dynamic-array return encoding is a codegen concern.
      some (ctx, { state with returnValue := none, halted := true })

  | Stmt.returnBytes _name =>
      -- The spec interpreter models scalar returnValue only.
      -- Dynamic-bytes return encoding is a codegen concern.
      some (ctx, { state with returnValue := none, halted := true })

  | Stmt.returnStorageWords _name =>
      -- The spec interpreter models scalar returnValue only.
      -- Dynamic array return encoding/storage reads are codegen concerns.
      some (ctx, { state with returnValue := none, halted := true })

  | Stmt.mstore _offset _value =>
      -- Memory writes are not modeled in the scalar SpecInterpreter.
      none

  | Stmt.returndataCopy _destOffset _sourceOffset _size =>
      -- Returndata memory effects are not modeled in the scalar SpecInterpreter.
      some (ctx, state)

  | Stmt.revertReturndata =>
      none

  | Stmt.stop =>
      some (ctx, { state with halted := true })

  | Stmt.ite cond thenBranch elseBranch =>
      let condVal := evalExpr ctx state.storage fields paramNames externalFns cond
      if condVal ≠ 0 then
        execStmts ctx fields paramNames externalFns state thenBranch
      else
        execStmts ctx fields paramNames externalFns state elseBranch

  | Stmt.forEach _varName _count _body =>
      -- forEach requires fuel-based execution for termination (the expanded loop
      -- body is not structurally smaller). Use execStmtsFuel / execFunctionFuel
      -- for contracts with loops. Revert instead of silently skipping the loop
      -- body.
      none

  | Stmt.emit eventName args =>
      let argVals := args.map (evalExpr ctx state.storage fields paramNames externalFns ·)
      some (ctx, { state with storage := state.storage.addEvent eventName argVals })

  | Stmt.internalCall _functionName _args =>
      -- Internal calls require function lookup (the `functions` parameter).
      -- The basic interpreter does not carry function definitions, so revert
      -- instead of silently producing wrong results. Use execStmtsFuel for
      -- contracts with internal calls.
      none
  | Stmt.internalCallAssign _names _functionName _args =>
      -- Multi-value internal-call bindings are only modeled in compiler/codegen.
      -- The basic interpreter does not model tuple return values.
      none
  | Stmt.externalCallBind _resultVars _externalName _args _isStatic _value =>
      -- External call bindings require linked Yul; not modeled in the basic interpreter.
      none

  | Stmt.rawLog _topics _dataOffset _dataSize =>
      -- Raw log emission requires memory model not available in the scalar
      -- SpecInterpreter. Revert instead of silently skipping.
      none

-- Execute a list of statements sequentially
-- Thread both context and state through the computation
-- Stop early if return/stop is encountered (halted = true)
def execStmts (ctx : EvalContext) (fields : List Field) (paramNames : List String) (externalFns : List (String × (List Nat → Nat))) (state : ExecState) (stmts : List Stmt) :
    Option (EvalContext × ExecState) :=
  match stmts with
  | [] => some (ctx, state)
  | stmt :: rest =>
    if state.halted then some (ctx, state)
    else match execStmt ctx fields paramNames externalFns state stmt with
      | none => none
      | some (ctx', state') => execStmts ctx' fields paramNames externalFns state' rest
end

/-!
### Fuel-based execution for contracts with loops and internal calls

For contracts that use `forEach` or `internalCall`, we provide a fuel-based
interpreter that properly handles bounded loops and recursive function calls.
The fuel decreases at each recursive step.

The `functions` parameter carries the full list of `FunctionSpec` entries from
the `ContractSpec`, enabling lookup and execution of internal functions (#181).
-/

-- Helper: Expand a forEach into N copies of the loop body with let bindings
private def expandForEach (varName : String) (count : Nat) (body : List Stmt) : List Stmt :=
  let bound := min count 10000
  let rec go (i : Nat) (acc : List Stmt) : List Stmt :=
    if _h : i >= bound then acc
    else go (i + 1) (acc ++ [Stmt.letVar varName (Expr.literal i)] ++ body)
  termination_by bound - i
  go 0 []

def execStmtsFuel (fuel : Nat) (ctx : EvalContext) (fields : List Field) (paramNames : List String) (externalFns : List (String × (List Nat → Nat)))
    (functions : List FunctionSpec)
    (state : ExecState) (stmts : List Stmt) : Option (EvalContext × ExecState) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match stmts with
    | [] => some (ctx, state)
    | stmt :: rest =>
      if state.halted then some (ctx, state)
      else
        let result := match stmt with
          | Stmt.forEach varName count body =>
              -- Desugar forEach into expanded statements
              if exprUsesUnsupportedLowLevel count then
                none
              else
              let countVal := evalExpr ctx state.storage fields paramNames externalFns count
              let expanded := expandForEach varName countVal body
              execStmtsFuel fuel' ctx fields paramNames externalFns functions state expanded
          | Stmt.ite cond thenBranch elseBranch =>
              if exprUsesUnsupportedLowLevel cond then
                none
              else
              let condVal := evalExpr ctx state.storage fields paramNames externalFns cond
              if condVal ≠ 0 then
                execStmtsFuel fuel' ctx fields paramNames externalFns functions state thenBranch
              else
                execStmtsFuel fuel' ctx fields paramNames externalFns functions state elseBranch
          | Stmt.internalCall functionName args =>
              if args.any exprUsesUnsupportedLowLevel then
                none
              else
              -- Look up the internal function and execute its body (#181)
              match functions.find? (·.name == functionName) with
              | none => none  -- Unknown function → revert
              | some func =>
                  -- Evaluate arguments in the caller's context
                  let argVals := evalExprs ctx state.storage fields paramNames externalFns args
                  -- Set up callee context with proper parameter binding:
                  -- params/paramTypes hold the callee's arguments (for Expr.param lookup),
                  -- localVars is fresh (callee has its own scope)
                  let calleeParamNames := func.params.map (·.name)
                  let calleeCtx : EvalContext := {
                    ctx with
                    params := argVals
                    paramTypes := func.params.map (·.ty)
                    localVars := []
                  }
                  -- Execute callee body with unhaltable state (callee's return/stop
                  -- should not terminate the caller)
                  let calleeState := { state with halted := false, returnValue := none }
                  match execStmtsFuel fuel' calleeCtx fields calleeParamNames externalFns functions calleeState func.body with
                  | none => none
                  | some (_, calleeResult) =>
                      -- Propagate only storage and events; restore caller's halted/return state
                      some (ctx, { state with storage := calleeResult.storage })
          | Stmt.internalCallAssign _names _functionName _args =>
              -- Fuel-based interpreter does not model tuple-valued internal call bindings yet.
              none
          | Stmt.externalCallBind _resultVars _externalName _args _isStatic _value =>
              -- External call bindings require linked Yul; not modeled in fuel-based interpreter.
              none
          | other => execStmt ctx fields paramNames externalFns state other
        match result with
        | none => none
        | some (ctx', state') => execStmtsFuel fuel' ctx' fields paramNames externalFns functions state' rest
termination_by fuel

/-!
## Function Execution

Execute a function from a ContractSpec.

`execFunction` / `execConstructor` use the basic `execStmts` path, which handles
all constructs except `Stmt.forEach` and `Stmt.internalCall` (both revert).
These are kept for backward compatibility with existing proofs.

`execFunctionFuel` / `execConstructorFuel` use the fuel-based `execStmtsFuel` path,
which fully supports `forEach`, `Stmt.internalCall`, and all features. Use these
for contracts that use loops or internal function calls.
-/

def execFunction (spec : ContractSpec) (funcName : String) (ctx : EvalContext) (externalFns : List (String × (List Nat → Nat)))
    (initialStorage : SpecStorage) : Option (EvalContext × ExecState) :=
  match spec.functions.find? (·.name == funcName) with
  | none => none
  | some func =>
      if specHasUnmodeledExternals spec externalFns then
        none
      else
        let fields := resolveFields spec
        let ctx := { ctx with paramTypes := func.params.map (·.ty) }
        let initialState : ExecState := {
          storage := initialStorage
          returnValue := none
          halted := false
        }
        let paramNames := func.params.map (·.name)
        execStmts ctx fields paramNames externalFns initialState func.body

def execConstructor (spec : ContractSpec) (ctx : EvalContext) (externalFns : List (String × (List Nat → Nat)))
    (initialStorage : SpecStorage) : Option (EvalContext × ExecState) :=
  match spec.constructor with
  | none => some (ctx, { storage := initialStorage, returnValue := none, halted := false })
  | some ctor =>
      if specHasUnmodeledExternals spec externalFns then
        none
      else
        let fields := resolveFields spec
        let ctx := { ctx with constructorParamTypes := ctor.params.map (·.ty) }
        let initialState : ExecState := {
          storage := initialStorage
          returnValue := none
          halted := false
        }
        let paramNames := ctor.params.map (·.name)
        execStmts ctx fields paramNames externalFns initialState ctor.body

/-- Execute a function using the fuel-based interpreter that supports all features
    including forEach loops and internal function calls. Default fuel of 10000
    is sufficient for most contracts. -/
def execFunctionFuel (spec : ContractSpec) (funcName : String) (ctx : EvalContext)
    (externalFns : List (String × (List Nat → Nat)))
    (initialStorage : SpecStorage) (fuel : Nat := 10000) : Option (EvalContext × ExecState) :=
  match spec.functions.find? (·.name == funcName) with
  | none => none
  | some func =>
      if specHasUnmodeledExternals spec externalFns then
        none
      else
        let fields := resolveFields spec
        let ctx := { ctx with paramTypes := func.params.map (·.ty) }
        let initialState : ExecState := {
          storage := initialStorage
          returnValue := none
          halted := false
        }
        let paramNames := func.params.map (·.name)
        execStmtsFuel fuel ctx fields paramNames externalFns spec.functions initialState func.body

/-- Execute a constructor using the fuel-based interpreter that supports all features
    including forEach loops and internal function calls. Default fuel of 10000
    is sufficient for most contracts. -/
def execConstructorFuel (spec : ContractSpec) (ctx : EvalContext)
    (externalFns : List (String × (List Nat → Nat)))
    (initialStorage : SpecStorage) (fuel : Nat := 10000) : Option (EvalContext × ExecState) :=
  match spec.constructor with
  | none => some (ctx, { storage := initialStorage, returnValue := none, halted := false })
  | some ctor =>
      if specHasUnmodeledExternals spec externalFns then
        none
      else
        let fields := resolveFields spec
        let ctx := { ctx with constructorParamTypes := ctor.params.map (·.ty) }
        let initialState : ExecState := {
          storage := initialStorage
          returnValue := none
          halted := false
        }
        let paramNames := ctor.params.map (·.name)
        execStmtsFuel fuel ctx fields paramNames externalFns spec.functions initialState ctor.body

/-!
## Top-Level Interpreter
-/

structure SpecResult where
  success : Bool
  returnValue : Option Nat
  revertReason : Option String
  finalStorage : SpecStorage
  deriving Repr

def interpretSpec (spec : ContractSpec) (initialStorage : SpecStorage) (tx : Transaction)
    (externalFns : List (String × (List Nat → Nat)) := []) : SpecResult :=
  if tx.functionName == "" then
    let ctx : EvalContext := {
      sender := tx.sender
      msgValue := tx.msgValue
      blockTimestamp := tx.blockTimestamp
      params := []
      paramTypes := []
      constructorArgs := tx.args
      constructorParamTypes := []
      localVars := []
      arrayParams := []
    }
    match execConstructor spec ctx externalFns initialStorage with
    | none =>
        { success := false, returnValue := none,
          revertReason := some "Constructor reverted", finalStorage := initialStorage }
    | some (_, finalState) =>
        { success := true, returnValue := finalState.returnValue,
          revertReason := none, finalStorage := finalState.storage }
  else
    let ctx : EvalContext := {
      sender := tx.sender
      msgValue := tx.msgValue
      blockTimestamp := tx.blockTimestamp
      params := tx.args
      paramTypes := []
      constructorArgs := []
      constructorParamTypes := []
      localVars := []
      arrayParams := []
    }
    match execFunction spec tx.functionName ctx externalFns initialStorage with
    | none =>
        { success := false, returnValue := none,
          revertReason := some s!"Function '{tx.functionName}' reverted",
          finalStorage := initialStorage }
    | some (_, finalState) =>
        { success := true, returnValue := finalState.returnValue,
          revertReason := none, finalStorage := finalState.storage }

end Verity.Proofs.Stdlib.SpecInterpreter
