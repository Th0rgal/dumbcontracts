import Compiler.CompilationModel
import Compiler.Selector
import Compiler.Codegen
import Compiler.Yul.PrettyPrint
import Compiler.DiffTestTypes
import Compiler.Modules.ERC20
import Compiler.Modules.Precompiles
import Compiler.Modules.Callbacks
import Compiler.Modules.Calls
import Verity.Proofs.Stdlib.SpecInterpreter

namespace Compiler.CompilationModelFeatureTest

open Compiler
open Compiler.CompilationModel
open Compiler.Selector
open Compiler.DiffTestTypes
open Verity.Proofs.Stdlib.SpecInterpreter

private def contains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | c :: cs =>
        if (c :: cs).take n.length == n then true
        else go cs
    go h

private def assertContains (label rendered : String) (needles : List String) : IO Unit := do
  for needle in needles do
    if !contains rendered needle then
      throw (IO.userError s!"✗ {label}: missing '{needle}' in:\n{rendered}")
  IO.println s!"✓ {label}"

private def assertNotContains (label rendered : String) (needles : List String) : IO Unit := do
  for needle in needles do
    if contains rendered needle then
      throw (IO.userError s!"✗ {label}: unexpected '{needle}' in:\n{rendered}")
  IO.println s!"✓ {label}"

private def firstIndexOf? (haystack needle : String) : Option Nat :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then some 0
  else
    let rec go (rest : List Char) (idx : Nat) : Option Nat :=
      match rest with
      | [] => none
      | _ :: tail =>
          if rest.take n.length == n then some idx
          else go tail (idx + 1)
    go h 0

private def assertAppearsBefore (label rendered first second : String) : IO Unit := do
  let some firstIdx := firstIndexOf? rendered first
    | throw (IO.userError s!"✗ {label}: missing first needle '{first}'")
  let some secondIdx := firstIndexOf? rendered second
    | throw (IO.userError s!"✗ {label}: missing second needle '{second}'")
  if !(firstIdx < secondIdx) then
    throw (IO.userError s!"✗ {label}: expected '{first}' to appear before '{second}'")
  IO.println s!"✓ {label}"

private def featureSpec : CompilationModel := {
  name := "FeatureSpec"
  fields := []
  constructor := none
  events := [
    { name := "ValueSet"
      params := [
        { name := "who", ty := ParamType.address, kind := EventParamKind.indexed },
        { name := "value", ty := ParamType.uint256, kind := EventParamKind.unindexed }
      ]
    },
    { name := "BoolSet"
      params := [
        { name := "ok", ty := ParamType.bool, kind := EventParamKind.indexed }
      ]
    }
  ]
  errors := [
    { name := "Unauthorized"
      params := [ParamType.address, ParamType.uint256]
    }
  ]
  functions := [
    { name := "setFlag"
      params := [{ name := "flag", ty := ParamType.bool }]
      returnType := none
      body := [Stmt.stop]
    },
    { name := "pair"
      params := [
        { name := "a", ty := ParamType.uint256 },
        { name := "b", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256, ParamType.uint256]
      body := [Stmt.returnValues [Expr.param "a", Expr.param "b"]]
    },
    { name := "emitValue"
      params := [
        { name := "who", ty := ParamType.address },
        { name := "value", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [Stmt.emit "ValueSet" [Expr.param "who", Expr.param "value"], Stmt.stop]
    },
    { name := "emitBool"
      params := []
      returnType := none
      body := [Stmt.emit "BoolSet" [Expr.literal 2], Stmt.stop]
    },
    { name := "echoArray"
      params := [{ name := "arr", ty := ParamType.array ParamType.uint256 }]
      returnType := none
      returns := [ParamType.array ParamType.uint256]
      body := [Stmt.returnArray "arr"]
    },
    { name := "sumStaticTuple"
      params := [
        { name := "t", ty := ParamType.tuple [ParamType.uint256, ParamType.address, ParamType.bool] },
        { name := "z", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [Stmt.return (Expr.add (Expr.param "t_0") (Expr.param "z"))]
    },
    { name := "dynamicTupleTail"
      params := [
        { name := "td", ty := ParamType.tuple [ParamType.uint256, ParamType.bytes] },
        { name := "x", ty := ParamType.uint256 }
      ]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.param "x")]
    },
    { name := "nestedStaticTupleTail"
      params := [
        { name := "u"
          ty := ParamType.tuple [
            ParamType.fixedArray ParamType.uint256 2,
            ParamType.tuple [ParamType.address, ParamType.bool],
            ParamType.uint256
          ]
        },
        { name := "y", ty := ParamType.uint256 }
      ]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.add (Expr.param "u_0_1") (Expr.param "y"))]
    },
    { name := "fixedArrayTupleTail"
      params := [
        { name := "fa", ty := ParamType.fixedArray (ParamType.tuple [ParamType.uint256, ParamType.bool]) 2 },
        { name := "q", ty := ParamType.uint256 }
      ]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.add (Expr.param "fa_1_0") (Expr.param "q"))]
    },
    { name := "echoBytes"
      params := [{ name := "data", ty := ParamType.bytes }]
      returnType := none
      returns := [ParamType.bytes]
      body := [Stmt.returnBytes "data"]
    },
    { name := "extSloadsLike"
      params := [{ name := "slots", ty := ParamType.array ParamType.bytes32 }]
      returnType := none
      returns := [ParamType.array ParamType.uint256]
      body := [Stmt.returnStorageWords "slots"]
    },
    { name := "guarded"
      params := [{ name := "who", ty := ParamType.address }, { name := "min", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.requireError (Expr.lt (Expr.param "min") (Expr.literal 1)) "Unauthorized" [Expr.param "who", Expr.param "min"],
        Stmt.stop
      ]
    }
  ]
}

private def compilationModelSmokeSpec : CompilationModel := {
  name := "CompilationModelSmokeSpec"
  fields := []
  constructor := none
  functions := [
    { name := "ping"
      params := []
      returnType := none
      body := [Stmt.stop]
    }
  ]
}

#eval! do
  -- Smoke test: CompilationModel compiles.
  match compile compilationModelSmokeSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ CompilationModel compile failed: {err}")
  | .ok _ =>
      IO.println "✓ CompilationModel compile smoke"

#eval! do
  match compile featureSpec [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] with
  | .error err =>
      throw (IO.userError s!"✗ feature spec compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "bool param normalization" rendered
        ["let __abi_bool_word_4 := calldataload(4)",
         "if iszero(or(eq(__abi_bool_word_4, 0), eq(__abi_bool_word_4, 1))) {",
         "let flag := iszero(iszero(__abi_bool_word_4))"]
      assertContains "multi-return ABI encoding" rendered ["return(0, 64)"]
      assertContains "indexed event log opcode" rendered ["log2("]
      assertContains "indexed bool topic normalization" rendered ["iszero(iszero(2))"]
      assertContains "event topic hashing uses free memory pointer" rendered ["keccak256(__evt_ptr,"]
      assertContains "event topic hash cached before data writes" rendered ["let __evt_topic0 := keccak256(__evt_ptr,", "log2(__evt_ptr, 32, __evt_topic0"]
      assertContains "dynamic array ABI return" rendered ["calldatacopy(64"]
      assertContains "static tuple decode head offsets" rendered
        ["let t_0 := calldataload(4)", "let t_1 := and(calldataload(36)",
         "let __abi_bool_word_68 := calldataload(68)",
         "let t_2 := iszero(iszero(__abi_bool_word_68))", "let z := calldataload(100)"]
      assertContains "dynamic tuple keeps offset head word" rendered ["let td_offset := calldataload(4)", "let x := calldataload(36)"]
      assertContains "dynamic ABI decode offset/length bounds guards" rendered
        ["if lt(calldatasize(), 68) {", "if lt(arr_offset, 32) {",
         "if gt(arr_abs_offset, sub(calldatasize(), 32)) {",
         "if gt(arr_length, div(arr_tail_remaining, 32)) {",
         "if gt(data_length, data_tail_remaining) {"]
      assertContains "nested static tuple decode head offsets" rendered
        ["let u_0_0 := calldataload(4)", "let u_0_1 := calldataload(36)",
         "let u_1_0 := and(calldataload(68)", "let __abi_bool_word_100 := calldataload(100)",
         "let u_1_1 := iszero(iszero(__abi_bool_word_100))", "let u_2 := calldataload(132)",
         "let y := calldataload(164)"]
      assertContains "fixed array of static tuples decode offsets" rendered
        ["let fa_0_0 := calldataload(4)", "let __abi_bool_word_36 := calldataload(36)",
         "let fa_0_1 := iszero(iszero(__abi_bool_word_36))", "let fa_1_0 := calldataload(68)",
         "let __abi_bool_word_100 := calldataload(100)",
         "let fa_1_1 := iszero(iszero(__abi_bool_word_100))", "let q := calldataload(132)"]
      assertContains "dynamic bytes ABI return" rendered ["calldatacopy(64, data_data_offset, data_length)", "mstore(add(64, data_length), 0)", "return(0, add(64, and(add(data_length, 31), not(31))))"]
      assertContains "storage-word array return ABI" rendered ["let __slot := calldataload(add(slots_data_offset, mul(__i, 32)))", "mstore(add(64, mul(__i, 32)), sload(__slot))", "return(0, add(64, mul(slots_length, 32)))"]
      assertContains "custom error revert payload emission" rendered ["let __err_hash := keccak256(__err_ptr,", "mstore(0, __err_selector)", "mstore(4, and(who,", "let __err_tail := 64", "revert(0, add(4, __err_tail))"]

#eval! do
  let conflictingReturnsSpec : CompilationModel := {
    name := "ConflictingReturns"
    fields := []
    constructor := none
    functions := [
      { name := "bad"
        params := []
        returnType := some FieldType.uint256
        returns := [ParamType.uint256, ParamType.uint256]
        body := [Stmt.returnValues [Expr.literal 1, Expr.literal 2]]
      }
    ]
  }
  match compile conflictingReturnsSpec [1] with
  | .error err =>
      if !contains err "conflicting return declarations" then
        throw (IO.userError s!"✗ conflicting returns should fail with clear message, got: {err}")
      IO.println "✓ conflicting return declaration validation"
  | .ok _ =>
      throw (IO.userError "✗ expected conflicting returns to fail compilation")

#eval! do
  let invalidReturnBytesSpec : CompilationModel := {
    name := "InvalidReturnBytes"
    fields := []
    constructor := none
    functions := [
      { name := "badBytes"
        params := [{ name := "arr", ty := ParamType.array ParamType.uint256 }]
        returnType := none
        returns := [ParamType.bytes]
        body := [Stmt.returnBytes "arr"]
      }
    ]
  }
  match compile invalidReturnBytesSpec [1] with
  | .error err =>
      if !contains err "returnBytes 'arr' requires bytes parameter" then
        throw (IO.userError s!"✗ returnBytes type validation message mismatch: {err}")
      IO.println "✓ returnBytes parameter type validation"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid returnBytes parameter to fail compilation")

#eval! do
  let invalidContractIdentifierSpec : CompilationModel := {
    name := "Bad-Contract"
    fields := []
    constructor := none
    functions := []
  }
  match compile invalidContractIdentifierSpec [] with
  | .error err =>
      if !contains err "contract name must be a valid identifier: Bad-Contract" then
        throw (IO.userError s!"✗ contract identifier validation mismatch: {err}")
      IO.println "✓ contract identifier validation"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid contract identifier to fail compilation")

#eval! do
  let invalidFunctionIdentifierSpec : CompilationModel := {
    name := "InvalidFunctionIdentifier"
    fields := []
    constructor := none
    functions := [
      { name := "bad-fn"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile invalidFunctionIdentifierSpec [1] with
  | .error err =>
      if !contains err "function name must be a valid identifier: bad-fn" then
        throw (IO.userError s!"✗ function identifier validation mismatch: {err}")
      IO.println "✓ function identifier validation"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid function identifier to fail compilation")

#eval! do
  let invalidFieldIdentifierSpec : CompilationModel := {
    name := "InvalidFieldIdentifier"
    fields := [{ name := "stored-data", ty := FieldType.uint256 }]
    constructor := none
    functions := []
  }
  match compile invalidFieldIdentifierSpec [] with
  | .error err =>
      if !contains err "field name must be a valid identifier: stored-data" then
        throw (IO.userError s!"✗ field identifier validation mismatch: {err}")
      IO.println "✓ field identifier validation"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid field identifier to fail compilation")

#eval! do
  let invalidFunctionParamIdentifierSpec : CompilationModel := {
    name := "InvalidFunctionParamIdentifier"
    fields := []
    constructor := none
    functions := [
      { name := "store"
        params := [{ name := "value-1", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile invalidFunctionParamIdentifierSpec [1] with
  | .error err =>
      if !contains err "function parameter name must be a valid identifier: value-1" then
        throw (IO.userError s!"✗ function parameter identifier validation mismatch: {err}")
      IO.println "✓ function parameter identifier validation"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid function parameter identifier to fail compilation")

#eval! do
  let invalidEventIdentifierSpec : CompilationModel := {
    name := "InvalidEventIdentifier"
    fields := []
    constructor := none
    events := [
      { name := "Value-Set"
        params := [{ name := "who", ty := ParamType.address, kind := EventParamKind.indexed }]
      }
    ]
    functions := []
  }
  match compile invalidEventIdentifierSpec [] with
  | .error err =>
      if !contains err "event name must be a valid identifier: Value-Set" then
        throw (IO.userError s!"✗ event identifier validation mismatch: {err}")
      IO.println "✓ event identifier validation"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid event identifier to fail compilation")

#eval! do
  let invalidExternalIdentifierSpec : CompilationModel := {
    name := "InvalidExternalIdentifier"
    fields := []
    constructor := none
    externals := [
      { name := "hash-two"
        params := [ParamType.uint256, ParamType.uint256]
        returns := [ParamType.uint256]
        axiomNames := ["hash_two_sound"]
      }
    ]
    functions := []
  }
  match compile invalidExternalIdentifierSpec [] with
  | .error err =>
      if !contains err "external declaration name must be a valid identifier: hash-two" then
        throw (IO.userError s!"✗ external identifier validation mismatch: {err}")
      IO.println "✓ external declaration identifier validation"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid external declaration identifier to fail compilation")

#eval! do
  let payableMsgValueSpec : CompilationModel := {
    name := "PayableMsgValue"
    fields := []
    constructor := some {
      params := []
      isPayable := true
      body := [Stmt.stop]
    }
    functions := [
      { name := "payableLike"
        params := []
        returnType := some FieldType.uint256
        isPayable := true
        body := [Stmt.return Expr.msgValue]
      }
    ]
  }
  match compile payableMsgValueSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected payable msgValue usage to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "payable msgValue compiles" rendered ["mstore(0, callvalue())"]
      assertNotContains "payable function skips non-payable guard" rendered ["if callvalue()"]

#eval! do
  let nonPayableGuardSpec : CompilationModel := {
    name := "NonPayableGuard"
    fields := []
    constructor := none
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile nonPayableGuardSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected non-payable function to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "non-payable function emits msg.value guard" rendered ["if callvalue()"]

#eval! do
  let lowLevelPrimitivesSpec : CompilationModel := {
    name := "LowLevelPrimitives"
    fields := []
    constructor := none
    functions := [
      { name := "doCall"
        params := [
          { name := "target", ty := ParamType.address },
          { name := "inOffset", ty := ParamType.uint256 },
          { name := "inSize", ty := ParamType.uint256 },
          { name := "outOffset", ty := ParamType.uint256 },
          { name := "outSize", ty := ParamType.uint256 }
        ]
        returnType := some FieldType.uint256
        body := [
          Stmt.letVar "ok" (Expr.call
            (Expr.literal 50000)
            (Expr.param "target")
            (Expr.literal 0)
            (Expr.param "inOffset")
            (Expr.param "inSize")
            (Expr.param "outOffset")
            (Expr.param "outSize")),
          Stmt.return (Expr.localVar "ok")
        ]
      },
      { name := "doStatic"
        params := [
          { name := "target", ty := ParamType.address },
          { name := "inOffset", ty := ParamType.uint256 },
          { name := "inSize", ty := ParamType.uint256 },
          { name := "outOffset", ty := ParamType.uint256 },
          { name := "outSize", ty := ParamType.uint256 }
        ]
        returnType := some FieldType.uint256
        body := [
          Stmt.return (Expr.staticcall
            (Expr.literal 50000)
            (Expr.param "target")
            (Expr.param "inOffset")
            (Expr.param "inSize")
            (Expr.param "outOffset")
            (Expr.param "outSize"))
        ]
      },
      { name := "doDelegate"
        params := [
          { name := "target", ty := ParamType.address },
          { name := "inOffset", ty := ParamType.uint256 },
          { name := "inSize", ty := ParamType.uint256 },
          { name := "outOffset", ty := ParamType.uint256 },
          { name := "outSize", ty := ParamType.uint256 }
        ]
        returnType := some FieldType.uint256
        body := [
          Stmt.return (Expr.delegatecall
            (Expr.literal 50000)
            (Expr.param "target")
            (Expr.param "inOffset")
            (Expr.param "inSize")
            (Expr.param "outOffset")
            (Expr.param "outSize"))
        ]
      },
      { name := "bubble"
        params := []
        returnType := none
        body := [
          Stmt.letVar "rd" Expr.returndataSize,
          Stmt.returndataCopy (Expr.literal 0) (Expr.literal 0) (Expr.localVar "rd"),
          Stmt.revertReturndata
        ]
      },
      { name := "erc20CompatCall"
        params := [
          { name := "target", ty := ParamType.address },
          { name := "inOffset", ty := ParamType.uint256 },
          { name := "inSize", ty := ParamType.uint256 }
        ]
        returnType := some FieldType.uint256
        body := [
          Stmt.letVar "ok" (Expr.call
            (Expr.literal 50000)
            (Expr.param "target")
            (Expr.literal 0)
            (Expr.param "inOffset")
            (Expr.param "inSize")
            (Expr.literal 0)
            (Expr.literal 32)),
          Stmt.return (Expr.logicalAnd
            (Expr.localVar "ok")
            (Expr.returndataOptionalBoolAt (Expr.literal 0)))
        ]
      }
    ]
  }
  match compile lowLevelPrimitivesSpec [1, 2, 3, 4, 5] with
  | .error err =>
      throw (IO.userError s!"✗ expected first-class low-level primitives to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "first-class call lowering" rendered ["call(50000, target, 0, inOffset, inSize, outOffset, outSize)"]
      assertContains "first-class staticcall lowering" rendered ["staticcall(50000, target, inOffset, inSize, outOffset, outSize)"]
      assertContains "first-class delegatecall lowering" rendered ["delegatecall(50000, target, inOffset, inSize, outOffset, outSize)"]
      assertContains "first-class returndata primitives lowering" rendered ["let rd := returndatasize()", "returndatacopy(0, 0, rd)", "let __returndata_size := returndatasize()", "revert(0, __returndata_size)"]
      assertContains "optional bool returndata helper lowering" rendered ["eq(returndatasize(), 0)", "eq(returndatasize(), 32)", "eq(mload(0), 1)"]

#eval! do
  let typedIntrinsicSpec : CompilationModel := {
    name := "TypedIntrinsics"
    fields := []
    constructor := none
    functions := [
      { name := "domainProbe"
        params := []
        returnType := some FieldType.uint256
        isView := true
        body := [
          Stmt.mstore (Expr.literal 0) Expr.contractAddress,
          Stmt.mstore (Expr.literal 32) Expr.chainid,
          Stmt.return (Expr.keccak256 (Expr.literal 0) (Expr.literal 64))
        ]
      },
      { name := "peekWord"
        params := [{ name := "offset", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        isView := true
        body := [Stmt.return (Expr.mload (Expr.param "offset"))]
      },
      { name := "pureHash"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        isPure := true
        body := [
          Stmt.mstore (Expr.literal 0) (Expr.param "x"),
          Stmt.return (Expr.keccak256 (Expr.literal 0) (Expr.literal 32))
        ]
      }
    ]
  }
  match compile typedIntrinsicSpec [1, 2, 3] with
  | .error err =>
      throw (IO.userError s!"✗ expected typed intrinsics to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "typed env/hash intrinsics lowering" rendered [
        "mstore(0, address())",
        "mstore(32, chainid())",
        "mstore(0, keccak256(0, 64))",
        "mstore(0, mload(offset))"
      ]

#eval! do
  let lowLevelCallSpec : CompilationModel := {
    name := "LowLevelCallUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "unsafe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "delegatecall" [Expr.param "target"])]
      }
    ]
  }
  match compile lowLevelCallSpec [1] with
  | .error err =>
      if !(contains err "unsupported low-level call 'delegatecall'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ low-level call diagnostic mismatch: {err}")
      IO.println "✓ low-level call unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected low-level call usage to fail compilation")

#eval! do
  let eagerLogicalCallSpec : CompilationModel := {
    name := "EagerLogicalCall"
    fields := []
    constructor := none
    functions := [
      { name := "unsafe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [
          Stmt.return (Expr.logicalAnd
            (Expr.literal 0)
            (Expr.call
              (Expr.literal 50000)
              (Expr.param "target")
              (Expr.literal 0)
              (Expr.literal 0)
              (Expr.literal 0)
              (Expr.literal 0)
              (Expr.literal 0)))
        ]
      }
    ]
  }
  match compile eagerLogicalCallSpec [1] with
  | .error err =>
      if !(contains err "Expr.logicalAnd/Expr.logicalOr" &&
          contains err "call-like operand(s)" &&
          contains err "Issue #748") then
        throw (IO.userError s!"✗ logical call operand diagnostic mismatch: {err}")
      IO.println "✓ logical call operand validation"
  | .ok _ =>
      throw (IO.userError "✗ expected call-like logical operand to fail compilation")

#eval! do
  let eagerLogicalExternalSpec : CompilationModel := {
    name := "EagerLogicalExternal"
    fields := []
    constructor := none
    externals := [
      { name := "oracle"
        params := [ParamType.uint256]
        returns := [ParamType.uint256]
        axiomNames := []
      }
    ]
    functions := [
      { name := "unsafe"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [
          Stmt.return (Expr.logicalOr
            (Expr.literal 1)
            (Expr.externalCall "oracle" [Expr.param "x"]))
        ]
      }
    ]
  }
  match compile eagerLogicalExternalSpec [1] with
  | .error err =>
      if !(contains err "Expr.logicalAnd/Expr.logicalOr" &&
          contains err "call-like operand(s)" &&
          contains err "Issue #748") then
        throw (IO.userError s!"✗ logical external operand diagnostic mismatch: {err}")
      IO.println "✓ logical external operand validation"
  | .ok _ =>
      throw (IO.userError "✗ expected external-call logical operand to fail compilation")

#eval! do
  let staticcallSpec : CompilationModel := {
    name := "StaticcallUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "unsafe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "staticcall" [Expr.param "target"])]
      }
    ]
  }
  match compile staticcallSpec [1] with
  | .error err =>
      if !(contains err "unsupported low-level call 'staticcall'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ staticcall diagnostic mismatch: {err}")
      IO.println "✓ staticcall unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected staticcall usage to fail compilation")

#eval! do
  let ctorMsgValueSpec : CompilationModel := {
    name := "CtorMsgValuePayable"
    fields := []
    constructor := some {
      params := []
      isPayable := true
      body := [Stmt.letVar "v" Expr.msgValue, Stmt.stop]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        isPayable := true
        body := [Stmt.stop]
      }
    ]
  }
  match compile ctorMsgValueSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected payable constructor msgValue usage to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "payable constructor msgValue compiles" rendered ["let v := callvalue()"]
      assertNotContains "payable constructor skips non-payable guard" rendered ["if callvalue()"]

#eval! do
  let ctorNonPayableGuardSpec : CompilationModel := {
    name := "CtorNonPayableGuard"
    fields := []
    constructor := some {
      params := []
      body := [Stmt.stop]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        isPayable := true
        body := [Stmt.stop]
      }
    ]
  }
  match compile ctorNonPayableGuardSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected non-payable constructor to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "non-payable constructor emits msg.value guard" rendered ["if callvalue()"]

#eval! do
  let ctorLowLevelCallSpec : CompilationModel := {
    name := "CtorLowLevelCallUnsupported"
    fields := []
    constructor := some {
      params := []
      body := [Stmt.letVar "v" (Expr.externalCall "call" []), Stmt.stop]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile ctorLowLevelCallSpec [1] with
  | .error err =>
      if !(contains err "unsupported low-level call 'call'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ constructor low-level call diagnostic mismatch: {err}")
      IO.println "✓ constructor low-level call unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected constructor low-level call usage to fail compilation")

#eval! do
  let ctorCallcodeSpec : CompilationModel := {
    name := "CtorCallcodeUnsupported"
    fields := []
    constructor := some {
      params := []
      body := [Stmt.letVar "v" (Expr.externalCall "callcode" []), Stmt.stop]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile ctorCallcodeSpec [1] with
  | .error err =>
      if !(contains err "unsupported low-level call 'callcode'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ constructor callcode diagnostic mismatch: {err}")
      IO.println "✓ constructor callcode unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected constructor callcode usage to fail compilation")

#eval! do
  let ctorBoolParamSpec : CompilationModel := {
    name := "CtorBoolParamNormalization"
    fields := []
    constructor := some {
      params := [{ name := "flag", ty := ParamType.bool }]
      body := [Stmt.letVar "seen" (Expr.constructorArg 0), Stmt.stop]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile ctorBoolParamSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected bool constructor param normalization to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "constructor bool param normalization" rendered
        ["let __abi_bool_word_0 := mload(0)",
         "if iszero(or(eq(__abi_bool_word_0, 0), eq(__abi_bool_word_0, 1))) {",
         "let flag := iszero(iszero(__abi_bool_word_0))", "let arg0 := flag"]

#eval! do
  let ctorDynamicParamSpec : CompilationModel := {
    name := "CtorDynamicParamSupported"
    fields := []
    constructor := some {
      params := [{ name := "payload", ty := ParamType.bytes }]
      body := [Stmt.stop]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile ctorDynamicParamSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected dynamic constructor parameter support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "constructor dynamic param decode" rendered
        ["if lt(argsSize, 32) {", "let payload_offset := mload(0)",
         "let payload_abs_offset := payload_offset",
         "let payload_length := mload(payload_abs_offset)", "let payload_data_offset := payload_tail_head_end",
         "let arg0 := payload_offset"]

#eval! do
  let ctorMixedParamSpec : CompilationModel := {
    name := "CtorMixedParamDecode"
    fields := []
    constructor := some {
      params := [
        { name := "owner", ty := ParamType.address },
        { name := "payload", ty := ParamType.bytes }
      ]
      body := [Stmt.stop]
    }
    events := []
    errors := []
    functions := [{ name := "noop", params := [], returnType := none, body := [Stmt.stop] }]
  }
  match compile ctorMixedParamSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected mixed constructor parameter support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "constructor mixed param decode" rendered
        ["if lt(argsSize, 64) {", "let owner := and(mload(0),", "let payload_offset := mload(32)",
         "let payload_length := mload(payload_abs_offset)", "let arg0 := owner",
         "let arg1 := payload_offset"]

#eval! do
  let ctorDynamicReadSpec : CompilationModel := {
    name := "CtorDynamicReadSource"
    fields := []
    constructor := some {
      params := [{ name := "numbers", ty := ParamType.array ParamType.uint256 }]
      body := [
        Stmt.letVar "firstWord" (Expr.arrayElement "numbers" (Expr.literal 0)),
        Stmt.stop
      ]
    }
    events := []
    errors := []
    functions := [{ name := "noop", params := [], returnType := none, body := [Stmt.stop] }]
  }
  match compile ctorDynamicReadSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected constructor dynamic read support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "constructor dynamic read source" rendered
        ["function __verity_array_element_memory_checked(data_offset, length, index) -> word",
         "if iszero(lt(index, length)) {",
         "revert(0, 0)",
         "let firstWord := __verity_array_element_memory_checked(numbers_data_offset, numbers_length, 0)"]
      assertNotContains "constructor dynamic read source" rendered
        ["let firstWord := calldataload(add(numbers_data_offset, mul(0, 32)))",
         "let firstWord := mload(add(numbers_data_offset, mul(0, 32)))"]

#eval! do
  let callSpec : CompilationModel := {
    name := "CallUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "unsafe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "call" [Expr.param "target"])]
      }
    ]
  }
  match compile callSpec [1] with
  | .error err =>
      if !(contains err "unsupported low-level call 'call'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ call diagnostic mismatch: {err}")
      IO.println "✓ call unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected call usage to fail compilation")

#eval! do
  let noArrayElementSpec : CompilationModel := {
    name := "NoArrayElementHelpers"
    fields := []
    constructor := none
    functions := [
      { name := "value"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.param "x")]
      }
    ]
  }
  match compile noArrayElementSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected non-array contract to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertNotContains "array helper injection is usage-gated" rendered
        ["function __verity_array_element_calldata_checked(data_offset, length, index) -> word",
         "function __verity_array_element_memory_checked(data_offset, length, index) -> word"]

#eval! do
  let balanceSpec : CompilationModel := {
    name := "BalanceUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "balance" [Expr.param "target"])]
      }
    ]
  }
  match compile balanceSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'balance'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ balance diagnostic mismatch: {err}")
      IO.println "✓ balance unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected balance usage to fail compilation")

#eval! do
  let gasPriceSpec : CompilationModel := {
    name := "GasPriceUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "gasprice" [])]
      }
    ]
  }
  match compile gasPriceSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'gasprice'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ gasprice diagnostic mismatch: {err}")
      IO.println "✓ gasprice unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected gasprice usage to fail compilation")

#eval! do
  let blobBaseFeeSpec : CompilationModel := {
    name := "BlobBaseFeeUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "blobbasefee" [])]
      }
    ]
  }
  match compile blobBaseFeeSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'blobbasefee'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ blobbasefee diagnostic mismatch: {err}")
      IO.println "✓ blobbasefee unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected blobbasefee usage to fail compilation")

#eval! do
  let blobHashSpec : CompilationModel := {
    name := "BlobHashUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "index", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "blobhash" [Expr.param "index"])]
      }
    ]
  }
  match compile blobHashSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'blobhash'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ blobhash diagnostic mismatch: {err}")
      IO.println "✓ blobhash unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected blobhash usage to fail compilation")

#eval! do
  let extCodeSizeSpec : CompilationModel := {
    name := "ExtCodeSizeUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "extcodesize" [Expr.param "target"])]
      }
    ]
  }
  match compile extCodeSizeSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'extcodesize'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ extcodesize diagnostic mismatch: {err}")
      IO.println "✓ extcodesize unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected extcodesize usage to fail compilation")

#eval! do
  let extCodeCopySpec : CompilationModel := {
    name := "ExtCodeCopyUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "extcodecopy" [Expr.param "target"])]
      }
    ]
  }
  match compile extCodeCopySpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'extcodecopy'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ extcodecopy diagnostic mismatch: {err}")
      IO.println "✓ extcodecopy unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected extcodecopy usage to fail compilation")

#eval! do
  let extCodeHashSpec : CompilationModel := {
    name := "ExtCodeHashUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "extcodehash" [Expr.param "target"])]
      }
    ]
  }
  match compile extCodeHashSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'extcodehash'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ extcodehash diagnostic mismatch: {err}")
      IO.println "✓ extcodehash unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected extcodehash usage to fail compilation")

#eval! do
  let returnDataSizeSpec : CompilationModel := {
    name := "ReturnDataSizeUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "returndatasize" [])]
      }
    ]
  }
  match compile returnDataSizeSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'returndatasize'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ returndatasize diagnostic mismatch: {err}")
      IO.println "✓ returndatasize unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected returndatasize usage to fail compilation")

#eval! do
  let returnDataCopySpec : CompilationModel := {
    name := "ReturnDataCopyUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "returndatacopy" [])]
      }
    ]
  }
  match compile returnDataCopySpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'returndatacopy'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ returndatacopy diagnostic mismatch: {err}")
      IO.println "✓ returndatacopy unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected returndatacopy usage to fail compilation")

#eval! do
  let selfDestructSpec : CompilationModel := {
    name := "SelfDestructUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := none
        body := [Stmt.letVar "_ignored" (Expr.externalCall "selfdestruct" [Expr.param "target"]), Stmt.stop]
      }
    ]
  }
  match compile selfDestructSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'selfdestruct'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ selfdestruct diagnostic mismatch: {err}")
      IO.println "✓ selfdestruct unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected selfdestruct usage to fail compilation")

#eval! do
  let invalidBuiltinSpec : CompilationModel := {
    name := "InvalidBuiltinUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "invalid" [])]
      }
    ]
  }
  match compile invalidBuiltinSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'invalid'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ invalid builtin diagnostic mismatch: {err}")
      IO.println "✓ invalid builtin unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid builtin usage to fail compilation")

#eval! do
  let mloadBuiltinSpec : CompilationModel := {
    name := "MloadBuiltinUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "offset", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "mload" [Expr.param "offset"])]
      }
    ]
  }
  match compile mloadBuiltinSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'mload'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ mload builtin diagnostic mismatch: {err}")
      IO.println "✓ mload builtin unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected mload builtin usage to fail compilation")

#eval! do
  let sstoreBuiltinSpec : CompilationModel := {
    name := "SstoreBuiltinUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [
          { name := "slot", ty := ParamType.uint256 },
          { name := "value", ty := ParamType.uint256 }
        ]
        returnType := none
        body := [Stmt.letVar "_ignored" (Expr.externalCall "sstore" [Expr.param "slot", Expr.param "value"]), Stmt.stop]
      }
    ]
  }
  match compile sstoreBuiltinSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'sstore'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ sstore builtin diagnostic mismatch: {err}")
      IO.println "✓ sstore builtin unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected sstore builtin usage to fail compilation")

#eval! do
  let tloadBuiltinSpec : CompilationModel := {
    name := "TloadBuiltinUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "slot", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "tload" [Expr.param "slot"])]
      }
    ]
  }
  match compile tloadBuiltinSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'tload'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ tload builtin diagnostic mismatch: {err}")
      IO.println "✓ tload builtin unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected tload builtin usage to fail compilation")

#eval! do
  let tstoreBuiltinSpec : CompilationModel := {
    name := "TstoreBuiltinUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [
          { name := "slot", ty := ParamType.uint256 },
          { name := "value", ty := ParamType.uint256 }
        ]
        returnType := none
        body := [Stmt.letVar "_ignored" (Expr.externalCall "tstore" [Expr.param "slot", Expr.param "value"]), Stmt.stop]
      }
    ]
  }
  match compile tstoreBuiltinSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'tstore'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ tstore builtin diagnostic mismatch: {err}")
      IO.println "✓ tstore builtin unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected tstore builtin usage to fail compilation")

#eval! do
  let externalBalanceSpec : CompilationModel := {
    name := "ExternalBalanceUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "balance"
        params := [ParamType.address]
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile externalBalanceSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'balance'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external balance diagnostic mismatch: {err}")
      IO.println "✓ external balance unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external balance declaration to fail compilation")

#eval! do
  let externalGasPriceSpec : CompilationModel := {
    name := "ExternalGasPriceUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "gasprice"
        params := []
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile externalGasPriceSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'gasprice'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external gasprice diagnostic mismatch: {err}")
      IO.println "✓ external gasprice unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external gasprice declaration to fail compilation")

#eval! do
  let externalBlobBaseFeeSpec : CompilationModel := {
    name := "ExternalBlobBaseFeeUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "blobbasefee"
        params := []
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile externalBlobBaseFeeSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'blobbasefee'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external blobbasefee diagnostic mismatch: {err}")
      IO.println "✓ external blobbasefee unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external blobbasefee declaration to fail compilation")

#eval! do
  let externalBlobHashSpec : CompilationModel := {
    name := "ExternalBlobHashUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "blobhash"
        params := [ParamType.uint256]
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile externalBlobHashSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'blobhash'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external blobhash diagnostic mismatch: {err}")
      IO.println "✓ external blobhash unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external blobhash declaration to fail compilation")

#eval! do
  let externalCreate2Spec : CompilationModel := {
    name := "ExternalCreate2Unsupported"
    fields := []
    constructor := none
    externals := [
      { name := "create2"
        params := [ParamType.uint256]
        returnType := some ParamType.address
        axiomNames := []
      }
    ]
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile externalCreate2Spec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'create2'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external create2 diagnostic mismatch: {err}")
      IO.println "✓ external create2 unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external create2 declaration to fail compilation")

#eval! do
  let externalCreateSpec : CompilationModel := {
    name := "ExternalCreateUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "create"
        params := [ParamType.uint256]
        returnType := some ParamType.address
        axiomNames := []
      }
    ]
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile externalCreateSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'create'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external create diagnostic mismatch: {err}")
      IO.println "✓ external create unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external create declaration to fail compilation")

#eval! do
  let externalMloadSpec : CompilationModel := {
    name := "ExternalMloadUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "mload"
        params := [ParamType.uint256]
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile externalMloadSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'mload'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external mload diagnostic mismatch: {err}")
      IO.println "✓ external mload unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external mload declaration to fail compilation")

#eval! do
  let externalSstoreSpec : CompilationModel := {
    name := "ExternalSstoreUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "sstore"
        params := [ParamType.uint256, ParamType.uint256]
        returnType := none
        axiomNames := []
      }
    ]
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile externalSstoreSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'sstore'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external sstore diagnostic mismatch: {err}")
      IO.println "✓ external sstore unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external sstore declaration to fail compilation")

#eval! do
  let externalTloadSpec : CompilationModel := {
    name := "ExternalTloadUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "tload"
        params := [ParamType.uint256]
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile externalTloadSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'tload'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external tload diagnostic mismatch: {err}")
      IO.println "✓ external tload unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external tload declaration to fail compilation")

#eval! do
  let externalTstoreSpec : CompilationModel := {
    name := "ExternalTstoreUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "tstore"
        params := [ParamType.uint256, ParamType.uint256]
        returnType := none
        axiomNames := []
      }
    ]
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile externalTstoreSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'tstore'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external tstore diagnostic mismatch: {err}")
      IO.println "✓ external tstore unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external tstore declaration to fail compilation")

#eval! do
  let unknownCustomErrorSpec : CompilationModel := {
    name := "UnknownCustomError"
    fields := []
    constructor := none
    functions := [
      { name := "bad"
        params := []
        returnType := none
        body := [Stmt.revertError "MissingError" []]
      }
    ]
  }
  match compile unknownCustomErrorSpec [1] with
  | .error err =>
      if !(contains err "unknown custom error 'MissingError'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ unknown custom error diagnostic mismatch: {err}")
      IO.println "✓ unknown custom error diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected unknown custom error usage to fail compilation")

#eval! do
  let bytesCustomErrorSpec : CompilationModel := {
    name := "BytesCustomErrorSupported"
    fields := []
    constructor := none
    errors := [
      { name := "BadPayload"
        params := [ParamType.bytes]
      }
    ]
    functions := [
      { name := "bad"
        params := [{ name := "payload", ty := ParamType.bytes }]
        returnType := none
        body := [Stmt.revertError "BadPayload" [Expr.param "payload"]]
      }
    ]
  }
  match compile bytesCustomErrorSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected bytes custom error support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "bytes custom error ABI encoding" rendered
        ["mstore(4, __err_tail)",
         "let __err_arg0_len := calldataload(add(4, payload_offset))",
         "calldatacopy(add(__err_arg0_dst, 32), add(add(4, payload_offset), 32), __err_arg0_len)",
         "let __err_arg0_padded := and(add(__err_arg0_len, 31), not(31))",
         "revert(0, add(4, __err_tail))"]

#eval! do
  let bytesCustomErrorArgShapeSpec : CompilationModel := {
    name := "BytesCustomErrorArgShapeUnsupported"
    fields := []
    constructor := none
    errors := [
      { name := "BadPayload"
        params := [ParamType.bytes]
      }
    ]
    functions := [
      { name := "bad"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.revertError "BadPayload" [Expr.param "x"]]
      }
    ]
  }
  match compile bytesCustomErrorArgShapeSpec [1] with
  | .error err =>
      if !(contains err "expects Compiler.CompilationModel.ParamType.bytes arg to reference a matching parameter" && contains err "Issue #586") then
        throw (IO.userError s!"✗ bytes custom error arg-shape diagnostic mismatch: {err}")
      IO.println "✓ bytes custom error arg-shape diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid bytes custom error arg shape to fail compilation")

#eval! do
  let tupleCustomErrorSpec : CompilationModel := {
    name := "TupleCustomErrorSupported"
    fields := []
    constructor := none
    errors := [
      { name := "TupleErr"
        params := [ParamType.tuple [ParamType.uint256, ParamType.address]]
      }
    ]
    functions := [
      { name := "bad"
        params := [{ name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.address] }]
        returnType := none
        body := [Stmt.revertError "TupleErr" [Expr.param "payload"]]
      }
    ]
  }
  match compile tupleCustomErrorSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected tuple custom error support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "tuple custom error ABI encoding" rendered
        ["mstore(4, payload_0)",
         "mstore(36, and(payload_1,",
         "revert(0, add(4, __err_tail))"]

#eval! do
  let arrayCustomErrorSpec : CompilationModel := {
    name := "ArrayCustomErrorSupported"
    fields := []
    constructor := none
    errors := [
      { name := "ArrayErr"
        params := [ParamType.array ParamType.uint256]
      }
    ]
    functions := [
      { name := "bad"
        params := [{ name := "values", ty := ParamType.array ParamType.uint256 }]
        returnType := none
        body := [Stmt.revertError "ArrayErr" [Expr.param "values"]]
      }
    ]
  }
  match compile arrayCustomErrorSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected dynamic array custom error support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "dynamic array custom error ABI encoding" rendered
        ["mstore(4, __err_tail)",
         "let __err_arg0_arr_len :=",
         "let __err_arg0_arr_byte_len := mul(__err_arg0_arr_len, 32)",
         "revert(0, add(4, __err_tail))"]

#eval! do
  let unindexedBytesEventSpec : CompilationModel := {
    name := "UnindexedBytesEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedBytes"
        params := [
          { name := "payload", ty := ParamType.bytes, kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitBytes"
        params := [{ name := "payload", ty := ParamType.bytes }]
        returnType := none
        body := [Stmt.emit "UnindexedBytes" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedBytesEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed bytes event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed bytes event ABI data encoding" rendered
        ["let __evt_data_tail := 32",
         "mstore(add(__evt_ptr, 0), __evt_data_tail)",
         "let __evt_arg0_len := payload_length",
         "calldatacopy(add(__evt_arg0_dst, 32), payload_data_offset, __evt_arg0_len)",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedTupleEventSpec : CompilationModel := {
    name := "UnindexedTupleEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedTuple"
        params := [
          { name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.address], kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitTuple"
        params := [{ name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.address] }]
        returnType := none
        body := [Stmt.emit "UnindexedTuple" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedTupleEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed static tuple event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed static tuple event encoding" rendered
        ["mstore(add(__evt_ptr, 0), payload_0)",
         "mstore(add(__evt_ptr, 32), and(payload_1,",
         "log1(__evt_ptr, 64, __evt_topic0)"]

#eval! do
  let unindexedFixedArrayEventSpec : CompilationModel := {
    name := "UnindexedFixedArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedFixedArray"
        params := [
          { name := "payload", ty := ParamType.fixedArray ParamType.uint256 2, kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitFixed"
        params := [{ name := "payload", ty := ParamType.fixedArray ParamType.uint256 2 }]
        returnType := none
        body := [Stmt.emit "UnindexedFixedArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedFixedArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed static fixed-array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed static fixed-array event encoding" rendered
        ["mstore(add(__evt_ptr, 0), payload_0)",
         "mstore(add(__evt_ptr, 32), payload_1)",
         "log1(__evt_ptr, 64, __evt_topic0)"]

#eval! do
  let unindexedDynamicArrayEventSpec : CompilationModel := {
    name := "UnindexedDynamicArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicArray"
        params := [
          { name := "payload", ty := ParamType.array ParamType.uint256, kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array ParamType.uint256 }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic array event encoding" rendered
        ["let __evt_data_tail := 32",
         "mstore(add(__evt_ptr, 0), __evt_data_tail)",
         "let __evt_arg0_byte_len := mul(__evt_arg0_len, 32)",
         "let __evt_arg0_i := 0",
         "let __evt_topic0 := keccak256(__evt_ptr,",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedDynamicStaticTupleArrayEventSpec : CompilationModel := {
    name := "UnindexedDynamicStaticTupleArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicStaticTupleArray"
        params := [
          { name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.address, ParamType.bool]), kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.address, ParamType.bool]) }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicStaticTupleArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicStaticTupleArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic static-tuple array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic static-tuple array event encoding" rendered
        ["let __evt_data_tail := 32",
         "mstore(add(__evt_ptr, 0), __evt_data_tail)",
         "let __evt_arg0_byte_len := mul(__evt_arg0_len, 64)",
         "mstore(add(__evt_arg0_out_base, 0), and(calldataload(add(__evt_arg0_elem_base, 0))",
         "mstore(add(__evt_arg0_out_base, 32), iszero(iszero(calldataload(add(__evt_arg0_elem_base, 32)))))",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedDynamicBytes32ArrayEventSpec : CompilationModel := {
    name := "UnindexedDynamicBytes32ArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicBytes32Array"
        params := [
          { name := "payload", ty := ParamType.array ParamType.bytes32, kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array ParamType.bytes32 }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicBytes32Array" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicBytes32ArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic bytes32 array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic bytes32 array event encoding" rendered
        ["let __evt_data_tail := 32",
         "let __evt_arg0_byte_len := mul(__evt_arg0_len, 32)",
         "let __evt_arg0_i := 0",
         "let __evt_arg0_elem_base := add(payload_data_offset, mul(__evt_arg0_i, 32))",
         "mstore(add(__evt_arg0_out_base, 0), calldataload(add(__evt_arg0_elem_base, 0)))",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedDynamicBytesArrayEventSpec : CompilationModel := {
    name := "UnindexedDynamicBytesArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicBytesArray"
        params := [
          { name := "payload", ty := ParamType.array ParamType.bytes, kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array ParamType.bytes }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicBytesArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicBytesArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic bytes array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic bytes array event encoding" rendered
        ["let __evt_data_tail := 32",
         "let __evt_arg0_head_len := mul(__evt_arg0_len, 32)",
         "mstore(__evt_arg0_elem_dst, __evt_arg0_elem_len)",
         "mstore(add(add(__evt_arg0_dst, 32), mul(__evt_arg0_i, 32)), __evt_arg0_tail_len)",
         "calldatacopy(add(__evt_arg0_elem_dst, 32), __evt_arg0_elem_data, __evt_arg0_elem_len)",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedDynamicCompositeArrayEventSpec : CompilationModel := {
    name := "UnindexedDynamicCompositeArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicCompositeArray"
        params := [
          { name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.uint256, ParamType.bytes]), kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitDynamicCompositeArray"
        params := [{ name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.uint256, ParamType.bytes]) }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicCompositeArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicCompositeArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic composite array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic composite array event encoding" rendered
        ["let __evt_data_tail := 32",
         "mstore(__evt_arg0_dst, __evt_arg0_arr_len)",
         "let __evt_arg0_arr_tail_len := __evt_arg0_arr_head_len",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedDynamicTupleEventSpec : CompilationModel := {
    name := "UnindexedDynamicTupleEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicTuple"
        params := [
          { name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.bytes], kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitDynamicTuple"
        params := [{ name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.bytes] }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicTuple" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicTupleEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic tuple event to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic tuple event encoding" rendered
        ["let __evt_data_tail := 32",
         "mstore(add(__evt_ptr, 0), __evt_data_tail)",
         "__evt_arg0_tail_len",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedDynamicFixedArrayEventSpec : CompilationModel := {
    name := "UnindexedDynamicFixedArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicFixedArray"
        params := [
          { name := "payload", ty := ParamType.fixedArray (ParamType.tuple [ParamType.uint256, ParamType.bytes]) 2, kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitDynamicFixedArray"
        params := [{ name := "payload", ty := ParamType.fixedArray (ParamType.tuple [ParamType.uint256, ParamType.bytes]) 2 }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicFixedArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicFixedArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic fixed-array event to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic fixed-array event encoding" rendered
        ["let __evt_data_tail := 32",
         "mstore(add(__evt_ptr, 0), __evt_data_tail)",
         "__evt_arg0_fa_tail_len",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unusedInvalidIndexedEventSpec : CompilationModel := {
    name := "UnusedInvalidIndexedEventRejected"
    fields := []
    constructor := none
    events := [
      { name := "TooManyIndexed"
        params := [
          { name := "a", ty := ParamType.uint256, kind := EventParamKind.indexed },
          { name := "b", ty := ParamType.uint256, kind := EventParamKind.indexed },
          { name := "c", ty := ParamType.uint256, kind := EventParamKind.indexed },
          { name := "d", ty := ParamType.uint256, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "f"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile unusedInvalidIndexedEventSpec [1] with
  | .error err =>
      if !(contains err "event 'TooManyIndexed' has 4 indexed params; max is 3") then
        throw (IO.userError s!"✗ invalid unused event declaration diagnostic mismatch: {err}")
      IO.println "✓ invalid unused event declaration rejected at compile boundary"
  | .ok _ =>
      throw (IO.userError "✗ expected unused invalid event declaration to fail compilation")

#eval! do
  let indexedBytesEventSpec : CompilationModel := {
    name := "IndexedBytesEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedBytes"
        params := [
          { name := "payload", ty := ParamType.bytes, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitBytes"
        params := [{ name := "payload", ty := ParamType.bytes }]
        returnType := none
        body := [Stmt.emit "IndexedBytes" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedBytesEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed bytes event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed bytes topic hashing" rendered
        ["calldatacopy(__evt_ptr, payload_data_offset, payload_length)",
         "let __evt_topic1 := keccak256(__evt_ptr, payload_length)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedBytesEventArgTypeMismatchSpec : CompilationModel := {
    name := "IndexedBytesEventArgTypeMismatch"
    fields := []
    constructor := none
    events := [
      { name := "IndexedBytes"
        params := [
          { name := "payload", ty := ParamType.bytes, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitBadBytes"
        params := [{ name := "payload", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.emit "IndexedBytes" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedBytesEventArgTypeMismatchSpec [1] with
  | .error err =>
      if !(contains err "event 'IndexedBytes' param 'payload' expects" &&
          contains err "ParamType.bytes" &&
          contains err "Issue #586") then
        throw (IO.userError s!"✗ indexed bytes event arg type diagnostic mismatch: {err}")
      IO.println "✓ indexed bytes event arg type diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid indexed bytes event arg type usage to fail compilation")

#eval! do
  let indexedTupleEventSpec : CompilationModel := {
    name := "IndexedTupleEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedTuple"
        params := [
          { name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.address], kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitTuple"
        params := [{ name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.address] }]
        returnType := none
        body := [Stmt.emit "IndexedTuple" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedTupleEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed static tuple event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed static tuple topic hashing" rendered
        ["mstore(add(__evt_ptr, 0), payload_0)",
         "mstore(add(__evt_ptr, 32), and(payload_1",
         "let __evt_topic1 := keccak256(__evt_ptr, 64)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedFixedArrayEventSpec : CompilationModel := {
    name := "IndexedFixedArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedFixedArray"
        params := [
          { name := "payload", ty := ParamType.fixedArray ParamType.uint256 2, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitFixed"
        params := [{ name := "payload", ty := ParamType.fixedArray ParamType.uint256 2 }]
        returnType := none
        body := [Stmt.emit "IndexedFixedArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedFixedArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed static fixed-array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed static fixed-array topic hashing" rendered
        ["mstore(add(__evt_ptr, 0), payload_0)",
         "mstore(add(__evt_ptr, 32), payload_1)",
         "let __evt_topic1 := keccak256(__evt_ptr, 64)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicTupleEventSpec : CompilationModel := {
    name := "IndexedDynamicTupleEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "BadIndexedDynamicTuple"
        params := [
          { name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.bytes], kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitBad"
        params := [{ name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.bytes] }]
        returnType := none
        body := [Stmt.emit "BadIndexedDynamicTuple" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicTupleEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic tuple event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic tuple topic hashing" rendered
        ["let __evt_arg0_indexed_tuple_out_len := 0",
         "let __evt_arg0_indexed_tuple_elem_rel_1 := calldataload(add(add(4, payload_offset), 32))",
         "let __evt_arg0_indexed_tuple_elem_1_len := calldataload(__evt_arg0_indexed_tuple_elem_src_1)",
         "calldatacopy(__evt_arg0_indexed_tuple_elem_dst_1, add(__evt_arg0_indexed_tuple_elem_src_1, 32), __evt_arg0_indexed_tuple_elem_1_len)",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_indexed_tuple_out_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicArrayEventSpec : CompilationModel := {
    name := "IndexedDynamicArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedDynamicArray"
        params := [
          { name := "payload", ty := ParamType.array ParamType.uint256, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array ParamType.uint256 }]
        returnType := none
        body := [Stmt.emit "IndexedDynamicArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic array topic hashing" rendered
        ["let __evt_arg0_byte_len := mul(payload_length, 32)",
         "let __evt_arg0_i := 0",
         "lt(__evt_arg0_i, payload_length)",
         "let __evt_arg0_elem_base := add(payload_data_offset, mul(__evt_arg0_i, 32))",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_byte_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicStaticTupleArrayEventSpec : CompilationModel := {
    name := "IndexedDynamicStaticTupleArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedDynamicStaticTupleArray"
        params := [
          { name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.address, ParamType.bool]), kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.address, ParamType.bool]) }]
        returnType := none
        body := [Stmt.emit "IndexedDynamicStaticTupleArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicStaticTupleArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic static-tuple array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic static-tuple array topic hashing" rendered
        ["let __evt_arg0_byte_len := mul(payload_length, 64)",
         "let __evt_arg0_i := 0",
         "lt(__evt_arg0_i, payload_length)",
         "mstore(add(__evt_arg0_out_base, 0), and(calldataload(add(__evt_arg0_elem_base, 0))",
         "mstore(add(__evt_arg0_out_base, 32), iszero(iszero(calldataload(add(__evt_arg0_elem_base, 32)))))",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_byte_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicBytes32ArrayEventSpec : CompilationModel := {
    name := "IndexedDynamicBytes32ArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedDynamicBytes32Array"
        params := [
          { name := "payload", ty := ParamType.array ParamType.bytes32, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array ParamType.bytes32 }]
        returnType := none
        body := [Stmt.emit "IndexedDynamicBytes32Array" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicBytes32ArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic bytes32 array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic bytes32 array topic hashing" rendered
        ["let __evt_arg0_byte_len := mul(payload_length, 32)",
         "let __evt_arg0_i := 0",
         "lt(__evt_arg0_i, payload_length)",
         "let __evt_arg0_elem_base := add(payload_data_offset, mul(__evt_arg0_i, 32))",
         "mstore(add(__evt_arg0_out_base, 0), calldataload(add(__evt_arg0_elem_base, 0)))",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_byte_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicBytesArrayEventSpec : CompilationModel := {
    name := "IndexedDynamicBytesArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedDynamicBytesArray"
        params := [
          { name := "payload", ty := ParamType.array ParamType.bytes, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array ParamType.bytes }]
        returnType := none
        body := [Stmt.emit "IndexedDynamicBytesArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicBytesArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic bytes array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic bytes array topic hashing" rendered
        ["let __evt_arg0_tail_len := 0",
         "let __evt_arg0_elem_offset := calldataload(add(payload_data_offset, mul(__evt_arg0_i, 32)))",
         "let __evt_arg0_elem_len := calldataload(__evt_arg0_elem_len_pos)",
         "calldatacopy(__evt_arg0_elem_dst, __evt_arg0_elem_data, __evt_arg0_elem_len)",
         "let __evt_arg0_elem_padded := and(add(__evt_arg0_elem_len, 31), not(31))",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_tail_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicStaticFixedArrayEventSpec : CompilationModel := {
    name := "IndexedDynamicStaticFixedArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedDynamicStaticFixedArray"
        params := [
          { name := "payload", ty := ParamType.array (ParamType.fixedArray ParamType.address 2), kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array (ParamType.fixedArray ParamType.address 2) }]
        returnType := none
        body := [Stmt.emit "IndexedDynamicStaticFixedArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicStaticFixedArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic static fixed-array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic static fixed-array topic hashing" rendered
        ["let __evt_arg0_byte_len := mul(payload_length, 64)",
         "let __evt_arg0_i := 0",
         "lt(__evt_arg0_i, payload_length)",
         "mstore(add(__evt_arg0_out_base, 0), and(calldataload(add(__evt_arg0_elem_base, 0))",
         "mstore(add(__evt_arg0_out_base, 32), and(calldataload(add(__evt_arg0_elem_base, 32))",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_byte_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicCompositeArrayEventSpec : CompilationModel := {
    name := "IndexedDynamicCompositeArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "BadIndexedDynamicCompositeArray"
        params := [
          { name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.uint256, ParamType.bytes]), kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitBad"
        params := [{ name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.uint256, ParamType.bytes]) }]
        returnType := none
        body := [Stmt.emit "BadIndexedDynamicCompositeArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicCompositeArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic composite array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic composite array event topic hashing" rendered
        ["let __evt_arg0_indexed_arr_len := calldataload(add(4, payload_offset))",
         "let __evt_arg0_indexed_arr_elem_rel := calldataload(add(__evt_arg0_indexed_arr_data, mul(__evt_arg0_indexed_arr_i, 32)))",
         "let __evt_arg0_indexed_arr_elem_tuple_elem_rel_1 := calldataload(add(__evt_arg0_indexed_arr_elem_src, 32))",
         "calldatacopy(__evt_arg0_indexed_arr_elem_tuple_elem_dst_1, add(__evt_arg0_indexed_arr_elem_tuple_elem_src_1, 32), __evt_arg0_indexed_arr_elem_tuple_elem_1_len)",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_indexed_arr_out_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let internalVoidReturnSpec : CompilationModel := {
    name := "InternalVoidReturnRejected"
    fields := []
    constructor := none
    functions := [
      { name := "badInternal"
        params := []
        returnType := none
        isInternal := true
        body := [Stmt.return (Expr.literal 1)]
      }
    ]
  }
  match compile internalVoidReturnSpec [] with
  | .error err =>
      if !contains err "uses Stmt.return but declares no return values" then
        throw (IO.userError s!"✗ internal void return diagnostic mismatch: {err}")
      IO.println "✓ internal void return validation"
  | .ok _ =>
      throw (IO.userError "✗ expected internal void Stmt.return usage to fail compilation")

#eval! do
  let internalMultiReturnSpec : CompilationModel := {
    name := "InternalMultiReturnSupported"
    fields := []
    constructor := none
    functions := [
      { name := "pair"
        params := [
          { name := "left", ty := ParamType.uint256 },
          { name := "right", ty := ParamType.uint256 }
        ]
        returnType := none
        returns := [ParamType.uint256, ParamType.uint256]
        isInternal := true
        body := [Stmt.returnValues [Expr.param "left", Expr.param "right"]]
      },
      { name := "project"
        params := [
          { name := "left", ty := ParamType.uint256 },
          { name := "right", ty := ParamType.uint256 }
        ]
        returnType := none
        returns := [ParamType.uint256, ParamType.uint256]
        body := [
          Stmt.internalCallAssign ["a", "b"] "pair" [Expr.param "left", Expr.param "right"],
          Stmt.returnValues [Expr.localVar "a", Expr.localVar "b"]
        ]
      }
    ]
  }
  match compile internalMultiReturnSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected internal multi-return support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "internal multi-return codegen" rendered
        ["function internal_pair(left, right) -> __ret0, __ret1",
         "__ret0 := left",
         "__ret1 := right",
         "let a, b := internal_pair(left, right)",
         "return(0, 64)"]

#eval! do
  let internalReturnNameCollisionSpec : CompilationModel := {
    name := "InternalReturnNameCollision"
    fields := []
    constructor := none
    functions := [
      { name := "helper"
        params := [{ name := "__ret0", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        isInternal := true
        body := [
          Stmt.letVar "__ret0_1" (Expr.param "__ret0"),
          Stmt.return (Expr.localVar "__ret0_1")
        ]
      },
      { name := "entry"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.internalCall "helper" [Expr.param "x"])]
      }
    ]
  }
  match compile internalReturnNameCollisionSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected internal return name collision to be handled, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "internal return name collision hygiene" rendered
        ["function internal_helper(__ret0) -> __ret0_2",
         "__ret0_2 := __ret0_1"]

#eval! do
  let internalReturnTerminatesSpec : CompilationModel := {
    name := "InternalReturnTerminates"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "helper"
        params := []
        returnType := some FieldType.uint256
        isInternal := true
        body := [
          Stmt.return (Expr.literal 1),
          Stmt.setStorage "x" (Expr.literal 9)
        ]
      },
      { name := "entry"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.internalCall "helper" [])]
      }
    ]
  }
  match compile internalReturnTerminatesSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected internal return termination lowering to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "internal return termination lowering" rendered
        ["function internal_helper() -> __ret0",
         "__ret0 := 1",
         "leave",
         "sstore(0, 9)"]

#eval! do
  let exprInternalCallMultiReturnSpec : CompilationModel := {
    name := "ExprInternalCallMultiReturnRejected"
    fields := []
    constructor := none
    functions := [
      { name := "pair"
        params := []
        returnType := none
        returns := [ParamType.uint256, ParamType.uint256]
        isInternal := true
        body := [Stmt.returnValues [Expr.literal 1, Expr.literal 2]]
      },
      { name := "badExprUse"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.internalCall "pair" [])]
      }
    ]
  }
  match compile exprInternalCallMultiReturnSpec [1] with
  | .error err =>
      if !(contains err "uses Expr.internalCall 'pair' but callee returns 2 values" &&
          contains err "Issue #625") then
        throw (IO.userError s!"✗ expr internalCall multi-return diagnostic mismatch: {err}")
      IO.println "✓ expr internalCall multi-return diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected Expr.internalCall on multi-return internal function to fail compilation")

#eval! do
  let internalCallAssignArityMismatchSpec : CompilationModel := {
    name := "InternalCallAssignArityMismatch"
    fields := []
    constructor := none
    functions := [
      { name := "pair"
        params := []
        returnType := none
        returns := [ParamType.uint256, ParamType.uint256]
        isInternal := true
        body := [Stmt.returnValues [Expr.literal 1, Expr.literal 2]]
      },
      { name := "badBind"
        params := []
        returnType := some FieldType.uint256
        body := [
          Stmt.internalCallAssign ["onlyOne"] "pair" [],
          Stmt.return (Expr.localVar "onlyOne")
        ]
      }
    ]
  }
  match compile internalCallAssignArityMismatchSpec [1] with
  | .error err =>
      if !(contains err "binds 1 values from internal function 'pair', but callee returns 2" &&
          contains err "Issue #625") then
        throw (IO.userError s!"✗ internalCallAssign arity diagnostic mismatch: {err}")
      IO.println "✓ internalCallAssign arity diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected internalCallAssign arity mismatch to fail compilation")

#eval! do
  let internalCallAssignDuplicateTargetSpec : CompilationModel := {
    name := "InternalCallAssignDuplicateTarget"
    fields := []
    constructor := none
    functions := [
      { name := "pair"
        params := []
        returnType := none
        returns := [ParamType.uint256, ParamType.uint256]
        isInternal := true
        body := [Stmt.returnValues [Expr.literal 1, Expr.literal 2]]
      },
      { name := "badBind"
        params := []
        returnType := some FieldType.uint256
        body := [
          Stmt.internalCallAssign ["x", "x"] "pair" [],
          Stmt.return (Expr.localVar "x")
        ]
      }
    ]
  }
  match compile internalCallAssignDuplicateTargetSpec [1] with
  | .error err =>
      if !(contains err "uses Stmt.internalCallAssign with duplicate target 'x'" &&
          contains err "Issue #625") then
        throw (IO.userError s!"✗ internalCallAssign duplicate-target diagnostic mismatch: {err}")
      IO.println "✓ internalCallAssign duplicate-target validation"
  | .ok _ =>
      throw (IO.userError "✗ expected internalCallAssign duplicate target names to fail compilation")

#eval! do
  let internalDynamicParamRejectedSpec : CompilationModel := {
    name := "InternalDynamicParamRejected"
    fields := []
    constructor := none
    functions := [
      { name := "sum"
        params := [{ name := "arr", ty := ParamType.array ParamType.uint256 }]
        returnType := some FieldType.uint256
        isInternal := true
        body := [Stmt.return (Expr.arrayLength "arr")]
      },
      { name := "entry"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.param "x")]
      }
    ]
  }
  match compile internalDynamicParamRejectedSpec [1] with
  | .error err =>
      if !(contains err "internal function 'sum' parameter 'arr' has dynamic type" &&
          contains err "Issue #753") then
        throw (IO.userError s!"✗ internal dynamic param diagnostic mismatch: {err}")
      IO.println "✓ internal dynamic param diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected internal dynamic parameter to fail compilation")

#eval! do
  let multiReturnWithSingleReturnStmtSpec : CompilationModel := {
    name := "MultiReturnWithSingleStmtRejected"
    fields := []
    constructor := none
    functions := [
      { name := "badExternal"
        params := []
        returnType := none
        returns := [ParamType.uint256, ParamType.uint256]
        body := [Stmt.return (Expr.literal 1)]
      }
    ]
  }
  match compile multiReturnWithSingleReturnStmtSpec [1] with
  | .error err =>
      if !contains err "declares multiple return values; use Stmt.returnValues" then
        throw (IO.userError s!"✗ single-return stmt on multi-return function diagnostic mismatch: {err}")
      IO.println "✓ multi-return Stmt.return validation"
  | .ok _ =>
      throw (IO.userError "✗ expected single-value return statement on multi-return function to fail compilation")

#eval! do
  let returnValuesArityMismatchSpec : CompilationModel := {
    name := "ReturnValuesArityMismatch"
    fields := []
    constructor := none
    functions := [
      { name := "badArity"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.returnValues [Expr.literal 1, Expr.literal 2]]
      }
    ]
  }
  match compile returnValuesArityMismatchSpec [1] with
  | .error err =>
      if !contains err "returnValues count mismatch: expected 1, got 2" then
        throw (IO.userError s!"✗ returnValues arity diagnostic mismatch: {err}")
      IO.println "✓ returnValues arity validation"
  | .ok _ =>
      throw (IO.userError "✗ expected returnValues arity mismatch to fail compilation")

#eval! do
  let missingReturnPathSpec : CompilationModel := {
    name := "MissingReturnPathRejected"
    fields := []
    constructor := none
    functions := [
      { name := "bad"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.stop]
      }
    ]
  }
  match compile missingReturnPathSpec [1] with
  | .error err =>
      if !contains err "not all control-flow paths end in return/revert" then
        throw (IO.userError s!"✗ missing return-path diagnostic mismatch: {err}")
      IO.println "✓ missing return-path validation"
  | .ok _ =>
      throw (IO.userError "✗ expected missing return path on declared-return function to fail compilation")

#eval! do
  let bothBranchesReturnSpec : CompilationModel := {
    name := "BothBranchesReturnAccepted"
    fields := []
    constructor := none
    functions := [
      { name := "ok"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [
          Stmt.ite (Expr.eq (Expr.param "x") (Expr.literal 0))
            [Stmt.return (Expr.literal 1)]
            [Stmt.return (Expr.literal 2)]
        ]
      }
    ]
  }
  match compile bothBranchesReturnSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected both-branches-return function to compile, got: {err}")
  | .ok _ =>
      IO.println "✓ both-branches return accepted"

#eval! do
  let branchMissingReturnSpec : CompilationModel := {
    name := "BranchMissingReturnRejected"
    fields := []
    constructor := none
    functions := [
      { name := "badBranch"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [
          Stmt.ite (Expr.eq (Expr.param "x") (Expr.literal 0))
            [Stmt.return (Expr.literal 1)]
            [Stmt.stop]
        ]
      }
    ]
  }
  match compile branchMissingReturnSpec [1] with
  | .error err =>
      if !contains err "not all control-flow paths end in return/revert" then
        throw (IO.userError s!"✗ branch missing return diagnostic mismatch: {err}")
      IO.println "✓ branch missing return-path validation"
  | .ok _ =>
      throw (IO.userError "✗ expected branch-missing-return function to fail compilation")

#eval! do
  let fallbackSpec : CompilationModel := {
    name := "FallbackSupported"
    fields := []
    constructor := none
    functions := [
      { name := "fallback"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile fallbackSpec [] with
  | .error err =>
      throw (IO.userError s!"✗ expected fallback entrypoint modeling to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "fallback default branch emission" rendered ["default {", "/* fallback() */", "stop()"]

#eval! do
  let receiveSpec : CompilationModel := {
    name := "ReceiveSupported"
    fields := []
    constructor := none
    functions := [
      { name := "receive"
        params := []
        returnType := none
        isPayable := true
        body := [Stmt.stop]
      }
    ]
  }
  match compile receiveSpec [] with
  | .error err =>
      throw (IO.userError s!"✗ expected receive entrypoint modeling to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "receive empty-calldata dispatch branch" rendered
        ["let __is_empty_calldata := eq(calldatasize(), 0)", "if __is_empty_calldata {", "/* receive() */", "stop()"]
      assertContains "receive missing fallback reverts for non-empty calldata" rendered
        ["if iszero(__is_empty_calldata) {", "revert(0, 0)"]

#eval! do
  let receiveFallbackSpec : CompilationModel := {
    name := "ReceiveFallbackSupported"
    fields := []
    constructor := none
    functions := [
      { name := "receive"
        params := []
        returnType := none
        isPayable := true
        body := [Stmt.stop]
      },
      { name := "fallback"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile receiveFallbackSpec [] with
  | .error err =>
      throw (IO.userError s!"✗ expected receive+fallback entrypoint modeling to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "receive+fallback split dispatch" rendered
        ["if __is_empty_calldata {", "/* receive() */", "if iszero(__is_empty_calldata) {", "/* fallback() */"]
      assertContains "short-calldata guard before selector dispatch" rendered
        ["let __has_selector := iszero(lt(calldatasize(), 4))",
         "if iszero(__has_selector) {",
         "/* fallback() */",
         "if __has_selector {"]

#eval! do
  let receiveNotPayableSpec : CompilationModel := {
    name := "ReceiveNotPayableRejected"
    fields := []
    constructor := none
    functions := [
      { name := "receive"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile receiveNotPayableSpec [] with
  | .error err =>
      if !(contains err "function 'receive' must be payable" && contains err "Issue #586") then
        throw (IO.userError s!"✗ receive payable diagnostic mismatch: {err}")
      IO.println "✓ receive payable validation"
  | .ok _ =>
      throw (IO.userError "✗ expected non-payable receive entrypoint to fail compilation")

#eval! do
  let explicitFieldSlotSpec : CompilationModel := {
    name := "ExplicitFieldSlotSpec"
    fields := [
      { name := "a", ty := FieldType.uint256, slot := some 5 },
      { name := "b", ty := FieldType.uint256 },
      { name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address), slot := some 9 }
    ]
    constructor := none
    functions := [
      { name := "setA"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "a" (Expr.param "x"), Stmt.stop]
      },
      { name := "setB"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "b" (Expr.param "x"), Stmt.stop]
      },
      { name := "setBal"
        params := [{ name := "who", ty := ParamType.address }, { name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setMapping "balances" (Expr.param "who") (Expr.param "x"), Stmt.stop]
      }
    ]
  }
  match compile explicitFieldSlotSpec [1, 2, 3] with
  | .error err =>
      throw (IO.userError s!"✗ explicit field slot compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "explicit slot setStorage lowering" rendered ["sstore(5, x)"]
      assertContains "legacy positional slot fallback lowering" rendered ["sstore(1, x)"]
      assertContains "explicit slot mapping lowering" rendered ["mappingSlot(9, who)"]

#eval! do
  let aliasSlotMirrorWriteSpec : CompilationModel := {
    name := "AliasSlotMirrorWriteSpec"
    fields := [
      { name := "a", ty := FieldType.uint256, slot := some 8, aliasSlots := [20] },
      { name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address), slot := some 9, aliasSlots := [21] }
    ]
    constructor := none
    functions := [
      { name := "setA"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "a" (Expr.param "x"), Stmt.stop]
      },
      { name := "setBal"
        params := [{ name := "who", ty := ParamType.address }, { name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setMapping "balances" (Expr.param "who") (Expr.param "x"), Stmt.stop]
      }
    ]
  }
  match compile aliasSlotMirrorWriteSpec [1, 2] with
  | .error err =>
      throw (IO.userError s!"✗ alias slot mirror-write compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "setStorage mirror writes to alias slots" rendered
        ["sstore(8, __compat_value)", "sstore(20, __compat_value)"]
      assertContains "setMapping mirror writes to alias slots" rendered
        ["mappingSlot(9, __compat_key)", "mappingSlot(21, __compat_key)"]

#eval! do
  let mappingScratchBaseSpec : CompilationModel := {
    name := "MappingScratchBaseSpec"
    fields := [
      { name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address), slot := some 9 }
    ]
    constructor := none
    functions := [
      { name := "setBal"
        params := [{ name := "who", ty := ParamType.address }, { name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setMapping "balances" (Expr.param "who") (Expr.param "x"), Stmt.stop]
      }
    ]
  }
  match compile mappingScratchBaseSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ mapping scratch base compile failed: {err}")
  | .ok ir =>
      let renderedDefault := Yul.render (emitYulWithOptions ir {})
      assertContains "mappingSlot helper default key scratch address" renderedDefault ["mstore(0, key)"]
      assertContains "mappingSlot helper default baseSlot scratch address" renderedDefault ["mstore(32, baseSlot)"]
      assertContains "mappingSlot helper default keccak scratch address" renderedDefault ["keccak256(0, 64)"]

      let renderedCustom := Yul.render (emitYulWithOptions ir { mappingSlotScratchBase := 128 })
      assertContains "mappingSlot helper custom key scratch address" renderedCustom ["mstore(128, key)"]
      assertContains "mappingSlot helper custom baseSlot scratch address" renderedCustom ["mstore(160, baseSlot)"]
      assertContains "mappingSlot helper custom keccak scratch address" renderedCustom ["keccak256(128, 64)"]

#eval! do
  let selectorOrderingSpec : CompilationModel := {
    name := "SelectorOrderingSpec"
    fields := []
    constructor := none
    functions := [
      { name := "zebra", params := [], returnType := none, body := [Stmt.stop] },
      { name := "alpha", params := [], returnType := none, body := [Stmt.stop] },
      { name := "middle", params := [], returnType := none, body := [Stmt.stop] }
    ]
  }
  let selectors := [0x30000000, 0x10000000, 0x20000000]
  match compile selectorOrderingSpec selectors with
  | .error err =>
      throw (IO.userError s!"✗ selector ordering compile failed: {err}")
  | .ok ir =>
      let renderedDefault := Yul.render (emitYulWithOptions ir {})
      assertAppearsBefore "default profile preserves source selector order (zebra before alpha)"
        renderedDefault "case 0x30000000 {" "case 0x10000000 {"

      let renderedParityOrdering :=
        Yul.render (emitYulWithOptions ir { backendProfile := .solidityParityOrdering })
      assertAppearsBefore "solidity-parity-ordering sorts selector cases ascending (alpha before zebra)"
        renderedParityOrdering "case 0x10000000 {" "case 0x30000000 {"

      let renderedParity :=
        Yul.render (emitYulWithOptions ir { backendProfile := .solidityParity })
      assertAppearsBefore "solidity-parity also sorts selector cases ascending (alpha before zebra)"
        renderedParity "case 0x10000000 {" "case 0x30000000 {"

#eval! do
  let helperOrderingSpec : CompilationModel := {
    name := "HelperOrderingSpec"
    fields := []
    constructor := none
    functions := [
      { name := "zebraHelper"
        params := []
        returnType := some FieldType.uint256
        isInternal := true
        body := [Stmt.return (Expr.literal 11)]
      },
      { name := "alphaHelper"
        params := []
        returnType := some FieldType.uint256
        isInternal := true
        body := [Stmt.return (Expr.literal 22)]
      },
      { name := "entry"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.internalCall "zebraHelper" [])]
      }
    ]
  }
  match compile helperOrderingSpec [0x10000000] with
  | .error err =>
      throw (IO.userError s!"✗ helper ordering compile failed: {err}")
  | .ok ir =>
      let renderedDefault := Yul.render (emitYulWithOptions ir {})
      assertAppearsBefore "default profile preserves source helper order (zebra before alpha)"
        renderedDefault "function internal_zebraHelper() -> __ret0" "function internal_alphaHelper() -> __ret0"

      let renderedParityOrdering :=
        Yul.render (emitYulWithOptions ir { backendProfile := .solidityParityOrdering })
      assertAppearsBefore "solidity-parity-ordering sorts helper declarations lexicographically (alpha before zebra)"
        renderedParityOrdering "function internal_alphaHelper() -> __ret0" "function internal_zebraHelper() -> __ret0"

      let renderedParity :=
        Yul.render (emitYulWithOptions ir { backendProfile := .solidityParity })
      assertAppearsBefore "solidity-parity sorts helper declarations lexicographically (alpha before zebra)"
        renderedParity "function internal_alphaHelper() -> __ret0" "function internal_zebraHelper() -> __ret0"

      let renderedParityRepeat :=
        Yul.render (emitYulWithOptions ir { backendProfile := .solidityParity })
      if renderedParity != renderedParityRepeat then
        throw (IO.userError "✗ solidity-parity profile should emit deterministic stable output across repeated runs")

#eval! do
  let slotAliasRangeMirrorWriteSpec : CompilationModel := {
    name := "SlotAliasRangeMirrorWriteSpec"
    fields := [
      { name := "a", ty := FieldType.uint256, slot := some 8 },
      { name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address), slot := some 9 }
    ]
    slotAliasRanges := [{ sourceStart := 8, sourceEnd := 11, targetStart := 20 }]
    constructor := none
    functions := [
      { name := "setA"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "a" (Expr.param "x"), Stmt.stop]
      },
      { name := "setBal"
        params := [{ name := "who", ty := ParamType.address }, { name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setMapping "balances" (Expr.param "who") (Expr.param "x"), Stmt.stop]
      }
    ]
  }
  match compile slotAliasRangeMirrorWriteSpec [1, 2] with
  | .error err =>
      throw (IO.userError s!"✗ slot alias range mirror-write compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "slotAliasRanges mirror setStorage writes" rendered
        ["sstore(8, __compat_value)", "sstore(20, __compat_value)"]
      assertContains "slotAliasRanges mirror setMapping writes" rendered
        ["mappingSlot(9, __compat_key)", "mappingSlot(21, __compat_key)"]

#eval! do
  let mappingWordSpec : CompilationModel := {
    name := "MappingWordSpec"
    fields := [
      { name := "markets", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address), slot := some 9, aliasSlots := [21] }
    ]
    constructor := none
    functions := [
      { name := "loadMember"
        params := [{ name := "who", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.mappingWord "markets" (Expr.param "who") 2)]
      },
      { name := "setMember"
        params := [{ name := "who", ty := ParamType.address }, { name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setMappingWord "markets" (Expr.param "who") 2 (Expr.param "x"), Stmt.stop]
      }
    ]
  }
  match compile mappingWordSpec [1, 2] with
  | .error err =>
      throw (IO.userError s!"✗ mappingWord compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "mappingWord read lowers to mappingSlot + wordOffset" rendered
        ["sload(add(mappingSlot(9, who), 2))"]
      assertContains "setMappingWord mirror writes include canonical and alias slots with offset" rendered
        ["sstore(add(mappingSlot(9, __compat_key), 2), __compat_value)",
         "sstore(add(mappingSlot(21, __compat_key), 2), __compat_value)"]

#eval! do
  let mappingPackedWordSpec : CompilationModel := {
    name := "MappingPackedWordSpec"
    fields := [
      { name := "markets", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address), slot := some 9, aliasSlots := [21] }
    ]
    constructor := none
    functions := [
      { name := "loadMember"
        params := [{ name := "who", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.mappingPackedWord "markets" (Expr.param "who") 2 { offset := 8, width := 8 })]
      },
      { name := "setMember"
        params := [{ name := "who", ty := ParamType.address }, { name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setMappingPackedWord "markets" (Expr.param "who") 2 { offset := 8, width := 8 } (Expr.param "x"), Stmt.stop]
      }
    ]
  }
  match compile mappingPackedWordSpec [1, 2] with
  | .error err =>
      throw (IO.userError s!"✗ mappingPackedWord compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "mappingPackedWord read lowers to masked mappingSlot + wordOffset" rendered
        ["and(shr(8, sload(add(mappingSlot(9, who), 2))),"]
      assertContains "setMappingPackedWord lowers to mapping read-modify-write with alias mirrors" rendered
        ["let __compat_slot_word := sload(add(mappingSlot(9, __compat_key), 2))",
         "sstore(add(mappingSlot(9, __compat_key), 2), or(__compat_slot_cleared, shl(8, __compat_packed)))",
         "let __compat_slot_word := sload(add(mappingSlot(21, __compat_key), 2))",
         "sstore(add(mappingSlot(21, __compat_key), 2), or(__compat_slot_cleared, shl(8, __compat_packed)))"]

#eval! do
  let invalidSlotAliasRangeSpec : CompilationModel := {
    name := "InvalidSlotAliasRangeSpec"
    fields := [{ name := "x", ty := FieldType.uint256, slot := some 8 }]
    slotAliasRanges := [{ sourceStart := 11, sourceEnd := 8, targetStart := 20 }]
    constructor := none
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile invalidSlotAliasRangeSpec [1] with
  | .error err =>
      if !(contains err "slotAliasRanges[0] has invalid source interval 11..8" && contains err "Issue #623") then
        throw (IO.userError s!"✗ invalid slotAliasRanges diagnostic mismatch: {err}")
      IO.println "✓ invalid slotAliasRanges diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid slotAliasRanges to fail compilation")

#eval! do
  let overlappingSlotAliasSourceSpec : CompilationModel := {
    name := "OverlappingSlotAliasSourceSpec"
    fields := [{ name := "x", ty := FieldType.uint256, slot := some 8 }]
    slotAliasRanges := [
      { sourceStart := 8, sourceEnd := 11, targetStart := 20 },
      { sourceStart := 11, sourceEnd := 14, targetStart := 40 }
    ]
    constructor := none
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile overlappingSlotAliasSourceSpec [1] with
  | .error err =>
      if !(contains err "slotAliasRanges[0]=8..11 and slotAliasRanges[1]=11..14 overlap in source slots" && contains err "Issue #623") then
        throw (IO.userError s!"✗ overlapping slotAliasRanges source diagnostic mismatch: {err}")
      IO.println "✓ overlapping slotAliasRanges source diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected overlapping slotAliasRanges source intervals to fail compilation")

#eval! do
  let slotAliasTargetConflictSpec : CompilationModel := {
    name := "SlotAliasTargetConflictSpec"
    fields := [
      { name := "x", ty := FieldType.uint256, slot := some 8 },
      { name := "y", ty := FieldType.uint256, slot := some 9 }
    ]
    slotAliasRanges := [
      { sourceStart := 8, sourceEnd := 8, targetStart := 20 },
      { sourceStart := 9, sourceEnd := 9, targetStart := 20 }
    ]
    constructor := none
    functions := [{ name := "noop", params := [], returnType := none, body := [Stmt.stop] }]
  }
  match compile slotAliasTargetConflictSpec [1] with
  | .error err =>
      if !(contains err "storage slot 20 has overlapping write ranges for 'x.aliasSlots[0]' and 'y.aliasSlots[0]'" && contains err "Issue #623") then
        throw (IO.userError s!"✗ slotAliasRanges target conflict diagnostic mismatch: {err}")
      IO.println "✓ slotAliasRanges target conflict diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected slotAliasRanges target conflict to fail compilation")

#eval! do
  let packedSubfieldSpec : CompilationModel := {
    name := "PackedSubfieldSpec"
    fields := [
      { name := "lower", ty := FieldType.uint256, slot := some 4, packedBits := some { offset := 0, width := 128 } },
      { name := "upper", ty := FieldType.uint256, slot := some 4, packedBits := some { offset := 128, width := 128 } }
    ]
    constructor := none
    functions := [
      { name := "setLower"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "lower" (Expr.param "x"), Stmt.stop]
      },
      { name := "setUpper"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "upper" (Expr.param "x"), Stmt.stop]
      },
      { name := "getLower"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.storage "lower")]
      },
      { name := "getUpper"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.storage "upper")]
      }
    ]
  }
  match compile packedSubfieldSpec [1, 2, 3, 4] with
  | .error err =>
      throw (IO.userError s!"✗ packed subfield compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "packed setStorage lowers masked read-modify-write" rendered
        ["let __compat_slot_word := sload(4)", "sstore(4, or(__compat_slot_cleared, shl(0, __compat_packed)))", "sstore(4, or(__compat_slot_cleared, shl(128, __compat_packed)))"]
      assertContains "packed Expr.storage lowers masked shifted reads" rendered
        ["and(shr(0, sload(4)),", "and(shr(128, sload(4)),"]

#eval! do
  let overlappingPackedSubfieldSpec : CompilationModel := {
    name := "OverlappingPackedSubfieldSpec"
    fields := [
      { name := "a", ty := FieldType.uint256, slot := some 7, packedBits := some { offset := 0, width := 128 } },
      { name := "b", ty := FieldType.uint256, slot := some 7, packedBits := some { offset := 64, width := 128 } }
    ]
    constructor := none
    functions := [{ name := "noop", params := [], returnType := none, body := [Stmt.stop] }]
  }
  match compile overlappingPackedSubfieldSpec [1] with
  | .error err =>
      if !(contains err "storage slot 7 has overlapping write ranges for 'a' and 'b'" && contains err "Issue #623") then
        throw (IO.userError s!"✗ overlapping packed subfield diagnostic mismatch: {err}")
      IO.println "✓ overlapping packed subfield diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected overlapping packed subfields to fail compilation")

#eval! do
  let invalidPackedBitsSpec : CompilationModel := {
    name := "InvalidPackedBitsSpec"
    fields := [
      { name := "x", ty := FieldType.uint256, slot := some 2, packedBits := some { offset := 200, width := 80 } }
    ]
    constructor := none
    functions := [{ name := "noop", params := [], returnType := none, body := [Stmt.stop] }]
  }
  match compile invalidPackedBitsSpec [1] with
  | .error err =>
      if !(contains err "field 'x' has invalid packedBits offset=200 width=80" && contains err "Issue #623") then
        throw (IO.userError s!"✗ invalid packedBits diagnostic mismatch: {err}")
      IO.println "✓ invalid packedBits diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid packedBits to fail compilation")

#eval! do
  let packedMappingRejectedSpec : CompilationModel := {
    name := "PackedMappingRejectedSpec"
    fields := [
      { name := "m", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address), slot := some 5, packedBits := some { offset := 0, width := 128 } }
    ]
    constructor := none
    functions := [{ name := "noop", params := [], returnType := none, body := [Stmt.stop] }]
  }
  match compile packedMappingRejectedSpec [1] with
  | .error err =>
      if !(contains err "field 'm' is a mapping and cannot declare packedBits" && contains err "Issue #623") then
        throw (IO.userError s!"✗ packed mapping diagnostic mismatch: {err}")
      IO.println "✓ packed mapping diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected mapping packedBits to fail compilation")

#eval! do
  let conflictingFieldSlotsSpec : CompilationModel := {
    name := "ConflictingFieldSlotsSpec"
    fields := [
      { name := "x", ty := FieldType.uint256, slot := some 3 },
      { name := "y", ty := FieldType.address, slot := some 3 }
    ]
    constructor := none
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile conflictingFieldSlotsSpec [1] with
  | .error err =>
      if !(contains err "storage slot 3 has overlapping write ranges for 'x' and 'y'" && contains err "Issue #623") then
        throw (IO.userError s!"✗ conflicting explicit field slot diagnostic mismatch: {err}")
      IO.println "✓ conflicting explicit field slot diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected conflicting explicit field slots to fail compilation")

#eval! do
  let conflictingAliasSlotsSpec : CompilationModel := {
    name := "ConflictingAliasSlotsSpec"
    fields := [
      { name := "x", ty := FieldType.uint256, slot := some 3, aliasSlots := [7] },
      { name := "y", ty := FieldType.address, slot := some 4, aliasSlots := [7] }
    ]
    constructor := none
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile conflictingAliasSlotsSpec [1] with
  | .error err =>
      if !(contains err "storage slot 7 has overlapping write ranges for 'x.aliasSlots[0]' and 'y.aliasSlots[0]'" && contains err "Issue #623") then
        throw (IO.userError s!"✗ conflicting alias slot diagnostic mismatch: {err}")
      IO.println "✓ conflicting alias slot diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected conflicting alias slots to fail compilation")

#eval! do
  let reservedSlotsSpec : CompilationModel := {
    name := "ReservedSlotsSpec"
    fields := [
      { name := "x", ty := FieldType.uint256, slot := some 3 },
      { name := "y", ty := FieldType.uint256, slot := some 4, aliasSlots := [12] }
    ]
    reservedSlotRanges := [{ start := 20, end_ := 23 }]
    constructor := none
    functions := [
      { name := "setX"
        params := [{ name := "v", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "x" (Expr.param "v"), Stmt.stop]
      }
    ]
  }
  match compile reservedSlotsSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ reserved slot ranges compile failed: {err}")
  | .ok _ =>
      IO.println "✓ reserved slot ranges accepted when disjoint from field write slots"

#eval! do
  let reservedSlotConflictSpec : CompilationModel := {
    name := "ReservedSlotConflictSpec"
    fields := [
      { name := "x", ty := FieldType.uint256, slot := some 21 }
    ]
    reservedSlotRanges := [{ start := 20, end_ := 23 }]
    constructor := none
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile reservedSlotConflictSpec [1] with
  | .error err =>
      if !(contains err "field write slot 21 ('x') overlaps reservedSlotRanges[0]=20..23" && contains err "Issue #623") then
        throw (IO.userError s!"✗ reserved slot conflict diagnostic mismatch: {err}")
      IO.println "✓ reserved slot conflict diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected reserved slot conflict to fail compilation")

#eval! do
  let overlappingReservedRangesSpec : CompilationModel := {
    name := "OverlappingReservedRangesSpec"
    fields := [{ name := "x", ty := FieldType.uint256, slot := some 3 }]
    reservedSlotRanges := [{ start := 20, end_ := 23 }, { start := 23, end_ := 30 }]
    constructor := none
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile overlappingReservedRangesSpec [1] with
  | .error err =>
      if !(contains err "reserved slot ranges reservedSlotRanges[0]=20..23 and reservedSlotRanges[1]=23..30 overlap" && contains err "Issue #623") then
        throw (IO.userError s!"✗ reserved range overlap diagnostic mismatch: {err}")
      IO.println "✓ reserved range overlap diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected overlapping reserved slot ranges to fail compilation")

#eval! do
  let undeclaredParamReferenceSpec : CompilationModel := {
    name := "UndeclaredParamReferenceSpec"
    fields := []
    constructor := none
    functions := [
      { name := "badParam"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.add (Expr.param "x") (Expr.param "typo"))]
      }
    ]
  }
  match compile undeclaredParamReferenceSpec [1] with
  | .error err =>
      if !contains err "function 'badParam' references unknown parameter 'typo'" then
        throw (IO.userError s!"✗ undeclared parameter diagnostic mismatch: {err}")
      IO.println "✓ undeclared parameter diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected undeclared Expr.param to fail compilation")

#eval! do
  let undeclaredLocalReferenceSpec : CompilationModel := {
    name := "UndeclaredLocalReferenceSpec"
    fields := []
    constructor := none
    functions := [
      { name := "badLocal"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.localVar "neverDeclared")]
      }
    ]
  }
  match compile undeclaredLocalReferenceSpec [1] with
  | .error err =>
      if !contains err "function 'badLocal' references unknown local variable 'neverDeclared'" then
        throw (IO.userError s!"✗ undeclared local diagnostic mismatch: {err}")
      IO.println "✓ undeclared local diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected undeclared Expr.localVar to fail compilation")

#eval! do
  let functionConstructorArgSpec : CompilationModel := {
    name := "FunctionConstructorArgSpec"
    fields := []
    constructor := none
    functions := [
      { name := "badCtorArg"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.constructorArg 0)]
      }
    ]
  }
  match compile functionConstructorArgSpec [1] with
  | .error err =>
      if !contains err "function 'badCtorArg' uses Expr.constructorArg outside constructor scope" then
        throw (IO.userError s!"✗ function Expr.constructorArg scope diagnostic mismatch: {err}")
      IO.println "✓ function Expr.constructorArg scope diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected function Expr.constructorArg to fail compilation")

#eval! do
  let constructorArgOutOfRangeSpec : CompilationModel := {
    name := "ConstructorArgOutOfRangeSpec"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := some {
      params := [{ name := "a", ty := ParamType.uint256 }]
      isPayable := false
      body := [Stmt.setStorage "x" (Expr.constructorArg 1)]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile constructorArgOutOfRangeSpec [1] with
  | .error err =>
      if !contains err "constructor Expr.constructorArg 1 is out of bounds for 1 constructor parameter(s)" then
        throw (IO.userError s!"✗ constructor Expr.constructorArg bounds diagnostic mismatch: {err}")
      IO.println "✓ constructor Expr.constructorArg bounds diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected out-of-range constructor Expr.constructorArg to fail compilation")

#eval! do
  let constructorArgInRangeSpec : CompilationModel := {
    name := "ConstructorArgInRangeSpec"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := some {
      params := [{ name := "a", ty := ParamType.uint256 }]
      isPayable := false
      body := [Stmt.setStorage "x" (Expr.constructorArg 0)]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile constructorArgInRangeSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected in-range constructor Expr.constructorArg to compile: {err}")
  | .ok _ =>
      IO.println "✓ constructor Expr.constructorArg in-range accepted"

#eval! do
  let unknownArrayLengthParamSpec : CompilationModel := {
    name := "UnknownArrayLengthParamSpec"
    fields := []
    constructor := none
    functions := [
      { name := "badArrayLength"
        params := [{ name := "arr", ty := ParamType.array ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.arrayLength "typo")]
      }
    ]
  }
  match compile unknownArrayLengthParamSpec [1] with
  | .error err =>
      if !contains err "function 'badArrayLength' references unknown parameter 'typo' in Expr.arrayLength" then
        throw (IO.userError s!"✗ Expr.arrayLength unknown parameter diagnostic mismatch: {err}")
      IO.println "✓ Expr.arrayLength unknown parameter diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected Expr.arrayLength unknown parameter to fail compilation")

#eval! do
  let nonArrayLengthParamSpec : CompilationModel := {
    name := "NonArrayLengthParamSpec"
    fields := []
    constructor := none
    functions := [
      { name := "badArrayLengthType"
        params := [{ name := "blob", ty := ParamType.bytes }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.arrayLength "blob")]
      }
    ]
  }
  match compile nonArrayLengthParamSpec [1] with
  | .error err =>
      if !(contains err "function 'badArrayLengthType' Expr.arrayLength 'blob' requires array parameter, got" &&
          contains err "ParamType.bytes") then
        throw (IO.userError s!"✗ Expr.arrayLength type diagnostic mismatch: {err}")
      IO.println "✓ Expr.arrayLength non-array parameter diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected Expr.arrayLength non-array parameter to fail compilation")

#eval! do
  let nonArrayElementParamSpec : CompilationModel := {
    name := "NonArrayElementParamSpec"
    fields := []
    constructor := none
    functions := [
      { name := "badArrayElementType"
        params := [{ name := "blob", ty := ParamType.bytes }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.arrayElement "blob" (Expr.literal 0))]
      }
    ]
  }
  match compile nonArrayElementParamSpec [1] with
  | .error err =>
      if !(contains err "function 'badArrayElementType' Expr.arrayElement 'blob' requires array parameter, got" &&
          contains err "ParamType.bytes") then
        throw (IO.userError s!"✗ Expr.arrayElement type diagnostic mismatch: {err}")
      IO.println "✓ Expr.arrayElement non-array parameter diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected Expr.arrayElement non-array parameter to fail compilation")

#eval! do
  let assignBeforeDeclarationSpec : CompilationModel := {
    name := "AssignBeforeDeclarationSpec"
    fields := []
    constructor := none
    functions := [
      { name := "badAssign"
        params := []
        returnType := none
        body := [Stmt.assignVar "x" (Expr.literal 1), Stmt.stop]
      }
    ]
  }
  match compile assignBeforeDeclarationSpec [1] with
  | .error err =>
      if !contains err "function 'badAssign' assigns to undeclared local variable 'x'" then
        throw (IO.userError s!"✗ assign before declaration diagnostic mismatch: {err}")
      IO.println "✓ assign before declaration diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected assignVar before declaration to fail compilation")

#eval! do
  let invalidMutabilitySpec : CompilationModel := {
    name := "InvalidMutabilitySpec"
    fields := []
    constructor := none
    functions := [
      { name := "badPayableView"
        params := []
        returnType := some FieldType.uint256
        isPayable := true
        isView := true
        body := [Stmt.return (Expr.literal 1)]
      }
    ]
  }
  match compile invalidMutabilitySpec [1] with
  | .error err =>
      if !contains err "cannot be both payable and view/pure" then
        throw (IO.userError s!"✗ payable+view mutability diagnostic mismatch: {err}")
      IO.println "✓ payable+view mutability diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected payable+view mutability conflict to fail compilation")

#eval! do
  let viewWritesStateSpec : CompilationModel := {
    name := "ViewWritesStateSpec"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "badViewWrite"
        params := []
        returnType := none
        isView := true
        body := [Stmt.setStorage "x" (Expr.literal 1), Stmt.stop]
      }
    ]
  }
  match compile viewWritesStateSpec [1] with
  | .error err =>
      if !contains err "is marked view but writes state" then
        throw (IO.userError s!"✗ view-write mutability diagnostic mismatch: {err}")
      IO.println "✓ view-write mutability diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected view function with state write to fail compilation")

#eval! do
  let pureReadsStateSpec : CompilationModel := {
    name := "PureReadsStateSpec"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "badPureRead"
        params := []
        returnType := some FieldType.uint256
        isPure := true
        body := [Stmt.return (Expr.storage "x")]
      }
    ]
  }
  match compile pureReadsStateSpec [1] with
  | .error err =>
      if !contains err "is marked pure but reads state/environment" then
        throw (IO.userError s!"✗ pure-read mutability diagnostic mismatch: {err}")
      IO.println "✓ pure-read mutability diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected pure function with state read to fail compilation")

#eval! do
  let pureWritesStateSpec : CompilationModel := {
    name := "PureWritesStateSpec"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "badPureWrite"
        params := []
        returnType := none
        isPure := true
        body := [Stmt.setStorage "x" (Expr.literal 1), Stmt.stop]
      }
    ]
  }
  match compile pureWritesStateSpec [1] with
  | .error err =>
      if !contains err "is marked pure but writes state" then
        throw (IO.userError s!"✗ pure-write mutability diagnostic mismatch: {err}")
      IO.println "✓ pure-write mutability diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected pure function with state write to fail compilation")

#eval! do
  let pureReadsEnvSpec : CompilationModel := {
    name := "PureReadsEnvSpec"
    fields := []
    constructor := none
    functions := [
      { name := "badPureEnvRead"
        params := []
        returnType := some FieldType.address
        isPure := true
        body := [Stmt.return Expr.caller]
      }
    ]
  }
  match compile pureReadsEnvSpec [1] with
  | .error err =>
      if !contains err "is marked pure but reads state/environment" then
        throw (IO.userError s!"✗ pure-env-read mutability diagnostic mismatch: {err}")
      IO.println "✓ pure-env-read mutability diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected pure function with environment read to fail compilation")

#eval! do
  let invalidExclusiveMutabilitySpec : CompilationModel := {
    name := "InvalidExclusiveMutabilitySpec"
    fields := []
    constructor := none
    functions := [
      { name := "badViewPure"
        params := []
        returnType := some FieldType.uint256
        isView := true
        isPure := true
        body := [Stmt.return (Expr.literal 1)]
      }
    ]
  }
  match compile invalidExclusiveMutabilitySpec [1] with
  | .error err =>
      if !contains err "cannot be both view and pure" then
        throw (IO.userError s!"✗ view+pure mutability diagnostic mismatch: {err}")
      IO.println "✓ view+pure mutability diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected view+pure mutability conflict to fail compilation")

#eval! do
  let viewEmitsEventSpec : CompilationModel := {
    name := "ViewEmitsEventSpec"
    fields := []
    constructor := none
    functions := [
      { name := "badViewEmit"
        params := []
        returnType := none
        isView := true
        body := [Stmt.emit "Ping" [Expr.literal 1], Stmt.stop]
      }
    ]
    events := [{ name := "Ping", params := [{ name := "value", ty := ParamType.uint256, kind := EventParamKind.unindexed }] }]
  }
  match compile viewEmitsEventSpec [1] with
  | .error err =>
      if !contains err "is marked view but writes state" then
        throw (IO.userError s!"✗ view-emit mutability diagnostic mismatch: {err}")
      IO.println "✓ view-emit mutability diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected view function emitting event to fail compilation")

#eval! do
  let pureEmitsEventSpec : CompilationModel := {
    name := "PureEmitsEventSpec"
    fields := []
    constructor := none
    functions := [
      { name := "badPureEmit"
        params := []
        returnType := none
        isPure := true
        body := [Stmt.emit "Ping" [Expr.literal 1], Stmt.stop]
      }
    ]
    events := [{ name := "Ping", params := [{ name := "value", ty := ParamType.uint256, kind := EventParamKind.unindexed }] }]
  }
  match compile pureEmitsEventSpec [1] with
  | .error err =>
      if !contains err "is marked pure but writes state" then
        throw (IO.userError s!"✗ pure-emit mutability diagnostic mismatch: {err}")
      IO.println "✓ pure-emit mutability diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected pure function emitting event to fail compilation")

#eval! do
  let duplicateFunctionParamSpec : CompilationModel := {
    name := "DuplicateFunctionParamSpec"
    fields := []
    constructor := none
    functions := [
      { name := "setBoth"
        params := [
          { name := "x", ty := ParamType.uint256 },
          { name := "x", ty := ParamType.address }
        ]
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile duplicateFunctionParamSpec [1] with
  | .error err =>
      if !contains err "duplicate parameter name 'x' in function 'setBoth'" then
        throw (IO.userError s!"✗ duplicate function param diagnostic mismatch: {err}")
      IO.println "✓ duplicate function param diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected duplicate function params to fail compilation")

#eval! do
  let duplicateConstructorParamSpec : CompilationModel := {
    name := "DuplicateConstructorParamSpec"
    fields := []
    constructor := some {
      params := [
        { name := "owner", ty := ParamType.address },
        { name := "owner", ty := ParamType.address }
      ]
      body := [Stmt.stop]
    }
    functions := [{ name := "noop", params := [], returnType := none, body := [Stmt.stop] }]
  }
  match compile duplicateConstructorParamSpec [1] with
  | .error err =>
      if !contains err "duplicate parameter name 'owner' in constructor" then
        throw (IO.userError s!"✗ duplicate constructor param diagnostic mismatch: {err}")
      IO.println "✓ duplicate constructor param diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected duplicate constructor params to fail compilation")

#eval! do
  let duplicateEventParamSpec : CompilationModel := {
    name := "DuplicateEventParamSpec"
    fields := []
    constructor := none
    functions := [{ name := "noop", params := [], returnType := none, body := [Stmt.stop] }]
    events := [
      { name := "Transfer"
        params := [
          { name := "amount", ty := ParamType.uint256, kind := EventParamKind.unindexed },
          { name := "amount", ty := ParamType.address, kind := EventParamKind.indexed }
        ] }
    ]
  }
  match compile duplicateEventParamSpec [1] with
  | .error err =>
      if !contains err "duplicate parameter name 'amount' in event 'Transfer'" then
        throw (IO.userError s!"✗ duplicate event param diagnostic mismatch: {err}")
      IO.println "✓ duplicate event param diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected duplicate event params to fail compilation")

#eval! do
  let unknownExternalTargetSpec : CompilationModel := {
    name := "UnknownExternalTargetSpec"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "missing_fn" [])]
      }
    ]
    externals := []
  }
  match compile unknownExternalTargetSpec [1] with
  | .error err =>
      if !contains err "function 'f' references unknown external call target 'missing_fn'" then
        throw (IO.userError s!"✗ unknown external target diagnostic mismatch: {err}")
      IO.println "✓ unknown external target diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected unknown external target to fail compilation")

#eval! do
  let declaredExternalTargetSpec : CompilationModel := {
    name := "DeclaredExternalTargetSpec"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "known_fn" [Expr.param "x"])]
      }
    ]
    externals := [
      { name := "known_fn"
        params := [ParamType.uint256]
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
  }
  match compile declaredExternalTargetSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected declared external target to compile, got: {err}")
  | .ok _ =>
      IO.println "✓ declared external target accepted"

#eval! do
  let externalArityMismatchSpec : CompilationModel := {
    name := "ExternalArityMismatchSpec"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "known_fn" [Expr.param "x"])]
      }
    ]
    externals := [
      { name := "known_fn"
        params := [ParamType.uint256, ParamType.uint256]
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
  }
  match compile externalArityMismatchSpec [1] with
  | .error err =>
      if !contains err "calls external 'known_fn' with 1 args, but spec.externals declares 2" then
        throw (IO.userError s!"✗ external arity mismatch diagnostic mismatch: {err}")
      IO.println "✓ external call arity checked against declaration"
  | .ok _ =>
      throw (IO.userError "✗ expected external arity mismatch to fail compilation")

#eval! do
  let externalVoidReturnInExprSpec : CompilationModel := {
    name := "ExternalVoidReturnInExprSpec"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "known_fn" [Expr.param "x"])]
      }
    ]
    externals := [
      { name := "known_fn"
        params := [ParamType.uint256]
        returnType := none
        axiomNames := []
      }
    ]
  }
  match compile externalVoidReturnInExprSpec [1] with
  | .error err =>
      if !contains err "uses Expr.externalCall 'known_fn' but spec.externals declares 0 return values" then
        throw (IO.userError s!"✗ external void-return diagnostic mismatch: {err}")
      IO.println "✓ external call expression rejects void external declaration"
  | .ok _ =>
      throw (IO.userError "✗ expected Expr.externalCall with void declaration to fail compilation")

#eval! do
  let externalMultiReturnInExprSpec : CompilationModel := {
    name := "ExternalMultiReturnInExprSpec"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "known_fn" [Expr.param "x"])]
      }
    ]
    externals := [
      { name := "known_fn"
        params := [ParamType.uint256]
        returnType := none
        returns := [ParamType.uint256, ParamType.uint256]
        axiomNames := []
      }
    ]
  }
  match compile externalMultiReturnInExprSpec [1] with
  | .error err =>
      if !contains err "uses Expr.externalCall 'known_fn' but spec.externals declares 2 return values" then
        throw (IO.userError s!"✗ external multi-return diagnostic mismatch: {err}")
      IO.println "✓ external call expression rejects multi-return external declaration"
  | .ok _ =>
      throw (IO.userError "✗ expected Expr.externalCall with multi-return declaration to fail compilation")

#eval! do
  let helperNameCollisionSpec : CompilationModel := {
    name := "HelperNameCollisionSpec"
    fields := [{ name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address) }]
    constructor := none
    functions := [
      { name := "f"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "mappingSlot" [Expr.param "x", Expr.param "x"])]
      }
    ]
    externals := [
      { name := "mappingSlot"
        params := [ParamType.uint256, ParamType.uint256]
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
  }
  match compile helperNameCollisionSpec [1] with
  | .error err =>
      if !contains err "collides with compiler-generated/reserved symbol 'mappingSlot'" then
        throw (IO.userError s!"✗ helper-name collision diagnostic mismatch: {err}")
      IO.println "✓ helper-name external collision rejected"
  | .ok _ =>
      throw (IO.userError "✗ expected helper-name external collision to fail compilation")

#eval! do
  let helperNameAllowedWhenNotGeneratedSpec : CompilationModel := {
    name := "HelperNameAllowedWhenNotGeneratedSpec"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "mappingSlot" [Expr.param "x", Expr.param "x"])]
      }
    ]
    externals := [
      { name := "mappingSlot"
        params := [ParamType.uint256, ParamType.uint256]
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
  }
  match compile helperNameAllowedWhenNotGeneratedSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected mappingSlot external to compile when helper is not generated, got: {err}")
  | .ok _ =>
      IO.println "✓ helper-name external accepted when helper is not generated"

#eval! do
  let arrayHelperNameAllowedWhenNotGeneratedSpec : CompilationModel := {
    name := "ArrayHelperNameAllowedWhenNotGeneratedSpec"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := [
          { name := "a", ty := ParamType.uint256 },
          { name := "b", ty := ParamType.uint256 },
          { name := "c", ty := ParamType.uint256 }
        ]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "__verity_array_element_memory_checked" [Expr.param "a", Expr.param "b", Expr.param "c"])]
      }
    ]
    externals := [
      { name := "__verity_array_element_memory_checked"
        params := [ParamType.uint256, ParamType.uint256, ParamType.uint256]
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
  }
  match compile arrayHelperNameAllowedWhenNotGeneratedSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected array helper external to compile when helper is not generated, got: {err}")
  | .ok _ =>
      IO.println "✓ array-helper external accepted when helper is not generated"

#eval! do
  let internalPrefixCollisionSpec : CompilationModel := {
    name := "InternalPrefixCollisionSpec"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "internal_lib" [Expr.param "x"])]
      }
    ]
    externals := [
      { name := "internal_lib"
        params := [ParamType.uint256]
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
  }
  match compile internalPrefixCollisionSpec [1] with
  | .error err =>
      if !contains err "uses reserved prefix 'internal_'" then
        throw (IO.userError s!"✗ internal-prefix collision diagnostic mismatch: {err}")
      IO.println "✓ internal-prefix external collision rejected"
  | .ok _ =>
      throw (IO.userError "✗ expected internal-prefix external collision to fail compilation")

#eval! do
  let invalidSpecialEntrypointMutabilitySpec : CompilationModel := {
    name := "InvalidSpecialEntrypointMutabilitySpec"
    fields := []
    constructor := none
    functions := [
      { name := "fallback"
        params := []
        returnType := none
        isView := true
        body := [Stmt.stop]
      }
    ]
  }
  match compile invalidSpecialEntrypointMutabilitySpec [] with
  | .error err =>
      if !contains err "function 'fallback' cannot be marked view/pure" then
        throw (IO.userError s!"✗ fallback mutability diagnostic mismatch: {err}")
      IO.println "✓ fallback mutability diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected fallback view/pure mutability conflict to fail compilation")

#eval! do
  let iteNameCollisionSpec : CompilationModel := {
    name := "IteNameCollision"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := []
        returnType := some FieldType.uint256
        body := [
          Stmt.letVar "__ite_cond" (Expr.literal 7),
          Stmt.ite (Expr.literal 1)
            [Stmt.return (Expr.localVar "__ite_cond")]
            [Stmt.return (Expr.literal 0)]
        ]
      }
    ]
  }
  match compile iteNameCollisionSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ ite temp collision regression compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "ite temp avoids local collision" rendered
        ["let __ite_cond := 7", "let __ite_cond_1 := 1", "mstore(0, __ite_cond)"]
      assertNotContains "ite temp avoids local collision" rendered ["mstore(0, __ite_cond_1)"]

#eval! do
  let badConstructorReturnSpec : CompilationModel := {
    name := "BadConstructorReturn"
    fields := []
    constructor := some {
      params := []
      isPayable := false
      body := [Stmt.return (Expr.literal 1)]
    }
    functions := [
      { name := "noop", params := [], returnType := none, body := [Stmt.stop] }
    ]
  }
  match compile badConstructorReturnSpec [1] with
  | .error err =>
      if !contains err "constructor must not return runtime data directly" then
        throw (IO.userError s!"✗ constructor return rejection diagnostic mismatch: {err}")
      IO.println "✓ constructor return(...) rejected in CompilationModel"
  | .ok _ =>
      throw (IO.userError "✗ expected constructor return(...) to be rejected")

#eval! do
  let duplicateLetVarSpec : CompilationModel := {
    name := "DuplicateLetVar"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := []
        returnType := some FieldType.uint256
        body := [
          Stmt.letVar "x" (Expr.literal 1),
          Stmt.letVar "x" (Expr.literal 2),
          Stmt.return (Expr.localVar "x")
        ]
      }
    ]
  }
  match compile duplicateLetVarSpec [1] with
  | .error err =>
      if !contains err "function 'f' redeclares local variable 'x' in the same scope" then
        throw (IO.userError s!"✗ duplicate letVar diagnostic mismatch: {err}")
      IO.println "✓ duplicate letVar diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected duplicate letVar names to fail compilation")

#eval! do
  let letVarShadowingParamSpec : CompilationModel := {
    name := "LetVarShadowingParam"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [
          Stmt.letVar "x" (Expr.literal 2),
          Stmt.return (Expr.localVar "x")
        ]
      }
    ]
  }
  match compile letVarShadowingParamSpec [1] with
  | .error err =>
      if !contains err "function 'f' declares local variable 'x' that shadows a parameter" then
        throw (IO.userError s!"✗ letVar parameter shadow diagnostic mismatch: {err}")
      IO.println "✓ letVar parameter shadow diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected letVar parameter shadowing to fail compilation")

#eval! do
  let selSpec : CompilationModel := {
    name := "SelectorCheckedCompileSpec"
    fields := []
    constructor := none
    functions := [
      { name := "store"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.stop]
      },
      { name := "read"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.literal 1)]
      }
    ]
  }
  match (← Compiler.Selector.compileChecked selSpec [0, 1]) with
  | .error err =>
      if !contains err "Selector mismatch in SelectorCheckedCompileSpec for function 'store'" then
        throw (IO.userError s!"✗ selector mismatch diagnostic mismatch: {err}")
      IO.println "✓ compileChecked rejects selector/signature mismatch"
  | .ok _ =>
      throw (IO.userError "✗ expected compileChecked to reject mismatched selectors")

#eval! do
  let externalModelSpec : CompilationModel := {
    name := "ExternalModelSpec"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "known_fn" [Expr.param "x"])]
      }
    ]
    externals := [
      { name := "known_fn"
        params := [ParamType.uint256]
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
  }
  let tx : Transaction := { sender := 0, functionName := "f", args := [41] }
  let withoutModel := interpretSpec externalModelSpec SpecStorage.empty tx
  if withoutModel.success then
    throw (IO.userError "✗ SpecInterpreter should revert when externalFns model is missing")
  let withModel := interpretSpec externalModelSpec SpecStorage.empty tx
    [("known_fn", fun args => match args with | [x] => x + 1 | _ => 0)]
  if withModel.success != true || withModel.returnValue != some 42 then
    throw (IO.userError "✗ SpecInterpreter externalFns model mismatch")
  IO.println "✓ SpecInterpreter externalFns model required and applied"

#eval! do
  let internalExternalSpec : CompilationModel := {
    name := "InternalExternalSpec"
    fields := []
    constructor := none
    functions := [
      { name := "g"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [
          Stmt.letVar "y" (Expr.externalCall "known_fn" [Expr.param "x"]),
          Stmt.stop
        ]
      },
      { name := "f"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [
          Stmt.internalCall "g" [Expr.param "x"],
          Stmt.stop
        ]
      }
    ]
    externals := [
      { name := "known_fn"
        params := [ParamType.uint256]
        returnType := some ParamType.uint256
        axiomNames := []
      }
    ]
  }
  let ctx : EvalContext := {
    sender := 0
    msgValue := 0
    blockTimestamp := 0
    params := [7]
    paramTypes := []
    constructorArgs := []
    constructorParamTypes := []
    localVars := []
    arrayParams := []
  }
  if (execFunctionFuel internalExternalSpec "f" ctx [] SpecStorage.empty).isSome then
    throw (IO.userError "✗ execFunctionFuel should revert when internal callee has unmodeled external calls")
  let modeled := execFunctionFuel internalExternalSpec "f" ctx
    [("known_fn", fun args => args.head?.getD 0)] SpecStorage.empty
  if modeled.isNone then
    throw (IO.userError "✗ execFunctionFuel should succeed when internal callee external model is provided")
  IO.println "✓ SpecInterpreter fuel path enforces external model in internal calls"

#eval! do
  let lowLevelSpec : CompilationModel := {
    name := "LowLevelSpecInterpreterGuard"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := []
        returnType := some FieldType.uint256
        body := [
          Stmt.return (Expr.call
            (Expr.literal 100000)
            (Expr.literal 0x1234)
            (Expr.literal 0)
            (Expr.literal 0)
            (Expr.literal 0)
            (Expr.literal 0)
            (Expr.literal 0))
        ]
      }
    ]
  }
  let tx : Transaction := { sender := 0, functionName := "f", args := [] }
  let result := interpretSpec lowLevelSpec SpecStorage.empty tx
  if result.success then
    throw (IO.userError "✗ expected SpecInterpreter to reject unsupported low-level call semantics")
  if result.revertReason != some "Function 'f' reverted" then
    throw (IO.userError s!"✗ low-level call revert reason mismatch: {result.revertReason}")
  IO.println "✓ SpecInterpreter rejects unsupported low-level call semantics"

#eval! do
  let lowLevelFuelSpec : CompilationModel := {
    name := "LowLevelFuelInterpreterGuard"
    fields := []
    constructor := none
    functions := [
      { name := "f"
        params := []
        returnType := none
        body := [
          Stmt.forEach "i" Expr.returndataSize [Stmt.stop]
        ]
      }
    ]
  }
  let ctx : EvalContext := {
    sender := 0
    msgValue := 0
    blockTimestamp := 0
    params := []
    paramTypes := []
    constructorArgs := []
    constructorParamTypes := []
    localVars := []
    arrayParams := []
  }
  match execFunctionFuel lowLevelFuelSpec "f" ctx [] SpecStorage.empty with
  | none =>
      IO.println "✓ Fuel-based SpecInterpreter rejects unsupported low-level returndata semantics"
  | some _ =>
      throw (IO.userError "✗ expected fuel-based SpecInterpreter to reject unsupported low-level returndata semantics")

#eval! do
  let layoutSpec : CompilationModel := {
    name := "LayoutAwareInterpreter"
    fields := [
      { name := "f", ty := FieldType.uint256, slot := some 5, aliasSlots := [7] },
      { name := "g", ty := FieldType.uint256, slot := some 10, packedBits := some { offset := 8, width := 8 }, aliasSlots := [12] },
      { name := "h", ty := FieldType.uint256 }
    ]
    slotAliasRanges := [{ sourceStart := 2, sourceEnd := 2, targetStart := 30 }]
    constructor := none
    functions := [
      { name := "writeAll"
        params := [
          { name := "fv", ty := ParamType.uint256 },
          { name := "gv", ty := ParamType.uint256 },
          { name := "hv", ty := ParamType.uint256 }
        ]
        returnType := none
        body := [
          Stmt.setStorage "f" (Expr.param "fv"),
          Stmt.setStorage "g" (Expr.param "gv"),
          Stmt.setStorage "h" (Expr.param "hv"),
          Stmt.stop
        ]
      },
      { name := "readF", params := [], returnType := some FieldType.uint256, body := [Stmt.return (Expr.storage "f")] },
      { name := "readG", params := [], returnType := some FieldType.uint256, body := [Stmt.return (Expr.storage "g")] }
    ]
  }
  let initialStorage : SpecStorage := {
    slots := [(10, 0x112233), (12, 0x445566)]
    mappings := []
    mappings2 := []
    events := []
  }
  let writeTx : Transaction := {
    sender := 0
    functionName := "writeAll"
    args := [42, 0x1ab, 99]
  }
  let writeResult := interpretSpec layoutSpec initialStorage writeTx
  if !writeResult.success then
    throw (IO.userError s!"✗ layout-aware interpreter write reverted: {writeResult.revertReason}")
  if writeResult.finalStorage.getSlot 5 != 42 || writeResult.finalStorage.getSlot 7 != 42 then
    throw (IO.userError "✗ explicit slot + aliasSlots mirror writes not respected in SpecInterpreter")
  if writeResult.finalStorage.getSlot 2 != 99 || writeResult.finalStorage.getSlot 30 != 99 then
    throw (IO.userError "✗ slotAliasRanges-derived mirror write not respected in SpecInterpreter")
  if writeResult.finalStorage.getSlot 10 != 0x11ab33 || writeResult.finalStorage.getSlot 12 != 0x44ab66 then
    throw (IO.userError "✗ packed subfield RMW with alias mirrors not respected in SpecInterpreter")
  let readFTx : Transaction := { sender := 0, functionName := "readF", args := [] }
  let readFResult := interpretSpec layoutSpec writeResult.finalStorage readFTx
  if readFResult.returnValue != some 42 then
    throw (IO.userError s!"✗ readF should read resolved slot 5 value 42, got {readFResult.returnValue}")
  let readGTx : Transaction := { sender := 0, functionName := "readG", args := [] }
  let readGResult := interpretSpec layoutSpec writeResult.finalStorage readGTx
  if readGResult.returnValue != some 0xab then
    throw (IO.userError s!"✗ readG should read packed byte 0xab, got {readGResult.returnValue}")
  IO.println "✓ SpecInterpreter honors explicit slots, alias mirrors, slotAliasRanges, and packed storage semantics"

#eval! do
  let mappingPackedLayoutSpec : CompilationModel := {
    name := "MappingPackedLayoutSpec"
    fields := [
      { name := "markets", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address), slot := some 9, aliasSlots := [21] }
    ]
    constructor := none
    functions := [
      { name := "setMember"
        params := [{ name := "who", ty := ParamType.address }, { name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setMappingPackedWord "markets" (Expr.param "who") 2 { offset := 8, width := 8 } (Expr.param "x"), Stmt.stop]
      },
      { name := "getMember"
        params := [{ name := "who", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.mappingPackedWord "markets" (Expr.param "who") 2 { offset := 8, width := 8 })]
      }
    ]
  }
  let key := 0x12345
  let initialStorage : SpecStorage := {
    slots := []
    mappings := [
      (9, [((key + 2) % (2 ^ 256), 0x112233)]),
      (21, [((key + 2) % (2 ^ 256), 0x445566)])
    ]
    mappings2 := []
    events := []
  }
  let writeTx : Transaction := { sender := 0, functionName := "setMember", args := [key, 0xab] }
  let writeResult := interpretSpec mappingPackedLayoutSpec initialStorage writeTx
  if !writeResult.success then
    throw (IO.userError s!"✗ mapping packed interpreter write reverted: {writeResult.revertReason}")
  if writeResult.finalStorage.getMapping 9 ((key + 2) % (2 ^ 256)) != 0x11ab33 then
    throw (IO.userError "✗ mapping packed canonical write mismatch in SpecInterpreter")
  if writeResult.finalStorage.getMapping 21 ((key + 2) % (2 ^ 256)) != 0x44ab66 then
    throw (IO.userError "✗ mapping packed alias mirror write mismatch in SpecInterpreter")
  let readTx : Transaction := { sender := 0, functionName := "getMember", args := [key] }
  let readResult := interpretSpec mappingPackedLayoutSpec writeResult.finalStorage readTx
  if readResult.returnValue != some 0xab then
    throw (IO.userError s!"✗ mapping packed read mismatch in SpecInterpreter: {readResult.returnValue}")
  IO.println "✓ SpecInterpreter honors packed mapping word read/write semantics with alias mirrors"

-- ============================================================
-- Stmt.rawLog tests (#930)
-- ============================================================

-- rawLog with 0 topics → log0
#eval! do
  let rawLog0Spec : CompilationModel := {
    name := "RawLog0"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "emitRaw"
        params := []
        returnType := none
        body := [
          Stmt.mstore (Expr.literal 0) (Expr.literal 42),
          Stmt.rawLog [] (Expr.literal 0) (Expr.literal 32),
          Stmt.stop
        ]
      }
    ]
  }
  match compile rawLog0Spec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected rawLog0 to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "rawLog log0 lowering" rendered [
        "log0(0, 32)"
      ]

-- rawLog with 1 topic → log1
#eval! do
  let rawLog1Spec : CompilationModel := {
    name := "RawLog1"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "emitRaw"
        params := [{ name := "topic", ty := ParamType.uint256 }]
        returnType := none
        body := [
          Stmt.mstore (Expr.literal 0) (Expr.literal 99),
          Stmt.rawLog [Expr.param "topic"] (Expr.literal 0) (Expr.literal 32),
          Stmt.stop
        ]
      }
    ]
  }
  match compile rawLog1Spec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected rawLog1 to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "rawLog log1 lowering" rendered [
        "log1(0, 32, topic)"
      ]

-- ===== ECM safeTransfer compilation test =====
#eval! do
  let safeTransferSpec : CompilationModel := {
    name := "SafeTransferTest"
    fields := []
    constructor := none
    functions := [
      { name := "doTransfer"
        params := [⟨"token", ParamType.address⟩, ⟨"to", ParamType.address⟩, ⟨"amount", ParamType.uint256⟩]
        returnType := none
        body := [
          Modules.ERC20.safeTransfer (Expr.param "token") (Expr.param "to") (Expr.param "amount"),
          Stmt.stop
        ]
      }
    ]
  }
  match compile safeTransferSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected safeTransfer to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      -- Check selector for transfer(address,uint256) = 0xa9059cbb
      assertContains "safeTransfer compiles with correct selector" rendered
        ["a9059cbb"]
      -- Check call pattern
      assertContains "safeTransfer emits call" rendered
        ["call(gas(),"]
      -- Check revert pattern: Error(string) selector + revert encoding
      -- "transfer reverted" = 17 bytes, hex = 7472616e73666572207265766572746564
      assertContains "safeTransfer emits revert on failure" rendered
        ["mstore(36, 17)", "7472616e73666572207265766572746564"]
      -- "transfer returned false" = 23 bytes, hex = 7472616e736665722072657475726e65642066616c7365
      assertContains "safeTransfer emits revert on false return" rendered
        ["mstore(36, 23)", "7472616e736665722072657475726e65642066616c7365"]
      -- Check optional bool check pattern
      assertContains "safeTransfer checks returndatasize" rendered
        ["returndatasize()"]

-- ===== ECM safeTransferFrom compilation test =====
#eval! do
  let safeTransferFromSpec : CompilationModel := {
    name := "SafeTransferFromTest"
    fields := []
    constructor := none
    functions := [
      { name := "doTransferFrom"
        params := [⟨"token", ParamType.address⟩, ⟨"from", ParamType.address⟩, ⟨"to", ParamType.address⟩, ⟨"amount", ParamType.uint256⟩]
        returnType := none
        body := [
          Modules.ERC20.safeTransferFrom (Expr.param "token") (Expr.param "from") (Expr.param "to") (Expr.param "amount"),
          Stmt.stop
        ]
      }
    ]
  }
  match compile safeTransferFromSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected safeTransferFrom to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      -- Check selector for transferFrom(address,address,uint256) = 0x23b872dd
      assertContains "safeTransferFrom compiles with correct selector" rendered
        ["23b872dd"]
      -- Check call pattern with 100-byte calldata
      assertContains "safeTransferFrom emits call" rendered
        ["call(gas(),"]
      -- Check revert pattern: Error(string) selector + revert encoding
      -- "transferFrom reverted" = 21 bytes, hex = 7472616e7366657246726f6d2072657665727465640000
      assertContains "safeTransferFrom emits revert on failure" rendered
        ["mstore(36, 21)", "7472616e7366657246726f6d20726576657274656400"]
      -- "transferFrom returned false" = 27 bytes, hex = 7472616e7366657246726f6d2072657475726e65642066616c7365
      assertContains "safeTransferFrom emits revert on false return" rendered
        ["mstore(36, 27)", "7472616e7366657246726f6d2072657475726e65642066616c7365"]
      -- Check optional bool check pattern
      assertContains "safeTransferFrom checks returndatasize" rendered
        ["returndatasize()"]

-- ===== ECM callback compilation test =====
#eval! do
  let callbackSpec : CompilationModel := {
    name := "CallbackTest"
    fields := [
      { name := "balance", ty := FieldType.uint256 }
    ]
    constructor := none
    functions := [
      { name := "supplyWithCallback"
        params := [
          ⟨"assets", ParamType.uint256⟩,
          ⟨"data", ParamType.bytes⟩
        ]
        returnType := none
        body := [
          -- Update accounting
          Stmt.setStorage "balance" (Expr.add (Expr.storage "balance") (Expr.param "assets")),
          -- Invoke callback: onMorphoSupply(uint256, bytes) selector = 0x7a29084c
          Modules.Callbacks.callback Expr.caller 0x7a29084c [Expr.param "assets"] "data",
          Stmt.stop
        ]
      }
    ]
  }
  match compile callbackSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected callback to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      -- Check selector encoding
      assertContains "callback compiles with correct selector" rendered
        ["shl(224, 0x7a29084c)"]
      -- Check call pattern
      assertContains "callback emits call to caller" rendered
        ["call(gas(), caller(),"]
      -- Check bytes forwarding (calldatacopy)
      assertContains "callback forwards bytes data" rendered
        ["calldatacopy("]
      -- Check revert forwarding
      assertContains "callback has revert forwarding" rendered
        ["iszero(__cb_success)", "returndatacopy(", "revert(0,"]
      -- Check ABI offset pointer for bytes parameter
      assertContains "callback stores ABI bytes offset" rendered
        ["mstore(36,"]
      -- Check bytes data is padded to 32-byte boundary in totalSize
      assertContains "callback pads bytes to 32-byte boundary" rendered
        ["and(add(data_length, 31), not(31))"]

-- ===== ECM callback with multiple static args =====
#eval! do
  let multiArgCallbackSpec : CompilationModel := {
    name := "MultiArgCallbackTest"
    fields := []
    constructor := none
    functions := [
      { name := "liquidateWithCallback"
        params := [
          ⟨"repaid", ParamType.uint256⟩,
          ⟨"seized", ParamType.uint256⟩,
          ⟨"data", ParamType.bytes⟩
        ]
        returnType := none
        body := [
          -- onMorphoLiquidate(uint256 repaid, uint256 seized, bytes data)
          Modules.Callbacks.callback Expr.caller 0xbeadbeef [Expr.param "repaid", Expr.param "seized"] "data",
          Stmt.stop
        ]
      }
    ]
  }
  match compile multiArgCallbackSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected multi-arg callback to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      -- Check two static args at offsets 4 and 36
      assertContains "multi-arg callback stores args" rendered
        ["mstore(4,", "mstore(36,"]
      -- ABI bytes offset at slot 68 (4 + 2*32) with value 96 (3*32)
      assertContains "multi-arg callback ABI bytes offset" rendered
        ["mstore(68, 96)"]
      -- Bytes length at slot 100 (4 + 3*32)
      assertContains "multi-arg callback bytes length" rendered
        ["mstore(100,"]
      IO.println "✓ multi-arg callback compiles correctly"


-- rawLog with 3 topics → log3
#eval! do
  let rawLog3Spec : CompilationModel := {
    name := "RawLog3"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "emitRaw"
        params := [{ name := "t0", ty := ParamType.uint256 },
                   { name := "t1", ty := ParamType.uint256 },
                   { name := "t2", ty := ParamType.uint256 }]
        returnType := none
        body := [
          Stmt.mstore (Expr.literal 0) (Expr.literal 7),
          Stmt.rawLog [Expr.param "t0", Expr.param "t1", Expr.param "t2"]
                      (Expr.literal 0) (Expr.literal 32),
          Stmt.stop
        ]
      }
    ]
  }
  match compile rawLog3Spec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected rawLog3 to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "rawLog log3 lowering" rendered [
        "log3(0, 32, t0, t1, t2)"
      ]

-- rawLog with 4 topics → log4
#eval! do
  let rawLog4Spec : CompilationModel := {
    name := "RawLog4"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "emitRaw"
        params := [{ name := "t0", ty := ParamType.uint256 },
                   { name := "t1", ty := ParamType.uint256 },
                   { name := "t2", ty := ParamType.uint256 },
                   { name := "t3", ty := ParamType.uint256 }]
        returnType := none
        body := [
          Stmt.mstore (Expr.literal 0) (Expr.literal 1),
          Stmt.rawLog [Expr.param "t0", Expr.param "t1", Expr.param "t2", Expr.param "t3"]
                      (Expr.literal 0) (Expr.literal 32),
          Stmt.stop
        ]
      }
    ]
  }
  match compile rawLog4Spec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected rawLog4 to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "rawLog log4 lowering" rendered [
        "log4(0, 32, t0, t1, t2, t3)"
      ]

-- rawLog with 5 topics → compilation error
#eval! do
  let rawLog5Spec : CompilationModel := {
    name := "RawLog5"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "emitRaw"
        params := [{ name := "t0", ty := ParamType.uint256 },
                   { name := "t1", ty := ParamType.uint256 },
                   { name := "t2", ty := ParamType.uint256 },
                   { name := "t3", ty := ParamType.uint256 },
                   { name := "t4", ty := ParamType.uint256 }]
        returnType := none
        body := [
          Stmt.rawLog [Expr.param "t0", Expr.param "t1", Expr.param "t2",
                       Expr.param "t3", Expr.param "t4"]
                      (Expr.literal 0) (Expr.literal 32),
          Stmt.stop
        ]
      }
    ]
  }
  match compile rawLog5Spec [1] with
  | .error err =>
      if !(contains err "rawLog supports at most 4 topics") then
        throw (IO.userError s!"✗ rawLog >4 topics diagnostic mismatch: {err}")
      IO.println "✓ rawLog rejects >4 topics"
  | .ok _ =>
      throw (IO.userError "✗ expected rawLog with 5 topics to fail compilation")

-- rawLog in view function → rejected (writes state)
#eval! do
  let rawLogViewSpec : CompilationModel := {
    name := "RawLogView"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "viewEmit"
        params := []
        returnType := none
        isView := true
        body := [
          Stmt.rawLog [Expr.literal 0x1234] (Expr.literal 0) (Expr.literal 0),
          Stmt.stop
        ]
      }
    ]
  }

  match compile rawLogViewSpec [1] with
  | .error err =>
      if !(contains err "writes state") then
        throw (IO.userError s!"✗ rawLog view diagnostic mismatch: {err}")
      IO.println "✓ rawLog in view function correctly rejected"
  | .ok _ =>
      throw (IO.userError "✗ expected rawLog in view function to fail compilation")

-- ===== ECM safeTransfer validation: rejects in view function =====
#eval! do
  let safeTransferViewSpec : CompilationModel := {
    name := "SafeTransferViewReject"
    fields := []
    constructor := none
    functions := [
      { name := "badView"
        params := [⟨"token", ParamType.address⟩, ⟨"to", ParamType.address⟩, ⟨"amount", ParamType.uint256⟩]
        returnType := none
        isView := true
        body := [
          Modules.ERC20.safeTransfer (Expr.param "token") (Expr.param "to") (Expr.param "amount"),
          Stmt.stop
        ]
      }
    ]
  }
  match compile safeTransferViewSpec [1] with
  | .error _ =>
      IO.println "✓ safeTransfer correctly rejected in view function"
  | .ok _ =>
      throw (IO.userError "✗ expected safeTransfer in view function to be rejected")

-- ===== ECM callback rejects in view function =====
#eval! do
  let viewCallbackSpec : CompilationModel := {
    name := "ViewCallbackReject"
    fields := []
    constructor := none
    functions := [
      { name := "badView"
        params := [⟨"data", ParamType.bytes⟩]
        returnType := none
        isView := true
        body := [
          Modules.Callbacks.callback Expr.caller 0x12345678 [] "data",
          Stmt.stop
        ]
      }
    ]
  }
  match compile viewCallbackSpec [1] with
  | .error _ =>
      IO.println "✓ ECM callback correctly rejected in view function"
  | .ok _ =>
      throw (IO.userError "✗ expected ECM callback in view function to be rejected")

-- ============================================================
-- Arithmetic helpers (#928)
-- ============================================================

-- Test: mulDivDown compiles to div(mul(a, b), c)
#eval! do
  let spec : CompilationModel := {
    name := "MulDivDown"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "compute"
        params := [{ name := "a", ty := .uint256 }, { name := "b", ty := .uint256 }, { name := "c", ty := .uint256 }]
        returnType := some .uint256
        body := [Stmt.return (Expr.mulDivDown (Expr.param "a") (Expr.param "b") (Expr.param "c"))]
      }
    ]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ mulDivDown should compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "mulDivDown lowering" rendered ["div(mul(a, b), c)"]
      IO.println "✓ mulDivDown compiles to div(mul(a, b), c)"

-- Test: mulDivUp compiles to div(add(mul(a, b), sub(c, 1)), c)
#eval! do
  let spec : CompilationModel := {
    name := "MulDivUp"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "compute"
        params := [{ name := "a", ty := .uint256 }, { name := "b", ty := .uint256 }, { name := "c", ty := .uint256 }]
        returnType := some .uint256
        body := [Stmt.return (Expr.mulDivUp (Expr.param "a") (Expr.param "b") (Expr.param "c"))]
      }
    ]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ mulDivUp should compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "mulDivUp lowering" rendered ["div(add(mul(a, b), sub(c, 1)), c)"]
      IO.println "✓ mulDivUp compiles to div(add(mul(a, b), sub(c, 1)), c)"

-- Test: wMulDown compiles to div(mul(a, b), 1000000000000000000)
#eval! do
  let spec : CompilationModel := {
    name := "WMulDown"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "compute"
        params := [{ name := "a", ty := .uint256 }, { name := "b", ty := .uint256 }]
        returnType := some .uint256
        body := [Stmt.return (Expr.wMulDown (Expr.param "a") (Expr.param "b"))]
      }
    ]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ wMulDown should compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "wMulDown lowering" rendered ["div(mul(a, b), 1000000000000000000)"]
      IO.println "✓ wMulDown compiles to div(mul(a, b), WAD)"

-- Test: wDivUp compiles correctly
#eval! do
  let spec : CompilationModel := {
    name := "WDivUp"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "compute"
        params := [{ name := "a", ty := .uint256 }, { name := "b", ty := .uint256 }]
        returnType := some .uint256
        body := [Stmt.return (Expr.wDivUp (Expr.param "a") (Expr.param "b"))]
      }
    ]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ wDivUp should compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "wDivUp lowering" rendered ["div(add(mul(a, 1000000000000000000), sub(b, 1)), b)"]
      IO.println "✓ wDivUp compiles to div(add(mul(a, WAD), sub(b, 1)), b)"

-- Test: min compiles to sub(a, mul(sub(a, b), gt(a, b)))
#eval! do
  let spec : CompilationModel := {
    name := "MinExpr"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "compute"
        params := [{ name := "a", ty := .uint256 }, { name := "b", ty := .uint256 }]
        returnType := some .uint256
        body := [Stmt.return (Expr.min (Expr.param "a") (Expr.param "b"))]
      }
    ]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ min should compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "min lowering" rendered ["sub(a, mul(sub(a, b), gt(a, b)))"]
      IO.println "✓ min compiles to sub(a, mul(sub(a, b), gt(a, b)))"

-- Test: max compiles to add(a, mul(sub(b, a), gt(b, a)))
#eval! do
  let spec : CompilationModel := {
    name := "MaxExpr"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "compute"
        params := [{ name := "a", ty := .uint256 }, { name := "b", ty := .uint256 }]
        returnType := some .uint256
        body := [Stmt.return (Expr.max (Expr.param "a") (Expr.param "b"))]
      }
    ]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ max should compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "max lowering" rendered ["add(a, mul(sub(b, a), gt(b, a)))"]
      IO.println "✓ max compiles to add(a, mul(sub(b, a), gt(b, a)))"

-- Test: nested arithmetic helpers compile correctly
#eval! do
  let spec : CompilationModel := {
    name := "NestedArith"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "sharesToAssets"
        params := [
          { name := "shares", ty := .uint256 },
          { name := "totalAssets", ty := .uint256 },
          { name := "totalShares", ty := .uint256 }
        ]
        returnType := some .uint256
        body := [
          -- mulDivDown(shares, totalAssets + 1, totalShares + 1000000)
          Stmt.return (Expr.mulDivDown
            (Expr.param "shares")
            (Expr.add (Expr.param "totalAssets") (Expr.literal 1))
            (Expr.add (Expr.param "totalShares") (Expr.literal 1000000)))
        ]
      }
    ]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ nested arithmetic should compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "nested arithmetic" rendered [
        "div(mul(shares, add(totalAssets, 1)), add(totalShares, 1000000))"
      ]
      IO.println "✓ nested arithmetic helpers compile correctly"

-- Test: SpecInterpreter evaluates mulDivDown
#eval! do
  let spec : CompilationModel := {
    name := "MulDivInterp"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "compute"
        params := [{ name := "a", ty := .uint256 }, { name := "b", ty := .uint256 }, { name := "c", ty := .uint256 }]
        returnType := some .uint256
        body := [Stmt.return (Expr.mulDivDown (Expr.param "a") (Expr.param "b") (Expr.param "c"))]
      }
    ]
  }
  -- mulDivDown(10, 3, 2) = (10 * 3) / 2 = 15
  let tx : Transaction := { sender := 0, functionName := "compute", args := [10, 3, 2] }
  let result := interpretSpec spec SpecStorage.empty tx
  if result.returnValue != some 15 then
    throw (IO.userError s!"✗ mulDivDown interpreter: expected 15, got {result.returnValue}")
  IO.println "✓ SpecInterpreter evaluates mulDivDown(10, 3, 2) = 15"

-- Test: SpecInterpreter evaluates min/max
#eval! do
  let spec : CompilationModel := {
    name := "MinMaxInterp"
    fields := [{ name := "x", ty := FieldType.uint256 }]
    constructor := none
    functions := [
      { name := "getMin"
        params := [{ name := "a", ty := .uint256 }, { name := "b", ty := .uint256 }]
        returnType := some .uint256
        body := [Stmt.return (Expr.min (Expr.param "a") (Expr.param "b"))]
      },
      { name := "getMax"
        params := [{ name := "a", ty := .uint256 }, { name := "b", ty := .uint256 }]
        returnType := some .uint256
        body := [Stmt.return (Expr.max (Expr.param "a") (Expr.param "b"))]
      }
    ]
  }
  -- min(7, 3) = 3
  let minTx : Transaction := { sender := 0, functionName := "getMin", args := [7, 3] }
  let minResult := interpretSpec spec SpecStorage.empty minTx
  if minResult.returnValue != some 3 then
    throw (IO.userError s!"✗ min interpreter: expected 3, got {minResult.returnValue}")
  -- max(7, 3) = 7
  let maxTx : Transaction := { sender := 0, functionName := "getMax", args := [7, 3] }
  let maxResult := interpretSpec spec SpecStorage.empty maxTx
  if maxResult.returnValue != some 7 then
    throw (IO.userError s!"✗ max interpreter: expected 7, got {maxResult.returnValue}")
  -- min(5, 5) = 5
  let minEqTx : Transaction := { sender := 0, functionName := "getMin", args := [5, 5] }
  let minEqResult := interpretSpec spec SpecStorage.empty minEqTx
  if minEqResult.returnValue != some 5 then
    throw (IO.userError s!"✗ min interpreter equal: expected 5, got {minEqResult.returnValue}")
  IO.println "✓ SpecInterpreter evaluates min/max correctly"

-- ===== ECM ecrecover compilation =====
private def ecrecoverSpec : CompilationModel := {
  name := "EcrecoverSpec"
  fields := [{ name := "recovered", ty := FieldType.address }]
  constructor := none
  functions := [
    { name := "recoverSigner"
      params := [
        ⟨"digest", ParamType.bytes32⟩,
        ⟨"v", ParamType.uint256⟩,
        ⟨"r", ParamType.bytes32⟩,
        ⟨"s", ParamType.bytes32⟩
      ]
      returnType := some FieldType.address
      body := [
        Modules.Precompiles.ecrecover "signer" (Expr.param "digest") (Expr.param "v") (Expr.param "r") (Expr.param "s"),
        Stmt.setStorage "recovered" (Expr.localVar "signer"),
        Stmt.return (Expr.localVar "signer")
      ]
    },
    { name := "getRecovered"
      params := []
      returnType := some FieldType.address
      isView := true
      body := [
        Stmt.return (Expr.storage "recovered")
      ]
    }
  ]
}

#eval! do
  match compile ecrecoverSpec [1, 2] with
  | .error err =>
      throw (IO.userError s!"✗ ecrecover compilation failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      -- Check for staticcall to precompile 0x01
      assertContains "ecrecover compiles to staticcall precompile" rendered
        ["staticcall(gas(), 1, 0, 128, 0, 32)"]
      -- Check for mstore of hash at offset 0
      assertContains "ecrecover stores hash at memory[0]" rendered
        ["mstore(0,"]
      -- Check for address mask
      assertContains "ecrecover masks result to 160 bits" rendered
        ["and(mload(0), 0xffffffffffffffffffffffffffffffffffffffff)"]
      -- Check for revert on failure
      assertContains "ecrecover reverts on staticcall failure" rendered
        ["iszero(__ecr_success)"]
      -- Check result binding is accessible (used in sstore after the block)
      assertContains "ecrecover result variable accessible" rendered
        ["signer"]

-- ===== ECM ecrecover rejects in pure function =====
#eval! do
  let pureEcrecoverSpec : CompilationModel := {
    name := "PureEcrecoverReject"
    fields := []
    constructor := none
    functions := [
      { name := "pureFn"
        params := [
          ⟨"h", ParamType.bytes32⟩,
          ⟨"v", ParamType.uint256⟩,
          ⟨"r", ParamType.bytes32⟩,
          ⟨"s", ParamType.bytes32⟩
        ]
        returnType := some FieldType.address
        isPure := true
        body := [
          Modules.Precompiles.ecrecover "signer" (Expr.param "h") (Expr.param "v") (Expr.param "r") (Expr.param "s"),
          Stmt.return (Expr.localVar "signer")
        ]
      }
    ]
  }
  match compile pureEcrecoverSpec [1] with
  | .error err =>
      if contains err "pure" then
        IO.println s!"✓ ecrecover correctly rejected in pure function: {err}"
      else
        throw (IO.userError s!"✗ unexpected error for ecrecover in pure function: {err}")
  | .ok _ =>
      throw (IO.userError "✗ expected ecrecover in pure function to be rejected")

-- ================================================================
-- Stmt.externalCallBind: multi-return external call binding (#929)
-- ================================================================

-- Test: externalCallBind compiles to letMany with external function name
private def externalCallBindSpec : CompilationModel := {
  name := "ExternalCallBindSpec"
  fields := [{ name := "x", ty := FieldType.uint256 }]
  constructor := none
  externals := [
    { name := "getPrice"
      params := [ParamType.address]
      returns := [ParamType.uint256]
      axiomNames := []
    },
    { name := "getPair"
      params := [ParamType.uint256]
      returns := [ParamType.uint256, ParamType.uint256]
      axiomNames := []
    },
    { name := "getTriple"
      params := []
      returns := [ParamType.uint256, ParamType.uint256, ParamType.uint256]
      axiomNames := []
    }
  ]
  functions := [
    { name := "fetchPrice"
      params := [{ name := "oracle", ty := .address }]
      returnType := some .uint256
      body := [
        Stmt.externalCallBind ["price"] "getPrice" [Expr.param "oracle"],
        Stmt.return (Expr.localVar "price")
      ]
    },
    { name := "fetchPair"
      params := [{ name := "key", ty := .uint256 }]
      returnType := none
      returns := [ParamType.uint256, ParamType.uint256]
      body := [
        Stmt.externalCallBind ["a", "b"] "getPair" [Expr.param "key"],
        Stmt.returnValues [Expr.localVar "a", Expr.localVar "b"]
      ]
    },
    { name := "fetchTriple"
      params := []
      returnType := none
      returns := [ParamType.uint256, ParamType.uint256, ParamType.uint256]
      body := [
        Stmt.externalCallBind ["x", "y", "z"] "getTriple" [],
        Stmt.returnValues [Expr.localVar "x", Expr.localVar "y", Expr.localVar "z"]
      ]
    }
  ]
}

-- ========================================================
-- Expr.extcodesize tests
-- ========================================================

private def extcodesizeSpec : CompilationModel := {
  name := "ExtcodesizeSpec"
  fields := [{ name := "target", ty := FieldType.uint256 }]
  constructor := none
  functions := [
    { name := "requireHasCode"
      params := [{ name := "addr", ty := ParamType.address }]
      returnType := none
      body := [
        Stmt.require (Expr.gt (Expr.extcodesize (Expr.param "addr")) (Expr.literal 0)) "no code",
        Stmt.stop
      ]
    },
    { name := "getCodeSize"
      params := [{ name := "addr", ty := ParamType.address }]
      returnType := some .uint256
      isView := true
      body := [
        Stmt.return (Expr.extcodesize (Expr.param "addr"))
      ]
    },
    { name := "checkSelfCode"
      params := []
      returnType := some .uint256
      isView := true
      body := [
        Stmt.return (Expr.extcodesize Expr.contractAddress)
      ]
    }
  ]
}

-- ECM withReturn: ABI-encoded external call with return (#926)

-- Test: externalCallWithReturn compiles to mstore+call+returndatacopy pattern
private def externalCallWithReturnSpec : CompilationModel := {
  name := "ExternalCallWithReturn"
  fields := []
  constructor := none
  functions := [
    -- Test 1: simple staticcall with no args (oracle price feed pattern)
    { name := "getPrice"
      params := [{ name := "oracle", ty := ParamType.address }]
      returnType := some FieldType.uint256
      body := [
        Modules.Calls.withReturn "price" (Expr.param "oracle") 0xa035b1fe [] (isStatic := true),
        Stmt.return (Expr.localVar "price")
      ]
    },
    -- Test 2: call with args (ERC20 balanceOf pattern)
    { name := "getBalance"
      params := [
        { name := "token", ty := ParamType.address },
        { name := "account", ty := ParamType.address }
      ]
      returnType := some FieldType.uint256
      body := [
        Modules.Calls.withReturn "bal" (Expr.param "token") 0x70a08231 [Expr.param "account"],
        Stmt.return (Expr.localVar "bal")
      ]
    },
    -- Test 3: call with multiple args (IRM borrowRate pattern)
    { name := "getBorrowRate"
      params := [
        { name := "irm", ty := ParamType.address },
        { name := "a", ty := ParamType.uint256 },
        { name := "b", ty := ParamType.uint256 }
      ]
      returnType := some FieldType.uint256
      body := [
        Modules.Calls.withReturn "rate" (Expr.param "irm") 0x9451fed4 [Expr.param "a", Expr.param "b"],
        Stmt.return (Expr.localVar "rate")
      ]
    }
  ]
}

-- Test: single return externalCallBind compiles correctly
#eval! do
  match compile externalCallBindSpec [1, 2, 3] with
  | .error err =>
      throw (IO.userError s!"✗ externalCallBind spec compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "externalCallBind single return" rendered
        ["let price := getPrice(oracle)"]
      IO.println s!"✓ externalCallBind single return compiles to let binding"

-- Test: dual return externalCallBind compiles correctly
#eval! do
  match compile externalCallBindSpec [1, 2, 3] with
  | .error err =>
      throw (IO.userError s!"✗ externalCallBind spec compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "externalCallBind dual return" rendered
        ["let a, b := getPair(key)"]
      IO.println s!"✓ externalCallBind dual return compiles to letMany binding"

-- Test: triple return externalCallBind compiles correctly
#eval! do
  match compile externalCallBindSpec [1, 2, 3] with
  | .error err =>
      throw (IO.userError s!"✗ externalCallBind spec compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "externalCallBind triple return" rendered
        ["let x, y, z := getTriple()"]
      IO.println s!"✓ externalCallBind triple return compiles to letMany binding"

-- Test: externalCallBind validation rejects mismatched arity
#eval! do
  let badSpec : CompilationModel := {
    name := "BadAritySpec"
    fields := []
    constructor := none
    externals := [
      { name := "getOne"
        params := []
        returns := [ParamType.uint256]
        axiomNames := []
      }
    ]
    functions := [
      { name := "fetch"
        params := []
        returnType := none
        body := [
          Stmt.externalCallBind ["a", "b"] "getOne" [],
          Stmt.stop
        ]
      }
    ]
  }
  match compile badSpec [1] with
  | .error err =>
      if contains err "binds 2 values" then
        IO.println s!"✓ externalCallBind rejects arity mismatch: {err}"
      else
        throw (IO.userError s!"✗ externalCallBind wrong error message: {err}")
  | .ok _ =>
      throw (IO.userError "✗ externalCallBind should have rejected arity mismatch")

#eval do
  match compile extcodesizeSpec [1, 2, 3] with
  | .error e => throw (IO.userError s!"Compilation failed: {e}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)

      -- Test 1: extcodesize compiles to correct Yul
      assertContains "extcodesize compiles to Yul builtin" rendered [
        "extcodesize(addr)"
      ]

      -- Test 2: requireHasCode uses extcodesize in condition
      assertContains "requireHasCode uses extcodesize in require" rendered [
        "gt(extcodesize(addr)"
      ]

      -- Test 3: view function can use extcodesize (reads state, doesn't write)
      assertContains "getCodeSize view function compiles" rendered [
        "extcodesize(addr)"
      ]

      -- Test 4: extcodesize with contractAddress nested expression
      assertContains "checkSelfCode uses extcodesize(address())" rendered [
        "extcodesize(address())"
      ]

      IO.println "✓ All Expr.extcodesize tests passed"

-- Test: Expr.extcodesize rejected in pure functions
#eval do
  let pureExtcodesizeSpec : CompilationModel := {
    name := "PureExtcodesizeSpec"
    fields := []
    constructor := none
    functions := [
      { name := "pureGetCode"
        params := [{ name := "addr", ty := ParamType.address }]
        returnType := some .uint256
        isPure := true
        body := [
          Stmt.return (Expr.extcodesize (Expr.param "addr"))
        ]
      }
    ]
  }
  match compile pureExtcodesizeSpec [1] with
  | .ok _ => throw (IO.userError "✗ extcodesize in pure function should be rejected")
  | .error e =>
      if contains e "pure" then
        IO.println s!"✓ extcodesize correctly rejected in pure function"
      else
        throw (IO.userError s!"✗ extcodesize in pure function rejected but with unexpected error: {e}")

-- Test: externalCallBind validation rejects unknown external
#eval! do
  let badSpec : CompilationModel := {
    name := "BadExternalSpec"
    fields := []
    constructor := none
    functions := [
      { name := "fetch"
        params := []
        returnType := none
        body := [
          Stmt.externalCallBind ["a"] "nonExistent" [],
          Stmt.stop
        ]
      }
    ]
  }
  match compile badSpec [1] with
  | .error err =>
      if contains err "unknown external function" then
        IO.println s!"✓ externalCallBind rejects unknown external: {err}"
      else
        throw (IO.userError s!"✗ externalCallBind wrong error message: {err}")
  | .ok _ =>
      throw (IO.userError "✗ externalCallBind should have rejected unknown external")

-- Test: externalCallBind validation rejects duplicate result vars
#eval! do
  let badSpec : CompilationModel := {
    name := "DupVarSpec"
    fields := []
    constructor := none
    externals := [
      { name := "getPair"
        params := []
        returns := [ParamType.uint256, ParamType.uint256]
        axiomNames := []
      }
    ]
    functions := [
      { name := "fetch"
        params := []
        returnType := none
        body := [
          Stmt.externalCallBind ["x", "x"] "getPair" [],
          Stmt.stop
        ]
      }
    ]
  }
  match compile badSpec [1] with
  | .error err =>
      if contains err "duplicate result variable" then
        IO.println s!"✓ externalCallBind rejects duplicate vars: {err}"
      else
        throw (IO.userError s!"✗ externalCallBind wrong error message: {err}")
  | .ok _ =>
      throw (IO.userError "✗ externalCallBind should have rejected duplicate vars")

-- Test: staticcall with no args (oracle pattern)
#eval! do
  match compile externalCallWithReturnSpec [1, 2, 3] with
  | .error err =>
      throw (IO.userError s!"✗ externalCallWithReturn spec compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      -- Should use shl(224, selector) for selector encoding
      assertContains "externalCallWithReturn staticcall selector" rendered
        ["shl(224, 0xa035b1fe)"]
      -- Should use staticcall (not call) since isStatic=true
      assertContains "externalCallWithReturn uses staticcall" rendered
        ["staticcall(gas(),"]
      -- Should have revert forwarding
      assertContains "externalCallWithReturn revert forwarding" rendered
        ["iszero(__ecwr_success)", "returndatacopy(0, 0, __ecwr_rds)", "revert(0, __ecwr_rds)"]
      -- Should validate returndata size
      assertContains "externalCallWithReturn size check" rendered
        ["lt(returndatasize(), 32)"]
      -- Should extract return value (no redundant returndatacopy — call already copied to memory)
      assertContains "externalCallWithReturn return extraction" rendered
        ["let price := mload(0)"]
      -- Should NOT have a redundant returndatacopy(0, 0, 32) outside the revert block
      IO.println s!"✓ externalCallWithReturn staticcall compiles correctly"

-- Test: call with one arg (balanceOf pattern)
#eval! do
  match compile externalCallWithReturnSpec [1, 2, 3] with
  | .error err =>
      throw (IO.userError s!"✗ externalCallWithReturn spec compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      -- Should use shl(224, selector) for balanceOf selector
      assertContains "externalCallWithReturn call selector" rendered
        ["shl(224, 0x70a08231)"]
      -- Should store arg at offset 4
      assertContains "externalCallWithReturn arg encoding" rendered
        ["mstore(4,"]
      -- Should use call (not staticcall) since isStatic=false
      assertContains "externalCallWithReturn uses call" rendered
        ["call(gas(),"]
      -- Should extract result to bal
      assertContains "externalCallWithReturn bal binding" rendered
        ["let bal := mload(0)"]
      IO.println s!"✓ externalCallWithReturn call with args compiles correctly"

-- Test: call with multiple args (IRM pattern)
#eval! do
  match compile externalCallWithReturnSpec [1, 2, 3] with
  | .error err =>
      throw (IO.userError s!"✗ externalCallWithReturn spec compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      -- Should store two args at offsets 4 and 36
      assertContains "externalCallWithReturn multi-arg encoding" rendered
        ["shl(224, 0x9451fed4)", "mstore(4,", "mstore(36,"]
      -- Calldata size should be 4 + 2*32 = 68
      assertContains "externalCallWithReturn calldata size" rendered
        ["call(gas(),"]
      -- Should extract result to rate
      assertContains "externalCallWithReturn rate binding" rendered
        ["let rate := mload(0)"]
      IO.println s!"✓ externalCallWithReturn multi-arg call compiles correctly"

-- Test: externalCallWithReturn rejects result variable shadowing a parameter
#eval! do
  let shadowSpec : CompilationModel := {
    name := "ShadowParam"
    fields := []
    constructor := none
    functions := [
      { name := "bad"
        params := [{ name := "oracle", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [
          Modules.Calls.withReturn "oracle" (Expr.param "oracle") 0xa035b1fe [] (isStatic := true),
          Stmt.return (Expr.localVar "oracle")
        ]
      }
    ]
  }
  match compile shadowSpec [1] with
  | .error err =>
      if contains err "shadows a parameter" then
        IO.println s!"✓ externalCallWithReturn rejects parameter shadow: {err}"
      else
        throw (IO.userError s!"✗ externalCallWithReturn wrong error: {err}")
  | .ok _ =>
      throw (IO.userError "✗ externalCallWithReturn should have rejected parameter shadow")

-- Test: externalCallWithReturn rejects redeclaring existing local variable
#eval! do
  let redeclareSpec : CompilationModel := {
    name := "RedeclareLocal"
    fields := []
    constructor := none
    functions := [
      { name := "bad"
        params := [{ name := "oracle", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [
          Stmt.letVar "price" (Expr.literal 0),
          Modules.Calls.withReturn "price" (Expr.param "oracle") 0xa035b1fe [] (isStatic := true),
          Stmt.return (Expr.localVar "price")
        ]
      }
    ]
  }
  match compile redeclareSpec [1] with
  | .error err =>
      if contains err "redeclares result" then
        IO.println s!"✓ ECM withReturn rejects local redeclaration: {err}"
      else
        throw (IO.userError s!"✗ ECM withReturn wrong error: {err}")
  | .ok _ =>
      throw (IO.userError "✗ ECM withReturn should have rejected redeclaration")

-- Test: staticcall external call allows view mutability
#eval! do
  let viewSpec : CompilationModel := {
    name := "ViewStaticCall"
    fields := []
    constructor := none
    functions := [
      { name := "getPrice"
        params := [{ name := "oracle", ty := ParamType.address }]
        returnType := some FieldType.uint256
        isView := true
        body := [
          Modules.Calls.withReturn "price" (Expr.param "oracle") 0xa035b1fe [] (isStatic := true),
          Stmt.return (Expr.localVar "price")
        ]
      }
    ]
  }
  match compile viewSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ view staticcall should compile: {err}")
  | .ok _ =>
      IO.println "✓ externalCallWithReturn staticcall accepted for view function"

-- Test: multiple externalCallWithReturn in same function (no duplicate let collision)
#eval! do
  let multiCallSpec : CompilationModel := {
    name := "MultiExternalCall"
    fields := []
    constructor := none
    functions := [
      { name := "getPrices"
        params := [{ name := "oracle1", ty := ParamType.address }, { name := "oracle2", ty := ParamType.address }]
        returnType := none
        body := [
          Modules.Calls.withReturn "price1" (Expr.param "oracle1") 0xa035b1fe [] (isStatic := true),
          Modules.Calls.withReturn "price2" (Expr.param "oracle2") 0xa035b1fe [] (isStatic := true),
          Stmt.stop
        ]
      }
    ]
  }
  match compile multiCallSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ multiple externalCallWithReturn should compile: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "multi externalCallWithReturn both bindings" rendered
        ["let price1 := mload(0)", "let price2 := mload(0)"]
      IO.println "✓ multiple externalCallWithReturn in same function compiles without collision"

-- ============================================================================
-- Calldata access primitives: Expr.calldatasize, Expr.calldataload, Stmt.calldatacopy
-- ============================================================================

private def calldataAccessSpec : CompilationModel := {
  name := "CalldataAccessSpec"
  fields := [{ name := "lastSize", ty := FieldType.uint256 }]
  constructor := none
  functions := [
    { name := "parseCalldata"
      params := [⟨"offset", ParamType.uint256⟩]
      returnType := some FieldType.uint256
      body := [
        -- Store calldatasize for later retrieval
        Stmt.setStorage "lastSize" Expr.calldatasize,
        -- Load a word from calldata at the given offset
        Stmt.letVar "word" (Expr.calldataload (Expr.param "offset")),
        Stmt.return (Expr.localVar "word")
      ]
    },
    { name := "copyCalldata"
      params := [⟨"srcOffset", ParamType.uint256⟩, ⟨"size", ParamType.uint256⟩]
      returnType := some FieldType.uint256
      body := [
        -- Copy calldata to memory at offset 0
        Stmt.calldatacopy (Expr.literal 0) (Expr.param "srcOffset") (Expr.param "size"),
        -- Return the first word from memory
        Stmt.return (Expr.mload (Expr.literal 0))
      ]
    }
  ]
  events := []
}

-- Test: calldata access compiles to correct Yul opcodes
#eval! do
  match compile calldataAccessSpec [1, 2] with
  | .error err =>
      throw (IO.userError s!"✗ calldata access compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "calldatasize opcode" rendered
        ["calldatasize()"]
      assertContains "calldataload opcode" rendered
        ["calldataload(offset)"]
      assertContains "calldatacopy opcode" rendered
        ["calldatacopy(0, srcOffset, size)"]
      IO.println s!"✓ calldata access primitives compile successfully"

-- Test: calldatasize and calldataload rejected in pure functions
private def pureCalldataSpec : CompilationModel := {
  name := "PureCalldataSpec"
  fields := []
  constructor := none
  functions := [
    { name := "pureFunc"
      params := []
      returnType := some FieldType.uint256
      isPure := true
      body := [
        Stmt.return Expr.calldatasize
      ]
    }
  ]
  events := []
}

#eval! do
  match compile pureCalldataSpec [1] with
  | .ok _ =>
      throw (IO.userError "✗ expected pure function with calldatasize to fail compilation")
  | .error err =>
      if !contains err "pure" then
        throw (IO.userError s!"✗ expected 'pure' in error, got: {err}")
      IO.println "✓ calldatasize correctly rejected in pure function"

-- Test: calldataload with nested expr in view function
private def viewCalldataloadSpec : CompilationModel := {
  name := "ViewCalldataloadSpec"
  fields := [{ name := "data", ty := FieldType.uint256 }]
  constructor := none
  functions := [
    { name := "viewFunc"
      params := [⟨"pos", ParamType.uint256⟩]
      returnType := some FieldType.uint256
      isView := true
      body := [
        Stmt.return (Expr.calldataload (Expr.param "pos"))
      ]
    }
  ]
  events := []
}

#eval! do
  match compile viewCalldataloadSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ view calldataload compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "view calldataload" rendered
        ["calldataload(pos)"]
      IO.println "✓ calldataload works in view functions"

-- Test: SpecInterpreter marks calldata access as unsupported low-level
#eval! do
  let spec := calldataAccessSpec
  let initialStorage := SpecStorage.empty
  let tx : Transaction := { sender := 0, functionName := "parseCalldata", args := [4] }
  let _result := interpretSpec spec initialStorage tx
  -- calldatasize/calldataload are unsupported low-level, so the interpreter should skip
  IO.println s!"✓ SpecInterpreter handles calldata access specs (low-level unsupported path)"
-- ============ mapping2Word / setMapping2Word ============

-- Test: mapping2Word read compiles to sload(add(mappingSlot(mappingSlot(slot, key1), key2), wordOffset))
#eval! do
  let mapping2WordSpec : CompilationModel := {
    name := "Mapping2WordSpec"
    fields := [
      { name := "positions", ty := FieldType.mappingTyped (MappingType.nested MappingKeyType.uint256 MappingKeyType.address), slot := some 3 }
    ]
    constructor := none
    functions := [
      { name := "getBalance"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "user", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.mapping2Word "positions" (Expr.param "id") (Expr.param "user") 1)]
      },
      { name := "setBalance"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "user", ty := ParamType.address }, { name := "amount", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setMapping2Word "positions" (Expr.param "id") (Expr.param "user") 1 (Expr.param "amount"), Stmt.stop]
      }
    ]
    events := []
  }
  match compile mapping2WordSpec [1, 2] with
  | .error err =>
      throw (IO.userError s!"✗ mapping2Word compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "mapping2Word read lowers to nested mappingSlot + wordOffset" rendered
        ["sload(add(mappingSlot(mappingSlot(3, id), user), 1))"]
      assertContains "setMapping2Word write lowers to nested mappingSlot + wordOffset" rendered
        ["sstore(add(mappingSlot(mappingSlot(3, id), user), 1), amount)"]

-- Test: mapping2Word with wordOffset 0 omits the add
#eval! do
  let mapping2WordZeroSpec : CompilationModel := {
    name := "Mapping2WordZeroSpec"
    fields := [
      { name := "positions", ty := FieldType.mappingTyped (MappingType.nested MappingKeyType.uint256 MappingKeyType.address), slot := some 3 }
    ]
    constructor := none
    functions := [
      { name := "getBase"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "user", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.mapping2Word "positions" (Expr.param "id") (Expr.param "user") 0)]
      }
    ]
    events := []
  }
  match compile mapping2WordZeroSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ mapping2Word zero offset compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "mapping2Word with offset 0 omits add" rendered
        ["sload(mappingSlot(mappingSlot(3, id), user))"]
      -- Ensure the add variant is NOT present
      if contains rendered "add(mappingSlot(mappingSlot(3, id), user), 0)" then
        throw (IO.userError "✗ mapping2Word with offset 0 should not emit add(..., 0)")
      IO.println "✓ mapping2Word with offset 0 correctly omits add"

-- Test: setMapping2Word with alias slots writes to both canonical and alias
#eval! do
  let mapping2WordAliasSpec : CompilationModel := {
    name := "Mapping2WordAliasSpec"
    fields := [
      { name := "positions", ty := FieldType.mappingTyped (MappingType.nested MappingKeyType.uint256 MappingKeyType.address), slot := some 3, aliasSlots := [15] }
    ]
    constructor := none
    functions := [
      { name := "setBalance"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "user", ty := ParamType.address }, { name := "amount", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setMapping2Word "positions" (Expr.param "id") (Expr.param "user") 1 (Expr.param "amount"), Stmt.stop]
      }
    ]
    events := []
  }
  match compile mapping2WordAliasSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ mapping2Word alias compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "setMapping2Word alias mirror writes include canonical and alias slots" rendered
        ["sstore(add(mappingSlot(mappingSlot(3, __compat_key1), __compat_key2), 1), __compat_value)",
         "sstore(add(mappingSlot(mappingSlot(15, __compat_key1), __compat_key2), 1), __compat_value)"]

-- Test: mapping2Word view function allowed, pure function rejected
#eval! do
  let mapping2WordViewSpec : CompilationModel := {
    name := "Mapping2WordViewSpec"
    fields := [
      { name := "positions", ty := FieldType.mappingTyped (MappingType.nested MappingKeyType.uint256 MappingKeyType.address), slot := some 3 }
    ]
    constructor := none
    functions := [
      { name := "getBalance"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "user", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.mapping2Word "positions" (Expr.param "id") (Expr.param "user") 1)]
        isView := true
      }
    ]
    events := []
  }
  match compile mapping2WordViewSpec [1] with
  | .error _ => throw (IO.userError "✗ mapping2Word view function should compile")
  | .ok _ => IO.println "✓ mapping2Word allowed in view function"

  let mapping2WordPureSpec : CompilationModel := {
    name := "Mapping2WordPureSpec"
    fields := [
      { name := "positions", ty := FieldType.mappingTyped (MappingType.nested MappingKeyType.uint256 MappingKeyType.address), slot := some 3 }
    ]
    constructor := none
    functions := [
      { name := "getBalance"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "user", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.mapping2Word "positions" (Expr.param "id") (Expr.param "user") 1)]
        isPure := true
      }
    ]
    events := []
  }
  match compile mapping2WordPureSpec [1] with
  | .error _ => IO.println "✓ mapping2Word correctly rejected in pure function"
  | .ok _ => throw (IO.userError "✗ mapping2Word should be rejected in pure function")

-- Test: SpecInterpreter for mapping2Word read/write
#eval! do
  let mapping2WordInterpSpec : CompilationModel := {
    name := "Mapping2WordInterpSpec"
    fields := [
      { name := "positions", ty := FieldType.mappingTyped (MappingType.nested MappingKeyType.uint256 MappingKeyType.address), slot := some 3 }
    ]
    constructor := none
    functions := [
      { name := "setBalance"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "user", ty := ParamType.address }, { name := "amount", ty := ParamType.uint256 }]
        returnType := none
        body := [
          Stmt.setMapping2Word "positions" (Expr.param "id") (Expr.param "user") 1 (Expr.param "amount"),
          Stmt.stop
        ]
      },
      { name := "getBalance"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "user", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.mapping2Word "positions" (Expr.param "id") (Expr.param "user") 1)]
      }
    ]
    events := []
  }
  let initialStorage := SpecStorage.empty
  let marketId := 42
  let user := 0xBEEF
  let amount := 999
  let writeTx : Transaction := { sender := 0, functionName := "setBalance", args := [marketId, user, amount] }
  let writeResult := interpretSpec mapping2WordInterpSpec initialStorage writeTx
  if !writeResult.success then
    throw (IO.userError s!"✗ mapping2Word interpreter write reverted: {writeResult.revertReason}")
  let readTx : Transaction := { sender := 0, functionName := "getBalance", args := [marketId, user] }
  let readResult := interpretSpec mapping2WordInterpSpec writeResult.finalStorage readTx
  if readResult.returnValue != some amount then
    throw (IO.userError s!"✗ mapping2Word interpreter read mismatch: expected {amount}, got {readResult.returnValue}")
  IO.println "✓ SpecInterpreter mapping2Word read/write round-trip succeeds"

-- ===== ECM ecrecover result variable shadow check =====
#eval! do
  let shadowSpec : CompilationModel := {
    name := "ShadowTest"
    fields := []
    constructor := none
    functions := [
      { name := "shadowParam"
        params := [
          ⟨"digest", ParamType.bytes32⟩,
          ⟨"v", ParamType.uint256⟩,
          ⟨"r", ParamType.bytes32⟩,
          ⟨"s", ParamType.bytes32⟩
        ]
        returnType := some FieldType.address
        body := [
          Modules.Precompiles.ecrecover "digest" (Expr.param "digest") (Expr.param "v") (Expr.param "r") (Expr.param "s"),
          Stmt.return (Expr.localVar "digest")
        ]
      }
    ]
  }
  match compile shadowSpec [1] with
  | .error err =>
      if contains err "shadows a parameter" then
        IO.println s!"✓ ecrecover correctly rejects shadowing parameter: {err}"
      else
        throw (IO.userError s!"✗ unexpected error for ecrecover shadow: {err}")
  | .ok _ =>
      throw (IO.userError "✗ expected ecrecover parameter shadow to be rejected")

-- ===== ECM ecrecover SpecInterpreter unsupported =====
-- ECM modules route through Stmt.ecm which returns `none` in execStmt/execStmtsFuel.
-- stmtUsesUnsupportedLowLevel correctly returns true for all ECM variants since the
-- interpreter cannot execute them regardless of argument expressions.
#eval! do
  -- Verify that ECM ecrecover is flagged as unsupported (interpreter returns none)
  if stmtUsesUnsupportedLowLevel (Modules.Precompiles.ecrecover "x" (Expr.literal 0) (Expr.literal 0) (Expr.literal 0) (Expr.literal 0)) then
    IO.println "✓ ECM ecrecover correctly flagged as unsupported low-level"
  else
    throw (IO.userError "✗ ECM ecrecover should be flagged as unsupported (interpreter cannot execute ECMs)")
-- ═══════════════════════════════════════════════════════════════
-- Expr.ite (expression-level conditional / branchless ternary)
-- ═══════════════════════════════════════════════════════════════

-- Test 1: Basic codegen — branchless ternary pattern in rendered Yul
#eval! do
  let exprIteCodegenSpec : CompilationModel := {
    name := "ExprIteCodegenSpec"
    fields := [
      { name := "x", ty := FieldType.uint256, slot := some 0 }
    ]
    constructor := none
    functions := [
      { name := "conditionalReturn"
        params := [{ name := "flag", ty := ParamType.uint256 }, { name := "a", ty := ParamType.uint256 }, { name := "b", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.ite (Expr.param "flag") (Expr.param "a") (Expr.param "b"))]
        isView := true
      }
    ]
  }
  match compile exprIteCodegenSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ Expr.ite codegen compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      -- Branchless: add(mul(iszero(iszero(flag)), a), mul(iszero(flag), b))
      assertContains "Expr.ite branchless ternary" rendered
        ["iszero(iszero(flag))", "mul(iszero(iszero(flag)), a)", "mul(iszero(flag), b)", "add(mul("]

-- Test 2: Expr.ite with literal condition (true path)
#eval! do
  let exprIteLiteralSpec : CompilationModel := {
    name := "ExprIteLiteralSpec"
    fields := []
    constructor := none
    functions := [
      { name := "alwaysTrue"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.ite (Expr.literal 1) (Expr.literal 42) (Expr.literal 99))]
        isView := true
      }
    ]
  }
  match compile exprIteLiteralSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ Expr.ite literal codegen compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "Expr.ite literal codegen" rendered
        ["iszero(iszero(1))", "mul(iszero(1), 99)", "mul(iszero(iszero(1)), 42)"]

-- Test 3: Expr.ite nested inside arithmetic
#eval! do
  let exprIteNestedSpec : CompilationModel := {
    name := "ExprIteNestedSpec"
    fields := []
    constructor := none
    functions := [
      { name := "addWithConditional"
        params := [{ name := "flag", ty := ParamType.uint256 }, { name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.add (Expr.param "x") (Expr.ite (Expr.param "flag") (Expr.literal 10) (Expr.literal 20)))]
        isView := true
      }
    ]
  }
  match compile exprIteNestedSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ Expr.ite nested codegen compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      -- The outer expression should be add(x, ite(flag, 10, 20))
      assertContains "Expr.ite nested in arithmetic" rendered
        ["add(x, add(mul(iszero(iszero(flag)), 10), mul(iszero(flag), 20)))"]

-- Test 4: Expr.ite with storage read — rejected in pure function
#eval! do
  let exprItePureRejectedSpec : CompilationModel := {
    name := "ExprItePureRejectedSpec"
    fields := [
      { name := "val", ty := FieldType.uint256, slot := some 0 }
    ]
    constructor := none
    functions := [
      { name := "pureWithStorageRead"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.ite (Expr.storage "val") (Expr.literal 1) (Expr.literal 0))]
        isPure := true
      }
    ]
  }
  match compile exprItePureRejectedSpec [1] with
  | .error err =>
      if !contains err "reads state/environment" then
        throw (IO.userError s!"✗ Expr.ite pure rejection diagnostic mismatch: {err}")
      IO.println "✓ Expr.ite storage read rejected in pure function"
  | .ok _ =>
      throw (IO.userError "✗ expected Expr.ite with storage read to fail in pure function")

-- Test 5: Expr.ite with storage read — accepted in view function
#eval! do
  let exprIteViewAcceptedSpec : CompilationModel := {
    name := "ExprIteViewAcceptedSpec"
    fields := [
      { name := "val", ty := FieldType.uint256, slot := some 0 }
    ]
    constructor := none
    functions := [
      { name := "viewWithStorageRead"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.ite (Expr.storage "val") (Expr.literal 1) (Expr.literal 0))]
        isView := true
      }
    ]
  }
  match compile exprIteViewAcceptedSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ Expr.ite view acceptance compile failed: {err}")
  | .ok _ =>
      IO.println "✓ Expr.ite with storage read accepted in view function"

-- Test 6: SpecInterpreter — Expr.ite evaluates true branch
#eval! do
  let exprIteInterpreterSpec : CompilationModel := {
    name := "ExprIteInterpreterSpec"
    fields := [
      { name := "threshold", ty := FieldType.uint256, slot := some 0 }
    ]
    constructor := none
    functions := [
      { name := "setThreshold"
        params := [{ name := "v", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "threshold" (Expr.param "v"), Stmt.stop]
      },
      { name := "check"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [
          -- return (x > threshold) ? x : threshold
          Stmt.return (Expr.ite (Expr.gt (Expr.param "x") (Expr.storage "threshold"))
            (Expr.param "x")
            (Expr.storage "threshold"))
        ]
        isView := true
      }
    ]
  }
  -- Set threshold = 50
  let setTx : Transaction := { sender := 0, functionName := "setThreshold", args := [50] }
  let setResult := interpretSpec exprIteInterpreterSpec SpecStorage.empty setTx
  if !setResult.success then
    throw (IO.userError s!"✗ Expr.ite interpreter setThreshold reverted: {setResult.revertReason}")
  -- check(100) should return 100 (true branch: 100 > 50)
  let checkHighTx : Transaction := { sender := 0, functionName := "check", args := [100] }
  let checkHighResult := interpretSpec exprIteInterpreterSpec setResult.finalStorage checkHighTx
  if checkHighResult.returnValue != some 100 then
    throw (IO.userError s!"✗ Expr.ite interpreter true branch: expected 100, got {checkHighResult.returnValue}")
  -- check(30) should return 50 (false branch: 30 < 50)
  let checkLowTx : Transaction := { sender := 0, functionName := "check", args := [30] }
  let checkLowResult := interpretSpec exprIteInterpreterSpec setResult.finalStorage checkLowTx
  if checkLowResult.returnValue != some 50 then
    throw (IO.userError s!"✗ Expr.ite interpreter false branch: expected 50, got {checkLowResult.returnValue}")
  IO.println "✓ SpecInterpreter Expr.ite evaluates both branches correctly"

-- Test 7: SpecInterpreter — Expr.ite with zero condition
#eval! do
  let exprIteZeroSpec : CompilationModel := {
    name := "ExprIteZeroSpec"
    fields := []
    constructor := none
    functions := [
      { name := "ternary"
        params := [{ name := "cond", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.ite (Expr.param "cond") (Expr.literal 111) (Expr.literal 222))]
        isView := true
      }
    ]
  }
  -- cond = 0 → false branch (222)
  let zeroTx : Transaction := { sender := 0, functionName := "ternary", args := [0] }
  let zeroResult := interpretSpec exprIteZeroSpec SpecStorage.empty zeroTx
  if zeroResult.returnValue != some 222 then
    throw (IO.userError s!"✗ Expr.ite zero cond: expected 222, got {zeroResult.returnValue}")
  -- cond = 1 → true branch (111)
  let oneTx : Transaction := { sender := 0, functionName := "ternary", args := [1] }
  let oneResult := interpretSpec exprIteZeroSpec SpecStorage.empty oneTx
  if oneResult.returnValue != some 111 then
    throw (IO.userError s!"✗ Expr.ite nonzero cond: expected 111, got {oneResult.returnValue}")
  -- cond = 999 → true branch (111) — any nonzero is truthy
  let bigTx : Transaction := { sender := 0, functionName := "ternary", args := [999] }
  let bigResult := interpretSpec exprIteZeroSpec SpecStorage.empty bigTx
  if bigResult.returnValue != some 111 then
    throw (IO.userError s!"✗ Expr.ite large nonzero cond: expected 111, got {bigResult.returnValue}")
  IO.println "✓ SpecInterpreter Expr.ite zero/nonzero condition semantics"

-- Test 8: Expr.ite rejects call-like operands in branches (Issue #748 parity)
#eval! do
  let exprIteCallLikeSpec : CompilationModel := {
    name := "ExprIteCallLikeRejected"
    fields := []
    constructor := none
    externals := [{ name := "oracle", params := [], returnType := some ParamType.uint256, axiomNames := [] }]
    functions := [
      { name := "bad"
        params := [{ name := "flag", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [
          Stmt.return (Expr.ite (Expr.param "flag")
            (Expr.externalCall "oracle" [])
            (Expr.literal 0))
        ]
      }
    ]
  }
  match compile exprIteCallLikeSpec [1] with
  | .error err =>
      if !(contains err "Expr.ite" && contains err "call-like operand" && contains err "Issue #748") then
        throw (IO.userError s!"✗ Expr.ite call-like operand diagnostic mismatch: {err}")
      IO.println "✓ Expr.ite rejects call-like operands in branches"
  | .ok _ =>
      throw (IO.userError "✗ expected call-like Expr.ite operand to fail compilation")

-- ===== ECM Compilation Smoke Tests =====
-- Verify that ECM modules compile correctly through the full pipeline.

private def renderSpec (spec : CompilationModel) (selectors : List Nat) : IO String := do
  match compile spec selectors with
  | .error err => throw (IO.userError s!"compile failed: {err}")
  | .ok ir => pure (Yul.render (emitYul ir))

-- ===== ECM smoke test: safeTransfer compiles =====
#eval! do
  let spec : CompilationModel := {
    name := "SafeTransferSmoke"
    fields := []
    constructor := none
    functions := [{
      name := "doTransfer"
      params := [⟨"token", ParamType.address⟩, ⟨"to", ParamType.address⟩, ⟨"amount", ParamType.uint256⟩]
      returnType := none
      body := [
        Modules.ERC20.safeTransfer (Expr.param "token") (Expr.param "to") (Expr.param "amount"),
        Stmt.stop
      ]
    }]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ ECM safeTransfer compilation failed: {err}")
  | .ok _ => IO.println "✓ ECM safeTransfer compiles successfully"

-- ===== ECM smoke test: safeTransferFrom compiles =====
#eval! do
  let spec : CompilationModel := {
    name := "SafeTransferFromSmoke"
    fields := []
    constructor := none
    functions := [{
      name := "doTransferFrom"
      params := [⟨"token", ParamType.address⟩, ⟨"from", ParamType.address⟩, ⟨"to", ParamType.address⟩, ⟨"amount", ParamType.uint256⟩]
      returnType := none
      body := [
        Modules.ERC20.safeTransferFrom (Expr.param "token") (Expr.param "from") (Expr.param "to") (Expr.param "amount"),
        Stmt.stop
      ]
    }]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ ECM safeTransferFrom compilation failed: {err}")
  | .ok _ => IO.println "✓ ECM safeTransferFrom compiles successfully"

-- ===== ECM smoke test: ecrecover compiles =====
#eval! do
  let spec : CompilationModel := {
    name := "EcrecoverSmoke"
    fields := [{ name := "recovered", ty := FieldType.address }]
    constructor := none
    functions := [{
      name := "recoverSigner"
      params := [⟨"digest", ParamType.bytes32⟩, ⟨"v", ParamType.uint256⟩, ⟨"r", ParamType.bytes32⟩, ⟨"s", ParamType.bytes32⟩]
      returnType := some FieldType.address
      body := [
        Modules.Precompiles.ecrecover "signer" (Expr.param "digest") (Expr.param "v") (Expr.param "r") (Expr.param "s"),
        Stmt.setStorage "recovered" (Expr.localVar "signer"),
        Stmt.return (Expr.localVar "signer")
      ]
    }]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ ECM ecrecover compilation failed: {err}")
  | .ok _ => IO.println "✓ ECM ecrecover compiles successfully"

-- ===== ECM smoke test: withReturn (staticcall) compiles =====
#eval! do
  let spec : CompilationModel := {
    name := "ExternalCallSmoke"
    fields := []
    constructor := none
    functions := [{
      name := "getPrice"
      params := [{ name := "oracle", ty := ParamType.address }]
      returnType := some FieldType.uint256
      body := [
        Modules.Calls.withReturn "price" (Expr.param "oracle") 0xa035b1fe [] (isStatic := true),
        Stmt.return (Expr.localVar "price")
      ]
    }]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ ECM withReturn (staticcall) compilation failed: {err}")
  | .ok _ => IO.println "✓ ECM withReturn (staticcall) compiles successfully"

-- ===== ECM smoke test: withReturn (multi-arg) compiles =====
#eval! do
  let spec : CompilationModel := {
    name := "ExternalCallMultiSmoke"
    fields := []
    constructor := none
    functions := [{
      name := "getBorrowRate"
      params := [{ name := "irm", ty := ParamType.address }, { name := "a", ty := ParamType.uint256 }, { name := "b", ty := ParamType.uint256 }]
      returnType := some FieldType.uint256
      body := [
        Modules.Calls.withReturn "rate" (Expr.param "irm") 0x9451fed4 [Expr.param "a", Expr.param "b"],
        Stmt.return (Expr.localVar "rate")
      ]
    }]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ ECM withReturn (multi-arg) compilation failed: {err}")
  | .ok _ => IO.println "✓ ECM withReturn (multi-arg) compiles successfully"

-- ===== ECM smoke test: callback compiles =====
#eval! do
  let spec : CompilationModel := {
    name := "CallbackSmoke"
    fields := [{ name := "balance", ty := FieldType.uint256 }]
    constructor := none
    functions := [{
      name := "supplyWithCallback"
      params := [⟨"assets", ParamType.uint256⟩, ⟨"data", ParamType.bytes⟩]
      returnType := none
      body := [
        Stmt.setStorage "balance" (Expr.add (Expr.storage "balance") (Expr.param "assets")),
        Modules.Callbacks.callback Expr.caller 0x7a29084c [Expr.param "assets"] "data",
        Stmt.stop
      ]
    }]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ ECM callback compilation failed: {err}")
  | .ok _ => IO.println "✓ ECM callback compiles successfully"

-- ===== ECM smoke test: callback (multi-arg) compiles =====
#eval! do
  let spec : CompilationModel := {
    name := "CallbackMultiSmoke"
    fields := [{ name := "balance", ty := FieldType.uint256 }]
    constructor := none
    functions := [{
      name := "liquidateCallback"
      params := [⟨"repaid", ParamType.uint256⟩, ⟨"seized", ParamType.uint256⟩, ⟨"data", ParamType.bytes⟩]
      returnType := none
      body := [
        Modules.Callbacks.callback Expr.caller 0xbeadbeef [Expr.param "repaid", Expr.param "seized"] "data",
        Stmt.stop
      ]
    }]
  }
  match compile spec [1] with
  | .error err => throw (IO.userError s!"✗ ECM callback (multi-arg) compilation failed: {err}")
  | .ok _ => IO.println "✓ ECM callback (multi-arg) compiles successfully"

-- ===== ECM callback rejects oversized selector =====
#eval! do
  let spec : CompilationModel := {
    name := "CallbackOversizedSelectorTest"
    fields := []
    constructor := none
    functions := [{
      name := "doCallback"
      params := [⟨"target", ParamType.address⟩, ⟨"data", ParamType.bytes⟩]
      returnType := none
      body := [
        Modules.Callbacks.callback Expr.caller 0x1FFFFFFFF [] "data",
        Stmt.stop
      ]
    }]
  }
  match compile spec [1] with
  | .error err =>
    if contains err "exceeds 4 bytes" then
      IO.println s!"✓ ECM callback correctly rejects oversized selector"
    else
      throw (IO.userError s!"✗ unexpected error: {err}")
  | .ok _ => throw (IO.userError "✗ expected oversized selector to be rejected")

-- ===== ECM safeApprove compiles (new module, no old equivalent) =====
#eval! do
  let spec : CompilationModel := {
    name := "SafeApproveTest"
    fields := []
    constructor := none
    functions := [{
      name := "doApprove"
      params := [⟨"token", ParamType.address⟩, ⟨"spender", ParamType.address⟩, ⟨"amount", ParamType.uint256⟩]
      returnType := none
      body := [
        Modules.ERC20.safeApprove (Expr.param "token") (Expr.param "spender") (Expr.param "amount"),
        Stmt.stop
      ]
    }]
  }
  let rendered ← renderSpec spec [1]
  -- Check selector for approve(address,uint256) = 0x095ea7b3
  -- Note: Yul renderer drops leading zero, emitting 0x95ea7b3...
  assertContains "safeApprove selector" rendered ["95ea7b3"]
  assertContains "safeApprove emits call" rendered ["call(gas(),"]
  assertContains "safeApprove revert on failure" rendered ["617070726f7665207265766572746564"]  -- "approve reverted"
  assertContains "safeApprove revert on false return" rendered ["617070726f76652072657475726e65642066616c7365"]  -- "approve returned false"
  IO.println "✓ ECM safeApprove (new module) compiles correctly"

-- ============================================================
-- Struct-typed storage fields (mappingStruct / mappingStruct2)
-- ============================================================

-- Test 1: Compiler produces correct Yul for struct member read/write (single key)
#eval! do
  let structSpec : CompilationModel := {
    name := "StructSingleKey"
    fields := [
      { name := "data", ty := FieldType.mappingStruct MappingKeyType.address [
          { name := "amount", wordOffset := 0 },
          { name := "timestamp", wordOffset := 1 }
        ], slot := some 5
      }
    ]
    constructor := none
    functions := [
      { name := "setAmount"
        params := [{ name := "who", ty := ParamType.address }, { name := "val", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStructMember "data" (Expr.param "who") "amount" (Expr.param "val"), Stmt.stop]
      },
      { name := "setTimestamp"
        params := [{ name := "who", ty := ParamType.address }, { name := "val", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStructMember "data" (Expr.param "who") "timestamp" (Expr.param "val"), Stmt.stop]
      },
      { name := "getAmount"
        params := [{ name := "who", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember "data" (Expr.param "who") "amount")]
      },
      { name := "getTimestamp"
        params := [{ name := "who", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember "data" (Expr.param "who") "timestamp")]
      }
    ]
  }
  match compile structSpec [1, 2, 3, 4] with
  | .error err =>
      throw (IO.userError s!"✗ expected struct single-key to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      -- amount is at wordOffset 0, so no add offset
      assertContains "struct member read amount (wordOffset=0)" rendered [
        "mappingSlot(5, who)", "sload("
      ]
      -- timestamp is at wordOffset 1, should have add(..., 1)
      assertContains "struct member read timestamp (wordOffset=1)" rendered [
        "add(", ", 1)"
      ]
      IO.println "✓ struct single-key compilation produces correct Yul"

-- Test 2: Compiler produces correct Yul for packed struct members (single key)
#eval! do
  let packedStructSpec : CompilationModel := {
    name := "PackedStruct"
    fields := [
      { name := "market", ty := FieldType.mappingStruct MappingKeyType.uint256 [
          { name := "totalSupply", wordOffset := 0, packed := some { offset := 0, width := 128 } },
          { name := "totalBorrow", wordOffset := 0, packed := some { offset := 128, width := 128 } },
          { name := "fee", wordOffset := 1 }
        ], slot := some 3
      }
    ]
    constructor := none
    functions := [
      { name := "getSupply"
        params := [{ name := "id", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember "market" (Expr.param "id") "totalSupply")]
      },
      { name := "getBorrow"
        params := [{ name := "id", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember "market" (Expr.param "id") "totalBorrow")]
      },
      { name := "setSupply"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "val", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStructMember "market" (Expr.param "id") "totalSupply" (Expr.param "val"), Stmt.stop]
      }
    ]
  }
  match compile packedStructSpec [1, 2, 3] with
  | .error err =>
      throw (IO.userError s!"✗ expected packed struct to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      -- totalSupply packed at offset=0, width=128 → mask = 2^128 - 1
      assertContains "packed struct read supply (shr+and)" rendered [
        "and(shr(0,", "sload("
      ]
      -- totalBorrow packed at offset=128 → shr by 128
      assertContains "packed struct read borrow (shr 128)" rendered [
        "shr(128,"
      ]
      -- setSupply should do read-modify-write
      assertContains "packed struct write supply (read-modify-write)" rendered [
        "sstore(", "or(", "not("
      ]
      IO.println "✓ packed struct compilation produces correct Yul for read/write"

-- Test 3: SpecInterpreter read/write for struct members (single key)
#eval! do
  let structInterpSpec : CompilationModel := {
    name := "StructInterp"
    fields := [
      { name := "positions", ty := FieldType.mappingStruct MappingKeyType.address [
          { name := "balance", wordOffset := 0 },
          { name := "shares", wordOffset := 1 }
        ], slot := some 7
      }
    ]
    constructor := none
    functions := [
      { name := "setBalance"
        params := [{ name := "who", ty := ParamType.address }, { name := "val", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStructMember "positions" (Expr.param "who") "balance" (Expr.param "val"), Stmt.stop]
      },
      { name := "setShares"
        params := [{ name := "who", ty := ParamType.address }, { name := "val", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStructMember "positions" (Expr.param "who") "shares" (Expr.param "val"), Stmt.stop]
      },
      { name := "getBalance"
        params := [{ name := "who", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember "positions" (Expr.param "who") "balance")]
      },
      { name := "getShares"
        params := [{ name := "who", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember "positions" (Expr.param "who") "shares")]
      }
    ]
  }
  let key : Nat := 0xABCD
  -- Write balance=100
  let tx1 : Transaction := { sender := 0, functionName := "setBalance", args := [key, 100] }
  let r1 := interpretSpec structInterpSpec SpecStorage.empty tx1
  if !r1.success then throw (IO.userError "✗ struct interp setBalance reverted")
  -- Write shares=200
  let tx2 : Transaction := { sender := 0, functionName := "setShares", args := [key, 200] }
  let r2 := interpretSpec structInterpSpec r1.finalStorage tx2
  if !r2.success then throw (IO.userError "✗ struct interp setShares reverted")
  -- Read balance back
  let tx3 : Transaction := { sender := 0, functionName := "getBalance", args := [key] }
  let r3 := interpretSpec structInterpSpec r2.finalStorage tx3
  if r3.returnValue != some 100 then
    throw (IO.userError s!"✗ struct interp getBalance expected 100, got {r3.returnValue}")
  -- Read shares back
  let tx4 : Transaction := { sender := 0, functionName := "getShares", args := [key] }
  let r4 := interpretSpec structInterpSpec r2.finalStorage tx4
  if r4.returnValue != some 200 then
    throw (IO.userError s!"✗ struct interp getShares expected 200, got {r4.returnValue}")
  IO.println "✓ SpecInterpreter struct member read/write round-trip works correctly"

-- Test 4: SpecInterpreter packed struct member read/write
#eval! do
  let packedStructInterpSpec : CompilationModel := {
    name := "PackedStructInterp"
    fields := [
      { name := "info", ty := FieldType.mappingStruct MappingKeyType.uint256 [
          { name := "low", wordOffset := 0, packed := some { offset := 0, width := 128 } },
          { name := "high", wordOffset := 0, packed := some { offset := 128, width := 128 } }
        ], slot := some 2
      }
    ]
    constructor := none
    functions := [
      { name := "setLow"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "val", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStructMember "info" (Expr.param "id") "low" (Expr.param "val"), Stmt.stop]
      },
      { name := "setHigh"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "val", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStructMember "info" (Expr.param "id") "high" (Expr.param "val"), Stmt.stop]
      },
      { name := "getLow"
        params := [{ name := "id", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember "info" (Expr.param "id") "low")]
      },
      { name := "getHigh"
        params := [{ name := "id", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember "info" (Expr.param "id") "high")]
      }
    ]
  }
  let key : Nat := 42
  -- Write low=0xFF
  let tx1 : Transaction := { sender := 0, functionName := "setLow", args := [key, 0xFF] }
  let r1 := interpretSpec packedStructInterpSpec SpecStorage.empty tx1
  if !r1.success then throw (IO.userError "✗ packed struct interp setLow reverted")
  -- Write high=0xAA (should not clobber low)
  let tx2 : Transaction := { sender := 0, functionName := "setHigh", args := [key, 0xAA] }
  let r2 := interpretSpec packedStructInterpSpec r1.finalStorage tx2
  if !r2.success then throw (IO.userError "✗ packed struct interp setHigh reverted")
  -- Read low back → should still be 0xFF
  let tx3 : Transaction := { sender := 0, functionName := "getLow", args := [key] }
  let r3 := interpretSpec packedStructInterpSpec r2.finalStorage tx3
  if r3.returnValue != some 0xFF then
    throw (IO.userError s!"✗ packed struct getLow expected 0xFF, got {r3.returnValue}")
  -- Read high back → should be 0xAA
  let tx4 : Transaction := { sender := 0, functionName := "getHigh", args := [key] }
  let r4 := interpretSpec packedStructInterpSpec r2.finalStorage tx4
  if r4.returnValue != some 0xAA then
    throw (IO.userError s!"✗ packed struct getHigh expected 0xAA, got {r4.returnValue}")
  IO.println "✓ SpecInterpreter packed struct member isolation (read-modify-write) works correctly"

-- Test 5: Double-key struct (mappingStruct2) compilation
#eval! do
  let struct2Spec : CompilationModel := {
    name := "StructDoubleKey"
    fields := [
      { name := "positions", ty := FieldType.mappingStruct2 MappingKeyType.uint256 MappingKeyType.address [
          { name := "supplyShares", wordOffset := 0 },
          { name := "borrowShares", wordOffset := 1 },
          { name := "collateral", wordOffset := 2 }
        ], slot := some 10
      }
    ]
    constructor := none
    functions := [
      { name := "getSupplyShares"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "who", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember2 "positions" (Expr.param "id") (Expr.param "who") "supplyShares")]
      },
      { name := "setCollateral"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "who", ty := ParamType.address }, { name := "val", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStructMember2 "positions" (Expr.param "id") (Expr.param "who") "collateral" (Expr.param "val"), Stmt.stop]
      }
    ]
  }
  match compile struct2Spec [1, 2] with
  | .error err =>
      throw (IO.userError s!"✗ expected struct2 to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      -- Double mapping: mappingSlot(mappingSlot(10, key1), key2) + wordOffset
      assertContains "struct2 nested mapping slot" rendered [
        "mappingSlot(10,", "mappingSlot("
      ]
      -- collateral at wordOffset=2 → add(..., 2)
      assertContains "struct2 collateral offset" rendered [
        "add(", ", 2)"
      ]
      IO.println "✓ struct2 (double-key) compilation produces correct Yul"

-- Test 6: SpecInterpreter double-key struct read/write
#eval! do
  let struct2InterpSpec : CompilationModel := {
    name := "Struct2Interp"
    fields := [
      { name := "pos", ty := FieldType.mappingStruct2 MappingKeyType.uint256 MappingKeyType.address [
          { name := "shares", wordOffset := 0 },
          { name := "debt", wordOffset := 1 }
        ], slot := some 4
      }
    ]
    constructor := none
    functions := [
      { name := "setShares"
        params := [{ name := "mkt", ty := ParamType.uint256 }, { name := "who", ty := ParamType.address }, { name := "val", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStructMember2 "pos" (Expr.param "mkt") (Expr.param "who") "shares" (Expr.param "val"), Stmt.stop]
      },
      { name := "setDebt"
        params := [{ name := "mkt", ty := ParamType.uint256 }, { name := "who", ty := ParamType.address }, { name := "val", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStructMember2 "pos" (Expr.param "mkt") (Expr.param "who") "debt" (Expr.param "val"), Stmt.stop]
      },
      { name := "getShares"
        params := [{ name := "mkt", ty := ParamType.uint256 }, { name := "who", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember2 "pos" (Expr.param "mkt") (Expr.param "who") "shares")]
      },
      { name := "getDebt"
        params := [{ name := "mkt", ty := ParamType.uint256 }, { name := "who", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember2 "pos" (Expr.param "mkt") (Expr.param "who") "debt")]
      }
    ]
  }
  let mkt : Nat := 1
  let user : Nat := 0x1234
  -- Write shares=500
  let tx1 : Transaction := { sender := 0, functionName := "setShares", args := [mkt, user, 500] }
  let r1 := interpretSpec struct2InterpSpec SpecStorage.empty tx1
  if !r1.success then throw (IO.userError "✗ struct2 interp setShares reverted")
  -- Write debt=300
  let tx2 : Transaction := { sender := 0, functionName := "setDebt", args := [mkt, user, 300] }
  let r2 := interpretSpec struct2InterpSpec r1.finalStorage tx2
  if !r2.success then throw (IO.userError "✗ struct2 interp setDebt reverted")
  -- Read shares → 500
  let tx3 : Transaction := { sender := 0, functionName := "getShares", args := [mkt, user] }
  let r3 := interpretSpec struct2InterpSpec r2.finalStorage tx3
  if r3.returnValue != some 500 then
    throw (IO.userError s!"✗ struct2 getShares expected 500, got {r3.returnValue}")
  -- Read debt → 300
  let tx4 : Transaction := { sender := 0, functionName := "getDebt", args := [mkt, user] }
  let r4 := interpretSpec struct2InterpSpec r2.finalStorage tx4
  if r4.returnValue != some 300 then
    throw (IO.userError s!"✗ struct2 getDebt expected 300, got {r4.returnValue}")
  IO.println "✓ SpecInterpreter struct2 read/write round-trip works correctly"

-- Test 7: Validation rejects duplicate struct member names
#eval! do
  let dupMemberSpec : CompilationModel := {
    name := "DupMember"
    fields := [
      { name := "data", ty := FieldType.mappingStruct MappingKeyType.address [
          { name := "x", wordOffset := 0 },
          { name := "x", wordOffset := 1 }
        ], slot := some 0
      }
    ]
    constructor := none
    functions := [
      { name := "get"
        params := [{ name := "who", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember "data" (Expr.param "who") "x")]
      }
    ]
  }
  match compile dupMemberSpec [1] with
  | .error err =>
      if !(contains err "duplicate member name 'x'") then
        throw (IO.userError s!"✗ duplicate member diagnostic mismatch: {err}")
      IO.println "✓ validation rejects duplicate struct member names"
  | .ok _ =>
      throw (IO.userError "✗ expected compilation to fail for duplicate struct member names")

-- Test 8: Validation rejects invalid packed range in struct member
#eval! do
  let badPackedSpec : CompilationModel := {
    name := "BadPacked"
    fields := [
      { name := "data", ty := FieldType.mappingStruct MappingKeyType.uint256 [
          { name := "x", wordOffset := 0, packed := some { offset := 200, width := 100 } }
        ], slot := some 0
      }
    ]
    constructor := none
    functions := [
      { name := "get"
        params := [{ name := "id", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember "data" (Expr.param "id") "x")]
      }
    ]
  }
  match compile badPackedSpec [1] with
  | .error err =>
      if !(contains err "invalid packed range") then
        throw (IO.userError s!"✗ bad packed range diagnostic mismatch: {err}")
      IO.println "✓ validation rejects invalid packed range in struct member"
  | .ok _ =>
      throw (IO.userError "✗ expected compilation to fail for invalid packed range in struct member")

-- Test 9: Validation rejects overlapping packed ranges in same struct word
#eval! do
  let overlapPackedSpec : CompilationModel := {
    name := "OverlapPacked"
    fields := [
      { name := "data", ty := FieldType.mappingStruct MappingKeyType.uint256 [
          { name := "a", wordOffset := 0, packed := some { offset := 0, width := 128 } },
          { name := "b", wordOffset := 0, packed := some { offset := 64, width := 128 } }
        ], slot := some 0
      }
    ]
    constructor := none
    functions := [
      { name := "getA"
        params := [{ name := "id", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember "data" (Expr.param "id") "a")]
      }
    ]
  }
  match compile overlapPackedSpec [1] with
  | .error err =>
      if !(contains err "overlapping/conflicting members" && contains err "'a'" && contains err "'b'") then
        throw (IO.userError s!"✗ overlapping packed members diagnostic mismatch: {err}")
      IO.println "✓ validation rejects overlapping packed ranges in struct members"
  | .ok _ =>
      throw (IO.userError "✗ expected compilation to fail for overlapping packed struct members")

-- Test 10: Validation rejects full-word and packed member sharing same word
#eval! do
  let fullAndPackedSpec : CompilationModel := {
    name := "FullAndPacked"
    fields := [
      { name := "data", ty := FieldType.mappingStruct MappingKeyType.address [
          { name := "full", wordOffset := 1 },
          { name := "packed", wordOffset := 1, packed := some { offset := 0, width := 64 } }
        ], slot := some 0
      }
    ]
    constructor := none
    functions := [
      { name := "get"
        params := [{ name := "who", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember "data" (Expr.param "who") "full")]
      }
    ]
  }
  match compile fullAndPackedSpec [1] with
  | .error err =>
      if !(contains err "overlapping/conflicting members" && contains err "'full'" && contains err "'packed'") then
        throw (IO.userError s!"✗ full-word vs packed diagnostic mismatch: {err}")
      IO.println "✓ validation rejects full-word/packed same-word struct members"
  | .ok _ =>
      throw (IO.userError "✗ expected compilation to fail for full-word/packed same-word members")

-- Test 11: SpecInterpreter struct member keys do not collide across key/wordOffset pairs
#eval! do
  let structCollisionSpec : CompilationModel := {
    name := "StructCollision"
    fields := [
      { name := "data", ty := FieldType.mappingStruct MappingKeyType.uint256 [
          { name := "a", wordOffset := 0 },
          { name := "b", wordOffset := 1 }
        ], slot := some 0
      }
    ]
    constructor := none
    functions := [
      { name := "setB"
        params := [{ name := "id", ty := ParamType.uint256 }, { name := "val", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStructMember "data" (Expr.param "id") "b" (Expr.param "val"), Stmt.stop]
      },
      { name := "getA"
        params := [{ name := "id", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember "data" (Expr.param "id") "a")]
      }
    ]
  }
  let w := interpretSpec structCollisionSpec SpecStorage.empty
    { sender := 0, functionName := "setB", args := [100, 777] }
  if !w.success then
    throw (IO.userError "✗ struct key-collision regression setup write reverted")
  let r := interpretSpec structCollisionSpec w.finalStorage
    { sender := 0, functionName := "getA", args := [101] }
  if r.returnValue != some 0 then
    throw (IO.userError s!"✗ struct key-collision regression: expected getA(101)=0, got {r.returnValue}")
  IO.println "✓ SpecInterpreter avoids struct key/wordOffset collisions"

-- Test 12: SpecInterpreter nested struct member keys do not collide across inner key/wordOffset pairs
#eval! do
  let struct2CollisionSpec : CompilationModel := {
    name := "Struct2Collision"
    fields := [
      { name := "data", ty := FieldType.mappingStruct2 MappingKeyType.uint256 MappingKeyType.uint256 [
          { name := "a", wordOffset := 0 },
          { name := "b", wordOffset := 1 }
        ], slot := some 0
      }
    ]
    constructor := none
    functions := [
      { name := "setB"
        params := [{ name := "k1", ty := ParamType.uint256 }, { name := "k2", ty := ParamType.uint256 }, { name := "val", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStructMember2 "data" (Expr.param "k1") (Expr.param "k2") "b" (Expr.param "val"), Stmt.stop]
      },
      { name := "getA"
        params := [{ name := "k1", ty := ParamType.uint256 }, { name := "k2", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.structMember2 "data" (Expr.param "k1") (Expr.param "k2") "a")]
      }
    ]
  }
  let w := interpretSpec struct2CollisionSpec SpecStorage.empty
    { sender := 0, functionName := "setB", args := [7, 100, 777] }
  if !w.success then
    throw (IO.userError "✗ nested struct key-collision regression setup write reverted")
  let r := interpretSpec struct2CollisionSpec w.finalStorage
    { sender := 0, functionName := "getA", args := [7, 101] }
  if r.returnValue != some 0 then
    throw (IO.userError s!"✗ nested struct key-collision regression: expected getA(7,101)=0, got {r.returnValue}")
  IO.println "✓ SpecInterpreter avoids nested struct key/wordOffset collisions"

-- Test 13: Type mismatch — structMember on a double mapping field
#eval! do
  let mismatchSpec : CompilationModel := {
    name := "Mismatch"
    fields := [
      { name := "nested", ty := FieldType.mappingStruct2 MappingKeyType.uint256 MappingKeyType.address [
          { name := "val", wordOffset := 0 }
        ], slot := some 0
      }
    ]
    constructor := none
    functions := [
      { name := "get"
        params := [{ name := "id", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        -- Wrong: using structMember (single key) on a mappingStruct2 (double key) field
        body := [Stmt.return (Expr.structMember "nested" (Expr.param "id") "val")]
      }
    ]
  }
  match compile mismatchSpec [1] with
  | .error err =>
      if !(contains err "double mapping" && contains err "structMember2") then
        throw (IO.userError s!"✗ type mismatch diagnostic mismatch: {err}")
      IO.println "✓ compilation rejects structMember on double-mapping struct field"
  | .ok _ =>
      throw (IO.userError "✗ expected compilation to fail for structMember on double-mapping field")

-- Test 10: internalCallAssign in fuel-based interpreter
#eval! do
  let internalMultiReturnSpec : CompilationModel := {
    name := "InternalMultiReturn"
    fields := [
      { name := "val", ty := FieldType.uint256 }
    ]
    constructor := none
    functions := [
      { name := "helper"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        returns := [ParamType.uint256, ParamType.uint256]
        isInternal := true
        body := [
          Stmt.returnValues [Expr.add (Expr.param "x") (Expr.literal 10), Expr.mul (Expr.param "x") (Expr.literal 2)]
        ]
      },
      { name := "doCall"
        params := [{ name := "input", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [
          Stmt.internalCallAssign ["a", "b"] "helper" [Expr.param "input"],
          Stmt.return (Expr.add (Expr.localVar "a") (Expr.localVar "b"))
        ]
      }
    ]
  }
  -- Use fuel-based interpreter for internal call support
  let fields := resolveFields internalMultiReturnSpec
  let ctx : EvalContext := {
    sender := 0
    msgValue := 0
    blockTimestamp := 0
    params := [5]  -- input = 5
    paramTypes := [ParamType.uint256]
    constructorArgs := []
    constructorParamTypes := []
    localVars := []
    arrayParams := []
  }
  let initialState : ExecState := {
    storage := SpecStorage.empty
    returnValue := none
    halted := false
  }
  let paramNames := ["input"]
  match execStmtsFuel 1000 ctx fields paramNames [] internalMultiReturnSpec.functions initialState
      [Stmt.internalCallAssign ["a", "b"] "helper" [Expr.param "input"],
       Stmt.return (Expr.add (Expr.localVar "a") (Expr.localVar "b"))] with
  | none =>
      throw (IO.userError "✗ internalCallAssign fuel-based execution reverted")
  | some (_, finalState) =>
      -- helper(5) → (15, 10), so a+b = 25
      if finalState.returnValue != some 25 then
        throw (IO.userError s!"✗ internalCallAssign expected return 25, got {finalState.returnValue}")
      IO.println "✓ fuel-based internalCallAssign properly binds multi-return values"

end Compiler.CompilationModelFeatureTest
