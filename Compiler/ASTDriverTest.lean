import Compiler.ASTDriver
import Compiler.ASTSpecs
import Compiler.Yul.PrettyPrint
import Verity.AST

/- Regression tests for AST driver constructor handling. -/
namespace Compiler.ASTDriverTest

open Compiler.ASTDriver
open Compiler.ASTSpecs
open Verity.AST

/-- Render deploy statements to a single string for assertions. -/
private def renderDeploy (stmts : List Yul.YulStmt) : String :=
  String.intercalate "\n" (Yul.ppStmts 0 stmts)

/-- Check that a string contains a substring. -/
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

/-- Assert that rendered output contains expected substrings. -/
private def assertContains (label rendered : String) (needles : List String) : IO Unit := do
  for needle in needles do
    if !contains rendered needle then
      throw (IO.userError s!"✗ {label}: missing '{needle}' in:\n{rendered}")
  IO.println s!"✓ {label}"

/-- Assert that rendered output does not contain forbidden substrings. -/
private def assertNotContains (label rendered : String) (needles : List String) : IO Unit := do
  for needle in needles do
    if contains rendered needle then
      throw (IO.userError s!"✗ {label}: unexpected '{needle}' in:\n{rendered}")
  IO.println s!"✓ {label}"

private def uniqueSelectors (spec : ASTContractSpec) : List Nat :=
  List.range spec.functions.length

#eval! do
  match compileSpec ownedSpec (uniqueSelectors ownedSpec) with
  | .error err =>
    throw (IO.userError s!"✗ owned constructor compile failed: {err}")
  | .ok ir =>
    let rendered := renderDeploy ir.deploy
    assertContains "Owned.deploy has constructor side effects" rendered ["sstore(0, initialOwner)"]
    assertNotContains "Owned.deploy strips constructor stop()" rendered ["stop()"]
    if ir.constructorPayable then
      throw (IO.userError "✗ Owned constructor should be non-payable by default")
    else
      IO.println "✓ Owned constructor defaults to non-payable"

#eval! do
  match compileSpec simpleTokenSpec (uniqueSelectors simpleTokenSpec) with
  | .error err =>
    throw (IO.userError s!"✗ simpleToken constructor compile failed: {err}")
  | .ok ir =>
    let rendered := renderDeploy ir.deploy
    assertContains "SimpleToken.deploy has constructor side effects" rendered ["sstore(0", "sstore(2"]
    assertNotContains "SimpleToken.deploy strips constructor stop()" rendered ["stop()"]

private def boolCtorSpec : ASTContractSpec := {
  name := "BoolCtorSpec"
  constructor := some {
    params := [{ name := "flag", ty := .bool }]
    body := Stmt.stop
  }
  functions := []
}

#eval! do
  match compileSpec boolCtorSpec [] with
  | .error err =>
    throw (IO.userError s!"✗ bool constructor compile failed: {err}")
  | .ok ir =>
    let rendered := renderDeploy ir.deploy
    assertContains "AST constructor bool decode enforces strict ABI domain" rendered
      ["let __abi_ctor_bool_word_0 := mload(0)",
       "if iszero(or(eq(__abi_ctor_bool_word_0, 0), eq(__abi_ctor_bool_word_0, 1))) {",
       "let flag := iszero(iszero(__abi_ctor_bool_word_0))"]

private def badConstructorReturnSpec : ASTContractSpec := {
  name := "BadConstructorReturn"
  constructor := some {
    params := []
    body := Stmt.ret (Expr.lit 0)
  }
  functions := []
}

#eval! do
  match compileSpec badConstructorReturnSpec [] with
  | .error err =>
    if contains err "must not return runtime data directly" then
      IO.println "✓ Constructor return(...) rejected in deploy path"
    else
      throw (IO.userError s!"✗ unexpected constructor error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected constructor return(...) to be rejected")

private def badEmptyContractNameSpec : ASTContractSpec := {
  name := "   "
  functions := []
}

#eval! do
  match compileSpec badEmptyContractNameSpec [] with
  | .error err =>
    if contains err "Contract name cannot be empty" then
      IO.println "✓ Empty contract name rejected in compileSpec"
    else
      throw (IO.userError s!"✗ unexpected empty-name error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected empty contract name to be rejected")

private def badDuplicateFunctionsSpec : ASTContractSpec := {
  name := "BadDuplicateFunctions"
  functions := [
    { name := "dup", params := [], returnType := .unit, body := Stmt.stop },
    { name := "dup", params := [], returnType := .unit, body := Stmt.stop }
  ]
}

#eval! do
  match compileSpec badDuplicateFunctionsSpec [0, 1] with
  | .error err =>
    if contains err "Duplicate function name" then
      IO.println "✓ Duplicate function names rejected in compileSpec"
    else
      throw (IO.userError s!"✗ unexpected duplicate-function error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected duplicate function names to be rejected")

private def badDuplicateSelectorsSpec : ASTContractSpec := {
  name := "BadDuplicateSelectors"
  functions := [
    { name := "f", params := [], returnType := .unit, body := Stmt.stop },
    { name := "g", params := [], returnType := .unit, body := Stmt.stop }
  ]
}

#eval! do
  match compileSpec badDuplicateSelectorsSpec [1, 1] with
  | .error err =>
    if contains err "Duplicate selector" then
      IO.println "✓ Duplicate selectors rejected in compileSpec"
    else
      throw (IO.userError s!"✗ unexpected duplicate-selector error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected duplicate selectors to be rejected")

private def badOutOfRangeSelectorSpec : ASTContractSpec := {
  name := "BadOutOfRangeSelector"
  functions := [
    { name := "f", params := [], returnType := .unit, body := Stmt.stop }
  ]
}

#eval! do
  match compileSpec badOutOfRangeSelectorSpec [((2 : Nat) ^ 32)] with
  | .error err =>
    if contains err "out of 4-byte range" then
      IO.println "✓ Out-of-range selectors rejected in compileSpec"
    else
      throw (IO.userError s!"✗ unexpected out-of-range selector error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected out-of-range selector to be rejected")

private def badFunctionIdentifierSpec : ASTContractSpec := {
  name := "BadFunctionIdentifier"
  functions := [
    { name := "bad-name", params := [], returnType := .unit, body := Stmt.stop }
  ]
}

#eval! do
  match compileSpec badFunctionIdentifierSpec [0] with
  | .error err =>
    if contains err "must be a valid identifier" then
      IO.println "✓ Invalid function identifiers rejected in compileSpec"
    else
      throw (IO.userError s!"✗ unexpected invalid-function-name error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected invalid function identifier to be rejected")

private def badParamIdentifierSpec : ASTContractSpec := {
  name := "BadParamIdentifier"
  functions := [
    { name := "goodName"
      params := [{ name := "0bad", ty := .uint256 }]
      returnType := .unit
      body := Stmt.stop }
  ]
}

#eval! do
  match compileSpec badParamIdentifierSpec [0] with
  | .error err =>
    if contains err "must be a valid identifier" then
      IO.println "✓ Invalid parameter identifiers rejected in compileSpec"
    else
      throw (IO.userError s!"✗ unexpected invalid-parameter-name error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected invalid parameter identifier to be rejected")

private def badFallbackNameSpec : ASTContractSpec := {
  name := "BadFallbackName"
  functions := [
    { name := "fallback", params := [], returnType := .unit, body := Stmt.stop }
  ]
}

#eval! do
  match compileSpec badFallbackNameSpec [0] with
  | .error err =>
    if contains err "reserved for ContractSpec special entrypoints" then
      IO.println "✓ Reserved function name fallback rejected in AST compileSpec"
    else
      throw (IO.userError s!"✗ unexpected reserved-name fallback error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected reserved function name fallback to be rejected")

private def badReceiveNameSpec : ASTContractSpec := {
  name := "BadReceiveName"
  functions := [
    { name := "receive", params := [], returnType := .unit, body := Stmt.stop }
  ]
}

#eval! do
  match compileSpec badReceiveNameSpec [0] with
  | .error err =>
    if contains err "reserved for ContractSpec special entrypoints" then
      IO.println "✓ Reserved function name receive rejected in AST compileSpec"
    else
      throw (IO.userError s!"✗ unexpected reserved-name receive error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected reserved function name receive to be rejected")

private def badContractIdentifierSpec : ASTContractSpec := {
  name := "0BadContract"
  functions := []
}

#eval! do
  match compileSpec badContractIdentifierSpec [] with
  | .error err =>
    if contains err "must be a valid identifier" then
      IO.println "✓ Invalid contract identifiers rejected in compileSpec"
    else
      throw (IO.userError s!"✗ unexpected invalid-contract-name error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected invalid contract identifier to be rejected")

#eval! do
  let rendered := emitASTContractABIJson simpleTokenSpec
  assertContains "AST ABI includes constructor and function entries" rendered
    ["\"type\": \"constructor\"",
     "\"name\": \"mint\"",
     "\"name\": \"transfer\"",
     "\"name\": \"balanceOf\""]
  assertContains "AST ABI includes typed returns" rendered
    ["\"name\": \"owner\"",
     "\"outputs\": [{\"name\": \"\", \"type\": \"address\"}]",
     "\"name\": \"totalSupply\"",
     "\"outputs\": [{\"name\": \"\", \"type\": \"uint256\"}]"]

private def payableFnSpec : ASTContractSpec := {
  name := "PayableFnSpec"
  functions := [
    { name := "deposit"
      params := []
      returnType := .unit
      isPayable := true
      body := Stmt.stop }
  ]
}

#eval! do
  match compileSpec payableFnSpec [0] with
  | .error err =>
    throw (IO.userError s!"✗ payable function compile failed: {err}")
  | .ok ir =>
    match ir.functions with
    | [fn] =>
      if !fn.payable then
        throw (IO.userError "✗ payable function should set IRFunction.payable")
      else
        IO.println "✓ AST function payability lowers to IR dispatch metadata"
    | _ =>
      throw (IO.userError "✗ expected exactly one function in payableFnSpec")

private def payableCtorSpec : ASTContractSpec := {
  name := "PayableCtorSpec"
  constructor := some {
    params := []
    isPayable := true
    body := Stmt.stop
  }
  functions := []
}

#eval! do
  match compileSpec payableCtorSpec [] with
  | .error err =>
    throw (IO.userError s!"✗ payable constructor compile failed: {err}")
  | .ok ir =>
    if !ir.constructorPayable then
      throw (IO.userError "✗ payable constructor should set IRContract.constructorPayable")
    else
      IO.println "✓ AST constructor payability lowers to IR deployment metadata"

private def abiMutabilitySpec : ASTContractSpec := {
  name := "AbiMutabilitySpec"
  constructor := some {
    params := []
    isPayable := true
    body := Stmt.stop
  }
  functions := [
    { name := "deposit"
      params := []
      returnType := .unit
      isPayable := true
      body := Stmt.stop },
    { name := "viewCount"
      params := []
      returnType := .uint256
      isView := true
      body := Stmt.ret (Expr.lit 1) },
    { name := "pureCount"
      params := []
      returnType := .uint256
      isPure := true
      body := Stmt.ret (Expr.lit 1) }
  ]
}

#eval! do
  let rendered := emitASTContractABIJson abiMutabilitySpec
  assertContains "AST ABI includes payable/view/pure mutability markers" rendered
    ["\"type\": \"constructor\"",
     "\"stateMutability\": \"payable\"",
     "\"name\": \"deposit\"",
     "\"stateMutability\": \"payable\"",
     "\"name\": \"viewCount\"",
     "\"stateMutability\": \"view\"",
     "\"name\": \"pureCount\"",
     "\"stateMutability\": \"pure\""]

private def invalidMutabilitySpecPayableView : ASTContractSpec := {
  name := "InvalidMutabilitySpecPayableView"
  functions := [
    { name := "bad"
      params := []
      returnType := .unit
      isPayable := true
      isView := true
      body := Stmt.stop }
  ]
}

#eval! do
  match compileSpec invalidMutabilitySpecPayableView [0] with
  | .error err =>
    if contains err "cannot be both payable and view/pure" then
      IO.println "✓ Invalid payable+view mutability rejected in compileSpec"
    else
      throw (IO.userError s!"✗ unexpected payable+view mutability error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected payable+view mutability to be rejected")

private def invalidMutabilitySpecViewPure : ASTContractSpec := {
  name := "InvalidMutabilitySpecViewPure"
  functions := [
    { name := "bad"
      params := []
      returnType := .unit
      isView := true
      isPure := true
      body := Stmt.stop }
  ]
}

#eval! do
  match compileSpec invalidMutabilitySpecViewPure [0] with
  | .error err =>
    if contains err "cannot be both view and pure" then
      IO.println "✓ Invalid view+pure mutability rejected in compileSpec"
    else
      throw (IO.userError s!"✗ unexpected view+pure mutability error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected view+pure mutability to be rejected")

private def invalidViewWritesStateSpec : ASTContractSpec := {
  name := "InvalidViewWritesStateSpec"
  functions := [
    { name := "mutate"
      params := []
      returnType := .unit
      isView := true
      body := Stmt.sstore 0 (Expr.lit 1) Stmt.stop }
  ]
}

#eval! do
  match compileSpec invalidViewWritesStateSpec [0] with
  | .error err =>
    if contains err "is marked view but writes state" then
      IO.println "✓ View mutability rejects state writes in AST body"
    else
      throw (IO.userError s!"✗ unexpected view-write mutability error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected view function with state write to be rejected")

private def invalidPureReadsStateSpec : ASTContractSpec := {
  name := "InvalidPureReadsStateSpec"
  functions := [
    { name := "readStorage"
      params := []
      returnType := .uint256
      isPure := true
      body := Stmt.ret (Expr.storage 0) }
  ]
}

#eval! do
  match compileSpec invalidPureReadsStateSpec [0] with
  | .error err =>
    if contains err "is marked pure but reads state/environment" then
      IO.println "✓ Pure mutability rejects state/environment reads in AST body"
    else
      throw (IO.userError s!"✗ unexpected pure-read mutability error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected pure function with state read to be rejected")

private def invalidDeclaredReturnStopsSpec : ASTContractSpec := {
  name := "InvalidDeclaredReturnStopsSpec"
  functions := [
    { name := "getValue"
      params := []
      returnType := .uint256
      body := Stmt.stop }
  ]
}

#eval! do
  match compileSpec invalidDeclaredReturnStopsSpec [0] with
  | .error err =>
    if contains err "declares uint256 returnType but terminates with stop" then
      IO.println "✓ AST compile rejects declared uint256 return with stop termination"
    else
      throw (IO.userError s!"✗ unexpected declared-return/stop mismatch error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected declared uint256 return with stop to be rejected")

private def invalidUnitReturnsValueSpec : ASTContractSpec := {
  name := "InvalidUnitReturnsValueSpec"
  functions := [
    { name := "f"
      params := []
      returnType := .unit
      body := Stmt.ret (Expr.lit 1) }
  ]
}

#eval! do
  match compileSpec invalidUnitReturnsValueSpec [0] with
  | .error err =>
    if contains err "declares unit returnType but returns a uint256 value" then
      IO.println "✓ AST compile rejects unit returnType with value return"
    else
      throw (IO.userError s!"✗ unexpected unit/value return mismatch error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected unit returnType with value return to be rejected")

private def validAddressReturnShapeSpec : ASTContractSpec := {
  name := "ValidAddressReturnShapeSpec"
  functions := [
    { name := "owner"
      params := []
      returnType := .address
      body := Stmt.bindAddr "sender" Expr.sender
        (Stmt.retAddr (Expr.varAddr "sender")) }
  ]
}

#eval! do
  match compileSpec validAddressReturnShapeSpec [0] with
  | .error err =>
    throw (IO.userError s!"✗ expected valid address return shape to compile, got: {err}")
  | .ok _ =>
    IO.println "✓ AST compile accepts valid address return shape"

private def invalidAddressReturnShapeSpec : ASTContractSpec := {
  name := "InvalidAddressReturnShapeSpec"
  functions := [
    { name := "owner"
      params := []
      returnType := .address
      body := Stmt.retAddr Expr.sender }
  ]
}

#eval! do
  match compileSpec invalidAddressReturnShapeSpec [0] with
  | .error err =>
    if contains err "malformed AST: retAddr expects a bound address variable" then
      IO.println "✓ AST compile rejects malformed retAddr expression shape"
    else
      throw (IO.userError s!"✗ unexpected malformed retAddr error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected malformed retAddr expression to be rejected")

private def malformedBindUintSourceSpec : ASTContractSpec := {
  name := "MalformedBindUintSourceSpec"
  functions := [
    { name := "f"
      params := []
      returnType := .unit
      body := Stmt.bindUint "x" Expr.sender Stmt.stop }
  ]
}

#eval! do
  match compileSpec malformedBindUintSourceSpec [0] with
  | .error err =>
    if contains err "malformed AST: bindUint expects storage(...) or mapping(..., varAddr ...)" then
      IO.println "✓ AST compile rejects malformed bindUint source shape"
    else
      throw (IO.userError s!"✗ unexpected malformed bindUint error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected malformed bindUint source to be rejected")

private def malformedRequireSomeSourceSpec : ASTContractSpec := {
  name := "MalformedRequireSomeSourceSpec"
  functions := [
    { name := "f"
      params := []
      returnType := .unit
      body := Stmt.requireSome "x" (Expr.lit 1) "bad" Stmt.stop }
  ]
}

#eval! do
  match compileSpec malformedRequireSomeSourceSpec [0] with
  | .error err =>
    if contains err "malformed AST: requireSome expects safeAdd(...) or safeSub(...)" then
      IO.println "✓ AST compile rejects malformed requireSome source shape"
    else
      throw (IO.userError s!"✗ unexpected malformed requireSome error: {err}")
  | .ok _ =>
    throw (IO.userError "✗ expected malformed requireSome source to be rejected")

end Compiler.ASTDriverTest
