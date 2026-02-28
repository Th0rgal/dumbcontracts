import Lean
import Verity.Macro.Syntax

namespace Verity.Macro

open Lean
open Lean.Elab
open Lean.Elab.Command

set_option hygiene false

abbrev Term := TSyntax `term
abbrev Cmd := TSyntax `command
abbrev Ident := TSyntax `ident

inductive ScalarType where
  | uint256
  | address
  | unit
  deriving BEq

structure StorageFieldDecl where
  ident : Ident
  name : String
  ty : ScalarType
  slotNum : Nat

structure ParamDecl where
  ident : Ident
  name : String
  ty : ScalarType

structure FunctionDecl where
  ident : Ident
  name : String
  params : Array ParamDecl
  returnTy : ScalarType
  body : Term

private def strTerm (s : String) : Term := ⟨Syntax.mkStrLit s⟩
private def natTerm (n : Nat) : Term := ⟨Syntax.mkNumLit (toString n)⟩

private def typeFromSyntax (ty : Term) : CommandElabM ScalarType := do
  match ty with
  | `(term| Uint256) => pure .uint256
  | `(term| Address) => pure .address
  | `(term| Unit) => pure .unit
  | _ => throwErrorAt ty "unsupported type '{ty}'; expected Uint256, Address, or Unit"

private def natFromSyntax (stx : Syntax) : CommandElabM Nat :=
  match stx.isNatLit? with
  | some n => pure n
  | none => throwErrorAt stx "expected natural literal"

private def modelFieldTypeTerm (ty : ScalarType) : CommandElabM Term :=
  match ty with
  | .uint256 => `(Compiler.CompilationModel.FieldType.uint256)
  | .address => `(Compiler.CompilationModel.FieldType.address)
  | .unit => throwError "storage fields cannot be Unit"

private def modelParamTypeTerm (ty : ScalarType) : CommandElabM Term :=
  match ty with
  | .uint256 => `(Compiler.CompilationModel.ParamType.uint256)
  | .address => `(Compiler.CompilationModel.ParamType.address)
  | .unit => throwError "function parameters cannot be Unit"

private def modelReturnTypeTerm (ty : ScalarType) : CommandElabM Term :=
  match ty with
  | .unit => `(none)
  | .uint256 => `(some Compiler.CompilationModel.FieldType.uint256)
  | .address => `(some Compiler.CompilationModel.FieldType.address)

private def contractScalarTypeTerm (ty : ScalarType) : CommandElabM Term :=
  match ty with
  | .uint256 => `(Uint256)
  | .address => `(Address)
  | .unit => `(Unit)

private def parseStorageField (stx : Syntax) : CommandElabM StorageFieldDecl := do
  match stx with
  | `(verityStorageField| $name:ident : $ty:term := slot $slotNum:num) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← typeFromSyntax ty
        slotNum := ← natFromSyntax slotNum
      }
  | _ => throwErrorAt stx "invalid storage field declaration"

private def parseParam (stx : Syntax) : CommandElabM ParamDecl := do
  match stx with
  | `(verityParam| $name:ident : $ty:term) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← typeFromSyntax ty
      }
  | _ => throwErrorAt stx "invalid parameter declaration"

private def parseFunction (stx : Syntax) : CommandElabM FunctionDecl := do
  match stx with
  | `(verityFunction| function $name:ident ($[$params:verityParam],*) : $retTy:term := $body:term) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM parseParam
        returnTy := ← typeFromSyntax retTy
        body := body
      }
  | _ => throwErrorAt stx "invalid function declaration"

private partial def stripParens (stx : Term) : Term :=
  match stx with
  | `(term| ($inner)) => stripParens inner
  | _ => stx

private def lookupStorageField (fields : Array StorageFieldDecl) (name : String) : CommandElabM StorageFieldDecl := do
  match fields.find? (fun f => f.name == name) with
  | some f => pure f
  | none => throwError s!"unknown storage field '{name}'"

private def expectStringLiteral (stx : Term) : CommandElabM String :=
  match (stripParens stx).raw.isStrLit? with
  | some s => pure s
  | none => throwErrorAt stx "expected string literal"

private def lookupVarExpr (params : Array ParamDecl) (locals : Array String) (name : String) : CommandElabM Term := do
  if params.any (fun p => p.name == name) then
    `(Compiler.CompilationModel.Expr.param $(strTerm name))
  else if locals.contains name then
    `(Compiler.CompilationModel.Expr.localVar $(strTerm name))
  else
    throwError s!"unknown variable '{name}'"

partial def translatePureExpr
    (params : Array ParamDecl)
    (locals : Array String)
    (stx : Term) : CommandElabM Term := do
  let stx := stripParens stx
  match stx with
  | `(term| $id:ident) => lookupVarExpr params locals (toString id.getId)
  | `(term| $n:num) => `(Compiler.CompilationModel.Expr.literal $n)
  | `(term| add $a $b) => `(Compiler.CompilationModel.Expr.add $(← translatePureExpr params locals a) $(← translatePureExpr params locals b))
  | `(term| sub $a $b) => `(Compiler.CompilationModel.Expr.sub $(← translatePureExpr params locals a) $(← translatePureExpr params locals b))
  | `(term| $a == $b) => `(Compiler.CompilationModel.Expr.eq $(← translatePureExpr params locals a) $(← translatePureExpr params locals b))
  | _ => throwErrorAt stx "unsupported expression in verity_contract body"

private def translateBindSource (fields : Array StorageFieldDecl) (rhs : Term) : CommandElabM Term := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| getStorage $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .uint256 => `(Compiler.CompilationModel.Expr.storage $(strTerm f.name))
      | .address => throwErrorAt rhs s!"field '{f.name}' is Address; use getStorageAddr"
      | .unit => throwErrorAt rhs "invalid field type"
  | `(term| getStorageAddr $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .address => `(Compiler.CompilationModel.Expr.storage $(strTerm f.name))
      | .uint256 => throwErrorAt rhs s!"field '{f.name}' is Uint256; use getStorage"
      | .unit => throwErrorAt rhs "invalid field type"
  | `(term| msgSender) => `(Compiler.CompilationModel.Expr.caller)
  | _ => throwErrorAt rhs "unsupported bind source; expected getStorage/getStorageAddr/msgSender"

private def translateEffectStmt
    (fields : Array StorageFieldDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (stx : Term) : CommandElabM Term := do
  let stx := stripParens stx
  match stx with
  | `(term| setStorage $field:ident $value) =>
      let f ← lookupStorageField fields (toString field.getId)
      if f.ty != .uint256 then
        throwErrorAt stx s!"field '{f.name}' is not Uint256; use setStorageAddr"
      `(Compiler.CompilationModel.Stmt.setStorage $(strTerm f.name) $(← translatePureExpr params locals value))
  | `(term| setStorageAddr $field:ident $value) =>
      let f ← lookupStorageField fields (toString field.getId)
      if f.ty != .address then
        throwErrorAt stx s!"field '{f.name}' is not Address; use setStorage"
      `(Compiler.CompilationModel.Stmt.setStorage $(strTerm f.name) $(← translatePureExpr params locals value))
  | `(term| require $cond $msg) =>
      `(Compiler.CompilationModel.Stmt.require $(← translatePureExpr params locals cond) $(strTerm (← expectStringLiteral msg)))
  | _ => throwErrorAt stx "unsupported statement in do block"

private def translateDoElem
    (fields : Array StorageFieldDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (elem : TSyntax `doElem) : CommandElabM (Array Term × Array String) := do
  match elem with
  | `(doElem| let $name:ident ← $rhs:term) =>
      let varName := toString name.getId
      if locals.contains varName then
        throwErrorAt name s!"duplicate local variable '{varName}'"
      let rhsExpr ← translateBindSource fields rhs
      pure (#[(← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $rhsExpr))], locals.push varName)
  | `(doElem| let $name:ident := $rhs:term) =>
      let varName := toString name.getId
      if locals.contains varName then
        throwErrorAt name s!"duplicate local variable '{varName}'"
      let rhsExpr ← translatePureExpr params locals rhs
      pure (#[(← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $rhsExpr))], locals.push varName)
  | `(doElem| return $value:term) =>
      pure (#[(← `(Compiler.CompilationModel.Stmt.return $(← translatePureExpr params locals value)))], locals)
  | `(doElem| $stmt:term) =>
      pure (#[(← translateEffectStmt fields params locals stmt)], locals)
  | _ => throwErrorAt elem "unsupported do element"

private def translateBodyToStmtTerms
    (fields : Array StorageFieldDecl)
    (fn : FunctionDecl) : CommandElabM (Array Term) := do
  match fn.body with
  | `(term| do $[$elems:doElem]*) =>
      let mut locals : Array String := #[]
      let mut stmts : Array Term := #[]
      for elem in elems do
        let (newStmts, newLocals) ← translateDoElem fields fn.params locals elem
        stmts := stmts ++ newStmts
        locals := newLocals
      if fn.returnTy == .unit then
        stmts := stmts.push (← `(Compiler.CompilationModel.Stmt.stop))
      pure stmts
  | _ => throwErrorAt fn.body "function body must be a do block"

def mkSuffixedIdent (base : Ident) (suffix : String) : CommandElabM Ident :=
  let rec appendSuffix : Name → Name
    | .anonymous => .str .anonymous suffix
    | .str p s => .str p (s ++ suffix)
    | .num p n => .str p (toString n ++ suffix)
  pure <| mkIdent <| appendSuffix base.getId

private def mkContractFnType (params : Array ParamDecl) (retTy : ScalarType) : CommandElabM Term := do
  let mut ty ← `(Verity.Contract $(← contractScalarTypeTerm retTy))
  for param in params.reverse do
    ty ← `(($(← contractScalarTypeTerm param.ty)) → $ty)
  pure ty

private def mkContractFnValue (params : Array ParamDecl) (body : Term) : CommandElabM Term := do
  let mut value := body
  for param in params.reverse do
    let pid := param.ident
    value ← `(fun ($pid : $(← contractScalarTypeTerm param.ty)) => $value)
  pure value

private def mkModelParamsTerm (params : Array ParamDecl) : CommandElabM Term := do
  let xs ← params.mapM fun p => do
    `(Compiler.CompilationModel.Param.mk $(strTerm p.name) $(← modelParamTypeTerm p.ty))
  `([ $[$xs],* ])

private def mkStorageDefCommand (field : StorageFieldDecl) : CommandElabM Cmd := do
  let storageTy ←
    match field.ty with
    | .uint256 => `(Uint256)
    | .address => `(Address)
    | .unit => throwError "storage field cannot be Unit"
  let fid := field.ident
  `(command| def $fid : Verity.StorageSlot $storageTy := ⟨$(natTerm field.slotNum)⟩)

private def mkModelFieldTerm (field : StorageFieldDecl) : CommandElabM Term := do
  `(Compiler.CompilationModel.Field.mk
      $(strTerm field.name)
      $(← modelFieldTypeTerm field.ty)
      (some $(natTerm field.slotNum))
      none
      [])

private def mkFunctionCommands (fields : Array StorageFieldDecl) (fn : FunctionDecl) : CommandElabM (Array Cmd) := do
  let fnType ← mkContractFnType fn.params fn.returnTy
  let fnValue ← mkContractFnValue fn.params fn.body
  let modelBodyName ← mkSuffixedIdent fn.ident "_modelBody"
  let modelName ← mkSuffixedIdent fn.ident "_model"
  let stmtTerms ← translateBodyToStmtTerms fields fn
  let modelParams ← mkModelParamsTerm fn.params

  let fnCmd : Cmd ← `(command| def $fn.ident : $fnType := $fnValue)
  let bodyCmd : Cmd ← `(command| def $modelBodyName : List Compiler.CompilationModel.Stmt := [ $[$stmtTerms],* ])
  let modelCmd : Cmd ← `(command| def $modelName : Compiler.CompilationModel.FunctionSpec := {
    name := $(strTerm fn.name)
    params := $modelParams
    returnType := $(← modelReturnTypeTerm fn.returnTy)
    body := $modelBodyName
  })
  pure #[fnCmd, bodyCmd, modelCmd]

private def mkSpecCommand
    (contractName : String)
    (fields : Array StorageFieldDecl)
    (functions : Array FunctionDecl) : CommandElabM Cmd := do
  let fieldTerms ← fields.mapM mkModelFieldTerm
  let functionModelIds ← functions.mapM fun fn => mkSuffixedIdent fn.ident "_model"
  `(command| def spec : Compiler.CompilationModel.CompilationModel := {
    name := $(strTerm contractName)
    fields := [ $[$fieldTerms],* ]
    constructor := none
    functions := [ $[$functionModelIds],* ]
  })

def parseContractSyntax (stx : Syntax) : CommandElabM (Ident × Array StorageFieldDecl × Array FunctionDecl) := do
  match stx with
  | `(command| verity_contract $contractName:ident where storage $[$storageFields:verityStorageField]* $[$functions:verityFunction]*) =>
      pure (contractName, (← storageFields.mapM parseStorageField), (← functions.mapM parseFunction))
  | _ => throwErrorAt stx "invalid verity_contract declaration"

def mkStorageDefCommandPublic (field : StorageFieldDecl) : CommandElabM Cmd :=
  mkStorageDefCommand field

def mkFunctionCommandsPublic
    (fields : Array StorageFieldDecl)
    (fn : FunctionDecl) : CommandElabM (Array Cmd) :=
  mkFunctionCommands fields fn

def mkSpecCommandPublic
    (contractName : String)
    (fields : Array StorageFieldDecl)
    (functions : Array FunctionDecl) : CommandElabM Cmd :=
  mkSpecCommand contractName fields functions

end Verity.Macro
