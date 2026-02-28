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
abbrev DoSeq := TSyntax `Lean.Parser.Term.doSeq

inductive ValueType where
  | uint256
  | address
  | unit
  deriving BEq

inductive StorageType where
  | scalar (ty : ValueType)
  | mappingAddressToUint256
  | mapping2AddressToAddressToUint256
  | mappingUintToUint256
  deriving BEq

structure StorageFieldDecl where
  ident : Ident
  name : String
  ty : StorageType
  slotNum : Nat

structure ParamDecl where
  ident : Ident
  name : String
  ty : ValueType

structure FunctionDecl where
  ident : Ident
  name : String
  params : Array ParamDecl
  returnTy : ValueType
  body : Term

structure ConstructorDecl where
  params : Array ParamDecl
  body : Term

private def strTerm (s : String) : Term := ⟨Syntax.mkStrLit s⟩
private def natTerm (n : Nat) : Term := ⟨Syntax.mkNumLit (toString n)⟩

private def valueTypeFromSyntax (ty : Term) : CommandElabM ValueType := do
  match ty with
  | `(term| Uint256) => pure .uint256
  | `(term| Address) => pure .address
  | `(term| Unit) => pure .unit
  | _ => throwErrorAt ty "unsupported type '{ty}'; expected Uint256, Address, or Unit"

private def storageTypeFromSyntax (ty : Term) : CommandElabM StorageType := do
  match ty with
  | `(term| Address → Uint256) => pure .mappingAddressToUint256
  | `(term| Address → Address → Uint256) => pure .mapping2AddressToAddressToUint256
  | `(term| Uint256 → Uint256) => pure .mappingUintToUint256
  | _ => pure (.scalar (← valueTypeFromSyntax ty))

private def natFromSyntax (stx : Syntax) : CommandElabM Nat :=
  match stx.isNatLit? with
  | some n => pure n
  | none => throwErrorAt stx "expected natural literal"

private def modelFieldTypeTerm (ty : StorageType) : CommandElabM Term :=
  match ty with
  | .scalar .uint256 => `(Compiler.CompilationModel.FieldType.uint256)
  | .scalar .address => `(Compiler.CompilationModel.FieldType.address)
  | .scalar .unit => throwError "storage fields cannot be Unit"
  | .mappingAddressToUint256 =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.simple Compiler.CompilationModel.MappingKeyType.address))
  | .mapping2AddressToAddressToUint256 =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.nested
            Compiler.CompilationModel.MappingKeyType.address
            Compiler.CompilationModel.MappingKeyType.address))
  | .mappingUintToUint256 =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.simple Compiler.CompilationModel.MappingKeyType.uint256))

private def modelParamTypeTerm (ty : ValueType) : CommandElabM Term :=
  match ty with
  | .uint256 => `(Compiler.CompilationModel.ParamType.uint256)
  | .address => `(Compiler.CompilationModel.ParamType.address)
  | .unit => throwError "function parameters cannot be Unit"

private def modelReturnTypeTerm (ty : ValueType) : CommandElabM Term :=
  match ty with
  | .unit => `(none)
  | .uint256 => `(some Compiler.CompilationModel.FieldType.uint256)
  | .address => `(some Compiler.CompilationModel.FieldType.address)

private def contractValueTypeTerm (ty : ValueType) : CommandElabM Term :=
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
        ty := ← storageTypeFromSyntax ty
        slotNum := ← natFromSyntax slotNum
      }
  | _ => throwErrorAt stx "invalid storage field declaration"

private def parseParam (stx : Syntax) : CommandElabM ParamDecl := do
  match stx with
  | `(verityParam| $name:ident : $ty:term) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← valueTypeFromSyntax ty
      }
  | _ => throwErrorAt stx "invalid parameter declaration"

private def parseFunction (stx : Syntax) : CommandElabM FunctionDecl := do
  match stx with
  | `(verityFunction| function $name:ident ($[$params:verityParam],*) : $retTy:term := $body:term) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM parseParam
        returnTy := ← valueTypeFromSyntax retTy
        body := body
      }
  | _ => throwErrorAt stx "invalid function declaration"

private def parseConstructor (stx : Syntax) : CommandElabM ConstructorDecl := do
  match stx with
  | `(verityConstructor| constructor ($[$params:verityParam],*) := $body:term) =>
      pure {
        params := ← params.mapM parseParam
        body := body
      }
  | _ => throwErrorAt stx "invalid constructor declaration"

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
  | `(term| $a >= $b) => `(Compiler.CompilationModel.Expr.ge $(← translatePureExpr params locals a) $(← translatePureExpr params locals b))
  | _ => throwErrorAt stx "unsupported expression in verity_contract body"

private def translateBindSource
    (fields : Array StorageFieldDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (rhs : Term) : CommandElabM Term := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| getStorage $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .uint256 => `(Compiler.CompilationModel.Expr.storage $(strTerm f.name))
      | .scalar .address => throwErrorAt rhs s!"field '{f.name}' is Address; use getStorageAddr"
      | .scalar .unit => throwErrorAt rhs "invalid field type"
      | _ => throwErrorAt rhs s!"field '{f.name}' is a mapping; use getMapping/getMapping2"
  | `(term| getStorageAddr $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .address => `(Compiler.CompilationModel.Expr.storage $(strTerm f.name))
      | .scalar .uint256 => throwErrorAt rhs s!"field '{f.name}' is Uint256; use getStorage"
      | .scalar .unit => throwErrorAt rhs "invalid field type"
      | _ => throwErrorAt rhs s!"field '{f.name}' is a mapping; use getMapping/getMapping2"
  | `(term| getMapping $field:ident $key:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Expr.mapping $(strTerm f.name) $(← translatePureExpr params locals key))
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Expr.mappingUint $(strTerm f.name) $(← translatePureExpr params locals key))
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMapping2 $field:ident $key1:term $key2:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mapping2AddressToAddressToUint256 =>
          `(Compiler.CompilationModel.Expr.mapping2
              $(strTerm f.name)
              $(← translatePureExpr params locals key1)
              $(← translatePureExpr params locals key2))
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a double mapping"
  | `(term| msgSender) => `(Compiler.CompilationModel.Expr.caller)
  | _ => throwErrorAt rhs "unsupported bind source; expected getStorage/getStorageAddr/getMapping/getMapping2/msgSender"

private def translateSafeRequireBind
    (params : Array ParamDecl)
    (locals : Array String)
    (varName : String)
    (rhs : Term) : CommandElabM (Option (Array Term)) := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| requireSomeUint $optExpr:term $msg:term) =>
      let msgLit ← strTerm <$> expectStringLiteral msg
      let optExpr := stripParens optExpr
      match optExpr with
      | `(term| safeAdd $a:term $b:term) =>
          let aExpr ← translatePureExpr params locals a
          let bExpr ← translatePureExpr params locals b
          let valueExpr : Term ← `(Compiler.CompilationModel.Expr.add $aExpr $bExpr)
          let guardExpr : Term ← `(Compiler.CompilationModel.Expr.ge $valueExpr $aExpr)
          pure (some #[
            (← `(Compiler.CompilationModel.Stmt.require $guardExpr $msgLit)),
            (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
          ])
      | `(term| safeSub $a:term $b:term) =>
          let aExpr ← translatePureExpr params locals a
          let bExpr ← translatePureExpr params locals b
          let valueExpr : Term ← `(Compiler.CompilationModel.Expr.sub $aExpr $bExpr)
          let guardExpr : Term ← `(Compiler.CompilationModel.Expr.ge $aExpr $bExpr)
          pure (some #[
            (← `(Compiler.CompilationModel.Stmt.require $guardExpr $msgLit)),
            (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
          ])
      | _ =>
          throwErrorAt rhs "unsupported requireSomeUint source; expected safeAdd or safeSub"
  | _ => pure none

private def translateEffectStmt
    (fields : Array StorageFieldDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (stx : Term) : CommandElabM Term := do
  let stx := stripParens stx
  match stx with
  | `(term| setStorage $field:ident $value) =>
      let f ← lookupStorageField fields (toString field.getId)
      if f.ty != .scalar .uint256 then
        throwErrorAt stx s!"field '{f.name}' is not Uint256; use setStorageAddr"
      `(Compiler.CompilationModel.Stmt.setStorage $(strTerm f.name) $(← translatePureExpr params locals value))
  | `(term| setStorageAddr $field:ident $value) =>
      let f ← lookupStorageField fields (toString field.getId)
      if f.ty != .scalar .address then
        throwErrorAt stx s!"field '{f.name}' is not Address; use setStorage"
      `(Compiler.CompilationModel.Stmt.setStorage $(strTerm f.name) $(← translatePureExpr params locals value))
  | `(term| setMapping $field:ident $key:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMapping
              $(strTerm f.name)
              $(← translatePureExpr params locals key)
              $(← translatePureExpr params locals value))
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMappingUint
              $(strTerm f.name)
              $(← translatePureExpr params locals key)
              $(← translatePureExpr params locals value))
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMapping2 $field:ident $key1:term $key2:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mapping2AddressToAddressToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMapping2
              $(strTerm f.name)
              $(← translatePureExpr params locals key1)
              $(← translatePureExpr params locals key2)
              $(← translatePureExpr params locals value))
      | _ => throwErrorAt stx s!"field '{f.name}' is not a double mapping"
  | `(term| require $cond $msg) =>
      `(Compiler.CompilationModel.Stmt.require $(← translatePureExpr params locals cond) $(strTerm (← expectStringLiteral msg)))
  | _ => throwErrorAt stx "unsupported statement in do block"

mutual
private partial def translateDoElems
    (fields : Array StorageFieldDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (elems : Array (TSyntax `doElem)) : CommandElabM (Array Term × Array String) := do
  let mut branchLocals := locals
  let mut stmts : Array Term := #[]
  for elem in elems do
    let (newStmts, newLocals) ← translateDoElem fields params branchLocals elem
    stmts := stmts ++ newStmts
    branchLocals := newLocals
  pure (stmts, branchLocals)

private partial def translateDoSeqToStmtTerms
    (fields : Array StorageFieldDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (doSeq : DoSeq) : CommandElabM (Array Term) := do
  match doSeq with
  | `(doSeq| $[$elems:doElem]*) =>
      pure (← (translateDoElems fields params locals elems)).1
  | _ => throwErrorAt doSeq "unsupported branch body; expected do-sequence"

private partial def translateDoElem
    (fields : Array StorageFieldDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (elem : TSyntax `doElem) : CommandElabM (Array Term × Array String) := do
  match elem with
  | `(doElem| let $name:ident ← $rhs:term) =>
      let varName := toString name.getId
      if locals.contains varName then
        throwErrorAt name s!"duplicate local variable '{varName}'"
      let safeBind? ← translateSafeRequireBind params locals varName rhs
      match safeBind? with
      | some safeStmts => pure (safeStmts, locals.push varName)
      | none =>
          let rhsExpr ← translateBindSource fields params locals rhs
          pure (#[(← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $rhsExpr))], locals.push varName)
  | `(doElem| let $name:ident := $rhs:term) =>
      let varName := toString name.getId
      if locals.contains varName then
        throwErrorAt name s!"duplicate local variable '{varName}'"
      let rhsExpr ← translatePureExpr params locals rhs
      pure (#[(← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $rhsExpr))], locals.push varName)
  | `(doElem| return $value:term) =>
      pure (#[(← `(Compiler.CompilationModel.Stmt.return $(← translatePureExpr params locals value)))], locals)
  | `(doElem| pure ()) =>
      pure (#[], locals)
  | `(doElem| if $cond:term then $thenBranch:doSeq else $elseBranch:doSeq) =>
      let condExpr ← translatePureExpr params locals cond
      let thenStmts ← translateDoSeqToStmtTerms fields params locals thenBranch
      let elseStmts ← translateDoSeqToStmtTerms fields params locals elseBranch
      pure
        (#[(← `(Compiler.CompilationModel.Stmt.ite
          $condExpr
          [ $[$thenStmts],* ]
          [ $[$elseStmts],* ]))],
          locals)
  | `(doElem| $stmt:term) =>
      pure (#[(← translateEffectStmt fields params locals stmt)], locals)
  | _ => throwErrorAt elem "unsupported do element"
end

private def translateBodyToStmtTerms
    (fields : Array StorageFieldDecl)
    (fn : FunctionDecl) : CommandElabM (Array Term) := do
  match fn.body with
  | `(term| do $[$elems:doElem]*) =>
      let stmts := (← translateDoElems fields fn.params #[] elems).1
      let mut stmts := stmts
      if fn.returnTy == .unit then
        stmts := stmts.push (← `(Compiler.CompilationModel.Stmt.stop))
      pure stmts
  | _ => throwErrorAt fn.body "function body must be a do block"

private def translateConstructorBodyToStmtTerms
    (fields : Array StorageFieldDecl)
    (ctor : ConstructorDecl) : CommandElabM (Array Term) := do
  match ctor.body with
  | `(term| do $[$elems:doElem]*) =>
      pure (← (translateDoElems fields ctor.params #[] elems)).1
  | _ => throwErrorAt ctor.body "constructor body must be a do block"

def mkSuffixedIdent (base : Ident) (suffix : String) : CommandElabM Ident :=
  let rec appendSuffix : Name → Name
    | .anonymous => .str .anonymous suffix
    | .str p s => .str p (s ++ suffix)
    | .num p n => .str p (toString n ++ suffix)
  pure <| mkIdent <| appendSuffix base.getId

private def mkContractFnType (params : Array ParamDecl) (retTy : ValueType) : CommandElabM Term := do
  let mut ty ← `(Verity.Contract $(← contractValueTypeTerm retTy))
  for param in params.reverse do
    ty ← `(($(← contractValueTypeTerm param.ty)) → $ty)
  pure ty

private def mkContractFnValue (params : Array ParamDecl) (body : Term) : CommandElabM Term := do
  let mut value := body
  for param in params.reverse do
    let pid := param.ident
    value ← `(fun ($pid : $(← contractValueTypeTerm param.ty)) => $value)
  pure value

private def mkModelParamsTerm (params : Array ParamDecl) : CommandElabM Term := do
  let xs ← params.mapM fun p => do
    `(Compiler.CompilationModel.Param.mk $(strTerm p.name) $(← modelParamTypeTerm p.ty))
  `([ $[$xs],* ])

private def mkStorageDefCommand (field : StorageFieldDecl) : CommandElabM Cmd := do
  let storageTy ←
    match field.ty with
    | .scalar .uint256 => `(Uint256)
    | .scalar .address => `(Address)
    | .scalar .unit => throwError "storage field cannot be Unit"
    | .mappingAddressToUint256 => `(Address → Uint256)
    | .mapping2AddressToAddressToUint256 => `(Address → Address → Uint256)
    | .mappingUintToUint256 => `(Uint256 → Uint256)
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
    (ctor : Option ConstructorDecl)
    (functions : Array FunctionDecl) : CommandElabM Cmd := do
  let fieldTerms ← fields.mapM mkModelFieldTerm
  let constructorTerm ←
    match ctor with
    | none => `(none)
    | some ctor =>
        let ctorParams ← mkModelParamsTerm ctor.params
        let ctorBodyTerms ← translateConstructorBodyToStmtTerms fields ctor
        `(some {
          params := $ctorParams
          body := [ $[$ctorBodyTerms],* ]
        })
  let functionModelIds ← functions.mapM fun fn => mkSuffixedIdent fn.ident "_model"
  `(command| def spec : Compiler.CompilationModel.CompilationModel := {
    name := $(strTerm contractName)
    fields := [ $[$fieldTerms],* ]
    «constructor» := $constructorTerm
    functions := [ $[$functionModelIds],* ]
  })

def parseContractSyntax
    (stx : Syntax)
    : CommandElabM (Ident × Array StorageFieldDecl × Option ConstructorDecl × Array FunctionDecl) := do
  match stx with
  | `(command| verity_contract $contractName:ident where storage $[$storageFields:verityStorageField]* $[$ctor:verityConstructor]? $[$functions:verityFunction]*) =>
      pure
        ( contractName
        , (← storageFields.mapM parseStorageField)
        , (← ctor.mapM parseConstructor)
        , (← functions.mapM parseFunction)
        )
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
    (ctor : Option ConstructorDecl)
    (functions : Array FunctionDecl) : CommandElabM Cmd :=
  mkSpecCommand contractName fields ctor functions

end Verity.Macro
