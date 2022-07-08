/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Binder
import Lean.Parser.Command

namespace Lake.DSL
open Lean Parser Command

abbrev DocComment := TSyntax ``docComment
abbrev Attributes := TSyntax ``Term.attributes
abbrev AttrInstance := TSyntax ``Term.attrInstance
abbrev WhereDecls := TSyntax ``Term.whereDecls

---

def expandAttrs (attrs? : Option Attributes) : Array AttrInstance :=
  if let some attrs := attrs? then
    match attrs with
    | `(Term.attributes| @[$attrs,*]) => attrs
    | _ => #[]
  else
    #[]

syntax structVal :=
  "{" manyIndent(group(Term.structInstField ", "?)) "}"

syntax declValDo :=
  ppSpace Term.do (Term.whereDecls)?

syntax declValStruct :=
  ppSpace structVal (Term.whereDecls)?

syntax declValTyped :=
  Term.typeSpec declValSimple

syntax declValOptTyped :=
  (Term.typeSpec)? declValSimple

syntax simpleDeclSig :=
  ident Term.typeSpec declValSimple

syntax structDeclSig :=
  ident (Command.whereStructInst <|> declValOptTyped <|> declValStruct)?

def fixName (id : Ident) : Option Name → Ident
| some n => mkIdentFrom id n
| none => id

def mkConfigStructDecl (name? : Option Name)
(doc? : Option DocComment) (attrs : Array AttrInstance) (ty : Term)
: (spec : Syntax) → MacroM Syntax
| `(structDeclSig| $id:ident) =>
  `($[$doc?]? @[$attrs,*] def $(fixName id name?) : $ty :=
    {name := $(quote id.getId)})
| `(structDeclSig| $id:ident where $ds;* $[$wds?]?) =>
  `($[$doc?]? @[$attrs,*] def $(fixName id name?) : $ty where
      name := $(quote id.getId); $ds;* $[$wds?]?)
| `(structDeclSig| $id:ident $[: $ty?]? := $defn $[$wds?]?) =>
  `($[$doc?]? @[$attrs,*] def $(fixName id name?) : $(ty?.getD ty) := $defn $[$wds?]?)
| `(structDeclSig| $id:ident { $[$fs $[,]?]* } $[$wds?]?) => do
  let defn ← `({ name := $(quote id.getId), $fs,* })
  `($[$doc?]? @[$attrs,*] def $(fixName id name?) : $ty := $defn $[$wds?]?)
| stx => Macro.throwErrorAt stx "ill-formed configuration syntax"
