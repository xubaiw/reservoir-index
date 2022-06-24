/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean

namespace Mathport.Translate.Tactic
open AST3 Mathport.Translate.Parser

-- # tactic.suggest

@[trTactic suggest] def trSuggest : TacM Syntax := do
  let n := (← parse (smallNat)?).map Quote.quote
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent |>.asNonempty
  let use := (← parse (tk "using" *> ident_*)?).getD #[] |>.map trBinderIdent |>.asNonempty
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| suggest $[(config := $cfg)]? $(n)? $[[$hs,*]]? $[with $attrs*]? $[using $use*]?)

@[trTactic library_search] def trLibrarySearch : TacM Syntax := do
  let bang ← parse (tk "!")?
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let attrs := (← parse (tk "with" *> ident*)?).getD #[] |>.map mkIdent |>.asNonempty
  let use := (← parse (tk "using" *> ident_*)?).getD #[] |>.map trBinderIdent |>.asNonempty
  let cfg ← liftM $ (← expr?).mapM trExpr
  match bang with
  | none => `(tactic| library_search
    $[(config := $cfg)]? $[[$hs,*]]? $[with $attrs*]? $[using $use*]?)
  | some _ => `(tactic| library_search!
    $[(config := $cfg)]? $[[$hs,*]]? $[with $attrs*]? $[using $use*]?)
