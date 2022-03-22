/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic
import Mathport.Syntax.Translate.Tactic.Lean3

open Lean

namespace Mathport.Translate.Tactic
open Parser

-- # tactic.finish

def trUsingList (args : Array (Spanned AST3.Expr)) : M Syntax :=
  @mkNullNode <$> match args with
  | #[] => pure #[]
  | args => return #[mkAtom "using", (mkAtom ",").mkSep $ ← args.mapM trExpr]

@[trTactic clarify] def trClarify : TacM Syntax := do
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let ps := (← (← parse (tk "using" *> pExprListOrTExpr)?).getD #[] |>.mapM (trExpr ·)).asNonempty
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| clarify $[(config := $cfg)]? $[[$hs,*]]? $[using $ps,*]?)

@[trTactic safe] def trSafe : TacM Syntax := do
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let ps := (← (← parse (tk "using" *> pExprListOrTExpr)?).getD #[] |>.mapM (trExpr ·)).asNonempty
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| safe $[(config := $cfg)]? $[[$hs,*]]? $[using $ps,*]?)

@[trTactic finish] def trFinish : TacM Syntax := do
  let hs := (← trSimpArgs (← parse simpArgList)).asNonempty
  let ps := (← (← parse (tk "using" *> pExprListOrTExpr)?).getD #[] |>.mapM (trExpr ·)).asNonempty
  let cfg ← liftM $ (← expr?).mapM trExpr
  `(tactic| finish $[(config := $cfg)]? $[[$hs,*]]? $[using $ps,*]?)
