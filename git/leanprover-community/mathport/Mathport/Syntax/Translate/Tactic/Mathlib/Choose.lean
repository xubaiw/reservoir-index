/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathport.Syntax.Translate.Tactic.Basic

open Lean
open Lean.Elab.Tactic (Location)

namespace Mathport.Translate.Tactic
open AST3 Parser

-- # tactic.choose

@[trTactic choose] def trChoose : TacM Syntax := do
  let nondep ← parse (tk "!")?
  let ns := (#[← parse ident] ++ (← parse ident*)).map mkIdent
  let tgt ← liftM $ (← parse (tk "using" *> pExpr)?).mapM trExpr
  match nondep with
  | none => `(tactic| choose $ns* $[using $tgt]?)
  | some _ => `(tactic| choose! $ns* $[using $tgt]?)

