import Mathlib.Tactic.LibrarySearch

inductive Untyped
| utrue
| ufalse
| uzero
| usucc : Untyped → Untyped
| uite : Untyped → Untyped → Untyped → Untyped
| upred : Untyped → Untyped
| uiszero : Untyped → Untyped

open Untyped

def consts : Untyped → List Untyped
| utrue => [utrue]
| ufalse => [ufalse]
| uzero => [uzero]
| usucc n => consts n
| uite c t e => (consts c).append ((consts t).append (consts e))
| upred p => consts p
| uiszero v => consts v

def size : Untyped → Nat
| utrue => 1
| ufalse => 1
| uzero => 1
| usucc n => 1 + size n
| uite c t e => 1 + size c + size t + size e
| upred p => 1 + size p
| uiszero v => 1 + size v

def depth : Untyped → Nat
| utrue => 1
| ufalse => 1
| uzero => 1
| usucc n => 1 + depth n
| uite c t e => 1 + max (depth c) (max (depth t) (depth e))
| upred p => 1 + depth p
| uiszero v => 1 + depth v


theorem consts_finite :
  ∀u, ∃n, (consts u).length = n
  := by
    intro u
    induction u with
    | utrue => exists 1
    | ufalse => exists 1
    | uzero => exists 1
    | usucc n a_ih => exists (consts n).length
    | uite a b c a_ih b_ih c_ih => 
          cases a_ih
          cases b_ih
          cases c_ih
          simp [consts]
          exists (consts a).length + ((consts b).length + (consts c).length)
    | upred n a_ih => exists (consts n).length
    | uiszero n a_ih => exists (consts n).length

    