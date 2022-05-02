/-
Copyright (c) 2020 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Qpf.MvFunctor
import Qpf.Qpf.Multivariate.Basic

/-!
# Constant functors are QPFs

Constant functors map every type vectors to the same target type. This
is a useful device for constructing data types from more basic types
that are not actually functorial. For instance `const n nat` makes
`nat` into a functor that can be used in a functor-based data type
specification.
-/


universe u

namespace MvQpf

-- open_locale MvFunctor

variable (n : ℕ)

/-- Constant multivariate functor -/
@[nolint unused_arguments]
def Const (A : Type _) (v : TypeVec.{u} n) : Type _ :=
  A

instance Const.inhabited {A α} [Inhabited A] : Inhabited (Const n A α) :=
  ⟨(default : A)⟩

namespace Const

open MvFunctor MvPFunctor

variable {n} {A : Type u} {α β : TypeVec.{u} n} (f : α ⟹ β)

/-- Constructor for constant functor -/
protected def mk (x : A) : (Const n A) α :=
  x

/-- Destructor for constant functor -/
protected def get (x : (Const n A) α) : A :=
  x

@[simp]
protected theorem mk_get (x : (Const n A) α) : Const.mk (Const.get x) = x :=
  rfl

@[simp]
protected theorem get_mk (x : A) : Const.get (Const.mk x : Const n A α) = x :=
  rfl

/-- `map` for constant functor -/
protected def map : (Const n A) α → (Const n A) β := fun x => x

instance instMvFunctor : MvFunctor (Const n A) where
  map := @fun α β f => Const.map

theorem map_mk (x : A) : f <$$> Const.mk x = Const.mk x :=
  rfl

theorem get_map (x : (Const n A) α) : Const.get (f <$$> x) = Const.get x :=
  rfl

instance mvqpf : @MvQpf _ (Const n A) MvQpf.Const.instMvFunctor where
  P := MvPFunctor.Const n A
  abs := @fun α x => MvPFunctor.Const.get x
  repr := @fun α x => MvPFunctor.Const.mk n x
  abs_repr := by
    intros <;> simp
  abs_map := by
    intros <;> simp <;> rfl

end Const

end MvQpf

