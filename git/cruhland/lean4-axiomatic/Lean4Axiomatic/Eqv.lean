import Lean4Axiomatic.Operators

open Operators (TildeDash TildeDashQuestion)

namespace Relation

class Swap {α : Sort u} {β : Sort v} (rα : α → α → β) (rβ : β → β → Prop) where
  swap : {x y : α} → rβ (rα x y) (rα y x)

export Swap (swap)

instance
    {α : Sort u} {rel : α → α → Prop} [inst : Swap rel (· → ·)]
    : Swap rel (· ↔ ·)
    where
  swap := ⟨swap (self := inst), swap (self := inst)⟩

class Refl {α : Sort u} (rel : α → α → Prop) where
  refl : {x : α} → rel x x

export Refl (refl)

instance : Refl (· → ·) where
  refl := id

class Symm {α : Sort u} (rel : α → α → Prop) where
  symm : {x y : α} → rel x y → rel y x

export Symm (symm)

instance {α : Sort u} {rel : α → α → Prop} [Symm rel] : Swap rel (· → ·) where
  swap := symm

class Trans {α : Sort u} (rel : α → α → Prop) where
  trans : {x y z : α} → rel x y → rel y z → rel x z

export Trans (trans)

instance : Trans (· → ·) where
  trans := λ f g x => g (f x)

class Eqv {α : Sort u} (rel : α → α → Prop)
    extends Refl rel, Symm rel, Trans rel

/--
Provides an equivalence relation over `α` with the operator `· ≃ ·`.

**Named parameters**
- `α`: the `Sort` of the elements in the relation.
-/
class EqvOp (α : Sort u) extends TildeDash α, Eqv tildeDash

def neq.symm {α : Sort u} [EqvOp α] {x y : α} : x ≄ y → y ≄ x := by
  intro (_ : x ≄ y) (_ : y ≃ x)
  show False
  apply ‹x ≄ y›
  show x ≃ y
  exact Symm.symm ‹y ≃ x›

/--
Extends `EqvOp` with `· ≃? ·`, a decision procedure for equivalence.

**Named parameters**
- `α`: the `Sort` of the elements in the relation.
-/
class EqvOp? (α : Sort u) extends EqvOp α, TildeDashQuestion tildeDash

end Relation

instance iff_symm : Relation.Symm (· ↔ ·) where
  symm {p q : Prop} := by
    intro ⟨(_ : p → q), (_ : q → p)⟩
    show q ↔ p
    exact ⟨‹q → p›, ‹p → q›⟩

instance {α : Sort u} [Relation.EqvOp α] : Relation.Symm (α := α) (· ≄ ·) where
  symm := Relation.neq.symm

instance
    {α : Sort u} {rel : α → α → Prop} [Relation.Trans rel]
    : Trans rel rel rel where
  trans := Relation.trans

namespace Eqv

export Relation (refl swap symm trans)

end Eqv
