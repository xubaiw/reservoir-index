import Lean4Axiomatic.Operators

open Operators (TildeDash TildeDashQuestion)

namespace Relation

class Swap {α : Sort u} {β : Sort v} (rα : α → α → β) (rβ : β → β → Prop) where
  swap : {x y : α} → rβ (rα x y) (rα y x)

class Refl {α : Sort u} (rel : α → α → Prop) where
  refl : {x : α} → rel x x

instance : Refl (· → ·) where
  refl := id

class Symm {α : Sort u} (rel : α → α → Prop) where
  symm : {x y : α} → rel x y → rel y x

instance {α : Sort u} {rel : α → α → Prop} [Symm rel] : Swap rel (· → ·) where
  swap := Symm.symm

class Trans {α : Sort u} (rel : α → α → Prop) where
  trans : {x y z : α} → rel x y → rel y z → rel x z

instance : Trans (· → ·) where
  trans := λ f g x => g (f x)

class Eqv {α : Sort u} (rel : α → α → Prop)
    extends Refl rel, Symm rel, Trans rel

class EqvOp (α : Sort u) extends TildeDash α Prop, Eqv tildeDash

def neq.symm {α : Sort u} [EqvOp α] {x y : α} : x ≄ y → y ≄ x := by
  intro (_ : x ≄ y) (_ : y ≃ x)
  show False
  apply ‹x ≄ y›
  show x ≃ y
  exact Symm.symm ‹y ≃ x›

class EqvOp? (α : Sort u)
    extends EqvOp α, TildeDashQuestion α (λ x y => Decidable (x ≃ y))

end Relation

instance {α : Sort u} [Relation.EqvOp α] : Relation.Symm (α := α) (· ≄ ·) where
  symm := Relation.neq.symm

instance
    {α : Sort u} {rel : α → α → Prop} [Relation.Trans rel]
    : Trans rel rel rel where
  trans := Relation.Trans.trans

namespace Eqv

export Relation.Swap (swap)
export Relation.Refl (refl)
export Relation.Symm (symm)
export Relation.Trans (trans)

end Eqv
