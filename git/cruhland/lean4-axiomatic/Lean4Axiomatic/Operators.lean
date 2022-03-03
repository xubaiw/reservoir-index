namespace Operators

class TildeDash (α : Sort u) (β : Sort v) where
  tildeDash : α → α → β

infix:50 " ≃ " => TildeDash.tildeDash

def tildeDashNot {α : Sort u} [TildeDash α Prop] (x y : α) : Prop :=
  ¬ (x ≃ y)

infix:50 " ≄ " => tildeDashNot

class TildeDashQuestion (α : Sort u) (β : outParam (α → α → Sort v)) where
  tildeDashQuestion : (x y : α) → β x y

infix:50 " ≃? " => TildeDashQuestion.tildeDashQuestion

def ltNot {α : Type u} [LT α] (x y : α) : Prop := ¬ (x < y)

infix:50 " ≮ " => ltNot

end Operators
