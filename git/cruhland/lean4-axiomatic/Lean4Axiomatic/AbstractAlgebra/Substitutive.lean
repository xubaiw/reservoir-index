import Lean4Axiomatic.AbstractAlgebra.Commutative
import Lean4Axiomatic.AbstractAlgebra.Core
import Lean4Axiomatic.Eqv

open Relation (EqvOp Swap Trans)

namespace AA

class Substitutive
    {α : Sort u} {β : Sort v}
    (f : α → β) (rα : outParam (α → α → Prop)) (rβ : β → β → Prop) where
  subst {x₁ x₂ : α} : rα x₁ x₂ → rβ (f x₁) (f x₂)

export Substitutive (subst)

class Injective
    {α : Sort u} {β : Sort v} (f : α → β)
    (rα : outParam (α → α → Prop)) (rβ : β → β → Prop) where
  inject {x₁ x₂ : α} : rβ (f x₁) (f x₂) → rα x₁ x₂

export Injective (inject)

class SubstitutiveForHand
    (hand : Hand) {α : Sort u} {β : Sort v} (f : α → α → β)
    (rα : outParam (α → α → Prop)) (rβ : β → β → Prop) where
  subst₂
    {x₁ x₂ y : α} : rα x₁ x₂ → rβ (forHand hand f x₁ y) (forHand hand f x₂ y)

export SubstitutiveForHand (subst₂)

abbrev substL := @subst₂ Hand.L
abbrev substR := @subst₂ Hand.R

class Substitutive₂
    {α : Sort u} {β : Sort v}
    (f : α → α → β) (rα : α → α → Prop) (rβ : β → β → Prop)
    where
  substitutiveL : SubstitutiveForHand Hand.L f rα rβ
  substitutiveR : SubstitutiveForHand Hand.R f rα rβ

attribute [instance] Substitutive₂.substitutiveL
attribute [instance] Substitutive₂.substitutiveR

instance
    {α : Type u} {β : Type v} {f : α → α → β} {rel : β → β → Prop}
    [EqvOp β] [Commutative f] [Relation.Refl rel]
    [SubstitutiveForHand Hand.R rel (· ≃ ·) (· → ·)]
    : Swap f rel where
  swap := by
    intro x y
    show rel (f x y) (f y x)
    have : rel (f x y) (f x y) := Eqv.refl
    exact substR (rβ := (· → ·)) comm ‹rel (f x y) (f x y)›

def substR_from_substL_swap
    {α : Sort u} {β : Sort v} {f : α → α → β}
    {rα : α → α → Prop} {rβ : β → β → Prop}
    [Trans rβ] [Swap f rβ]
    : SubstitutiveForHand Hand.L f rα rβ →
    SubstitutiveForHand Hand.R f rα rβ := by
  intro
  constructor
  intro x₁ x₂ y (_ : rα x₁ x₂)
  show rβ (f y x₁) (f y x₂)
  calc
    rβ (f y x₁) (f x₁ y) := Swap.swap
    rβ (f x₁ y) (f x₂ y) := AA.substL ‹rα x₁ x₂›
    rβ (f x₂ y) (f y x₂) := Swap.swap

instance eqv_substL {α : Sort u} [EqvOp α]
    : SubstitutiveForHand Hand.L (α := α) (· ≃ ·) (· ≃ ·) (· → ·) := by
  constructor
  intro x₁ x₂ y (_ : x₁ ≃ x₂) (_ : x₁ ≃ y)
  show x₂ ≃ y
  exact Eqv.trans (Eqv.symm ‹x₁ ≃ x₂›) ‹x₁ ≃ y›

instance eqv_substR {α : Sort u} [EqvOp α]
    : SubstitutiveForHand Hand.R (α := α) (· ≃ ·) (· ≃ ·) (· → ·) :=
  substR_from_substL_swap eqv_substL

instance eqv_substitutive {α : Sort u} [EqvOp α]
    : Substitutive₂ (α := α) (· ≃ ·) (· ≃ ·) (· → ·) where
  substitutiveL := eqv_substL
  substitutiveR := eqv_substR

instance neq_substL
    {α : Sort u} [EqvOp α]
    : SubstitutiveForHand Hand.L (α := α) (· ≄ ·) (· ≃ ·) (· → ·) := by
  constructor
  intro x₁ x₂ y (_ : x₁ ≃ x₂) (_ : x₁ ≄ y) (_ : x₂ ≃ y)
  show False
  apply ‹x₁ ≄ y›
  show x₁ ≃ y
  exact Eqv.trans ‹x₁ ≃ x₂› ‹x₂ ≃ y›

instance neq_substitutive
    {α : Sort u} [EqvOp α] : Substitutive₂ (α := α) (· ≄ ·) (· ≃ ·) (· → ·)
    where
  substitutiveL := neq_substL
  substitutiveR := substR_from_substL_swap neq_substL

class Cancellative
    (hand : Hand) {α : Sort u} {β : Sort v}
    (f : α → α → β) (rα : outParam (α → α → Prop)) (rβ : β → β → Prop) where
  cancel
    {x y₁ y₂ : α} : rβ (forHand hand f x y₁) (forHand hand f x y₂) → rα y₁ y₂

export Cancellative (cancel)

abbrev cancelL := @cancel Hand.L
abbrev cancelR := @cancel Hand.R

class Cancellative₂
    {α : Sort u} {β : Sort v}
    (f : α → α → β) (rα : outParam (α → α → Prop)) (rβ : β → β → Prop) where
  cancellativeL : Cancellative Hand.L f rα rβ
  cancellativeR : Cancellative Hand.R f rα rβ

def cancelR_from_cancelL
    {α : Sort u} {β : Sort v}
    {f : α → α → β} {rα : α → α → Prop} {rβ : β → β → Prop}
    [EqvOp β] [Commutative f] [Substitutive₂ rβ (· ≃ ·) (· → ·)]
    : Cancellative Hand.L f rα rβ → Cancellative Hand.R f rα rβ := by
  intro
  constructor
  intro x y₁ y₂ (hyp : rβ (f y₁ x) (f y₂ x))
  show rα y₁ y₂
  have : rβ (f x y₁) (f y₂ x) := AA.substL (rβ := (· → ·)) AA.comm hyp
  have : rβ (f x y₁) (f x y₂) := AA.substR (rβ := (· → ·)) AA.comm this
  exact AA.cancelL this

end AA
