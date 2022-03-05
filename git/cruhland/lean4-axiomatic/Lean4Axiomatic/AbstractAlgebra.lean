import Lean4Axiomatic.Eqv

open Relation (EqvOp Refl Swap Symm Trans)

namespace AA

inductive Hand where
| L | R

def forHand {α : Sort u} {β : Sort v} : Hand → (α → α → β) → (α → α → β)
| Hand.L => id
| Hand.R => flip

class Commutative {α : Sort u} {β : Sort v} [EqvOp β] (f : α → α → β) where
  comm {x y : α} : f x y ≃ f y x

export Commutative (comm)

/--
Class for types and operations that satisfy the associative property.

For more information see `Associative.assoc` or
[consult Wikipedia](https://en.wikipedia.org/wiki/Associative_property).

**Named parameters**
- `α`: the type that the binary operation `f` is defined over.
- `f`: the binary operation that obeys the associative property.

**Class parameters**
- `EqvOp α`: necessary because the property expresses an equality on `α`.
-/
class Associative {α : Sort u} [EqvOp α] (f : α → α → α) where
  /--
  The associative property of a binary operation `f` defined over a type `α`.

  Some well-known examples from arithmetic are that addition and multiplication
  are associative; we have `(a + b) + c ≃ a + (b + c)` and
  `(a * b) * c ≃ a * (b * c)` for all natural numbers `a`, `b`, and `c`.

  **Named parameters**
  - see `Associative` for the class parameters.
  - `x`: the first operand (when reading from left to right).
  - `y`: the second operand.
  - `z`: the third operand.
  -/
  assoc {x y z : α} : f (f x y) z ≃ f x (f y z)

export Associative (assoc)

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

/--
Class for types and operations that satisfy either the left- or right-handed
distributive property.

For more information see `DistributiveOn.distrib` or
[consult Wikipedia](https://en.wikipedia.org/wiki/Distributive_property).

**Named parameters**
- `hand`: indicates whether the property is left- or right-handed.
- `α`: the type that the binary operations `f` and `g` are defined over.
- `f`: the binary operation that distributes over `g`.
- `g`: the binary operation that `f` distributes over.

**Class parameters**
- `EqvOp α`: necessary because the property expresses an equality on `α`.
-/
class DistributiveOn
    (hand : Hand) {α : Sort u} [EqvOp α] (f g : α → α → α) where
  /--
  The left- or right-handed distributive property of two binary operations `f`
  and `g` defined over a type `α`.

  If this property is satisfied, one says that `f` _distributes_ over `g`. A
  well-known example from arithmetic is that multiplication distributes over
  addition; `a * (b + c) ≃ a * b + a * c` for the left-handed case and
  `(b + c) * a ≃ b * a + c * a` for the right-handed case.

  **Named parameters**
  - see `DistributiveOn` for the class parameters.
  - `x`: the argument to `f` that gets distributed; the `hand` parameter
    indicates which side of `f` it is on.
  - `y`: the left argument to `g`.
  - `z`: the right argument to `g`.
  -/
  distrib {x y z : α} :
    let f' := forHand hand f
    f' x (g y z) ≃ g (f' x y) (f' x z)

export DistributiveOn (distrib)

/--
Convenience function for the left-handed distributive property.

Can often resolve cases where type inference gets stuck when using the more
general `distrib` function.

See `DistributiveOn.distrib` for detailed documentation.
-/
abbrev distribL := @distrib Hand.L

/--
Convenience function for the right-handed distributive property.

Can often resolve cases where type inference gets stuck when using the more
general `distrib` function.

See `DistributiveOn.distrib` for detailed documentation.
-/
abbrev distribR := @distrib Hand.R

/--
Convenience class for types and operations that satisfy the full (left- **and**
right-handed) distributive property.

See `DistributiveOn` for detailed documentation.
-/
class Distributive {α : Sort u} [EqvOp α] (f g : α → α → α) where
  distributiveL : DistributiveOn Hand.L f g
  distributiveR : DistributiveOn Hand.R f g

attribute [instance] Distributive.distributiveL
attribute [instance] Distributive.distributiveR

/--
Derive right-distributivity from left-distributivity for operations `f` and `g`
meeting certain conditions.
-/
def distributiveR_from_distributiveL
    {α : Sort u} {f g : α → α → α}
    [EqvOp α] [Commutative f] [Substitutive₂ g (· ≃ ·) (· ≃ ·)]
    : DistributiveOn Hand.L f g → DistributiveOn Hand.R f g := by
  intro
  constructor
  intro x y z f'
  show f (g y z) x ≃ g (f y x) (f z x)
  calc
    f (g y z) x       ≃ _ := AA.comm
    f x (g y z)       ≃ _ := AA.distribL
    g (f x y) (f x z) ≃ _ := AA.substL AA.comm
    g (f y x) (f x z) ≃ _ := AA.substR AA.comm
    g (f y x) (f z x) ≃ _ := Eqv.refl

inductive OneOfThree (α β γ : Prop) : Prop where
| first  (a : α)
| second (b : β)
| third  (c : γ)

inductive TwoOfThree (α β γ : Prop) : Prop where
| oneAndTwo   (a : α) (b : β)
| oneAndThree (a : α) (c : γ)
| twoAndThree (b : β) (c : γ)

structure ExactlyOneOfThree (α β γ : Prop) : Prop where
  atLeastOne :   OneOfThree α β γ
  atMostOne  : ¬ TwoOfThree α β γ

end AA
