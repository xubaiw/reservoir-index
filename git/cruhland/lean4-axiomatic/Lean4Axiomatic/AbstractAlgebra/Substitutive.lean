import Lean4Axiomatic.AbstractAlgebra.Commutative
import Lean4Axiomatic.AbstractAlgebra.Core
import Lean4Axiomatic.Eqv

namespace AA

open Relation (EqvOp Swap Trans)

/-!
# (Generalized) substitution and related properties

Generalized substitution allows the equalities of the ordinary substitution
property to be replaced by arbitrary binary relations.
-/

/--
Class for types and operations that satisfy the unary generalized substitution
property.

For more information see `Substitutive₁.subst₁`.

**Named parameters**
- `α`: the argument type of the unary operation `f`.
- `β`: the result type of the unary operation `f`.
- `f`: the unary operation that obeys the generalized substitution property.
- `rα`: a binary relation over `f`'s argument type `α`.
- `rβ`: a binary relation over `f`'s result type `β`.
-/
class Substitutive₁
    {α : Sort u} {β : Sort v}
    (f : α → β) (rα : outParam (α → α → Prop)) (rβ : β → β → Prop) where
  /--
  The generalized substitution property of an unary operation `f`.

  An `f` that satisfies this property must map values of type `α` that are
  related by `rα` to values of type `β` that are related by `rβ`.

  Often `α` and `β` will be the same type, and `rα` and `rβ` will be the same
  relation. The canonical example is the ordinary
  [substitution property of equality](https://w.wiki/4vEu): if we have `x = y`
  for any values `x` and `y`, then we know `f x = f y`.

  **Named parameters**
  - see `Substitutive₁` for the class parameters.
  - `x₁` and `x₂`: the arguments to `f`, related by `rα`.
  -/
  subst₁ {x₁ x₂ : α} : rα x₁ x₂ → rβ (f x₁) (f x₂)

export Substitutive₁ (subst₁)

/--
Class for types and operations that satisfy the unary generalized injective
property.

For more information see `Injective.inject`.

**Named parameters**
- `α`: the argument type of the unary operation `f`.
- `β`: the result type of the unary operation `f`.
- `f`: the unary operation that obeys the generalized injective property.
- `rα`: a binary relation over `f`'s argument type `α`.
- `rβ`: a binary relation over `f`'s result type `β`.
-/
class Injective
    {α : Sort u} {β : Sort v} (f : α → β)
    (rα : outParam (α → α → Prop)) (rβ : β → β → Prop) where
  /--
  The generalized injective property of an unary operation `f`.

  Operations `f` that have this property can be traced backward in some sense.
  It is the converse of the substitution property. In other words, if we know
  that the results of two operations, `f x₁` and `f x₂`, are related by `rβ`,
  then we can conclude that the inputs `x₁` and `x₂` are related by `rα`.

  Often `α` and `β` will be the same type, and `rα` and `rβ` will be the same
  relation. The canonical example is the ordinary
  [injective property of functions](https://w.wiki/4vTb): if we have
  `f x = f y` for any values `x` and `y`, then we know `x = y`.

  **Named parameters**
  - see `Injective` for the class parameters.
  - `x₁` and `x₂`: the arguments to `f`.
  -/
  inject {x₁ x₂ : α} : rβ (f x₁) (f x₂) → rα x₁ x₂

export Injective (inject)

/--
Class for types and operations that satisfy either the left- or right-handed
binary generalized substitution property.

For more information see `SubstitutiveOn.subst₂`.

**Named parameters**
- `hand`: indicates whether the property is left- or right-handed.
- `α`: the argument type of the binary operation `f`.
- `β`: the result type of the binary operation `f`.
- `f`: the binary operation that obeys the generalized substitution property.
- `rα`: a binary relation over `f`'s argument type `α`.
- `rβ`: a binary relation over `f`'s result type `β`.
-/
class SubstitutiveOn
    (hand : Hand) {α : Sort u} {β : Sort v}
    (f : α → α → β) (rα : outParam (α → α → Prop)) (rβ : β → β → Prop)
    where
  /--
  The left- or right-handed generalized substitution property of a binary
  operation `f`.

  An `f` that satisfies this property must map values of type `α` that are
  related by `rα` -- given as arguments in the position specified by `hand` --
  to values of type `β` that are related by `rβ`.

  Often `α` and `β` will be the same type, and `rα` and `rβ` will be the same
  relation. A simple example is of addition on natural numbers: if we know
  `n₁ ≃ n₂`, then we can conclude that `n₁ + m ≃ n₂ + m`, or that
  `m + n₁ ≃ m + n₂`.

  **Named parameters**
  - see `SubstitutiveOn` for the class parameters.
  - `x₁` and `x₂`: the arguments to `f`, related by `rα`; the `hand` parameter
    indicates which side of `f` they are given on.
  - `y`: the other argument to `f`; goes on the side opposite `hand`.
  -/
  subst₂
    {x₁ x₂ y : α} : rα x₁ x₂ → rβ (forHand hand f x₁ y) (forHand hand f x₂ y)

export SubstitutiveOn (subst₂)

/--
Convenience function for the left-handed binary generalized substitution
property.

Can often resolve cases where type inference gets stuck when using the more
general `subst₂` function.

See `SubstitutiveOn.subst₂` for detailed documentation.
-/
abbrev substL := @subst₂ Hand.L

/--
Convenience function for the right-handed binary generalized substitution
property.

Can often resolve cases where type inference gets stuck when using the more
general `subst₂` function.

See `SubstitutiveOn.subst₂` for detailed documentation.
-/
abbrev substR := @subst₂ Hand.R

/--
Convenience class for types and operations that satisfy the full (left- **and**
right-handed) binary generalized substitution property.

See `SubstitutiveOn` for detailed documentation.
-/
class Substitutive₂
    {α : Sort u} {β : Sort v}
    (f : α → α → β) (rα : α → α → Prop) (rβ : β → β → Prop)
    where
  substitutiveL : SubstitutiveOn Hand.L f rα rβ
  substitutiveR : SubstitutiveOn Hand.R f rα rβ

attribute [instance] Substitutive₂.substitutiveL
attribute [instance] Substitutive₂.substitutiveR

/--
Convenience definition that converts instances of `Commutative` into instances
of `Swap`.

The `Swap` class is a generalization of the commutative and symmetric
properties, and is used in very abstract, general definitions. This instance
makes it easy for those definitions to apply to commutative functions.

**Named parameters**
- `α`: the argument type of the commutative function `f`.
- `β`: the result type of the commutative function `f`.
- `f`: the commutative function to produce a `Swap` instance for.
- `rel`: the binary relation that connects the two sides of the `Swap`.

**Class parameters**
- `EqvOp β`: required by `Commutative f`.
- `Commutative f`: the property to translate into a `Swap` instance.
- `Relation.Refl rel`: necessary to provide a starting point for substitution.
- `SubstitutitveOn Hand.R rel (· ≃ ·) (· → ·)`: necessary for transfering
  commutativity from `EqvOp β` to `rel`.
-/
instance
    {α : Type u} {β : Type v} {f : α → α → β} {rel : β → β → Prop}
    [EqvOp β] [Commutative f] [Relation.Refl rel]
    [SubstitutiveOn Hand.R rel (· ≃ ·) (· → ·)]
    : Swap f rel where
  swap := by
    intro x y
    show rel (f x y) (f y x)
    have : rel (f x y) (f x y) := Eqv.refl
    exact substR (rβ := (· → ·)) comm ‹rel (f x y) (f x y)›

/--
Derives the right-handed binary generalized substitution property from its
left-handed counterpart, provided that the relation `rβ` satisfies a few
properties.

**Intuition**: if `rβ` permits exchanging the arguments to `f`, then we can
switch them, apply left-handed substitution, and switch back.

**Named parameters**
- `α`: the argument type of the binary operation `f`.
- `β`: the result type of the binary operation `f`.
- `f`: the binary operation that obeys the generalized substitution property.
- `rα`: a binary relation over `f`'s argument type `α`.
- `rβ`: a binary relation over `f`'s result type `β`.

**Class parameters**
- `Trans rβ`: needed to join the steps of the proof together.
- `Swap f rβ`: needed to temporarily move the right argument of `f` to the left
  position, so that left-handed substitution can be applied to it.
-/
def substR_from_substL_swap
    {α : Sort u} {β : Sort v}
    {f : α → α → β} {rα : α → α → Prop} {rβ : β → β → Prop}
    [Trans rβ] [Swap f rβ]
    : SubstitutiveOn Hand.L f rα rβ → SubstitutiveOn Hand.R f rα rβ := by
  intro
  constructor
  intro x₁ x₂ y (_ : rα x₁ x₂)
  show rβ (f y x₁) (f y x₂)
  calc
    rβ (f y x₁) (f x₁ y) := Swap.swap
    rβ (f x₁ y) (f x₂ y) := AA.substL ‹rα x₁ x₂›
    rβ (f x₂ y) (f y x₂) := Swap.swap

/--
The left-hand side of an equivalence can be replaced by an equivalent value.

**Intuition**: this is a somewhat trivial case of binary substitution,
essentially just transivity expressed in a slightly different way.

**Named parameters**
- `α`: the type of values involved in the equivalence.

**Class parameters**
- `EqvOp α`: needed for equivalence to be expressed between terms of type `α`.
-/
def eqv_substL
    {α : Sort u} [EqvOp α]
    : SubstitutiveOn Hand.L (α := α) (· ≃ ·) (· ≃ ·) (· → ·) := by
  constructor
  intro x₁ x₂ y (_ : x₁ ≃ x₂) (_ : x₁ ≃ y)
  show x₂ ≃ y
  exact Eqv.trans (Eqv.symm ‹x₁ ≃ x₂›) ‹x₁ ≃ y›

/--
Equivalence respects the binary generalized substitution property.

**Intuition**: see `eqv_substL` for the left-handed property. The right-handed
property follows from the symmetry of equivalence.

**Named parameters**
- `α`: the type of values involved in the equivalence.

**Class parameters**
- `EqvOp α`: needed for equivalence to be expressed between terms of type `α`.
-/
instance eqv_substitutive {α : Sort u} [EqvOp α]
    : Substitutive₂ (α := α) (· ≃ ·) (· ≃ ·) (· → ·) where
  substitutiveL := eqv_substL
  substitutiveR := substR_from_substL_swap eqv_substL

/--
The left-hand side of a negated equivalence can be replaced by an equivalent
value.

**Intuition**: if we know two terms are unequal, and replace the left-hand one
with an equivalent term, the right-hand term should still be unequal to the new
term.

**Named parameters**
- `α`: the type of values involved in the (negated) equivalence.

**Class parameters**
- `EqvOp α`: needed for (in)equivalence to be expressed between terms of type
  `α`.
-/
def neq_substL
    {α : Sort u} [EqvOp α]
    : SubstitutiveOn Hand.L (α := α) (· ≄ ·) (· ≃ ·) (· → ·) := by
  constructor
  intro x₁ x₂ y (_ : x₁ ≃ x₂) (_ : x₁ ≄ y) (_ : x₂ ≃ y)
  show False
  apply ‹x₁ ≄ y›
  show x₁ ≃ y
  exact Eqv.trans ‹x₁ ≃ x₂› ‹x₂ ≃ y›

/--
Negated equivalence respects the binary generalized substitution property.

**Intuition**: see `neq_substL` for the left-handed property. The right-handed
property follows from the symmetry of negated equivalence.

**Named parameters**
- `α`: the type of values involved in the (negated) equivalence.

**Class parameters**
- `EqvOp α`: needed for (in)equivalence to be expressed between terms of type
  `α`.
-/
instance neq_substitutive
    {α : Sort u} [EqvOp α] : Substitutive₂ (α := α) (· ≄ ·) (· ≃ ·) (· → ·)
    where
  substitutiveL := neq_substL
  substitutiveR := substR_from_substL_swap neq_substL

/--
Class for types and operations that satisfy either the left- or right-handed
generalized cancellation property.

For more information see `CancellativeOn.cancel`.

**Named parameters**
- `hand`: indicates whether the property is left- or right-handed.
- `α`: the argument type of the binary operation `f`.
- `β`: the result type of the binary operation `f`.
- `f`: the binary operation that obeys the generalized cancellation property.
- `rα`: a binary relation over `f`'s argument type `α`.
- `rβ`: a binary relation over `f`'s result type `β`.
-/
class CancellativeOn
    (hand : Hand) {α : Sort u} {β : Sort v}
    (f : α → α → β) (rα : outParam (α → α → Prop)) (rβ : β → β → Prop) where
  /--
  The left- or right-handed generalized cancellation property of a binary
  operation `f`.

  This property is in some sense the converse of the generalized substitution
  property; see `SubstitutiveOn.subst₂`. It says: knowing that the results of
  two invocations of `f` satisfy the relation `rβ` tells us that the two left-
  or right-handed arguments to `f` satisfy the relation `rα`.

  Often `α` and `β` will be the same type, and `rα` and `rβ` will be the same
  relation. A simple example is of addition on natural numbers: if we know that
  `n₁ + m ≃ n₂ + m`, or that `m + n₁ ≃ m + n₂`, then we can conclude that
  `n₁ ≃ n₂`.

  **Named parameters**
  - see `CancellativeOn` for the class parameters.
  - `x`: the "cancelled" argument to `f`; the `hand` parameter
    indicates which side of `f` it appears on.
  - `y₁` and `y₂`: the other arguments to `f`; appearing on the side opposite
    `hand`. They are related by `rα` in the result.
  -/
  cancel
    {x y₁ y₂ : α} : rβ (forHand hand f x y₁) (forHand hand f x y₂) → rα y₁ y₂

export CancellativeOn (cancel)

/--
Convenience function for the left-handed generalized cancellation property.

Can often resolve cases where type inference gets stuck when using the more
general `cancel` function.

See `CancellativeOn.cancel` for detailed documentation.
-/
abbrev cancelL := @cancel Hand.L

/--
Convenience function for the right-handed generalized cancellation property.

Can often resolve cases where type inference gets stuck when using the more
general `cancel` function.

See `CancellativeOn.cancel` for detailed documentation.
-/
abbrev cancelR := @cancel Hand.R

/--
Convenience class for types and operations that satisfy the full (left- **and**
right-handed) generalized cancellation property.

See `CancellativeOn` for detailed documentation.
-/
class Cancellative
    {α : Sort u} {β : Sort v}
    (f : α → α → β) (rα : outParam (α → α → Prop)) (rβ : β → β → Prop) where
  cancellativeL : CancellativeOn Hand.L f rα rβ
  cancellativeR : CancellativeOn Hand.R f rα rβ

attribute [instance] Cancellative.cancellativeL
attribute [instance] Cancellative.cancellativeR

/--
Derives the right-handed generalized cancellation property from its left-handed
counterpart, provided that the types and operations involved obey some
restrictions.

**Intuition**: if `f` is commutative and `rβ` supports substitution, then the
arguments to `f` can be swapped so that left-handed cancellation can be used.

**Named parameters**
- `α`: the argument type of the binary operation `f`.
- `β`: the result type of the binary operation `f`.
- `f`: the binary operation that obeys the generalized cancellation property.
- `rα`: a binary relation over `f`'s argument type `α`.
- `rβ`: a binary relation over `f`'s result type `β`.

**Class parameters**
- `EqvOp β`: needed for both the `Commutative` and `Substitutive₂` parameters
- `Commutative f`: needed for swapping the arguments to `f`.
- `Substitutive₂ rβ (· ≃ ·) (· → ·)`: needed to update the right-handed
  hypothesis involving `rβ` to a left-handed hypothesis.
-/
def cancelR_from_cancelL
    {α : Sort u} {β : Sort v}
    {f : α → α → β} {rα : α → α → Prop} {rβ : β → β → Prop}
    [EqvOp β] [Commutative f] [Substitutive₂ rβ (· ≃ ·) (· → ·)]
    : CancellativeOn Hand.L f rα rβ → CancellativeOn Hand.R f rα rβ := by
  intro
  constructor
  intro x y₁ y₂ (hyp : rβ (f y₁ x) (f y₂ x))
  show rα y₁ y₂
  have : rβ (f x y₁) (f y₂ x) := AA.substL (rβ := (· → ·)) AA.comm hyp
  have : rβ (f x y₁) (f x y₂) := AA.substR (rβ := (· → ·)) AA.comm this
  exact AA.cancelL this

end AA
