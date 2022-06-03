import Lean4Axiomatic.AbstractAlgebra.Commutative
import Lean4Axiomatic.AbstractAlgebra.Core

namespace Lean4Axiomatic.AA

open Relation.Equivalence (EqvOp)

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
- `C`: a constraint that the non-`hand` argument to `f` must meet.
- `rα`: a binary relation over `f`'s argument type `α`.
- `rβ`: a binary relation over `f`'s result type `β`.
-/
class SubstitutiveOn
    (hand : Hand) {α : Sort u} {β : Sort v}
    (f : α → α → β) (C : outParam (α → Prop))
    (rα : outParam (α → α → Prop)) (rβ : β → β → Prop)
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

  More advanced applications may require a nontrivial constraint `C` on `y`; an
  example is that `x₁ < x₂` implies `x₁ * y < x₂ * y` only for positive `y`.

  **Named parameters**
  - see `SubstitutiveOn` for the class parameters.
  - `x₁` and `x₂`: the arguments to `f`, related by `rα`; the `hand` parameter
    indicates which side of `f` they are given on.
  - `y`: the other argument to `f`; goes on the side opposite `hand`.
  - `cy`: evidence that the constraint on `y` is satisfied.
  -/
  subst₂
    {x₁ x₂ y : α} (cy : C y)
    : rα x₁ x₂ → rβ (forHand hand f x₁ y) (forHand hand f x₂ y)

export SubstitutiveOn (subst₂)

/--
Convenience function for the left-handed binary generalized substitution
property, without a constraint on `y`.

Can often resolve cases where type inference gets stuck when using the more
general `subst₂` function.

See `SubstitutiveOn.subst₂` for detailed documentation.
-/
abbrev substL
    {α : Sort u} {β : Sort v} {f : α → α → β} {rα : α → α → Prop}
    {rβ : β → β → Prop} [self : SubstitutiveOn Hand.L f tc rα rβ]
    {x₁ x₂ y : α} :=
  @subst₂ Hand.L α β f tc rα rβ self x₁ x₂ y True.intro

/--
Convenience function for the right-handed binary generalized substitution
property, without a constraint on `y`.

Can often resolve cases where type inference gets stuck when using the more
general `subst₂` function.

See `SubstitutiveOn.subst₂` for detailed documentation.
-/
abbrev substR
    {α : Sort u} {β : Sort v} {f : α → α → β} {rα : α → α → Prop}
    {rβ : β → β → Prop} [self : SubstitutiveOn Hand.R f tc rα rβ]
    {x₁ x₂ y : α} :=
  @subst₂ Hand.R α β f tc rα rβ self x₁ x₂ y True.intro

/--
Convenience function for the left-handed binary generalized substitution
property, with an explicit argument for the constraint on `y`.

Can often resolve cases where type inference gets stuck when using the more
general `subst₂` function.

See `SubstitutiveOn.subst₂` for detailed documentation.
-/
abbrev substLC := @subst₂ Hand.L

/--
Convenience function for the right-handed binary generalized substitution
property, with an explicit argument for the constraint on `y`.

Can often resolve cases where type inference gets stuck when using the more
general `subst₂` function.

See `SubstitutiveOn.subst₂` for detailed documentation.
-/
abbrev substRC := @subst₂ Hand.R

/--
Convenience class for types and operations that satisfy the full (left- **and**
right-handed) binary generalized substitution property.

See `SubstitutiveOn` for detailed documentation.
-/
class Substitutive₂
    {α : Sort u} {β : Sort v}
    (f : α → α → β) (C : α → Prop) (rα : α → α → Prop) (rβ : β → β → Prop)
    where
  substitutiveL : SubstitutiveOn Hand.L f C rα rβ
  substitutiveR : SubstitutiveOn Hand.R f C rα rβ

attribute [instance] Substitutive₂.substitutiveL
attribute [instance] Substitutive₂.substitutiveR

/--
If two properties are logically equivalent, one can be substituted for the
other as the assumption (i.e. antecedent) of an implication.

**Proof intuition**: assume one of the properties, then convert it to the other
using the equivalence, and obtain the implication's conclusion.

**Named parameters**:
- `p₁`: one of the two equivalent properties.
- `p₂`: the other equivalent property.
- `q`: the conclusion of the implication.
-/
def iff_substL {p₁ p₂ q : Prop} : (p₁ ↔ p₂) → (p₁ → q) → (p₂ → q) := by
  intro ⟨(_ : p₁ → p₂), (_ : p₂ → p₁)⟩ (_ : p₁ → q) (_ : p₂)
  show q
  have : p₁ := ‹p₂ → p₁› ‹p₂›
  have : q := ‹p₁ → q› ‹p₁›
  exact ‹q›

/--
If two properties are logically equivalent, one can be substituted for the
other as the conclusion (i.e. consequent) of an implication.

**Proof intuition**: obtain one of the properties from the given implication
and common assumption, then convert it to the other using the equivalence.

**Named parameters**:
- `p₁`: one of the two equivalent properties.
- `p₂`: the other equivalent property.
- `q`: the assumption of the implication.
-/
def iff_substR {p₁ p₂ q : Prop} : (p₁ ↔ p₂) → (q → p₁) → (q → p₂) := by
  intro ⟨(_ : p₁ → p₂), (_ : p₂ → p₁)⟩ (_ : q → p₁) (_ : q)
  show p₂
  have : p₁ := ‹q → p₁› ‹q›
  have : p₂ := ‹p₁ → p₂› ‹p₁›
  exact ‹p₂›

/--
Logically equivalent properties can be substituted on both sides of an
implication.
-/
instance iff_substitutive : Substitutive₂ (· → ·) tc (· ↔ ·) (· → ·) where
  substitutiveL := SubstitutiveOn.mk λ (_ : True) => iff_substL
  substitutiveR := SubstitutiveOn.mk λ (_ : True) => iff_substR

/--
Convenience definition that converts instances of `Commutative` into instances
of `Swappable`.

The `Swappable` class is a generalization of the commutative and symmetric
properties, and is used in very abstract, general definitions. This instance
makes it easy for those definitions to apply to commutative functions.

**Named parameters**
- `α`: the argument type of the commutative function `f`.
- `β`: the result type of the commutative function `f`.
- `f`: the commutative function to produce a `Swappable` instance for.
- `R`: the binary relation that connects the two sides of the `swap` operation.

**Class parameters**
- `EqvOp β`:
    required by `Commutative f`.
- `Commutative f`:
    the property to translate into a `Swappable` instance.
- `Relation.Reflexive R`:
    provides a starting point for substitution.
- `SubstitutitveOn Hand.R R tc (· ≃ ·) (· → ·)`:
    necessary for transfering commutativity from `EqvOp β` to `R`.
-/
instance swappable_from_commutative
    {α : Type u} {β : Type v} {f : α → α → β} {R : β → β → Prop}
    [EqvOp β] [inst : SubstitutiveOn Hand.R R tc (· ≃ ·) (· → ·)]
    [Relation.Reflexive R] [Commutative f] : Fn.Swappable f R
    := {
  swap := by
    intro x y
    show R (f x y) (f y x)
    have : R (f x y) (f x y) := Rel.refl
    exact substR (self := inst) comm ‹R (f x y) (f x y)›
}

/--
Derives the right-handed binary generalized substitution property from its
left-handed counterpart, provided that the arguments to the operation `f` can
be swapped in an appropriate way.

There are many binary operations that have a symmetry between their left- and
right-handed arguments. This convenience function is a general-purpose way to
leverage that symmetry to avoid having to write a redundant proof of
right-handed substitution.

**Proof intuition**: apply left-handed substitution, then swap the arguments to
both invocations of `f`.

**Named parameters**
- `α`: the argument type of the binary operation `f`.
- `β`: the result type of the binary operation `f`.
- `f`: the binary operation that obeys the generalized substitution property.
- `C`: a constraint that the opposite-handed argument to `f` must meet.
- `rα`: how the substitutable arguments to `f` are related.
- `rβ`: how the invocations of `f` pre- and post-substitution are related.
- `rS`: how an invocation of `f` is related to its swapped-argument version.

**Class parameters**
- `Fn.Swappable f rS`:
    The arguments of `f` need to be swappable to go from left-handed to right-
    handed substitution.
- `Substitutive₂ rβ tc rS (· → ·)`:
    Allows the result of left-handed substitution, which is an instance of the
    relation `rβ`, to be converted into the right-handed result. Both the left
    and right sides of `rβ` are invocations of `f`, and can be replaced by
    their swapped-argument versions due to how `rS` is used here and in
    `Fn.Swappable f rS`.
-/
def substR_from_substL_swap
    {α : Sort u} {β : Sort v}
    {f : α → α → β} {C : α → Prop} {rα : α → α → Prop} {rβ rS : β → β → Prop}
    [Fn.Swappable f rS] [Substitutive₂ rβ tc rS (· → ·)]
    : SubstitutiveOn Hand.L f C rα rβ → SubstitutiveOn Hand.R f C rα rβ := by
  intro _ -- Make left-substitution available for instance search
  apply SubstitutiveOn.mk
  intro x₁ x₂ y (_ : C y) (_ : rα x₁ x₂)
  show rβ (f y x₁) (f y x₂)
  have : rβ (f x₁ y) (f x₂ y) := AA.substLC ‹C y› ‹rα x₁ x₂›
  have : rβ (f y x₁) (f x₂ y) := AA.substL (rβ := (· → ·)) Fn.swap this
  have : rβ (f y x₁) (f y x₂) := AA.substR (rβ := (· → ·)) Fn.swap this
  exact this

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
    : SubstitutiveOn Hand.L (α := α) (· ≃ ·) tc (· ≃ ·) (· → ·) := by
  constructor
  intro x₁ x₂ y _ (_ : x₁ ≃ x₂) (_ : x₁ ≃ y)
  show x₂ ≃ y
  exact Rel.trans (Rel.symm ‹x₁ ≃ x₂›) ‹x₁ ≃ y›

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
    : Substitutive₂ (α := α) (· ≃ ·) tc (· ≃ ·) (· → ·) where
  substitutiveL := eqv_substL
  substitutiveR := substR_from_substL_swap (rS := (· ↔ ·)) eqv_substL

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
    : SubstitutiveOn Hand.L (α := α) (· ≄ ·) tc (· ≃ ·) (· → ·) := by
  constructor
  intro x₁ x₂ y _ (_ : x₁ ≃ x₂) (_ : x₁ ≄ y) (_ : x₂ ≃ y)
  show False
  apply ‹x₁ ≄ y›
  show x₁ ≃ y
  exact Rel.trans ‹x₁ ≃ x₂› ‹x₂ ≃ y›

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
    {α : Sort u} [EqvOp α] : Substitutive₂ (α := α) (· ≄ ·) tc (· ≃ ·) (· → ·)
    where
  substitutiveL := neq_substL
  substitutiveR := substR_from_substL_swap (rS := (· ↔ ·)) neq_substL

/--
Class for types and operations that satisfy either the left- or right-handed
generalized cancellation property.

For more information see `CancellativeOn.cancel`.

**Named parameters**
- `hand`: indicates whether the property is left- or right-handed.
- `α`: the argument type of the binary operation `f`.
- `β`: the result type of the binary operation `f`.
- `f`: the binary operation that obeys the generalized cancellation property.
- `C`: a constraint that the argument on the `hand` side of `f` must meet.
- `rα`: a binary relation over `f`'s argument type `α`.
- `rβ`: a binary relation over `f`'s result type `β`.
-/
class CancellativeOn
    (hand : Hand) {α : Sort u} {β : Sort v}
    (f : α → α → β) (C : outParam (α → Prop))
    (rα : outParam (α → α → Prop)) (rβ : β → β → Prop)
    where
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

  More advanced applications may require a nontrivial constraint `C` on `x`; an
  example is that `x * y₁ ≃ x * y₂` implies `y₁ ≃ y₂` only for nonzero `x`.

  **Named parameters**
  - see `CancellativeOn` for the class parameters.
  - `x`: the "cancelled" argument to `f`; the `hand` parameter
    indicates which side of `f` it appears on.
  - `y₁` and `y₂`: the other arguments to `f`; appearing on the side opposite
    `hand`. They are related by `rα` in the result.
  - `cx`: evidence that the constraint on `x` is satisfied.
  -/
  cancel
    {x y₁ y₂ : α} (cx : C x)
    : rβ (forHand hand f x y₁) (forHand hand f x y₂) → rα y₁ y₂

export CancellativeOn (cancel)

/--
Convenience function for the left-handed generalized cancellation property,
without a constraint on `x`.

Can often resolve cases where type inference gets stuck when using the more
general `cancel` function.

See `CancellativeOn.cancel` for detailed documentation.
-/
abbrev cancelL
    {α : Sort u} {β : Sort v} {f : α → α → β} {rα : α → α → Prop}
    {rβ : β → β → Prop} [self : CancellativeOn Hand.L f tc rα rβ]
    {x y₁ y₂ : α} :=
  @cancel Hand.L α β f tc rα rβ self x y₁ y₂ True.intro

/--
Convenience function for the right-handed generalized cancellation property,
without a constraint on `x`.

Can often resolve cases where type inference gets stuck when using the more
general `cancel` function.

See `CancellativeOn.cancel` for detailed documentation.
-/
abbrev cancelR
    {α : Sort u} {β : Sort v} {f : α → α → β} {rα : α → α → Prop}
    {rβ : β → β → Prop} [self : CancellativeOn Hand.R f tc rα rβ]
    {x y₁ y₂ : α} :=
  @cancel Hand.R α β f tc rα rβ self x y₁ y₂ True.intro

/--
Convenience function for the left-handed generalized cancellation property,
with an explicit argument for the constraint on `x`.

Can often resolve cases where type inference gets stuck when using the more
general `cancel` function.

See `CancellativeOn.cancel` for detailed documentation.
-/
abbrev cancelLC := @cancel Hand.L

/--
Convenience function for the right-handed generalized cancellation property,
with an explicit argument for the constraint on `x`.

Can often resolve cases where type inference gets stuck when using the more
general `cancel` function.

See `CancellativeOn.cancel` for detailed documentation.
-/
abbrev cancelRC := @cancel Hand.R

/--
Convenience class for types and operations that satisfy the full (left- **and**
right-handed) generalized cancellation property.

See `CancellativeOn` for detailed documentation.
-/
class Cancellative
    {α : Sort u} {β : Sort v}
    (f : α → α → β) (C : outParam (α → Prop))
    (rα : outParam (α → α → Prop)) (rβ : β → β → Prop)
    where
  cancellativeL : CancellativeOn Hand.L f C rα rβ
  cancellativeR : CancellativeOn Hand.R f C rα rβ

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
- `C`: a constraint that the argument on the cancellation-hand side of `f` must
  meet.
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
    {f : α → α → β} {C : α → Prop} {rα : α → α → Prop} {rβ : β → β → Prop}
    [EqvOp β] [Commutative f] [Substitutive₂ rβ tc (· ≃ ·) (· → ·)]
    : CancellativeOn Hand.L f C rα rβ → CancellativeOn Hand.R f C rα rβ := by
  intro
  constructor
  intro x y₁ y₂ (_ : C x) (_ : rβ (f y₁ x) (f y₂ x))
  show rα y₁ y₂
  have : rβ (f x y₁) (f y₂ x) :=
    AA.substL (rβ := (· → ·)) AA.comm ‹rβ (f y₁ x) (f y₂ x)›
  have : rβ (f x y₁) (f x y₂) :=
    AA.substR (rβ := (· → ·)) AA.comm ‹rβ (f x y₁) (f y₂ x)›
  exact AA.cancelLC ‹C x› ‹rβ (f x y₁) (f x y₂)›

end Lean4Axiomatic.AA
