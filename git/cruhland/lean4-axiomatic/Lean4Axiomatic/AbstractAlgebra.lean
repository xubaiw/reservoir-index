import Lean4Axiomatic.AbstractAlgebra.Substitutive

namespace Lean4Axiomatic.AA

open Relation.Equivalence (EqvOp)

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

/--
Class for types, values, and operations that satisfy either the left- or
right-handed identity property.

For more information see `IdentityOn.ident` or
[consult Wikipedia](https://en.wikipedia.org/wiki/Identity_element).

**Named parameters**
- `hand`:
  Indicates whether the property is left- or right-handed.
- `α`:
  The `Sort` of the identity element and the parameters of the operation.
- `e`:
  The identity element. It's labeled as an `outParam` because it's useful to
  have it be inferred in some contexts; see `InverseOn` for an example.
- `f`:
  The binary operation that obeys the identity property with `e`.

**Class parameters**
- `EqvOp α`: Necessary because the property expresses an equality on `α`.
-/
class IdentityOn
    (hand : Hand) {α : Sort u} [EqvOp α] (e : outParam α) (f : α → α → α)
    :=
  /--
  The left- or right-handed identity property of a distinguished element `e`
  and a binary operation `f` defined over a sort `α`.

  The most well-known examples are the additive and multiplicative identities
  from arithmetic. Zero is the identity element for addition (because
  `0 + n ≃ n + 0 ≃ n` for all `n`), while one is the identity for
  multiplication (because `1 * m ≃ m * 1 ≃ m` for all `m`).

  **Named parameters**
  - See `IdentityOn` for the class parameters.
  - `x`:
    The argument to `f` that is not the identity element; it will be in the
    position that is the opposite of `hand`.
  -/
  ident {x : α} : hand.align f e x ≃ x

export IdentityOn (ident)

/--
Convenience function for the left-handed identity property.

Can often resolve cases where type inference gets stuck when using the more
general `ident` function.

See `IdentityOn.ident` for detailed documentation.
-/
abbrev identL := @ident Hand.L

/--
Convenience function for the right-handed identity property.

Can often resolve cases where type inference gets stuck when using the more
general `ident` function.

See `IdentityOn.ident` for detailed documentation.
-/
abbrev identR := @ident Hand.R

/--
Convenience class for types, values, and operations that satisfy the full
(left- **and** right-handed) identity property.

See `IdentityOn` for detailed documentation.
-/
class Identity {α : Sort u} [EqvOp α] (e : outParam α) (f : α → α → α) :=
  identityL : IdentityOn Hand.L e f
  identityR : IdentityOn Hand.R e f

attribute [instance] Identity.identityL
attribute [instance] Identity.identityR

/--
Derive the right-identity property from left-identity for operations `f`
meeting certain conditions.

**Intuition**: Both the left-handed and right-handed versions of the property
equate an application of `f` to the same value. Thus if `f` is commutative, one
version implies the other.

**Named parameters**
- `α`: The `Sort` of the identity element and the parameters of the operation.
- `e`: The identity element.
- `f`: The binary operation that obeys the identity property with `e`.

**Class parameters**
- `EqvOp α`: Necessary because `IdentityOn.ident` expresses an equality on `α`.
- `Commutative f`: Restriction on `f` that's required for the derivation.
-/
def identityR_from_identityL
    {α : Sort u} [EqvOp α] {e : α} {f : α → α → α} [Commutative f]
    : IdentityOn Hand.L e f → IdentityOn Hand.R e f
    := by
  intro _ -- Make left identity available to instance search
  apply IdentityOn.mk
  intro (x : α)
  show f x e ≃ x
  exact Rel.trans AA.comm identL

/--
Class for types and operations that satisfy either the left- or right-handed
inverse property.

For more information see `InverseOn.inverse` or
[consult Wikipedia](https://en.wikipedia.org/wiki/Inverse_element).

**Named parameters**
- `hand`: Indicates whether the property is left- or right-handed.
- `α`: The `Sort` of the operations' parameters.
- `e`: An identity element under the operation `f`.
- `inv`: An operation that turns any `α` value into its inverse.
- `f`: The binary operation that, with `inv`, obeys the inverse property.

**Class parameters**
- `EqvOp α`: Necessary because the property expresses an equality on `α`.
- `IdentityOn hand e f`: Evidence that `e` is an identity element.
-/
class InverseOn
    (hand : Hand) {α : Sort u} {e : α} (inv : outParam (α → α)) (f : α → α → α)
    [EqvOp α] [IdentityOn hand e f]
    :=
  /--
  The left- or right-handed inverse property of an inverse operation `inv` and
  a binary operation `f` defined over a sort `α`.

  The most well-known examples are additive and multiplicative inverses from
  arithmetic. Integers are the simplest numbers to have additive inverses, via
  negation; `a + (-a) ≃ (-a) + a ≃ 0` for all `a`. Similarly, rational numbers
  are the simplest ones with multiplicative inverses, via reciprocation;
  `q * q⁻¹ ≃ q⁻¹ * q ≃ 1` for all nonzero `q`.

  **Named parameters**
  - See `InverseOn` for the class parameters.
  - `x`: The value that is combined (via `f`) with its own inverse.
  -/
  inverse {x : α} : hand.align f (inv x) x ≃ e

export InverseOn (inverse)

/--
Convenience function for the left-handed inverse property.

Can often resolve cases where type inference gets stuck when using the more
general `inverse` function.

See `InverseOn.inverse` for detailed documentation.
-/
abbrev inverseL := @inverse Hand.L

/--
Convenience function for the right-handed inverse property.

Can often resolve cases where type inference gets stuck when using the more
general `inverse` function.

See `InverseOn.inverse` for detailed documentation.
-/
abbrev inverseR := @inverse Hand.R

/--
Convenience class for types and operations that satisfy the full (left- **and**
right-handed) inverse property.

See `InverseOn` for detailed documentation.
-/
class Inverse
    {α : Sort u} {e : α} (inv : outParam (α → α)) (f : α → α → α)
    [EqvOp α] [Identity e f] :=
  inverseL : InverseOn Hand.L inv f
  inverseR : InverseOn Hand.R inv f

/--
Derive the right-inverse property from left-inverse for operations `f`
meeting certain conditions.

**Intuition**: Both the left-handed and right-handed versions of the property
equate an application of `f` to the same value. Thus if `f` is commutative, one
version implies the other.

**Named parameters**
- `α`: The `Sort` of the operations' parameters.
- `e`: An identity element under the operation `f`.
- `inv`: An operation that turns any `α` value into its inverse.
- `f`: The binary operation that, with `inv`, obeys the inverse property.

**Class parameters**
- `EqvOp α`: Necessary because the property expresses an equality on `α`.
- `IdentityOn hand e f`: Evidence that `e` is an identity element.
- `Commutative f`: Restriction on `f` that's required for the derivation.
-/
def inverseR_from_inverseL
    {α : Sort u} {e : α} {inv : α → α} {f : α → α → α}
    [EqvOp α] [Identity e f] [Commutative f]
    : InverseOn Hand.L inv f → InverseOn Hand.R inv f
    := by
  intro _ -- Make left inverse available to instance search
  apply InverseOn.mk
  intro (x : α)
  show f x (inv x) ≃ e
  exact Rel.trans AA.comm inverseL

/--
Class for types and operations that satisfy either the left- or right-handed
semicompatibility property.

This property doesn't seem to have a standard name. For more information see
`SemicompatibleOn.scompat`

**Named parameters**
- `hand`: Indicates whether the property is left- or right-handed.
- `α`: The `Sort` that the operations `f` and `g` are defined over.
- `f`: An unary operation on `α`.
- `g`: A binary operation on `α`.

**Class parameters**
- `EqvOp α`: Necessary because the property expresses an equivalence on `α`.
-/
class SemicompatibleOn
    (hand : Hand) {α : Sort u} [EqvOp α] (f : α → α) (g : α → α → α)
    :=
  /--
  The left- or right-handed semicompatibility property of two operations `f`
  and `g` defined over a sort `α`.

  The property is called _semi_-compatible because when `f` is exchanged with
  `g`, it only operates on one of `g`'s arguments, rather than both. An example
  of operations that are semicompatible are _successor_ (i.e., `step`) and
  _addition_ on natural numbers: `step n + m ≃ step (n + m) ≃ n + step m`.
  Another example is negation and multiplication on integers:
  `(-a) * b ≃ -(a * b) ≃ a * (-b)`.

  **Named parameters**
  - See `SemicompatibleOn` for the class parameters.
  - `x`: The left-hand argument to `g`.
  - `y`: The right-hand argument to `g`.
  -/
  scompat {x y : α} : f (g x y) ≃ hand.pick (g (f x) y) (g x (f y))

export SemicompatibleOn (scompat)

/--
Convenience function for the left-handed semicompatibility property.

Can often resolve cases where type inference gets stuck when using the more
general `scompat` function.

See `SemicompatibleOn.scompat` for detailed documentation.
-/
abbrev scompatL := @scompat Hand.L

/--
Convenience function for the right-handed semicompatibility property.

Can often resolve cases where type inference gets stuck when using the more
general `scompat` function.

See `SemicompatibleOn.scompat` for detailed documentation.
-/
abbrev scompatR := @scompat Hand.R

/--
Convenience class for types and operations that satisfy the full (left- **and**
right-handed) semicompatibility property.

See `SemicompatibleOn` for detailed documentation.
-/
class Semicompatible {α : Sort u} [EqvOp α] (f : α → α) (g : α → α → α) :=
  semicompatibleL : SemicompatibleOn Hand.L f g
  semicompatibleR : SemicompatibleOn Hand.R f g

attribute [instance] Semicompatible.semicompatibleL
attribute [instance] Semicompatible.semicompatibleR

/--
Derive the right-semicompatibility property from left-semicompatibility for
operations `f` and `g` meeting certain conditions.

**Intuition**: Both the left-handed and right-handed versions of the property
have one side of their equivalences in common. Thus if `g` is commutative, one
version implies the other.

**Named parameters**
- `α`: The `Sort` of the operations' parameters.
- `f`: An unary operation on `α`.
- `g`: A binary operation on `α`.

**Class parameters**
- `EqvOp α`:
    Necessary because the property expresses an equivalence on `α`.
- `Substitutive₁ f (· ≃ ·) (· ≃ ·)`:
    Needed to transform an expression passed to `f`. Nearly every useful `f`
    will satisfy this property.
- `Commutative g`:
    Restriction on `g` that's required for the derivation.
-/
def semicompatibleR_from_semicompatibleL
    {α : Sort u} {f : α → α} {g : α → α → α}
    [EqvOp α] [Substitutive₁ f (· ≃ ·) (· ≃ ·)] [Commutative g]
    : SemicompatibleOn Hand.L f g → SemicompatibleOn Hand.R f g
    := by
  intro _ -- Make the left-hand property available to instance search
  apply SemicompatibleOn.mk
  intro x y
  show f (g x y) ≃ g x (f y)
  calc
    f (g x y) ≃ _ := AA.subst₁ AA.comm
    f (g y x) ≃ _ := AA.scompatL
    g (f y) x ≃ _ := AA.comm
    g x (f y) ≃ _ := Rel.refl

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
    hand.align f x (g y z) ≃ g (hand.align f x y) (hand.align f x z)

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
    [EqvOp α] [Commutative f] [Substitutive₂ g AA.tc (· ≃ ·) (· ≃ ·)]
    : DistributiveOn Hand.L f g → DistributiveOn Hand.R f g := by
  intro
  constructor
  intro x y z
  show f (g y z) x ≃ g (f y x) (f z x)
  calc
    f (g y z) x       ≃ _ := AA.comm
    f x (g y z)       ≃ _ := AA.distribL
    g (f x y) (f x z) ≃ _ := AA.substL AA.comm
    g (f y x) (f x z) ≃ _ := AA.substR AA.comm
    g (f y x) (f z x) ≃ _ := Rel.refl

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

/--
Swaps the middle two elements of a balanced four-element expression involving a
single binary operation.

The sort `α` and its binary operation `f` must form a commutative semigroup.

**Named parameters**
- `α`: the sort over which `f` operates.
- `f`: the binary operation used in the expression.
- `a`, `b`, `c`, `d`: the operands to `f` in the expression.

**Class parameters**
- `EqvOp α`: needed to express the identity between expressions.
- `Associative f`, `Commutative f`: needed to rearrange the operands freely.
- `Substitutive₂ f tc (· ≃ ·) (· ≃ ·)`: needed to rearrange subexpressions.
-/
theorem expr_xxfxxff_lr_swap_rl
    {α : Sort u} {f : α → α → α} {a b c d : α} [EqvOp α]
    [Associative f] [Commutative f] [Substitutive₂ f tc (· ≃ ·) (· ≃ ·)]
    : f (f a b) (f c d) ≃ f (f a c) (f b d)
    := calc
  f (f a b) (f c d) ≃ _ := AA.assoc
  f a (f b (f c d)) ≃ _ := AA.substR (Rel.symm AA.assoc)
  f a (f (f b c) d) ≃ _ := AA.substR (AA.substL AA.comm)
  f a (f (f c b) d) ≃ _ := AA.substR AA.assoc
  f a (f c (f b d)) ≃ _ := Rel.symm AA.assoc
  f (f a c) (f b d) ≃ _ := Rel.refl

/--
Swaps the second and fourth elements of a balanced four-element expression
involving a single binary operation.

The sort `α` and its binary operation `f` must form a commutative semigroup.

**Named parameters**
- `α`: the sort over which `f` operates.
- `f`: the binary operation used in the expression.
- `a`, `b`, `c`, `d`: the operands to `f` in the expression.

**Class parameters**
- `EqvOp α`: needed to express the identity between expressions.
- `Associative f`, `Commutative f`: needed to rearrange the operands freely.
- `Substitutive₂ f tc (· ≃ ·) (· ≃ ·)`: needed to rearrange subexpressions.
-/
theorem expr_xxfxxff_lr_swap_rr
    {α : Sort u} {f : α → α → α} {a b c d : α} [EqvOp α]
    [Associative f] [Commutative f] [Substitutive₂ f tc (· ≃ ·) (· ≃ ·)]
    : f (f a b) (f c d) ≃ f (f a d) (f c b)
    := calc
  f (f a b) (f c d) ≃ _ := AA.substR AA.comm
  f (f a b) (f d c) ≃ _ := expr_xxfxxff_lr_swap_rl
  f (f a d) (f b c) ≃ _ := AA.substR AA.comm
  f (f a d) (f c b) ≃ _ := Rel.refl

end Lean4Axiomatic.AA
