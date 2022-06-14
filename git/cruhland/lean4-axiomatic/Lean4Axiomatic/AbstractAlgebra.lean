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
