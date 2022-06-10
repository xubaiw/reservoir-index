import Lean4Axiomatic.Function
import Lean4Axiomatic.Operators

/-!
# Equivalence relations

## Fundamental definitions and properties
-/

namespace Lean4Axiomatic
namespace Relation

/--
Class for
[reflexive relations](https://en.wikipedia.org/wiki/Reflexive_relation).

Paraphrasing Wikipedia, a homogeneous binary relation `R` on a sort `α` is
**reflexive** iff it relates every inhabitant of `α` to itself.

This property is provided by the single field `Reflexive.refl`; see its
documentation for more details.

**Named parameters**
- `α`: The `Sort` of `R`'s parameters.
- `R`: The homogeneous binary relation obeying the reflexive property.
-/
class Reflexive {α : Sort u} (R : α → α → Prop) :=
  /--
  The reflexive property of a homogeneous binary relation `R` on a sort `α`.

  Equality, or equivalence, are the archetypes of reflexive relations: if a
  sort `α` has an equivalence relation (see `Eqv` and `EqvOp`), then any
  inhabitant `x : α` is equivalent to itself (i.e., `x ≃ x`).

  Another reflexive relation is _divisibility_, from number theory. We say an
  integer `a` divides an integer `b` iff `b ≃ c * a` for some integer `c`. We
  can show that all integers divide themselves by taking `c ≃ 1`.

  An example of a relation that is _not_ reflexive is "`n * m` is even" for
  natural numbers `n`, `m`. While "`n * n` is even" holds for even numbers `n`,
  it fails for odd numbers and thus is not reflexive on the natural numbers.
  Credit goes to Wikipedia for this example.

  **Named parameters**
  - See `Reflexive` for the parameters provided by the class.
  - `x`: `R`'s first and second argument.
  -/
  refl : {x : α} → R x x

export Reflexive (refl)

/--
The type of logical implication (i.e., the arrow type or exponential) is
reflexive: there are inhabitants of the type `α → α` for all `α : Prop`.

**Intuition**: The identity function (i.e, the function that simply returns its
single argument) meets this requirement.
-/
instance implication_reflexive : Reflexive (· → ·) := {
  refl := id
}

/--
Class for
[symmetric relations](https://en.wikipedia.org/wiki/Symmetric_relation).

A homogeneous binary relation `R` on a sort `α` is **symmetric** iff its truth
value remains the same when its arguments are exchanged.

This property is provided by the single field `Symmetric.symm`; see its
documentation for more details.

**Named parameters**
- `α`: The `Sort` of `R`'s parameters.
- `R`: The homogeneous binary relation obeying the symmetric property.
-/
class Symmetric {α : Sort u} (R : α → α → Prop) :=
  /--
  The symmetric property of a homogeneous binary relation `R` on a sort `α`.

  Equality, or equivalence, are the archetypes of symmetric relations: if a
  sort `α` has an equivalence relation (see `Eqv` and `EqvOp`), and for some
  inhabitants `x y : α` we know that `x` is equivalent to `y` (i.e., `x ≃ y`),
  then we also know that `y` is equivalent to `x` (i.e., `y ≃ x`).

  Another example is actually the non-example from `Reflexive.refl`,
  "`n * m` is even" for natural numbers `n` and `m`. In this case it's because
  multiplication of natural numbers is commutative.

  A relation that fails to be symmetric is "X likes Y" where X and Y are
  people. While there are many specific Xs and Ys that like each other, this
  unfortunately doesn't hold in general.

  **Named parameters**
  - See `Symmetric` for the parameters provided by the class.
  - `x`, `y`: The arguments to `R`.
  -/
  symm : {x y : α} → R x y → R y x

export Symmetric (symm)

/--
`Symmetric` relations are special cases of `Fn.Swappable` functions.

**Intuition**: Just going by syntax, a relation `R` that satisfies
`Symmetric.symm` also satisfies `Fn.swap` as the swappable function `f`, with
logical implication (i.e., the function type or arrow type) as the relation
between swapped invocations.

**Named parameters**
- `α`: The `Sort` of `R`'s parameters.
- `R`: The symmetric relation.

**Class parameters**
- `Symmetric R`: Evidence that `R` is symmetric.
-/
instance swappable_over_implication_from_symmetric
    {α : Sort u} {R : α → α → Prop} [Symmetric R] : Fn.Swappable R (· → ·)
    := {
  swap := symm
}

/--
The negation of a symmetric relation is also symmetric.

**Intuition**: Consider the set of all input pairs to the relation. It can be
divided into two disjoint subsets: the pairs that satisfy the relation, and
the pairs that don't. Both subsets must be closed under the operation of
swapping the components of the pairs, otherwise the relation wouldn't be
symmetric.

**Named parameters**
- `α`: The `Sort` of `R`'s parameters.
- `R`: The symmetric relation.

**Class parameters**
- `Symmetric R`: Evidence that `R` is symmetric.
-/
instance negation_preserves_symmetry
    {α : Sort u} {R : α → α → Prop} [Symmetric R] : Symmetric (¬ R · ·)
    := {
  symm := mt symm
}

/--
Conjunction (i.e. logical _and_) is symmetric.

**Intuition**: The order of a conjunction's arguments doesn't affect its truth
value.
-/
instance and_symmetric : Symmetric (· ∧ ·) := by
  apply Symmetric.mk
  intro p q (And.intro (_ : p) (_ : q))
  show q ∧ p
  exact And.intro ‹q› ‹p›

/--
Class for
[transitive relations](https://en.wikipedia.org/wiki/Transitive_relation).

A homogeneous binary relation `R` on a sort `α` is **transitive** iff when `R`
relates `x` to `y`, and `y` to `z`, then it also relates `x` to `z`, for all
`x`, `y`, and `z` inhabiting `α`. Transitive relations are useful because new
pairs of values can be shown to be related by chaining already known pairs
together.

This property is provided by the single field `Transitive.trans`; see its
documentation for more details.

**Named parameters**
- `α`: The `Sort` of `R`'s parameters.
- `R`: The homogeneous binary relation obeying the transitive property.
-/
class Transitive {α : Sort u} (R : α → α → Prop) :=
  /--
  The transitive property of a homogeneous binary relation `R` on a sort `α`.

  Equality, or equivalence, are the archetypes of transitive relations: if a
  sort `α` has an equivalence relation (see `Eqv` and `EqvOp`), and for some
  inhabitants `x y z : α` we know that `x` is equivalent to `y` (i.e. `x ≃ y`)
  and `y` is equivalent to `z` (i.e. `y ≃ z`), then we also know that `x` is
  equivalent to `z` (i.e. `x ≃ z`).

  Another transitive relation is _divisibility_, from number theory. We say an
  integer `a` divides an integer `b` iff `b ≃ c * a` for some integer `c`. If
  we know that `x` divides `y` (into, say, `p` copies of `x`), and `y` divides
  `z` (into `q` copies of `y`), then `z` must consist of `p * q` copies of `x`,
  and therefore `x` divides `z`.

  A relation that fails to be transitive is "X likes Y" where X and Y are
  people. If Alice likes Bob, and Bob likes Carol, then Alice might be a bit
  jealous of Carol, and definitely not inclined to like her!

  **Named parameters**
  - See `Transitive` for the parameters provided by the class.
  - `x`, `y`, `z`: The arguments to `R`.
  -/
  trans : {x y z : α} → R x y → R y z → R x z

export Transitive (trans)

/--
`Transitive` is a special case of the `Trans` class from Lean's Prelude.

**Intuition**: The Prelude's `Trans` allows the three values involved in the
property to be of different sorts. Which means it must support three
heterogeneous relations to pair up the values. Our `Transitive` is the special
case where all values are of the same sort, and only one homogeneous relation
is needed.

**Named parameters**
- `α`: The `Sort` of `R`'s parameters.
- `R`: The transitive relation.

**Class parameters**
- `Transitive R`: Evidence that `R` is transitive.
-/
instance prelude_trans_from_transitive
    {α : Sort u} {R : α → α → Prop} [Transitive R] : Trans R R R
    := {
  trans := trans
}

/--
Logical implication (i.e. the function type or the arrow type) is transitive.

**Intuition**: This is essentially why implications are so useful in logic,
because intermediate deductions can be combined into a larger, more significant
result. Alternatively, this is just function composition.
-/
instance implication_transitive : Transitive (· → ·) := {
  trans := flip Function.comp
}

namespace Equivalence

/--
Class for
[equivalence relations](https://en.wikipedia.org/wiki/Equivalence_relation).

A homogeneous binary relation `R` on a sort `α` is an **equivalence relation**
iff it is reflexive, symmetric, and transitive.

Equality is the simplest example of an equivalence relation, where each
inhabitant of `α` is equivalent only to itself. A less trivial example is the
relation where two integers are equivalent iff they have the same sign.

**Named parameters**
- `α`: The `Sort` of `R`'s parameters.
- `R`: The equivalence relation.
-/
class Eqv {α : Sort u} (R : α → α → Prop)
    extends Reflexive R, Symmetric R, Transitive R

/--
Provides an equivalence relation over `α` with the operator `· ≃ ·`.

**Named parameters**
- `α`: The `Sort` of the elements in the relation.
-/
class EqvOp (α : Sort u) extends Operators.TildeDash α, Eqv tildeDash

/--
Extends `EqvOp` with `· ≃? ·`, a decision procedure for equivalence.

**Named parameters**
- `α`: The `Sort` of the elements in the relation.
-/
class EqvOp? (α : Sort u)
    extends EqvOp α, Operators.TildeDashQuestion tildeDash

end Equivalence
end Relation

namespace Rel
export Relation (refl symm trans)
end Rel

end Lean4Axiomatic
