import Lean4Axiomatic.Natural.Exponentiation
import Lean4Axiomatic.Natural.Order
import Lean4Axiomatic.Natural.Sign

namespace Lean4Axiomatic

open Natural

/--
The class of [natural numbers](https://en.wikipedia.org/wiki/Natural_number).

The fields of this class express many natural number properties. Any type `α`
for which an instance of `Natural α` exists must obey all of them. However,
most of the properties can be derived from a few essential ones (e.g. the
[Peano axioms](https://en.wikipedia.org/wiki/Peano_axioms)), reducing the work
required to construct an instance.

**Named parameters**
- `ℕ`: a type that obeys all of the properties provided by this class.
-/
class Natural (ℕ : Type) where
  toCore : Core ℕ
  toAddition : Addition.Derived ℕ
  toSign : Sign.Derived ℕ
  toOrder : Order.Derived ℕ
  toMultiplication : Multiplication.Derived ℕ
  toExponentiation : Exponentiation.Base ℕ

namespace Natural

attribute [instance] toAddition
attribute [instance] toCore
attribute [instance] toMultiplication
attribute [instance] toOrder
attribute [instance] toSign

export Addition (
  add_associative add_cancellative add_commutative add_one_step addOp add_step
  add_substitutive add_zero step_add zero_add zero_sum_split
)
export Axioms (cases_on ind ind_on step_injective step_neq_zero)
export Core (step_substitutive)
export Equality (eqvOp?)
export Exponentiation (powOp pow_step pow_zero)
export Literals (literal literal_step literal_zero)
export Multiplication (
  mul_associative mul_cancellative mul_commutative mul_distributive mulOp
  mul_positive mul_split_zero mul_substitutive_eq mul_substitutive_lt step_mul
  zero_mul
)
export Order (
  le_antisymm le_defn le_reflexive le_split le_transitive leOp
  lt_defn lt_defn_add ltOp lt_split lt_step lt_step_le lt_zero lt_zero_pos
  trichotomy
)
export Sign (Positive positive_add positive_defn positive_step)

end Lean4Axiomatic.Natural
