import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Operators

import Lean4Axiomatic.Natural.Exponentiation
import Lean4Axiomatic.Natural.Order
import Lean4Axiomatic.Natural.Sign

namespace Lean4Axiomatic.Natural

open Operators (TildeDash)

class Decl (ℕ : Type) where
  toCore : Core ℕ
  toAddition : Addition.Derived ℕ
  toSign : Sign.Derived ℕ
  toOrder : Order.Derived ℕ
  toMultiplication : Multiplication.Derived ℕ
  toExponentiation : Exponentiation.Base ℕ

export Addition (
  add_associative add_commutative add_one_step addOp add_step add_substitutive
  add_zero cancel_add step_add zero_add zero_sum_split
)
export Axioms (cases_on ind ind_on step_injective step_neq_zero)
export Core (step_substitutive)
export Equality (eqvOp?)
export Exponentiation (powOp pow_step pow_zero)
export Literals (literal literal_step literal_zero)
export Multiplication (
  mul_associative mul_cancellative mul_commutative mul_distributive mulOp
  mul_positive mul_substitutive_eq mul_substitutive_lt mul_zero step_mul
  zero_mul zero_product_split
)
export Order (
  le_antisymm le_defn le_reflexive le_split le_transitive leOp
  lt_defn lt_defn_add ltOp lt_split lt_step lt_step_le lt_zero lt_zero_pos
  trichotomy
)
export Sign (Positive positive_add positive_defn positive_step)

end Lean4Axiomatic.Natural
