import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Operators

import Lean4Axiomatic.Natural.Multiplication
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

export Addition (
  add_associative add_commutative add_one_step addOp add_step add_substitutive
  add_zero cancel_add step_add zero_add zero_sum_split
)
export Axioms (cases_on ind ind_on step_injective step_neq_zero)
export Core (step_substitutive)
export Equality (eqvOp?)
export Literals (literal literal_step literal_zero)
export Multiplication (
  mul_associative mul_commutative mul_distributive mulOp mul_positive
  mul_substitutive mul_zero step_mul zero_mul zero_product_split
)
export Order (
  le_antisymm le_defn le_reflexive le_split le_transitive leOp
  lt_defn lt_defn_add ltOp lt_split lt_step lt_step_le lt_zero trichotomy
)
export Sign (Positive positive_add positive_defn positive_step)

end Lean4Axiomatic.Natural
