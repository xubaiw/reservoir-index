import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Addition

namespace Lean4Axiomatic.Integer

/-!
# Definition and properties of integer multiplication
-/

/--
Definition of multiplication, and properties that it must satisfy.

All other properties of multiplication can be derived from these.

**Named parameters**
- `ℤ`: The type of integers.

**Class parameters**
- `Equality ℤ`: Required to express most properties of multiplication.
-/
class Multiplication.Base
    (ℕ : Type) [Natural ℕ]
    (ℤ : Type) [Equality ℤ] [Conversion ℕ ℤ] [Addition.Base ℕ ℤ]
    :=
  /-- Definition of and syntax for multiplication. -/
  mulOp : Mul ℤ

  /--
  Multiplication preserves equality of integers; two equal integers are still
  equal after the same quantity is multiplied with both (on the left or right).
  -/
  mul_substitutive : AA.Substitutive₂ (α := ℤ) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)

  /-- Exchanging the operands of multiplication does not change the result. -/
  mul_commutative : AA.Commutative (α := ℤ) (· * ·)

  /-- The grouping of the terms in a product doesn't matter. -/
  mul_associative : AA.Associative (α := ℤ) (· * ·)

  /-- Multiplying an integer by one produces the same integer. -/
  mul_identity : AA.Identity (α := ℤ) ↑(1 : ℕ) (· * ·)

  /--
  Multiplication of a sum by a value is equivalent to summing the
  multiplication of each term by that value.
  -/
  mul_distributive : AA.Distributive (α := ℤ) (· * ·) (· + ·)

namespace Multiplication
export Multiplication.Base (mulOp)
end Multiplication

end Lean4Axiomatic.Integer
