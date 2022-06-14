import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Core

namespace Lean4Axiomatic.Integer

/-!
# Definition and properties of integer multiplication
-/

/--
Definition of multiplication, and properties that it must satisfy.

All other properties of multiplication can be derived from these.
-/
class Multiplication.Base (ℤ : Type) [Core ℤ] :=
  /-- Definition of and syntax for multiplication. -/
  mulOp : Mul ℤ

  /--
  Multiplication preserves equality of integers; two equal integers are still
  equal after the same quantity is multiplied with both (on the left or right).
  -/
  mul_substitutive : AA.Substitutive₂ (α := ℤ) (· * ·) AA.tc (· ≃ ·) (· ≃ ·)

  /-- Exchanging the operands of multiplication does not change the result. -/
  mul_commutative : AA.Commutative (α := ℤ) (· * ·)

namespace Multiplication
export Multiplication.Base (mulOp)
end Multiplication

end Lean4Axiomatic.Integer
