import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Core

namespace Lean4Axiomatic.Integer

/-!
# Definition and properties of integer negation and subtraction
-/

/--
Definition of negation, and properties that it must satisfy.

All other properties of negation can be derived from these.

**Named parameters**
- `ℤ`: The type of integers.

**Class parameters**
- `Equality ℤ`: Required to express most properties of negation.
-/
class Negation.Base (ℤ : Type) [Equality ℤ] :=
  /-- Definition of and syntax for negation. -/
  negOp : Neg ℤ

  /--
  Negation preserves equality of integers; two equal integers are still equal
  after both are negated.
  -/
  neg_substitutive : AA.Substitutive₁ (α := ℤ) (-·) (· ≃ ·) (· ≃ ·)

namespace Negation
export Negation.Base (negOp)
end Negation

end Lean4Axiomatic.Integer
