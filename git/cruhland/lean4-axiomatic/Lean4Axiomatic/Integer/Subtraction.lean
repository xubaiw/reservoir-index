import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Core

namespace Lean4Axiomatic.Integer

/-!
# Definition and properties of integer subtraction
-/

/--
Definition of subtraction, and properties that it must satisfy.

All other properties of subtraction can be derived from these.

**Named parameters**
- `ℤ`: The integers.

**Class parameters**
- All other class parameters provide the subset of integer properties necessary
  to define the fields of this class.
-/
class Subtraction.Base (ℤ : Type) [Equivalence ℤ] :=
  /-- Definition of and syntax for subtraction. -/
  subOp : Sub ℤ

  /--
  Subtraction preserves equivalence of integers; two equivalent integers are
  still equivalent after the same quantity is subtracted from both (or if both
  are subtracted from the same quantity).
  -/
  sub_substitutive : AA.Substitutive₂ (α := ℤ) (· - ·) AA.tc (· ≃ ·) (· ≃ ·)

end Lean4Axiomatic.Integer
