
namespace Lean4Axiomatic.Integer

/-!
# Definition and properties of integer multiplication
-/

/--
Definition of multiplication, and properties that it must satisfy.

All other properties of multiplication can be derived from these.
-/
class Multiplication.Base (ℤ : Type) :=
  /-- Definition of and syntax for multiplication. -/
  mulOp : Mul ℤ

namespace Multiplication
export Multiplication.Base (mulOp)
end Multiplication

end Lean4Axiomatic.Integer
