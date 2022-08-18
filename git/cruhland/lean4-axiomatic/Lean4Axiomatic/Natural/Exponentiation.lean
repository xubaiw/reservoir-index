import Lean4Axiomatic.Natural.Addition
import Lean4Axiomatic.Natural.Multiplication

namespace Lean4Axiomatic.Natural

/-!
# Definition and properties of natural number exponentiation
-/

/--
Definition of exponentiation, and properties that it must satisfy.

All other properties of exponentiation can be derived from these.
-/
class Exponentiation.Base
    (ℕ : Type) [Core ℕ] [Addition ℕ] [Multiplication.Base ℕ] where
  /-- Definition of and syntax for exponentiation. -/
  powOp : Pow ℕ ℕ

  /-- Raising a natural number to the power zero always gives one. -/
  pow_zero {n : ℕ} : n ^ (0 : ℕ) ≃ 1

  /--
  Each increment of the exponent puts another factor of the base on the result.
  -/
  pow_step {n m : ℕ} : n ^ step m ≃ (n ^ m) * n

attribute [instance] Exponentiation.Base.powOp

namespace Exponentiation
export Exponentiation.Base (powOp pow_step pow_zero)
end Exponentiation

end Lean4Axiomatic.Natural
