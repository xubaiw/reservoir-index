import Lean4Axiomatic.Integer.Impl.Difference.Addition
import Lean4Axiomatic.Integer.Impl.Difference.Core
import Lean4Axiomatic.Integer.Impl.Difference.Multiplication
import Lean4Axiomatic.Integer.Impl.Difference.Negation

/-!
# Implementation of integers as formal differences of natural numbers
-/

namespace Lean4Axiomatic.Integer.Impl.Difference

variable {ℕ : Type}
variable [Natural ℕ]

instance integer : Integer ℕ (Difference ℕ) := {
  toAddition := addition
  toConversion := conversion
  toEquality := equality
  toMultiplication := multiplication
  toNegation := negation
}

end Lean4Axiomatic.Integer.Impl.Difference
