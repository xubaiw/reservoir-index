import Lean4Axiomatic.Integer.Impl.Default.Subtraction
import Lean4Axiomatic.Integer.Impl.Difference.Addition
import Lean4Axiomatic.Integer.Impl.Difference.Core
import Lean4Axiomatic.Integer.Impl.Difference.Multiplication
import Lean4Axiomatic.Integer.Impl.Difference.Negation
import Lean4Axiomatic.Integer.Impl.Difference.Sign

/-!
# Implementation of integers as formal differences of natural numbers
-/

namespace Lean4Axiomatic.Integer.Impl.Difference

variable {ℕ : Type} [Natural ℕ]

namespace Inst

def addition.base := @addition ℕ ‹Natural ℕ›

def multiplication.base := @multiplication ℕ ‹Natural ℕ›

end Inst

instance integer : Integer ℕ (Difference ℕ) := {
  toAddition := Inst.addition.base
  toCore := core
  toMultiplication := Inst.multiplication.base
  toNegation := negation
  toSign := sign
  toSubtraction := Default.subtraction
}

end Lean4Axiomatic.Integer.Impl.Difference
