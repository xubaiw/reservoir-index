import Lean4Axiomatic.Integer.Impl.Derived.Core
import Lean4Axiomatic.Integer.Impl.Derived.Subtraction
import Lean4Axiomatic.Integer.Impl.Difference.Addition
import Lean4Axiomatic.Integer.Impl.Difference.Core
import Lean4Axiomatic.Integer.Impl.Difference.Multiplication
import Lean4Axiomatic.Integer.Impl.Difference.Negation
import Lean4Axiomatic.Integer.Impl.Difference.Sign

/-!
# Implementation of integers as formal differences of natural numbers
-/

namespace Lean4Axiomatic.Integer.Impl.Difference

variable {ℕ : Type}
variable [Natural ℕ]

namespace Inst

def core.base := @core ℕ ‹Natural ℕ›

def core.derived := @Derived.core ℕ ‹Natural ℕ› (Difference ℕ) core.base

def addition.base := @addition ℕ ‹Natural ℕ›

def multiplication.base := @multiplication ℕ ‹Natural ℕ›

def subtraction.base := @Derived.subtraction
  ℕ ‹Natural ℕ›
  (Difference ℕ) core.base addition.base negation

end Inst

instance integer : Integer ℕ (Difference ℕ) := {
  toAddition := Inst.addition.base
  toCore := Inst.core.derived
  toMultiplication := Inst.multiplication.base
  toNegation := negation
  toSign := sign
  toSubtraction := Derived.subtraction
}

end Lean4Axiomatic.Integer.Impl.Difference
