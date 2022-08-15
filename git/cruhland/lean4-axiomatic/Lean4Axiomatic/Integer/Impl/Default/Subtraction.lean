import Lean4Axiomatic.Integer.Negation
import Lean4Axiomatic.Integer.Subtraction

/-!
# Default implementation of subtraction axioms
-/

namespace Lean4Axiomatic.Integer.Impl.Default

variable {ℕ : Type}
variable [Natural ℕ]
variable {ℤ : Type}
variable [Core.Base ℕ ℤ]
variable [Addition.Base ℕ ℤ]
variable [Negation ℕ ℤ]

/-- Define subtraction of a value from another as adding its negation. -/
def sub (a b : ℤ) : ℤ := a + (-b)

def subOp : Sub ℤ := {
  sub := sub
}

instance subtraction : Subtraction ℕ ℤ := {
  subOp := subOp
  sub_defn := Rel.refl
}

end Lean4Axiomatic.Integer.Impl.Default
