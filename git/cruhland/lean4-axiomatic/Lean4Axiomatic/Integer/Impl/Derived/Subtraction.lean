import Lean4Axiomatic.Integer.Negation
import Lean4Axiomatic.Integer.Subtraction

namespace Lean4Axiomatic.Integer.Impl.Derived

/-! # Subtraction derived from addition and negation -/

variable {ℕ : Type}
variable [Natural ℕ]
variable {ℤ : Type}
variable [Equality ℤ]
variable [Conversion ℕ ℤ]
variable [Addition.Base ℕ ℤ]
variable [Negation.Base ℕ ℤ]

/-- Define subtraction of a value from another as adding its negation. -/
def sub (a b : ℤ) : ℤ := a + (-b)

instance subOp : Sub ℤ := {
  sub := sub (ℕ := ℕ)
}

/--
Subtraction is left-substitutive.

**Proof intuition**: Trivial; just substitutes on the underlying addition.
-/
theorem sub_substL {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → a₁ - b ≃ a₂ - b := by
  intro (_ : a₁ ≃ a₂)
  show a₁ - b ≃ a₂ - b
  show a₁ + (-b) ≃ a₂ + (-b)
  exact AA.substL ‹a₁ ≃ a₂›

def sub_substitutiveL
    : AA.SubstitutiveOn Hand.L (α := ℤ) (· - ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  subst₂ := λ (_ : True) => sub_substL
}

/--
Subtraction is right-substitutive.

**Proof intuition**: Trivial; just substitutes on the underlying addition and
negation.
-/
theorem sub_substR {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → b - a₁ ≃ b - a₂ := by
  intro (_ : a₁ ≃ a₂)
  show b - a₁ ≃ b - a₂
  show b + (-a₁) ≃ b + (-a₂)
  exact AA.substR (AA.subst₁ ‹a₁ ≃ a₂›)

def sub_substitutiveR
    : AA.SubstitutiveOn Hand.R (α := ℤ) (· - ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  subst₂ := λ (_ : True) => sub_substR
}

def sub_substitutive
    : AA.Substitutive₂ (α := ℤ) (· - ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := sub_substitutiveL
  substitutiveR := sub_substitutiveR
}

instance subtraction : Subtraction.Base ℤ := {
  subOp := subOp (ℕ := ℕ)
  sub_substitutive := sub_substitutive
}

end Lean4Axiomatic.Integer.Impl.Derived
