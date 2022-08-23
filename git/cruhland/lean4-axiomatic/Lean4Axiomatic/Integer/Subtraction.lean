import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Sign

/-!
# Integer subtraction
-/

namespace Lean4Axiomatic.Integer

/-!
## Axioms
-/

/--
Definition of subtraction, and properties that it must satisfy.

All other properties of subtraction can be derived from these.
-/
class Subtraction
    (ℕ : Type) [Natural ℕ]
    (ℤ : Type) [Core ℕ ℤ] [Addition ℕ ℤ] [Negation ℕ ℤ]
    :=
  /-- Definition of and syntax for subtraction. -/
  subOp : Sub ℤ

  /-- Subtraction of a value is equivalent to adding its negation. -/
  sub_defn {a b : ℤ} : a - b ≃ a + (-b)

attribute [instance] Subtraction.subOp

export Subtraction (sub_defn subOp)

/-!
## Derived properties
-/

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℕ ℤ] [Addition ℕ ℤ] [Multiplication ℕ ℤ]
variable [Negation ℕ ℤ] [Sign ℕ ℤ] [Subtraction ℕ ℤ]

/--
Subtraction is left-substitutive.

**Proof intuition**: Trivial; just substitutes on the underlying addition.
-/
theorem sub_substL {a₁ a₂ b : ℤ} : a₁ ≃ a₂ → a₁ - b ≃ a₂ - b := by
  intro (_ : a₁ ≃ a₂)
  show a₁ - b ≃ a₂ - b
  calc
    a₁ - b    ≃ _ := sub_defn
    a₁ + (-b) ≃ _ := AA.substL ‹a₁ ≃ a₂›
    a₂ + (-b) ≃ _ := Rel.symm sub_defn
    a₂ - b    ≃ _ := Rel.refl

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
  calc
    b - a₁    ≃ _ := sub_defn
    b + (-a₁) ≃ _ := AA.substR (AA.subst₁ ‹a₁ ≃ a₂›)
    b + (-a₂) ≃ _ := Rel.symm sub_defn
    b - a₂    ≃ _ := Rel.refl

def sub_substitutiveR
    : AA.SubstitutiveOn Hand.R (α := ℤ) (· - ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  subst₂ := λ (_ : True) => sub_substR
}

instance sub_substitutive
    : AA.Substitutive₂ (α := ℤ) (· - ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := sub_substitutiveL
  substitutiveR := sub_substitutiveR
}

/--
Equivalent integers are the only ones to differ by zero.

**Proof intuition**: The reverse direction is trivial; the forward direction
uses the additive inverse property and the assumption `a - b ≃ 0` to replace
`a` with `b`.
-/
theorem sub_eqv_zero {a b : ℤ} : a - b ≃ 0 ↔ a ≃ b := by
  apply Iff.intro
  case mp =>
    intro (_ : a - b ≃ 0)
    show a ≃ b
    calc
      a              ≃ _ := Rel.symm AA.identR
      a + 0          ≃ _ := AA.substR (Rel.symm AA.inverseL)
      a + (-b + b)   ≃ _ := Rel.symm AA.assoc
      (a + (-b)) + b ≃ _ := AA.substL (Rel.symm sub_defn)
      (a - b) + b    ≃ _ := AA.substL ‹a - b ≃ 0›
      0 + b          ≃ _ := AA.identL
      b              ≃ _ := Rel.refl
  case mpr =>
    intro (_ : a ≃ b)
    show a - b ≃ 0
    calc
      a - b    ≃ _ := AA.substL ‹a ≃ b›
      b - b    ≃ _ := sub_defn
      b + (-b) ≃ _ := AA.inverseR
      0        ≃ _ := Rel.refl

/--
Multiplication distributes over subtraction (on the left).

**Property and proof intuition**: This is the same as multiplication
distributing over addition: just expand the definition of subtraction.
-/
theorem mul_distribL_sub {a b c : ℤ} : a * (b - c) ≃ a * b - a * c := calc
  a * (b - c)      ≃ _ := AA.substR sub_defn
  a * (b + -c)     ≃ _ := AA.distribL
  a * b + a * -c   ≃ _ := AA.substR (Rel.symm AA.scompatR)
  a * b + -(a * c) ≃ _ := Rel.symm sub_defn
  a * b - a * c    ≃ _ := Rel.refl

def mul_distributiveL_sub
    : AA.DistributiveOn Hand.L (α := ℤ) (· * ·) (· - ·)
    := {
  distrib := mul_distribL_sub
}

instance mul_distributive_sub : AA.Distributive (α := ℤ) (· * ·) (· - ·) := {
  distributiveL := mul_distributiveL_sub
  distributiveR := AA.distributiveR_from_distributiveL mul_distributiveL_sub
}

/--
Multiplication by a nonzero value on the left is injective.

**Property and proof intuition**: Viewing multiplication as a scaling
operation, this says that if two values are equivalent after being scaled by
the same amount, then their unscaled values must have been equivalent as well.
This seems to be consistent with our intuitive understanding of multiplication.
-/
def mul_cancelL {a b c : ℤ} : a ≄ 0 → a * b ≃ a * c → b ≃ c := by
  intro (_ : a ≄ 0) (_ : a * b ≃ a * c)
  show b ≃ c
  have : a * b - a * c ≃ 0 := sub_eqv_zero.mpr ‹a * b ≃ a * c›
  have : a * (b - c) ≃ 0 := Rel.trans AA.distribL ‹a * b - a * c ≃ 0›
  have : a ≃ 0 ∨ b - c ≃ 0 := mul_split_zero.mp ‹a * (b - c) ≃ 0›
  match ‹a ≃ 0 ∨ b - c ≃ 0› with
  | Or.inl (_ : a ≃ 0) =>
    show b ≃ c
    exact absurd ‹a ≃ 0› ‹a ≄ 0›
  | Or.inr (_ : b - c ≃ 0) =>
    show b ≃ c
    exact sub_eqv_zero.mp ‹b - c ≃ 0›

def mul_cancellativeL
    : AA.CancellativeOn Hand.L (α := ℤ) (· * ·) (· ≄ 0) (· ≃ ·) (· ≃ ·)
    := {
  cancel := mul_cancelL
}

instance mul_cancellative
    : AA.Cancellative (α := ℤ) (· * ·) (· ≄ 0) (· ≃ ·) (· ≃ ·)
    := {
  cancellativeL := mul_cancellativeL
  cancellativeR := AA.cancelR_from_cancelL mul_cancellativeL
}

end Lean4Axiomatic.Integer
