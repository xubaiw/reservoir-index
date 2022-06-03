import Lean4Axiomatic.Natural.Sign

namespace Lean4Axiomatic.Natural.Derived

variable {ℕ : Type}
variable [Core ℕ]
variable [Axioms.Derived ℕ]
variable [Addition.Derived ℕ]
variable [Sign.Base ℕ]

namespace Base
export Sign (Positive positive_add positive_step)
end Base

open Base (Positive)

theorem positive_subst {n₁ n₂ : ℕ} : n₁ ≃ n₂ → Positive n₁ → Positive n₂ := by
  intro (_ : n₁ ≃ n₂) (_ : Positive n₁)
  show Positive n₂
  have : n₁ ≄ 0 := Sign.Base.positive_defn.mp ‹Positive n₁›
  apply Sign.Base.positive_defn.mpr
  show n₂ ≄ 0
  exact AA.substL (self := AA.neq_substL) ‹n₁ ≃ n₂› ‹n₁ ≄ 0›

instance positive_substitutive
    : AA.Substitutive₁ (α := ℕ) Positive (· ≃ ·) (· → ·) where
  subst₁ := positive_subst

theorem positive_step {n : ℕ} : Positive n → ∃ m : ℕ, step m ≃ n := by
  apply Axioms.cases_on (motive := λ n => Positive n → ∃ m, step m ≃ n) n
  case zero =>
    intro (_ : Positive (0 : ℕ))
    apply False.elim
    show False
    have : 0 ≄ 0 := Sign.Base.positive_defn.mp ‹Positive (0 : ℕ)›
    apply this
    show 0 ≃ 0
    exact Rel.refl
  case step =>
    intro n (_ : Positive (step n))
    exists n
    show step n ≃ step n
    exact Rel.refl

theorem positive_add {n m : ℕ} : Positive n → Positive (n + m) := by
  intro (_ : Positive n)
  show Positive (n + m)
  apply Axioms.cases_on (motive := λ m => Positive (n + m)) m
  case zero =>
    show Positive (n + 0)
    apply AA.subst₁ (rβ := (· → ·)) (Rel.symm Addition.add_zero)
    exact ‹Positive n›
  case step =>
    intro m
    show Positive (n + step m)
    apply AA.subst₁ (rβ := (· → ·)) (Rel.symm Addition.add_step)
    show Positive (step (n + m))
    apply Sign.Base.positive_defn.mpr
    show step (n + m) ≄ 0
    exact Axioms.step_neq_zero

instance sign_derived : Sign.Derived ℕ where
  positive_substitutive := positive_substitutive
  positive_step := positive_step
  positive_add := positive_add

end Lean4Axiomatic.Natural.Derived
