import Lean4Axiomatic.Natural

namespace Lean4Axiomatic.Natural

variable {ℕ : Type}
variable [Natural ℕ]

open Signed (Positive)

/-- Convenience lemma for several integer proofs. -/
theorem add_swapped_zeros_eqv {n m : ℕ} : n + 0 ≃ 0 + m ↔ n ≃ m := by
  apply Iff.intro
  case mp =>
    intro (_ : n + 0 ≃ 0 + m)
    show n ≃ m
    calc
      n     ≃ _ := Rel.symm AA.identR
      n + 0 ≃ _ := ‹n + 0 ≃ 0 + m›
      0 + m ≃ _ := AA.identL
      m     ≃ _ := Rel.refl
  case mpr =>
    intro (_ : n ≃ m)
    show n + 0 ≃ 0 + m
    calc
      n + 0 ≃ _ := AA.identR
      n     ≃ _ := ‹n ≃ m›
      m     ≃ _ := Rel.symm AA.identL
      0 + m ≃ _ := Rel.refl

/--
Zero is the only natural number less than one.

This is a lemma to help with the proof of `sqrt1` below.
-/
theorem zero_lt_one {n : ℕ} : n < 1 ↔ n ≃ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : n < 1)
    show n ≃ 0
    have : n < step 0 := AA.substRFn Natural.literal_step ‹n < 1›
    have : n < 0 ∨ n ≃ 0 := Natural.lt_split ‹n < step 0›
    match ‹n < 0 ∨ n ≃ 0› with
    | Or.inl (_ : n < 0) => exact absurd ‹n < 0› Natural.lt_zero
    | Or.inr (_ : n ≃ 0) => exact ‹n ≃ 0›
  case mpr =>
    intro (_ : n ≃ 0)
    show n < 1
    have : (0 : ℕ) < step 0 := Natural.lt_step
    have : n < step 0 := AA.substLFn (Rel.symm ‹n ≃ 0›) ‹(0 : ℕ) < step 0›
    have : n < 1 := AA.substRFn (Rel.symm Natural.literal_step) ‹n < step 0›
    exact ‹n < 1›

/--
The only square root of unity in the natural numbers is `1`.

**Property and proof intuition**: It can only be one, because zero squared is
zero, and squaring any natural number greater than one always produces a larger
result.
-/
theorem sqrt1 {n : ℕ} : n * n ≃ 1 ↔ n ≃ 1 := by
  apply Iff.intro
  case mp =>
    intro (_ : n * n ≃ 1)
    show n ≃ 1
    have tri_n_1 : AA.ExactlyOneOfThree (n < 1) (n ≃ 1) (n > 1) :=
      Natural.trichotomy n 1
    match tri_n_1.atLeastOne with
    | AA.OneOfThree.first (_ : n < 1) =>
      apply False.elim
      show False
      have : n ≃ 0 := zero_lt_one.mp ‹n < 1›
      have : step 0 ≃ 0 := calc
        step 0  ≃ _ := Rel.symm Natural.literal_step
        1       ≃ _ := Rel.symm ‹n * n ≃ 1›
        n * n   ≃ _ := AA.substL ‹n ≃ 0›
        0 * n   ≃ _ := AA.absorbL
        0       ≃ _ := Rel.refl
      exact absurd ‹step (0 : ℕ) ≃ 0› Natural.step_neq_zero
    | AA.OneOfThree.second (_ : n ≃ 1) =>
      exact ‹n ≃ 1›
    | AA.OneOfThree.third (_ : n > 1) =>
      apply False.elim
      show False
      apply tri_n_1.atMostOne
      show AA.TwoOfThree (n < 1) (n ≃ 1) (n > 1)
      have : step 0 < n := AA.substLFn Natural.literal_step ‹1 < n›
      have : 0 < n := Rel.trans Natural.lt_step ‹step 0 < n›
      have : Positive n := Natural.lt_zero_pos.mpr ‹0 < n›
      have : 1 * n < n * n := AA.substLC ‹Positive n› ‹1 < n›
      have : n < n * n := AA.substLFn AA.identL ‹1 * n < n * n›
      have : n < 1 := AA.substRFn ‹n * n ≃ 1› ‹n < n * n›
      exact AA.TwoOfThree.oneAndThree ‹n < 1› ‹n > 1›
  case mpr =>
    intro (_ : n ≃ 1)
    show n * n ≃ 1
    calc
      n * n ≃ _ := AA.substL ‹n ≃ 1›
      1 * n ≃ _ := AA.identL
      n     ≃ _ := ‹n ≃ 1›
      1     ≃ _ := Rel.refl

end Lean4Axiomatic.Natural
