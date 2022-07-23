import Lean4Axiomatic.Integer.Core

namespace Lean4Axiomatic.Integer.Impl.Derived

/-! # Integer properties derived from `Core.Base` -/

variable {ℕ : Type}
variable [Natural ℕ]
variable {ℤ : Type}
variable [Core.Base ℕ ℤ]

/--
The integer one is not the same as the integer zero.

**Proof intuition**: All the laws of algebra for integers continue to hold if
`0 ≃ 1` (see [zero ring](https://en.wikipedia.org/wiki/Zero_ring)), so we need
to use a non-algebraic fact. This is provided by the mapping from natural
numbers to integers, specifically its injectivity which allows us to translate
the property that a successor is never the same as zero into the integers.
-/
theorem one_neqv_zero : (1 : ℤ) ≄ 0 := by
  intro (_ : (1 : ℤ) ≃ 0)
  show False
  have : ↑(1 : ℕ) ≃ ↑(0 : ℕ) := ‹(1 : ℤ) ≃ 0›
  have : (1 : ℕ) ≃ 0 := AA.inject ‹↑(1 : ℕ) ≃ ↑(0 : ℕ)›
  have : Natural.step (0 : ℕ) ≃ 0 :=
    Rel.trans (Rel.symm Natural.literal_step) ‹(1 : ℕ) ≃ 0›
  exact absurd ‹Natural.step (0 : ℕ) ≃ 0› Natural.step_neq_zero

instance core : Core.Derived ℕ ℤ := {
  one_neqv_zero := one_neqv_zero
}

end Lean4Axiomatic.Integer.Impl.Derived
