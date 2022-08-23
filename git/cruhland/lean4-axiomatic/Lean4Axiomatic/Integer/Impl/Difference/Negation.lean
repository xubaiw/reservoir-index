import Lean4Axiomatic.Integer.Impl.Difference.Addition

namespace Lean4Axiomatic.Integer.Impl.Difference

/-! ## Negation of formal differences -/

variable {ℕ : Type} [Natural ℕ]

open Signed (Positive)

/--
Negation of differences.

**Definition intuition**: It's easiest to use the "directed gap" interpretation
of differences to see this. If `a——b` represents the process of traveling from
`a` to `b`, then its negation should represent the opposite process: traveling
from `b` to `a`.
-/
def neg : Difference ℕ → Difference ℕ
| a——b => b——a

instance negOp : Neg (Difference ℕ) := {
  neg := neg
}

/--
Negating two equivalent differences preserves their equivalence.

**Property intuition**: For negation to make sense as an operation (i.e., have
a consistent definition as a function) on integers, this property must be true.

**Proof intuition**: Nothing too insightful here, it's just expanding the
definitions of negation and equality and performing some algebra.
-/
theorem neg_subst {a₁ a₂ : Difference ℕ} : a₁ ≃ a₂ → -a₁ ≃ -a₂ := by
  revert a₁; intro (n——m); revert a₂; intro (k——j)
  intro (_ : n——m ≃ k——j)
  show -(n——m) ≃ -(k——j)
  have : n + j ≃ k + m := ‹n——m ≃ k——j›
  show m——n ≃ j——k
  show m + k ≃ j + n
  calc
    m + k ≃ _ := AA.comm
    k + m ≃ _ := Rel.symm ‹n + j ≃ k + m›
    n + j ≃ _ := AA.comm
    j + n ≃ _ := Rel.refl

def neg_substitutive
    : AA.Substitutive₁ (α := Difference ℕ) (-·) (· ≃ ·) (· ≃ ·)
    := {
  subst₁ := neg_subst
}

/--
The negation of a natural number difference is that difference's left additive
inverse.

**Property intuition**: This property is pretty much why the integers are a
useful concept in the first place.

**Proof intuition**: Negation swaps the elements of a difference, so adding a
difference to its negation will result in a difference with equal elements. All
differences with equal elements represent zero.
-/
theorem neg_invL {a : Difference ℕ} : (-a) + a ≃ 0 := by
  revert a; intro (n——m)
  show -(n——m) + n——m ≃ 0——0
  show m——n + n——m ≃ 0——0
  show (m + n)——(n + m) ≃ 0——0
  show (m + n) + 0 ≃ 0 + (n + m)
  apply Natural.add_swapped_zeros_eqv.mpr
  show m + n ≃ n + m
  exact AA.comm

def neg_inverseL : AA.InverseOn Hand.L (α := Difference ℕ) (-·) (· + ·) := {
  inverse := neg_invL
}

def neg_inverse : AA.Inverse (α := Difference ℕ) (-·) (· + ·) := {
  inverseL := neg_inverseL
  inverseR := AA.inverseR_from_inverseL neg_inverseL
}

instance negation : Negation ℕ (Difference ℕ) := {
  negOp := negOp
  neg_substitutive := neg_substitutive
  neg_inverse := neg_inverse
}

end Lean4Axiomatic.Integer.Impl.Difference
