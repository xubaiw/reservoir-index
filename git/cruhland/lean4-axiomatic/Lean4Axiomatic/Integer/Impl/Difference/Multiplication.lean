import Lean4Axiomatic.Integer.Impl.Difference.Core

namespace Lean4Axiomatic.Integer.Impl.Difference

/-! ## Multiplication of formal differences -/

variable {ℕ : Type}
variable [Natural ℕ]

/--
Multiplication of differences.

**Definition intuition**: Geometry might be the best way to understand this
definition. Let's interpret each difference as the sum of a _positive_ value
(on the left) and a _negative_ value (on the right). Visualize this as a line
segment divided into two subsegments, colored black and red, with lengths
proportional to the positive and negative parts of the difference,
respectively.

The multiplication of two differences is then represented by a rectangle, where
each difference gets a dimension. The rectangle is divided into four smaller
rectangles, one for each combination of subsegments. The four regions are
colored according to the rules for multiplication of signs: if both sides of a
region are the same color, the region is colored black; if they are different
colors, the region is colored red. The difference in area between the black and
red regions is the result of the multiplication.
-/
def mul : Difference ℕ → Difference ℕ → Difference ℕ
| a——b, c——d => (a * c + b * d)——(a * d + b * c)

instance mulOp : Mul (Difference ℕ) := {
  mul := mul
}

/--
Multiplication of natural number differences is commutative.

**Proof intuition**: Expand definitions to see that we need to show the
equivalence of two differences of natural number sums of products. The left and
right elements of the differences are directly equivalent via commutativity of
natural number addition and multiplication, so convert the differences into
ordered pairs and use commutativity element-wise.
-/
theorem mul_comm {a b : Difference ℕ} : a * b ≃ b * a := by
  revert a; intro (n——m); revert b; intro (k——j)
  show n——m * k——j ≃ k——j * n——m
  show (n * k + m * j)——(n * j + m * k) ≃ (k * n + j * m)——(k * m + j * n)
  show from_prod (n * k + m * j, n * j + m * k)
     ≃ from_prod (k * n + j * m, k * m + j * n)
  apply AA.subst₁
  show (n * k + m * j, n * j + m * k) ≃ (k * n + j * m, k * m + j * n)
  calc
    (n * k + m * j, n * j + m * k) ≃ _ := AA.substL (AA.substL AA.comm)
    (k * n + m * j, n * j + m * k) ≃ _ := AA.substL (AA.substR AA.comm)
    (k * n + j * m, n * j + m * k) ≃ _ := AA.substR (AA.substL AA.comm)
    (k * n + j * m, j * n + m * k) ≃ _ := AA.substR (AA.substR AA.comm)
    (k * n + j * m, j * n + k * m) ≃ _ := AA.substR AA.comm
    (k * n + j * m, k * m + j * n) ≃ _ := Rel.refl

instance mul_commutative : AA.Commutative (α := Difference ℕ) (· * ·) := {
  comm := mul_comm
}

/--
Multiplying the same difference on the right of two equivalent differences
preserves their equivalence.

**Proof intuition**: The property is already intuitively true; imagine
stretching two line segments of the same length by the same amount. So the
proof just expands all definitions into equalities of sums of products of
natural numbers, and performs algebra to obtain the desired result.
-/
theorem mul_substL {a₁ a₂ b : Difference ℕ} : a₁ ≃ a₂ → a₁ * b ≃ a₂ * b := by
  revert a₁; intro (n——m); revert a₂; intro (k——j); revert b; intro (p——q)
  intro (_ : n——m ≃ k——j)
  have h : n + j ≃ k + m := ‹n——m ≃ k——j›
  show n——m * p——q ≃ k——j * p——q
  show (n * p + m * q)——(n * q + m * p) ≃ (k * p + j * q)——(k * q + j * p)
  show (n * p + m * q) + (k * q + j * p) ≃ (k * p + j * q) + (n * q + m * p)
  calc
    (n * p + m * q) + (k * q + j * p) ≃ _ := Rel.symm expand_swap
    (n + j) * p     + (k + m) * q     ≃ _ := AA.substL (AA.substL h)
    (k + m) * p     + (k + m) * q     ≃ _ := AA.substR (AA.substL (Rel.symm h))
    (k + m) * p     + (n + j) * q     ≃ _ := expand_swap
    (k * p + j * q) + (n * q + m * p) ≃ _ := Rel.refl
where
  expand_swap
      {u v w x y z : ℕ}
      : (w + x) * u + (y + z) * v ≃ (w * u + z * v) + (y * v + x * u)
      := calc
    (w + x) * u     + (y + z) * v     ≃ _ := AA.substL AA.distribR
    (w * u + x * u) + (y + z) * v     ≃ _ := AA.substR AA.distribR
    (w * u + x * u) + (y * v + z * v) ≃ _ := AA.expr_xxfxxff_lr_swap_rr
    (w * u + z * v) + (y * v + x * u) ≃ _ := Rel.refl

def mul_substitutiveL
    : AA.SubstitutiveOn
      Hand.L (α := Difference ℕ) (· * ·) AA.tc (· ≃ ·) (· ≃ ·) := {
  subst₂ := λ (_ : True) => mul_substL
}

def mul_substitutive
    : AA.Substitutive₂ (α := Difference ℕ) (· * ·) AA.tc (· ≃ ·) (· ≃ ·) := {
  substitutiveL := mul_substitutiveL
  substitutiveR := AA.substR_from_substL_swap (rS := (· ≃ ·)) mul_substitutiveL
}

def multiplication : Multiplication.Base (Difference ℕ) := {
  mulOp := mulOp
  mul_commutative := mul_commutative
  mul_substitutive := mul_substitutive
}

end Lean4Axiomatic.Integer.Impl.Difference
