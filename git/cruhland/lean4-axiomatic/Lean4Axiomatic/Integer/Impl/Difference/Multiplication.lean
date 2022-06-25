import Lean4Axiomatic.Integer.Impl.Difference.Core
import Lean4Axiomatic.Relation.Equivalence

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

/--
Multiplication of natural number differences is associative.

**Intuition**: It's not really clear why the property is true, or if there's a
clear principle behind the proof; brute force definition expansion and algebra
get the job done anyway.
-/
theorem mul_assoc {a b c : Difference ℕ} : (a * b) * c ≃ a * (b * c) := by
  revert a; intro (q——p); revert b; intro (n——m); revert c; intro (k——j)
  show (q——p * n——m) * k——j ≃ q——p * (n——m * k——j)
  let qn_pm := q * n + p * m
  let qm_pn := q * m + p * n
  let nk_mj := n * k + m * j
  let nj_mk := n * j + m * k
  show qn_pm——qm_pn * k——j ≃ q——p * nk_mj——nj_mk
  show (qn_pm * k + qm_pn * j)——(qn_pm * j + qm_pn * k)
     ≃ (q * nk_mj + p * nj_mk)——(q * nj_mk + p * nk_mj)
  show from_prod (qn_pm * k + qm_pn * j, qn_pm * j + qm_pn * k)
     ≃ from_prod (q * nk_mj + p * nj_mk, q * nj_mk + p * nk_mj)
  apply AA.subst₁
  show (qn_pm * k + qm_pn * j, qn_pm * j + qm_pn * k)
     ≃ (q * nk_mj + p * nj_mk, q * nj_mk + p * nk_mj)
  apply Relation.Equivalence.Impl.Prod.eqv_defn.mpr
  show qn_pm * k + qm_pn * j ≃ q * nk_mj + p * nj_mk
     ∧ qn_pm * j + qm_pn * k ≃ q * nj_mk + p * nk_mj
  have redistribute (x y : ℕ)
      : (q * n + p * m) * x + (q * m + p * n) * y
      ≃  q * (n * x + m * y) + p * (n * y + m * x)
      := calc
    (q * n + p * m) * x + (q * m + p * n) * y
      ≃ _ := AA.substL AA.distribR
    (q * n) * x + (p * m) * x + (q * m + p * n) * y
      ≃ _ := AA.substR AA.distribR
    (q * n) * x + (p * m) * x + ((q * m) * y + (p * n) * y)
      ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (q * n) * x + (q * m) * y + ((p * m) * x + (p * n) * y)
      ≃ _ := AA.substR AA.comm
    (q * n) * x + (q * m) * y + ((p * n) * y + (p * m) * x)
      ≃ _ := AA.substL (AA.substL AA.assoc)
    q * (n * x) + (q * m) * y + ((p * n) * y + (p * m) * x)
      ≃ _ := AA.substL (AA.substR AA.assoc)
    q * (n * x) + q * (m * y) + ((p * n) * y + (p * m) * x)
      ≃ _ := AA.substR (AA.substL AA.assoc)
    q * (n * x) + q * (m * y) + (p * (n * y) + (p * m) * x)
      ≃ _ := AA.substR (AA.substR AA.assoc)
    q * (n * x) + q * (m * y) + (p * (n * y) + p * (m * x))
      ≃ _ := AA.substL (Rel.symm AA.distribL)
    q * (n * x + m * y) + (p * (n * y) + p * (m * x))
      ≃ _ := AA.substR (Rel.symm AA.distribL)
    q * (n * x + m * y) + p * (n * y + m * x)
      ≃ _ := Rel.refl
  apply And.intro
  · show qn_pm * k + qm_pn * j ≃ q * nk_mj + p * nj_mk
    exact redistribute k j
  · show qn_pm * j + qm_pn * k ≃ q * nj_mk + p * nk_mj
    exact redistribute j k

def mul_associative : AA.Associative (α := Difference ℕ) (· * ·) := {
  assoc := mul_assoc
}

def multiplication : Multiplication.Base (Difference ℕ) := {
  mulOp := mulOp
  mul_commutative := mul_commutative
  mul_substitutive := mul_substitutive
  mul_associative := mul_associative
}

end Lean4Axiomatic.Integer.Impl.Difference
