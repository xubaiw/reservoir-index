import Lean4Axiomatic.Integer.Impl.Difference.Addition

namespace Lean4Axiomatic.Integer.Impl.Difference

/-! ## Multiplication of formal differences -/

variable {ℕ : Type} [Natural ℕ]

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

/--
The natural number difference `1` is a left multiplicative identity element.

**Property intuition**: A sum of a single value produces that same value.

**Proof intuition**: Not sure there's any deep insight here, the proof is the
standard formula of (1) expand definitions and (2) algebra.
-/
theorem mul_identL {a : Difference ℕ} : 1 * a ≃ a := by
  revert a; intro (n——m)
  show 1——0 * n——m ≃ n——m
  show (1 * n + 0 * m)——(1 * m + 0 * n) ≃ n——m
  show from_prod (1 * n + 0 * m, 1 * m + 0 * n) ≃ from_prod (n, m)
  apply AA.subst₁
  show (1 * n + 0 * m, 1 * m + 0 * n) ≃ (n, m)
  calc
    (1 * n + 0 * m, 1 * m + 0 * n) ≃ _ := AA.substL (AA.substL AA.identL)
    (n + 0 * m, 1 * m + 0 * n)     ≃ _ := AA.substL (AA.substR AA.absorbL)
    (n + 0, 1 * m + 0 * n)         ≃ _ := AA.substR (AA.substL AA.identL)
    (n + 0, m + 0 * n)             ≃ _ := AA.substR (AA.substR AA.absorbL)
    (n + 0, m + 0)                 ≃ _ := AA.substL AA.identR
    (n, m + 0)                     ≃ _ := AA.substR AA.identR
    (n, m)                         ≃ _ := Rel.refl

def mul_identityL : AA.IdentityOn Hand.L (α := Difference ℕ) 1 (· * ·) := {
  ident := mul_identL
}

def mul_identity : AA.Identity (α := Difference ℕ) 1 (· * ·) := {
  identityL := mul_identityL
  identityR := AA.identityR_from_identityL mul_identityL
}

/--
Multiplication on the left distributes over addition.

**Property intuition**

If we think of natural number differences as 1-dimensional vectors representing
the distance and direction to get from their first component to their second
component, then addition of differences is just the sum of vectors (magnitudes
and directions combine and some cancellation may occur) and multiplication of
differences is scaling, with a change in direction if the signs are opposite.

With that interpretation, this property then says that adding (combining) two
differences and multiplying (scaling with direction) the result is the same as
multiplying each difference before adding them. Geometrically this seems
plausible.

**Proof intuition**

After all definitions are expanded, the resulting equivalence of differences
turns out to follow from the "pointwise" equivalence of their components. So
the proof can be split into two cases, each of which follows from the same
algebraic identity on natural numbers.
-/
theorem mul_distribL {a b c : Difference ℕ} : a * (b + c) ≃ a * b + a * c := by
  revert a; intro (q——p); revert b; intro (n——m); revert c; intro (k——j)
  show q——p * (n——m + k——j) ≃ q——p * n——m + q——p * k——j
  let n_k := n + k; let m_j := m + j
  let qn := q * n; let qm := q * m; let qk := q * k; let qj := q * j
  let pn := p * n; let pm := p * m; let pk := p * k; let pj := p * j
  show q——p * n_k——m_j ≃ (qn + pm)——(qm + pn) + (qk + pj)——(qj + pk)
  show (q * n_k + p * m_j)——(q * m_j + p * n_k)
     ≃ ((qn + pm) + (qk + pj))——((qm + pn) + (qj + pk))
  show from_prod (q * n_k + p * m_j, q * m_j + p * n_k)
     ≃ from_prod ((qn + pm) + (qk + pj), (qm + pn) + (qj + pk))
  apply AA.subst₁
  show (q * n_k + p * m_j, q * m_j + p * n_k)
     ≃ ((qn + pm) + (qk + pj), (qm + pn) + (qj + pk))
  apply Relation.Equivalence.Impl.Prod.eqv_defn.mpr
  show q * n_k + p * m_j ≃ (qn + pm) + (qk + pj)
     ∧ q * m_j + p * n_k ≃ (qm + pn) + (qj + pk)
  have distrib_swap (w x y z : ℕ)
      : q * (w + y) + p * (x + z) ≃ (q * w + p * x) + (q * y + p * z)
      := calc
    q * (w + y) + p * (x + z)         ≃ _ := AA.substL AA.distribL
    (q * w + q * y) + p * (x + z)     ≃ _ := AA.substR AA.distribL
    (q * w + q * y) + (p * x + p * z) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (q * w + p * x) + (q * y + p * z) ≃ _ := Rel.refl
  apply And.intro
  · show q * n_k + p * m_j ≃ (qn + pm) + (qk + pj)
    exact distrib_swap n m k j
  · show q * m_j + p * n_k ≃ (qm + pn) + (qj + pk)
    exact distrib_swap m n j k

def mul_distributiveL
    : AA.DistributiveOn Hand.L (α := Difference ℕ) (· * ·) (· + ·)
    := {
  distrib := mul_distribL
}

def mul_distributive : AA.Distributive (α := Difference ℕ) (· * ·) (· + ·) := {
  distributiveL := mul_distributiveL
  distributiveR := AA.distributiveR_from_distributiveL mul_distributiveL
}

/--
Conversion from `ℕ` to `Difference ℕ` is compatible with multiplication.

**Proprty intuition**: One would hope this is true, otherwise we could not say
that the set of differences (integers) is a superset of the natural numbers.

**Proof intuition**: Expand definitions to see that we only need to prove
equivalence of differences element-wise. And then it's just a matter of
reducing terms to zero and removing them.
-/
theorem mul_compat_natural
    {n m : ℕ} : ↑(n * m) ≃ (↑n : Difference ℕ) * ↑m
    := by
  show (n * m)——0 ≃ (n * m + 0 * 0)——(n * 0 + 0 * m)
  show from_prod (n * m, 0) ≃ from_prod (n * m + 0 * 0, n * 0 + 0 * m)
  apply AA.subst₁
  show (n * m, 0) ≃ (n * m + 0 * 0, n * 0 + 0 * m)
  apply Rel.symm (α := ℕ × ℕ)
  show (n * m + 0 * 0, n * 0 + 0 * m) ≃ (n * m, 0)
  calc
    (n * m + 0 * 0, n * 0 + 0 * m) ≃ _ := AA.substL (AA.substR AA.absorbL)
    (n * m + 0, n * 0 + 0 * m)     ≃ _ := AA.substL Natural.add_zero
    (n * m, n * 0 + 0 * m)         ≃ _ := AA.substR (AA.substL AA.absorbR)
    (n * m, 0 + 0 * m)             ≃ _ := AA.substR Natural.zero_add
    (n * m, 0 * m)                 ≃ _ := AA.substR AA.absorbL
    (n * m, 0)                     ≃ _ := Rel.refl

def mul_compatible_from_natural
    : AA.Compatible₂ (α := ℕ) (β := Difference ℕ) (↑·) (· * ·) (· * ·)
    := {
  compat₂ := mul_compat_natural
}

instance multiplication : Multiplication ℕ (Difference ℕ) := {
  mulOp := mulOp
  mul_commutative := mul_commutative
  mul_substitutive := mul_substitutive
  mul_associative := mul_associative
  mul_identity := mul_identity
  mul_distributive := mul_distributive
  mul_compatible_from_natural := mul_compatible_from_natural
}

end Lean4Axiomatic.Integer.Impl.Difference
