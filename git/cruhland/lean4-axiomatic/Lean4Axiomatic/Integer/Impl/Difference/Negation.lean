import Lean4Axiomatic.Integer.Impl.Difference.Addition

namespace Lean4Axiomatic.Integer.Impl.Difference

/-! ## Negation of formal differences -/

variable {ℕ : Type}
variable [Natural ℕ]

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
Every natural number difference is equivalent to exactly one of the following:
* zero;
* a positive natural number;
* the negation of a positive natural number.

**Proof intuition**: This property is equivalent to the trichotomy of order on
the natural number components of differences. Given a difference `n——m`, it is
equal to
* zero when `n ≃ m`;
* a positive natural number when `n > m`;
* the negation of a positive natural number when `n < m`.

The whole proof is just translating from one form of trichotomy into the other.
-/
theorem trichotomy
    {a : Difference ℕ}
    : AA.ExactlyOneOfThree
      (a ≃ 0)
      (∃ (k : ℕ), Natural.Positive k ∧ a ≃ k)
      (∃ (k : ℕ), Natural.Positive k ∧ a ≃ -k)
    := by
  revert a; intro (n——m)
  show AA.ExactlyOneOfThree
    (n——m ≃ 0——0)
    (∃ (k : ℕ), Natural.Positive k ∧ n——m ≃ k——0)
    (∃ (k : ℕ), Natural.Positive k ∧ n——m ≃ 0——k)
  have natOrderTri : AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m) :=
    Natural.trichotomy n m
  apply AA.ExactlyOneOfThree.mk
  case atLeastOne =>
    show AA.OneOfThree
      (n + 0 ≃ 0 + m)
      (∃ (k : ℕ), Natural.Positive k ∧ n + 0 ≃ k + m)
      (∃ (k : ℕ), Natural.Positive k ∧ n + k ≃ 0 + m)
    match natOrderTri.atLeastOne with
    | AA.OneOfThree.first (_ : n < m) =>
      have : ∃ k, Natural.Positive k ∧ n + k ≃ 0 + m := lt_eqv.mp ‹n < m›
      exact AA.OneOfThree.third this
    | AA.OneOfThree.second (_ : n ≃ m) =>
      have : n + 0 ≃ 0 + m := eq_eqv.mp ‹n ≃ m›
      exact AA.OneOfThree.first this
    | AA.OneOfThree.third (_ : n > m) =>
      have : ∃ k, Natural.Positive k ∧ n + 0 ≃ k + m := gt_eqv.mp ‹n > m›
      exact AA.OneOfThree.second this
  case atMostOne =>
    intro (h : AA.TwoOfThree
      (n + 0 ≃ 0 + m)
      (∃ (k : ℕ), Natural.Positive k ∧ n + 0 ≃ k + m)
      (∃ (k : ℕ), Natural.Positive k ∧ n + k ≃ 0 + m))
    have twoOfThree : AA.TwoOfThree (n < m) (n ≃ m) (n > m) := match h with
      | AA.TwoOfThree.oneAndTwo h₁ h₂ =>
          AA.TwoOfThree.twoAndThree (eq_eqv.mpr h₁) (gt_eqv.mpr h₂)
      | AA.TwoOfThree.oneAndThree h₁ h₃ =>
          AA.TwoOfThree.oneAndTwo (lt_eqv.mpr h₃) (eq_eqv.mpr h₁)
      | AA.TwoOfThree.twoAndThree h₂ h₃ =>
          AA.TwoOfThree.oneAndThree (lt_eqv.mpr h₃) (gt_eqv.mpr h₂)
    show False
    have notTwoOfThree : ¬ AA.TwoOfThree (n < m) (n ≃ m) (n > m) :=
      natOrderTri.atMostOne
    exact absurd twoOfThree notTwoOfThree
where
  eq_eqv {n m : ℕ} : n ≃ m ↔ n + 0 ≃ 0 + m := by
    apply Iff.intro
    case mp =>
      intro (_ : n ≃ m)
      show n + 0 ≃ 0 + m
      calc
        n + 0 ≃ _ := Natural.add_zero
        n     ≃ _ := ‹n ≃ m›
        m     ≃ _ := Rel.symm Natural.zero_add
        0 + m ≃ _ := Rel.refl
    case mpr =>
      intro (_ : n + 0 ≃ 0 + m)
      show n ≃ m
      calc
        n     ≃ _ := Rel.symm Natural.add_zero
        n + 0 ≃ _ := ‹n + 0 ≃ 0 + m›
        0 + m ≃ _ := Natural.zero_add
        m     ≃ _ := Rel.refl

  lt_eqv
      {n m : ℕ}
      : n < m ↔ ∃ (k : ℕ), Natural.Positive k ∧ n + k ≃ 0 + m
      := by
    apply Iff.intro
    case mp =>
      intro (_ : n < m)
      show ∃ (k : ℕ), Natural.Positive k ∧ n + k ≃ 0 + m
      have (Exists.intro k (p : Natural.Positive k ∧ m ≃ n + k)) :=
        Natural.lt_defn_add.mp ‹n < m›
      have (And.intro (_ : Natural.Positive k) (_ : m ≃ n + k)) := p
      have : 0 + m ≃ n + k := Rel.trans Natural.zero_add ‹m ≃ n + k›
      exists k
      show Natural.Positive k ∧ n + k ≃ 0 + m
      exact And.intro ‹Natural.Positive k› (Rel.symm ‹0 + m ≃ n + k›)
    case mpr =>
      intro (Exists.intro k (p : Natural.Positive k ∧ n + k ≃ 0 + m))
      have (And.intro (_ : Natural.Positive k) (_ : n + k ≃ 0 + m)) := p
      show n < m
      apply Natural.lt_defn_add.mpr
      exists k
      show Natural.Positive k ∧ m ≃ n + k
      have : n + k ≃ m := Rel.trans ‹n + k ≃ 0 + m› Natural.zero_add
      exact And.intro ‹Natural.Positive k› (Rel.symm ‹n + k ≃ m›)

  gt_eqv
      {n m : ℕ}
      : n > m ↔ ∃ (k : ℕ), Natural.Positive k ∧ n + 0 ≃ k + m
      := by
    apply Iff.intro
    case mp =>
      intro (_ : m < n)
      show ∃ (k : ℕ), Natural.Positive k ∧ n + 0 ≃ k + m
      have (Exists.intro k (p : Natural.Positive k ∧ m + k ≃ 0 + n)) :=
        lt_eqv.mp ‹m < n›
      have (And.intro (_ : Natural.Positive k) (_ : m + k ≃ 0 + n)) := p
      exists k
      show Natural.Positive k ∧ n + 0 ≃ k + m
      have : k + m ≃ n + 0 :=
        Rel.trans AA.comm (Rel.trans ‹m + k ≃ 0 + n› AA.comm)
      exact And.intro ‹Natural.Positive k› (Rel.symm ‹k + m ≃ n + 0›)
    case mpr =>
      intro (Exists.intro k (p : Natural.Positive k ∧ n + 0 ≃ k + m))
      have (And.intro (_ : Natural.Positive k) (_ : n + 0 ≃ k + m)) := p
      show m < n
      apply lt_eqv.mpr
      exists k
      show Natural.Positive k ∧ m + k ≃ 0 + n
      have : 0 + n ≃ m + k :=
        Rel.trans AA.comm (Rel.trans ‹n + 0 ≃ k + m› AA.comm)
      exact And.intro ‹Natural.Positive k› (Rel.symm ‹0 + n ≃ m + k›)

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
  calc
    (m + n) + 0 ≃ _ := AA.identR
    m + n       ≃ _ := AA.comm
    n + m       ≃ _ := Rel.symm AA.identL
    0 + (n + m) ≃ _ := Rel.refl

def neg_inverseL : AA.InverseOn Hand.L (α := Difference ℕ) (-·) (· + ·) := {
  inverse := neg_invL
}

def neg_inverse : AA.Inverse (α := Difference ℕ) (-·) (· + ·) := {
  inverseL := neg_inverseL
  inverseR := AA.inverseR_from_inverseL neg_inverseL
}

def negation : Negation.Base ℕ (Difference ℕ) := {
  negOp := negOp
  neg_substitutive := neg_substitutive
  trichotomy := trichotomy
  neg_inverse := neg_inverse
}

end Lean4Axiomatic.Integer.Impl.Difference
