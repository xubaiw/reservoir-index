import Lean4Axiomatic.Natural.Addition
import Lean4Axiomatic.Natural.Multiplication
import Lean4Axiomatic.Natural.Sign

namespace Lean4Axiomatic.Natural.Derived

/-!
# Natural number multiplication -- proofs of derived properties

These proofs are all derived from the properties in `Multiplication.Base`.
-/

variable {ℕ : Type}
variable [Core ℕ]
variable [Axioms.Derived ℕ]
variable [Addition.Derived ℕ]
variable [Multiplication.Base ℕ]

namespace Base
export Multiplication (step_mul zero_mul)
end Base

open Sign (Positive)

/--
Multiplying by zero on the right always gives zero.

Intuition: the multiplication `count * value` is defined as `count` copies of
`value` added together. So `n * 0` is `n` copies of `0` added together, which
by properties of addition must always give `0`.
-/
theorem mul_zero {n : ℕ} : n * 0 ≃ 0 := by
  apply Axioms.ind_on (motive := λ x => x * 0 ≃ 0) n
  case zero =>
    show 0 * 0 ≃ 0
    exact Base.zero_mul
  case step =>
    intro n (ih : n * 0 ≃ 0)
    show step n * 0 ≃ 0
    calc
      step n * 0 ≃ _ := Base.step_mul
      n * 0 + 0  ≃ _ := AA.substL ih
      0 + 0      ≃ _ := Addition.zero_add
      0          ≃ _ := Eqv.refl

/--
Take a product and increment the right-hand factor. This gives the same result
as adding a copy of the left-hand factor to the original product.

This is a key lemma towards proving the commutativity of multiplication. Even
though multiplication is defined as `count * value`, this result shows that it
works just as well to swap the roles of `count` and `value`.

Intuition: `n` copies of `step m` added together can be rearranged into the sum
of `n` copies of `m`, plus the sum of `n` copies of `1`. Since adding `n`
copies of `1` together is just `n`, the whole result is `n * m + n`.
-/
theorem mul_step {n m : ℕ} : n * step m ≃ n * m + n := by
  apply Axioms.ind_on (motive := λ x => x * step m ≃ x * m + x) n
  case zero =>
    show 0 * step m ≃ 0 * m + 0
    calc
      0 * step m ≃ _ := Base.zero_mul
      0          ≃ _ := Eqv.symm Addition.zero_add
      0 + 0      ≃ _ := Eqv.symm (AA.substL Base.zero_mul)
      0 * m + 0  ≃ _ := Eqv.refl
  case step =>
    intro n (ih : n * step m ≃ n * m + n)
    show step n * step m ≃ step n * m + step n
    calc
      step n * step m
    ≃ _ := Base.step_mul
      n * step m + step m
    ≃ _ := AA.substL ih
      (n * m + n) + step m
    ≃ _ := Addition.add_step
      step ((n * m + n) + m)
    ≃ _ := AA.subst₁ AA.assoc
      step (n * m + (n + m))
    ≃ _ := AA.subst₁ (AA.substR AA.comm)
      step (n * m + (m + n))
    ≃ _ := Eqv.symm (AA.subst₁ AA.assoc)
      step ((n * m + m) + n)
    ≃ _ := Eqv.symm (AA.subst₁ (AA.substL Base.step_mul))
      step (step n * m + n)
    ≃ _ := Eqv.symm Addition.add_step
      step n * m + step n
    ≃ _ := Eqv.refl

/--
The order of the factors in a product doesn't matter.

Intuition: combine the results from `mul_zero` and `mul_step`.
-/
theorem mul_comm {n m : ℕ} : n * m ≃ m * n := by
  apply Axioms.ind_on (motive := λ x => x * m ≃ m * x) n
  case zero =>
    show 0 * m ≃ m * 0
    calc
      0 * m ≃ _ := Base.zero_mul
      0     ≃ _ := Eqv.symm mul_zero
      m * 0 ≃ _ := Eqv.refl
  case step =>
    intro n (ih : n * m ≃ m * n)
    show step n * m ≃ m * step n
    calc
      step n * m ≃ _ := Base.step_mul
      n * m + m  ≃ _ := AA.substL ih
      m * n + m  ≃ _ := Eqv.symm mul_step
      m * step n ≃ _ := Eqv.refl

instance mul_commutative : AA.Commutative (α := ℕ) (· * ·) where
  comm := mul_comm

/--
Multiplication by a fixed value as the right-hand operand preserves equality.

Intuition: addition preserves equality; multiplication is repeated addition.
-/
theorem subst_mul {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ * m ≃ n₂ * m := by
  apply Axioms.ind_on (motive := λ x => ∀ y, x ≃ y → x * m ≃ y * m) n₁
  case zero =>
    intro n₂
    show 0 ≃ n₂ → 0 * m ≃ n₂ * m
    apply Axioms.cases_on (motive := λ y => 0 ≃ y → 0 * m ≃ y * m)
    case zero =>
      intro (_ : 0 ≃ (0 : ℕ))
      show 0 * m ≃ 0 * m
      exact Eqv.refl
    case step =>
      intro n₂ (_ : 0 ≃ step n₂)
      apply False.elim
      show False
      exact absurd (Eqv.symm ‹0 ≃ step n₂›) Axioms.step_neq_zero
  case step =>
    intro n₁ (ih : ∀ y, n₁ ≃ y → n₁ * m ≃ y * m) n₂
    show step n₁ ≃ n₂ → step n₁ * m ≃ n₂ * m
    apply Axioms.cases_on (motive := λ y => step n₁ ≃ y → step n₁ * m ≃ y * m)
    case zero =>
      intro (_ : step n₁ ≃ 0)
      apply False.elim
      show False
      exact absurd ‹step n₁ ≃ 0› Axioms.step_neq_zero
    case step =>
      intro n₂ (_ : step n₁ ≃ step n₂)
      show step n₁ * m ≃ step n₂ * m
      have : n₁ ≃ n₂ := AA.inject ‹step n₁ ≃ step n₂›
      have : n₁ * m ≃ n₂ * m := ih n₂ ‹n₁ ≃ n₂›
      calc
        step n₁ * m  ≃ _ := Base.step_mul
        (n₁ * m) + m ≃ _ := AA.substL ‹n₁ * m ≃ n₂ * m›
        (n₂ * m) + m ≃ _ := Eqv.symm Base.step_mul
        step n₂ * m  ≃ _ := Eqv.refl

instance mul_substL
    : AA.SubstitutiveForHand AA.Hand.L (α := ℕ) (· * ·) (· ≃ ·) (· ≃ ·) where
  subst₂ := subst_mul

instance mul_substR
    : AA.SubstitutiveForHand AA.Hand.R (α := ℕ) (· * ·) (· ≃ ·) (· ≃ ·) :=
  AA.substR_from_substL_swap mul_substL

instance mul_substitutive
    : AA.Substitutive₂ (α := ℕ) (· * ·) (· ≃ ·) (· ≃ ·) where
  substitutiveL := mul_substL
  substitutiveR := mul_substR

/--
A product is zero iff at least one of its factors is zero.

Intuition
- forwards: if one factor is nonzero, then the product is a nonempty sum that
  results in zero. By `Addition.zero_sum_split`, the terms of the sum must be
  zero.
- backwards: by `Base.zero_mul` or `Derived.mul_zero`.
-/
theorem zero_product_split {n m : ℕ} : n * m ≃ 0 ↔ n ≃ 0 ∨ m ≃ 0 := by
  apply Iff.intro
  · show n * m ≃ 0 → n ≃ 0 ∨ m ≃ 0
    apply Axioms.cases_on (motive := λ x => x * m ≃ 0 → x ≃ 0 ∨ m ≃ 0) n
    case zero =>
      intro (_ : 0 * m ≃ 0)
      show 0 ≃ 0 ∨ m ≃ 0
      exact Or.inl Eqv.refl
    case step =>
      intro n (_ : step n * m ≃ 0)
      show step n ≃ 0 ∨ m ≃ 0
      apply Or.inr
      show m ≃ 0
      have : n * m + m ≃ 0 := calc
        n * m + m ≃ _ := Eqv.symm Base.step_mul
        step n * m ≃ _ := ‹step n * m ≃ 0›
        0 ≃ _ := Eqv.refl
      have ⟨_, (_ : m ≃ 0)⟩ := Addition.zero_sum_split ‹n * m + m ≃ 0›
      exact ‹m ≃ 0›
  · intro (_ : n ≃ 0 ∨ m ≃ 0)
    show n * m ≃ 0
    apply Or.elim ‹n ≃ 0 ∨ m ≃ 0›
    · intro (_ : n ≃ 0)
      show n * m ≃ 0
      calc
        n * m ≃ _ := AA.substL ‹n ≃ 0›
        0 * m ≃ _ := Base.zero_mul
        0     ≃ _ := Eqv.refl
    · intro (_ : m ≃ 0)
      show n * m ≃ 0
      calc
        n * m ≃ _ := AA.substR ‹m ≃ 0›
        n * 0 ≃ _ := Derived.mul_zero
        0     ≃ _ := Eqv.refl

/--
The product of positive natural numbers is positive.

Intuition: reframe positive as nonzero, then contradict with
`Derived.zero_product_split`.
-/
theorem mul_positive [Sign.Base ℕ] {n m : ℕ}
    : Positive n → Positive m → Positive (n * m) := by
  intro (_ : Positive n) (_ : Positive m)
  show Positive (n * m)
  have : n ≄ 0 := Sign.positive_defn.mp ‹Positive n›
  have : m ≄ 0 := Sign.positive_defn.mp ‹Positive m›
  apply Sign.positive_defn.mpr
  show n * m ≄ 0
  intro (_ : n * m ≃ 0)
  show False
  have : n ≃ 0 ∨ m ≃ 0 := Derived.zero_product_split.mp ‹n * m ≃ 0›
  apply Or.elim ‹n ≃ 0 ∨ m ≃ 0›
  · intro (_ : n ≃ 0)
    show False
    exact absurd ‹n ≃ 0› ‹n ≄ 0›
  · intro (_ : m ≃ 0)
    show False
    exact absurd ‹m ≃ 0› ‹m ≄ 0›

/--
Multiplication on the left distributes over addition.

**Intuition**: Viewing `a * b` as the sum of `a` copies of `b`, this theorem
says that the sum of `n` copies of `m + k` is the same as the sum of `n` copies
of `m` added to the sum of `n` copies of `k`. Using the commutativity and
associativity of addition to rearrange the sums shows this is clearly true.
-/
theorem mul_distribL_add {n m k : ℕ} : n * (m + k) ≃ n * m + n * k := by
  apply Axioms.ind_on (motive := λ x => x * (m + k) ≃ x * m + x * k) n
  case zero =>
    show 0 * (m + k) ≃ 0 * m + 0 * k
    calc
      0 * (m + k)   ≃ _ := Base.zero_mul
      0             ≃ _ := Eqv.symm Addition.zero_add
      0 + 0         ≃ _ := Eqv.symm (AA.substL Base.zero_mul)
      0 * m + 0     ≃ _ := Eqv.symm (AA.substR Base.zero_mul)
      0 * m + 0 * k ≃ _ := Eqv.refl
  case step =>
    intro n (ih : n * (m + k) ≃ n * m + n * k)
    show step n * (m + k) ≃ step n * m + step n * k
    calc
      step n * (m + k)          ≃ _ := Base.step_mul
      n * (m + k) + (m + k)     ≃ _ := AA.substL ih
      n * m + n * k + (m + k)   ≃ _ := AA.assoc
      n * m + (n * k + (m + k)) ≃ _ := Eqv.symm (AA.substR AA.assoc)
      n * m + ((n * k + m) + k) ≃ _ := AA.substR (AA.substL AA.comm)
      n * m + ((m + n * k) + k) ≃ _ := AA.substR AA.assoc
      n * m + (m + (n * k + k)) ≃ _ := Eqv.symm AA.assoc
      (n * m + m) + (n * k + k) ≃ _ := Eqv.symm (AA.substL Base.step_mul)
      step n * m + (n * k + k)  ≃ _ := Eqv.symm (AA.substR Base.step_mul)
      step n * m + step n * k   ≃ _ := Eqv.refl

def mul_distributiveL : AA.DistributiveOn AA.Hand.L (α := ℕ) (· * ·) (· + ·) :=
  AA.DistributiveOn.mk mul_distribL_add

instance mul_distributive : AA.Distributive (α := ℕ) (· * ·) (· + ·) where
  distributiveL := mul_distributiveL
  distributiveR := AA.distributiveR_from_distributiveL mul_distributiveL

/--
The grouping of the factors in a product doesn't matter.

**Intuition**: Imagine a collection of identical objects arranged into a
rectangle `n * m` objects long and `k` objects high. Partition this into `m`
smaller rectangles having length `n` and height `k`. Clearly the number of
objects remains the same in both arrangements.
-/
def mul_associative : AA.Associative (α := ℕ) (· * ·) := by
  constructor
  intro n m k
  show (n * m) * k ≃ n * (m * k)
  apply Axioms.ind_on (motive := λ x => (x * m) * k ≃ x * (m * k))
  case zero =>
    show (0 * m) * k ≃ 0 * (m * k)
    calc
      (0 * m) * k ≃ _ := AA.substL Base.zero_mul
      0 * k       ≃ _ := Base.zero_mul
      0           ≃ _ := Eqv.symm Base.zero_mul
      0 * (m * k) ≃ _ := Eqv.refl
  case step =>
    intro n (ih : (n * m) * k ≃ n * (m * k))
    show (step n * m) * k ≃ step n * (m * k)
    calc
      (step n * m) * k    ≃ _ := AA.substL Base.step_mul
      (n * m + m) * k     ≃ _ := AA.distribR
      (n * m) * k + m * k ≃ _ := AA.substL ih
      n * (m * k) + m * k ≃ _ := Eqv.symm Base.step_mul
      step n * (m * k)    ≃ _ := Eqv.refl

instance multiplication_derived [Sign.Base ℕ] : Multiplication.Derived ℕ where
  mul_substitutive := mul_substitutive
  mul_zero := mul_zero
  mul_step := mul_step
  mul_commutative := mul_commutative
  zero_product_split := zero_product_split
  mul_positive := mul_positive
  mul_distributive := mul_distributive
  mul_associative := mul_associative

end Lean4Axiomatic.Natural.Derived
