import Lean4Axiomatic.Natural.Addition

namespace Lean4Axiomatic.Natural

namespace Derived

variable {ℕ : Type}
variable [Core ℕ]
variable [Axioms.Derived ℕ]
variable [Addition.Base ℕ]

theorem add_zero {n : ℕ} : n + 0 ≃ n := by
  apply Axioms.ind_on (motive := λ n => n + 0 ≃ n) n
  case zero =>
    show 0 + 0 ≃ 0
    calc
      0 + (0 : ℕ) ≃ _ := Addition.zero_add
      0           ≃ _ := Rel.refl
  case step =>
    intro n (ih : n + 0 ≃ n)
    show step n + 0 ≃ step n
    calc
      step n + 0   ≃ _ := Addition.step_add
      step (n + 0) ≃ _ := AA.subst₁ ih
      step n       ≃ _ := Rel.refl

theorem add_step {n m : ℕ} : n + step m ≃ step (n + m) := by
  apply Axioms.ind_on (motive := λ n => n + step m ≃ step (n + m)) n
  case zero =>
    show 0 + step m ≃ step (0 + m)
    calc
      0 + step m   ≃ _ := Addition.zero_add
      step m       ≃ _ := AA.subst₁ (Rel.symm Addition.zero_add)
      step (0 + m) ≃ _ := Rel.refl
  case step =>
    intro n (ih : n + step m ≃ step (n + m))
    show step n + step m ≃ step (step n + m)
    calc
      step n + step m     ≃ _ := Addition.step_add
      step (n + step m)   ≃ _ := AA.subst₁ ih
      step (step (n + m)) ≃ _ := AA.subst₁ (Rel.symm Addition.step_add)
      step (step n + m)   ≃ _ := Rel.refl

theorem add_comm {n m : ℕ} : n + m ≃ m + n := by
  apply Axioms.ind_on (motive := λ n => n + m ≃ m + n) n
  case zero =>
    show 0 + m ≃ m + 0
    calc
      0 + m ≃ _ := Addition.zero_add
      m     ≃ _ := Rel.symm add_zero
      m + 0 ≃ _ := Rel.refl
  case step =>
    intro n (ih : n + m ≃ m + n)
    show step n + m ≃ m + step n
    calc
      step n + m   ≃ _ := Addition.step_add
      step (n + m) ≃ _ := AA.subst₁ ih
      step (m + n) ≃ _ := Rel.symm add_step
      m + step n   ≃ _ := Rel.refl

instance add_commutative : AA.Commutative (α := ℕ) (· + ·) where
  comm := add_comm

theorem subst_add {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ + m ≃ n₂ + m := by
  apply Axioms.ind_on (motive := λ x => ∀ y, x ≃ y → x + m ≃ y + m) n₁
  case zero =>
    intro n₂
    show 0 ≃ n₂ → 0 + m ≃ n₂ + m
    apply Axioms.cases_on (motive := λ y => 0 ≃ y → 0 + m ≃ y + m)
    case zero =>
      intro (_ : 0 ≃ (0 : ℕ))
      show 0 + m ≃ 0 + m
      exact Rel.refl
    case step =>
      intro n₂ (_ : 0 ≃ step n₂)
      show 0 + m ≃ step n₂ + m
      apply False.elim
      show False
      exact Axioms.step_neq_zero (Rel.symm ‹0 ≃ step n₂›)
  case step =>
    intro n₁ (ih : ∀ y, n₁ ≃ y → n₁ + m ≃ y + m) n₂
    show step n₁ ≃ n₂ → step n₁ + m ≃ n₂ + m
    apply Axioms.cases_on (motive := λ y => step n₁ ≃ y → step n₁ + m ≃ y + m)
    case zero =>
      intro (_ : step n₁ ≃ 0)
      show step n₁ + m ≃ 0 + m
      apply False.elim
      show False
      exact Axioms.step_neq_zero ‹step n₁ ≃ 0›
    case step =>
      intro n₂ (_ : step n₁ ≃ step n₂)
      show step n₁ + m ≃ step n₂ + m
      have : n₁ ≃ n₂ := AA.inject ‹step n₁ ≃ step n₂›
      calc
        step n₁ + m   ≃ _ := Addition.step_add
        step (n₁ + m) ≃ _ := AA.subst₁ (ih _ ‹n₁ ≃ n₂›)
        step (n₂ + m) ≃ _ := Rel.symm Addition.step_add
        step n₂ + m   ≃ _ := Rel.refl

def add_substL
    : AA.SubstitutiveOn Hand.L (α := ℕ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·) where
  subst₂ := λ (_ : True) => subst_add

instance add_substitutive
    : AA.Substitutive₂ (α := ℕ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·) where
  substitutiveL := add_substL
  substitutiveR := AA.substR_from_substL_swap (rS := (· ≃ ·)) add_substL

theorem add_one_step {n : ℕ} : n + 1 ≃ step n := by
  calc
    n + 1        ≃ _ := AA.substR Literals.literal_step
    n + step 0   ≃ _ := add_step
    step (n + 0) ≃ _ := AA.subst₁ add_zero
    step n       ≃ _ := Rel.refl

/--
The grouping of the terms in a sum doesn't matter.

**Intuition**: the `step_add` and `add_step` properties allow `step`s to be
moved arbitrarily between terms. Given any particular grouping of a sum, all of
the `step`s can be moved over to the first term, always producing the same
result.
-/
def add_associative : AA.Associative (α := ℕ) (· + ·) := by
  constructor
  intro n m k
  show (n + m) + k ≃ n + (m + k)
  apply Axioms.ind_on (motive := λ n => (n + m) + k ≃ n + (m + k)) n
  case zero =>
    show (0 + m) + k ≃ 0 + (m + k)
    calc
      (0 + m) + k ≃ _ := AA.substL Addition.zero_add
      m + k       ≃ _ := Rel.symm Addition.zero_add
      0 + (m + k) ≃ _ := Rel.refl
  case step =>
    intro n (ih : (n + m) + k ≃ n + (m + k))
    show (step n + m) + k ≃ step n + (m + k)
    calc
      (step n + m) + k   ≃ _ := AA.substL Addition.step_add
      step (n + m) + k   ≃ _ := Addition.step_add
      step ((n + m) + k) ≃ _ := AA.subst₁ ih
      step (n + (m + k)) ≃ _ := Rel.symm Addition.step_add
      step n + (m + k)   ≃ _ := Rel.refl

/--
The right-hand sides of two equal sums are equal if their left-hand sides are.

**Proof intuition**: the left-hand sides can be removed one `step` at a time by
applying `step_injective` and finally `zero_add`, leaving the desired result.
-/
theorem cancel_add {n m k : ℕ} : n + m ≃ n + k → m ≃ k := by
  apply Axioms.ind_on (motive := λ n => n + m ≃ n + k → m ≃ k) n
  case zero =>
    intro (_ : 0 + m ≃ 0 + k)
    show m ≃ k
    calc
      m     ≃ _ := Rel.symm Addition.zero_add
      0 + m ≃ _ := ‹0 + m ≃ 0 + k›
      0 + k ≃ _ := Addition.zero_add
      k     ≃ _ := Rel.refl
  case step =>
    intro n (ih : n + m ≃ n + k → m ≃ k) (_ : step n + m ≃ step n + k)
    show m ≃ k
    apply ih
    show n + m ≃ n + k
    apply AA.inject (β := ℕ) (f := step) (rβ := (· ≃ ·))
    show step (n + m) ≃ step (n + k)
    calc
      step (n + m) ≃ _ := Rel.symm Addition.step_add
      step n + m   ≃ _ := ‹step n + m ≃ step n + k›
      step n + k   ≃ _ := Addition.step_add
      step (n + k) ≃ _ := Rel.refl

def add_cancelL
    : AA.CancellativeOn Hand.L (α := ℕ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·) := {
  cancel := λ (_ : True) => cancel_add
}

instance add_cancellative
    : AA.Cancellative (α := ℕ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·) := {
  cancellativeL := add_cancelL
  cancellativeR := AA.cancelR_from_cancelL add_cancelL
}

theorem zero_sum_split {n m : ℕ} : n + m ≃ 0 → n ≃ 0 ∧ m ≃ 0 := by
  apply Axioms.cases_on (motive := λ n => n + m ≃ 0 → n ≃ 0 ∧ m ≃ 0) n
  case zero =>
    intro (_ : 0 + m ≃ 0)
    show 0 ≃ 0 ∧ m ≃ 0
    have : m ≃ 0 := Rel.trans (Rel.symm Addition.zero_add) ‹0 + m ≃ 0›
    exact And.intro Rel.refl ‹m ≃ 0›
  case step =>
    intro n (_ : step n + m ≃ 0)
    show step n ≃ 0 ∧ m ≃ 0
    apply False.elim
    show False
    have : step (n + m) ≃ 0 :=
      Rel.trans (Rel.symm Addition.step_add) ‹step n + m ≃ 0›
    exact Axioms.step_neq_zero ‹step (n + m) ≃ 0›

instance addition_derived : Addition.Derived ℕ where
  add_zero := add_zero
  add_step := add_step
  add_substitutive := add_substitutive
  add_one_step := add_one_step
  add_commutative := add_commutative
  add_associative := add_associative
  add_cancellative := add_cancellative
  zero_sum_split := zero_sum_split

end Derived

end Lean4Axiomatic.Natural
