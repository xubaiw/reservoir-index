import Lean4Axiomatic.Natural.Addition
import Lean4Axiomatic.Natural.Sign

/-!
# Natural number ordering
-/

namespace Lean4Axiomatic.Natural

open Signed (Positive)

/-!
## Axioms
-/

/--
Definition of the _less than or equal to_ and _less than_ relations.

All other properties of ordering on natural numbers can be derived from this.
-/
class Order (ℕ : Type) [Core ℕ] [Addition ℕ] :=
  /-- Definition of and syntax for the _less than or equal to_ relation. -/
  leOp : LE ℕ

  /--
  The _less than or equal to_ relation between two natural numbers `n` and `m`
  is equivalent to there being a natural number -- the _difference_ between `n`
  and `m` -- that, when added to `n`, results in `m`.
  -/
  le_defn {n m : ℕ} : n ≤ m ↔ ∃ k : ℕ, n + k ≃ m

  /-- Definition of and syntax for the _less than_ relation. -/
  ltOp : LT ℕ

  /--
  The _less than_ relation between two natural numbers is defined to be the
  same as _less than or equal to_, with the added condition that the numbers
  are not equal.
  -/
  lt_defn {n m : ℕ} : n < m ↔ n ≤ m ∧ n ≄ m

-- Higher priority than the stdlib definitions
attribute [instance default+1] Order.leOp
attribute [instance default+1] Order.ltOp

export Order (le_defn leOp lt_defn ltOp)

/-!
## Derived properties
-/

variable {ℕ : Type}
variable [Core ℕ]
variable [Axioms ℕ]
variable [Addition ℕ]
variable [Sign ℕ]
variable [Order ℕ]

/--
The _less than or equal to_ relation is preserved when both sides are
incremented.
-/
theorem le_subst_step {n₁ n₂ : ℕ} : n₁ ≤ n₂ → step n₁ ≤ step n₂ := by
  intro (_ : n₁ ≤ n₂)
  show step n₁ ≤ step n₂
  have ⟨d, (_ : n₁ + d ≃ n₂)⟩ := le_defn.mp ‹n₁ ≤ n₂›
  apply le_defn.mpr
  exists d
  show step n₁ + d ≃ step n₂
  calc
    step n₁ + d   ≃ _ := step_add
    step (n₁ + d) ≃ _ := AA.subst₁ ‹n₁ + d ≃ n₂›
    step n₂       ≃ _ := Rel.refl

instance le_substitutive_step
    : AA.Substitutive₁ (α := ℕ) step (· ≤ ·) (· ≤ ·)
    := {
  subst₁ := le_subst_step
}

/--
The _less than or equal to_ relation is preserved when both sides are
decremented.
-/
theorem le_inject_step {n₁ n₂ : ℕ} : step n₁ ≤ step n₂ → n₁ ≤ n₂ := by
  intro (_ : step n₁ ≤ step n₂)
  show n₁ ≤ n₂
  have ⟨d, (_ : step n₁ + d ≃ step n₂)⟩ := le_defn.mp ‹step n₁ ≤ step n₂›
  apply le_defn.mpr
  exists d
  show n₁ + d ≃ n₂
  have : step (n₁ + d) ≃ step n₂ := calc
    step (n₁ + d) ≃ _ := Rel.symm step_add
    step n₁ + d   ≃ _ := ‹step n₁ + d ≃ step n₂›
    step n₂       ≃ _ := Rel.refl
  exact AA.inject ‹step (n₁ + d) ≃ step n₂›

instance le_injective_step : AA.Injective (α := ℕ) step (· ≤ ·) (· ≤ ·) := {
  inject := le_inject_step
}

/--
Equal natural numbers can be substituted on the left side of
_less than or equal to_.
-/
theorem le_subst_eqv {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ ≤ m → n₂ ≤ m := by
  intro (_ : n₁ ≃ n₂) (_ : n₁ ≤ m)
  show n₂ ≤ m
  have ⟨d, (_ : n₁ + d ≃ m)⟩ := le_defn.mp ‹n₁ ≤ m›
  apply le_defn.mpr
  exists d
  show n₂ + d ≃ m
  calc
    n₂ + d ≃ _ := Rel.symm (AA.substL ‹n₁ ≃ n₂›)
    n₁ + d ≃ _ := ‹n₁ + d ≃ m›
    m      ≃ _ := Rel.refl

def le_substL_eqv
    : AA.SubstitutiveOn Hand.L (α := ℕ) (· ≤ ·) AA.tc (· ≃ ·) (· → ·)
    := {
  subst₂ := λ (_ : True) => le_subst_eqv
}

/--
Equal natural numbers can be substituted on the right side of
_less than or equal to_.
-/
theorem le_eqv_subst {n m₁ m₂ : ℕ} : m₁ ≃ m₂ → n ≤ m₁ → n ≤ m₂ := by
  intro (_ : m₁ ≃ m₂) (_ : n ≤ m₁)
  show n ≤ m₂
  have ⟨d, (_ : n + d ≃ m₁)⟩ := le_defn.mp ‹n ≤ m₁›
  apply le_defn.mpr
  exists d
  show n + d ≃ m₂
  exact Rel.trans ‹n + d ≃ m₁› ‹m₁ ≃ m₂›

def le_substR_eqv
    : AA.SubstitutiveOn Hand.R (α := ℕ) (· ≤ ·) AA.tc (· ≃ ·) (· → ·)
    := {
  subst₂ := λ (_ : True) => le_eqv_subst
}

instance le_substitutive_eqv
    : AA.Substitutive₂ (α := ℕ) (· ≤ ·) AA.tc (· ≃ ·) (· → ·)
    := {
  substitutiveL := le_substL_eqv
  substitutiveR := le_substR_eqv
}

/-- All natural numbers are _less than or equal to_ themselves. -/
theorem le_refl {n : ℕ} : n ≤ n := by
  apply le_defn.mpr
  exists (0 : ℕ)
  show n + 0 ≃ n
  exact add_zero

instance le_reflexive : Relation.Reflexive (α := ℕ) (· ≤ ·) := {
  refl := le_refl
}

theorem le_step_split {n m : ℕ} : n ≤ step m → n ≤ m ∨ n ≃ step m := by
  intro (_ : n ≤ step m)
  show n ≤ m ∨ n ≃ step m
  have ⟨d, (_ : n + d ≃ step m)⟩ := le_defn.mp ‹n ≤ step m›
  let motive := λ x => d ≃ x → n ≤ m ∨ n ≃ step m
  apply (cases_on (motive := motive) d · · Rel.refl)
  · intro (_ : d ≃ 0)
    apply Or.inr
    show n ≃ step m
    calc
      n      ≃ _ := Rel.symm add_zero
      n + 0  ≃ _ := AA.substR (Rel.symm ‹d ≃ 0›)
      n + d  ≃ _ := ‹n + d ≃ step m›
      step m ≃ _ := Rel.refl
  · intro e (_ : d ≃ step e)
    apply Or.inl
    show n ≤ m
    apply le_defn.mpr
    exists e
    show n + e ≃ m
    apply AA.inject (β := ℕ) (rβ := (· ≃ ·))
    show step (n + e) ≃ step m
    calc
      step (n + e) ≃ _ := Rel.symm add_step
      n + step e   ≃ _ := AA.substR (Rel.symm ‹d ≃ step e›)
      n + d        ≃ _ := ‹n + d ≃ step m›
      step m       ≃ _ := Rel.refl

theorem le_step {n m : ℕ} : n ≤ m → n ≤ step m := by
  intro (_ : n ≤ m)
  show n ≤ step m
  have ⟨d, (_ : n + d ≃ m)⟩ := le_defn.mp ‹n ≤ m›
  apply le_defn.mpr
  exists step d
  show n + step d ≃ step m
  calc
    n + step d   ≃ _ := add_step
    step (n + d) ≃ _ := AA.subst₁ ‹n + d ≃ m›
    step m       ≃ _ := Rel.refl

/--
The _less than or equal to_ relation can be extended through intermediate
values.
-/
theorem le_trans {n m k : ℕ} : n ≤ m → m ≤ k → n ≤ k := by
  intro (_ : n ≤ m)
  have ⟨d, (_ : n + d ≃ m)⟩ := le_defn.mp ‹n ≤ m›
  apply ind_on (motive := λ k => m ≤ k → n ≤ k) k
  case zero =>
    intro (_ : m ≤ 0)
    have ⟨e, (_ : m + e ≃ 0)⟩ := le_defn.mp ‹m ≤ 0›
    show n ≤ 0
    apply le_defn.mpr
    exists d + e
    show n + (d + e) ≃ 0
    calc
      n + (d + e) ≃ _ := Rel.symm AA.assoc
      (n + d) + e ≃ _ := AA.substL ‹n + d ≃ m›
      m + e       ≃ _ := ‹m + e ≃ 0›
      0           ≃ _ := Rel.refl
  case step =>
    intro k (ih : m ≤ k → n ≤ k) (_ : m ≤ step k)
    show n ≤ step k
    match le_step_split ‹m ≤ step k› with
    | Or.inl (_ : m ≤ k) =>
      exact le_step (ih ‹m ≤ k›)
    | Or.inr (_ : m ≃ step k) =>
      exact AA.substRFn ‹m ≃ step k› ‹n ≤ m›

instance le_transitive : Relation.Transitive (α := ℕ) (· ≤ ·) := {
  trans := le_trans
}

/--
The _less than or equal to_ relation is preserved when the same value is
added on the left to both sides.
-/
theorem le_subst_add {n₁ n₂ m : ℕ} : n₁ ≤ n₂ → n₁ + m ≤ n₂ + m := by
  intro (_ : n₁ ≤ n₂)
  show n₁ + m ≤ n₂ + m
  have ⟨d, (_ : n₁ + d ≃ n₂)⟩ := le_defn.mp ‹n₁ ≤ n₂›
  apply le_defn.mpr
  exists d
  show (n₁ + m) + d ≃ n₂ + m
  calc
    (n₁ + m) + d ≃ _ := AA.assoc
    n₁ + (m + d) ≃ _ := AA.substR AA.comm
    n₁ + (d + m) ≃ _ := Rel.symm AA.assoc
    (n₁ + d) + m ≃ _ := AA.substL ‹n₁ + d ≃ n₂›
    n₂ + m       ≃ _ := Rel.refl

def le_substL_add
    : AA.SubstitutiveOn Hand.L (α := ℕ) (· + ·) AA.tc (· ≤ ·) (· ≤ ·)
    := {
  subst₂ := λ (_ : True) => le_subst_add
}

instance le_substitutive_add
    : AA.Substitutive₂ (α := ℕ) (· + ·) AA.tc (· ≤ ·) (· ≤ ·)
    := {
  substitutiveL := le_substL_add
  substitutiveR := AA.substR_from_substL_swap (rS := (· ≃ ·)) le_substL_add
}

/--
The _less than or equal to_ relation is preserved when the same value is
removed from the left side of an addition on both sides of an equivalence.
-/
theorem le_cancel_add {n m₁ m₂ : ℕ} : n + m₁ ≤ n + m₂ → m₁ ≤ m₂ := by
  intro (_ : n + m₁ ≤ n + m₂)
  show m₁ ≤ m₂
  have ⟨d, (_ : (n + m₁) + d ≃ n + m₂)⟩ := le_defn.mp ‹n + m₁ ≤ n + m₂›
  apply le_defn.mpr
  exists d
  show m₁ + d ≃ m₂
  have : n + (m₁ + d) ≃ n + m₂ := calc
    n + (m₁ + d) ≃ _ := Rel.symm AA.assoc
    (n + m₁) + d ≃ _ := ‹(n + m₁) + d ≃ n + m₂›
    n + m₂       ≃ _ := Rel.refl
  exact AA.cancelL ‹n + (m₁ + d) ≃ n + m₂›

def le_cancelL_add
    : AA.CancellativeOn Hand.L (α := ℕ) (· + ·) AA.tc (· ≤ ·) (· ≤ ·)
    := {
  cancel := λ (_ : True) => le_cancel_add
}

instance le_cancellative_add
    : AA.Cancellative (α := ℕ) (· + ·) AA.tc (· ≤ ·) (· ≤ ·) := {
  cancellativeL := le_cancelL_add
  cancellativeR := AA.cancelR_from_cancelL le_cancelL_add
}

/-- Two natural numbers `n` and `m` are equal if `n ≤ m` and `m ≤ n`. -/
theorem le_antisymm {n m : ℕ} : n ≤ m → m ≤ n → n ≃ m := by
  intro (_ : n ≤ m) (_ : m ≤ n)
  show n ≃ m
  have ⟨d₁, (_ : n + d₁ ≃ m)⟩ := le_defn.mp ‹n ≤ m›
  have ⟨d₂, (_ : m + d₂ ≃ n)⟩ := le_defn.mp ‹m ≤ n›
  have : n + (d₁ + d₂) ≃ n + 0 := calc
    n + (d₁ + d₂) ≃ _ := Rel.symm AA.assoc
    (n + d₁) + d₂ ≃ _ := AA.substL ‹n + d₁ ≃ m›
    m + d₂        ≃ _ := ‹m + d₂ ≃ n›
    n             ≃ _ := Rel.symm add_zero
    n + 0         ≃ _ := Rel.refl
  have : d₁ + d₂ ≃ 0 := AA.cancelL ‹n + (d₁ + d₂) ≃ n + 0›
  have ⟨(_ : d₁ ≃ 0), _⟩ := zero_sum_split ‹d₁ + d₂ ≃ 0›
  calc
    n      ≃ _ := Rel.symm add_zero
    n + 0  ≃ _ := AA.substR (Rel.symm ‹d₁ ≃ 0›)
    n + d₁ ≃ _ := ‹n + d₁ ≃ m›
    m      ≃ _ := Rel.refl

/--
Equivalent natural numbers can be substituted on the left side of _less than_.
-/
theorem lt_subst_eqv {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → n₁ < m → n₂ < m := by
  intro (_ : n₁ ≃ n₂) (_ : n₁ < m)
  show n₂ < m
  have ⟨(_ : n₁ ≤ m), (_ : n₁ ≄ m)⟩ := lt_defn.mp ‹n₁ < m›
  have : n₂ ≤ m := AA.substLFn ‹n₁ ≃ n₂› ‹n₁ ≤ m›
  have : n₂ ≄ m := AA.substLFn (f := (· ≄ ·)) ‹n₁ ≃ n₂› ‹n₁ ≄ m›
  apply lt_defn.mpr
  exact ⟨‹n₂ ≤ m›, ‹n₂ ≄ m›⟩

def lt_substL_eqv
    : AA.SubstitutiveOn Hand.L (α := ℕ) (· < ·) AA.tc (· ≃ ·) (· → ·)
    := {
  subst₂ := λ (_ : True) => lt_subst_eqv
}

/--
Equivalent natural numbers can be substituted on the right side of _less than_.
-/
theorem lt_eqv_subst {n₁ n₂ m : ℕ} : n₁ ≃ n₂ → m < n₁ → m < n₂ := by
  intro (_ : n₁ ≃ n₂) (_ : m < n₁)
  show m < n₂
  have ⟨(_ : m ≤ n₁), (_ : m ≄ n₁)⟩ := lt_defn.mp ‹m < n₁›
  have : m ≤ n₂ := AA.substRFn ‹n₁ ≃ n₂› ‹m ≤ n₁›
  have : m ≄ n₂ := AA.substRFn (f := (· ≄ ·)) ‹n₁ ≃ n₂› ‹m ≄ n₁›
  apply lt_defn.mpr
  exact ⟨‹m ≤ n₂›, ‹m ≄ n₂›⟩

def lt_substR_eqv
    : AA.SubstitutiveOn Hand.R (α := ℕ) (· < ·) AA.tc (· ≃ ·) (· → ·)
    := {
  subst₂ := λ (_ : True) => lt_eqv_subst
}

instance lt_substitutive_eqv
    : AA.Substitutive₂ (α := ℕ) (· < ·) AA.tc (· ≃ ·) (· → ·)
    := {
  substitutiveL := lt_substL_eqv
  substitutiveR := lt_substR_eqv
}

/-- A natural number is always less than its successor. -/
theorem lt_step {n : ℕ} : n < step n := by
  show n < step n
  apply lt_defn.mpr
  apply And.intro
  · show n ≤ step n
    apply le_defn.mpr
    exists (1 : ℕ)
    show n + 1 ≃ step n
    exact add_one_step
  · show n ≄ step n
    exact Rel.symm step_neq

/--
A useful way to convert between _less than_ and _less than or equal to_ while
keeping the larger number fixed.
-/
theorem lt_step_le {n m : ℕ} : n < m ↔ step n ≤ m := by
  apply Iff.intro
  · intro (_ : n < m)
    show step n ≤ m
    have ⟨(_ : n ≤ m), (_ : n ≄ m)⟩ := lt_defn.mp ‹n < m›
    have ⟨d, (_ : n + d ≃ m)⟩ := le_defn.mp ‹n ≤ m›
    have : d ≄ 0 := by
      intro (_ : d ≃ 0)
      show False
      apply ‹n ≄ m›
      show n ≃ m
      calc
        n     ≃ _ := Rel.symm add_zero
        n + 0 ≃ _ := AA.substR (Rel.symm ‹d ≃ 0›)
        n + d ≃ _ := ‹n + d ≃ m›
        m     ≃ _ := Rel.refl
    have : Positive d := Signed.positive_defn.mpr ‹d ≄ 0›
    have ⟨d', (_ : step d' ≃ d)⟩ := positive_step ‹Positive d›
    show step n ≤ m
    apply le_defn.mpr
    exists d'
    show step n + d' ≃ m
    calc
      step n + d'   ≃ _ := step_add
      step (n + d') ≃ _ := Rel.symm add_step
      n + step d'   ≃ _ := AA.substR ‹step d' ≃ d›
      n + d         ≃ _ := ‹n + d ≃ m›
      m             ≃ _ := Rel.refl
  · intro (_ : step n ≤ m)
    show n < m
    have ⟨d, (_ : step n + d ≃ m)⟩ := le_defn.mp ‹step n ≤ m›
    have : n + step d ≃ m := calc
      n + step d   ≃ _ := add_step
      step (n + d) ≃ _ := Rel.symm step_add
      step n + d   ≃ _ := ‹step n + d ≃ m›
      m            ≃ _ := Rel.refl
    have : ∃ d, n + d ≃ m := ⟨step d, ‹n + step d ≃ m›⟩
    have : n ≤ m := le_defn.mpr ‹∃ d, n + d ≃ m›
    have : n ≄ m := by
      intro (_ : n ≃ m)
      show False
      have : n + step d ≃ n + 0 := calc
        n + step d ≃ _ := ‹n + step d ≃ m›
        m          ≃ _ := Rel.symm ‹n ≃ m›
        n          ≃ _ := Rel.symm add_zero
        n + 0      ≃ _ := Rel.refl
      have : step d ≃ 0 := AA.cancelL ‹n + step d ≃ n + 0›
      exact absurd this Axioms.step_neq_zero
    show n < m
    apply lt_defn.mpr
    exact ⟨‹n ≤ m›, ‹n ≄ m›⟩

/--
The _less than_ relation between two natural numbers `n` and `m` is
equivalent to there being a positive natural number -- the _difference_
between `n` and `m` -- that, when added to `n`, results in `m`.

**Intuition**: This is already quite intuitive, as it's clear that for one
number to be less than another, there must be a nonzero gap between them.
-/
theorem lt_defn_add {n m : ℕ} : n < m ↔ ∃ k, Positive k ∧ m ≃ n + k := by
  apply Iff.intro
  · intro (_ : n < m)
    show ∃ k, Positive k ∧ m ≃ n + k
    have : step n ≤ m := lt_step_le.mp ‹n < m›
    have ⟨k, (_ : step n + k ≃ m)⟩ := le_defn.mp ‹step n ≤ m›
    exists step k
    apply And.intro
    · show Positive (step k)
      apply Signed.positive_defn.mpr
      show step k ≄ 0
      exact Axioms.step_neq_zero
    · show m ≃ n + step k
      calc
        m            ≃ _ := Rel.symm ‹step n + k ≃ m›
        step n + k   ≃ _ := step_add
        step (n + k) ≃ _ := Rel.symm add_step
        n + step k   ≃ _ := Rel.refl
  · intro ⟨k, (_ : Positive k), (_ : m ≃ n + k)⟩
    show n < m
    apply lt_step_le.mpr
    show step n ≤ m
    apply le_defn.mpr
    show ∃ k, step n + k ≃ m
    have ⟨k', (_ : step k' ≃ k)⟩ := positive_step ‹Positive k›
    exists k'
    show step n + k' ≃ m
    calc
      step n + k'   ≃ _ := step_add
      step (n + k') ≃ _ := Rel.symm add_step
      n + step k'   ≃ _ := AA.substR ‹step k' ≃ k›
      n + k         ≃ _ := Rel.symm ‹m ≃ n + k›
      m             ≃ _ := Rel.refl

/-- No natural number is less than zero. -/
theorem lt_zero {n : ℕ} : n ≮ 0 := by
  intro (_ : n < 0)
  show False
  have : step n ≤ 0 := lt_step_le.mp ‹n < 0›
  have ⟨d, (_ : step n + d ≃ 0)⟩ := le_defn.mp ‹step n ≤ 0›
  have : step (n + d) ≃ 0 := calc
    step (n + d) ≃ _ := Rel.symm step_add
    step n + d   ≃ _ := ‹step n + d ≃ 0›
    0            ≃ _ := Rel.refl
  exact absurd ‹step (n + d) ≃ 0› Axioms.step_neq_zero

/--
A natural number is positive iff it's greater than zero.

**Proof intuition**: The _less than_ relation can be defined in terms of a
positive difference between its two arguments. If the left argument is zero,
then the right argument must be positive.
-/
theorem lt_zero_pos {n : ℕ} : Positive n ↔ n > 0 := by
  apply Iff.intro
  · intro (_ : Positive n)
    show 0 < n
    apply lt_defn_add.mpr
    show ∃ k, Positive k ∧ n ≃ 0 + k
    exists n
    apply And.intro
    · show Positive n
      exact ‹Positive n›
    · show n ≃ 0 + n
      exact Rel.symm zero_add
  · intro (_ : 0 < n)
    show Positive n
    have ⟨k, ⟨(_ : Positive k), (_ : n ≃ 0 + k)⟩⟩ := lt_defn_add.mp ‹0 < n›
    have : k ≃ n := Rel.symm (Rel.trans ‹n ≃ 0 + k› zero_add)
    exact AA.subst₁ (f := Positive) (rβ := (· → ·)) ‹k ≃ n› ‹Positive k›

/-- Weakens equivalence to _less than or equal to_. -/
theorem le_from_eqv {n m : ℕ} : n ≃ m → n ≤ m := by
  intro (_ : n ≃ m)
  show n ≤ m
  have : n ≤ n := Rel.refl
  exact AA.substRFn ‹n ≃ m› ‹n ≤ n›

/-- Weakens _less than_ to _less than or equal to_. -/
theorem le_from_lt {n m : ℕ} : n < m → n ≤ m := by
  intro (_ : n < m)
  show n ≤ m
  have ⟨(_ : n ≤ m), _⟩ := lt_defn.mp ‹n < m›
  exact ‹n ≤ m›

/--
As the name implies, if _less than or equal to_ holds between two natural
numbers, then either _less than_ holds between them as well, or the numbers are
equivalent.
-/
theorem le_split {n m : ℕ} : n ≤ m → n < m ∨ n ≃ m := by
  intro (_ : n ≤ m)
  show n < m ∨ n ≃ m
  have ⟨d, (h : n + d ≃ m)⟩ := le_defn.mp ‹n ≤ m›
  revert h
  apply cases_on (motive := λ d => n + d ≃ m → n < m ∨ n ≃ m) d
  case zero =>
    intro (_ : n + 0 ≃ m)
    apply Or.inr
    show n ≃ m
    calc
      n     ≃ _ := Rel.symm add_zero
      n + 0 ≃ _ := ‹n + 0 ≃ m›
      m     ≃ _ := Rel.refl
  case step =>
    intro d (_ : n + step d ≃ m)
    apply Or.inl
    show n < m
    apply lt_step_le.mpr
    show step n ≤ m
    apply le_defn.mpr
    exists d
    show step n + d ≃ m
    calc
      step n + d   ≃ _ := step_add
      step (n + d) ≃ _ := Rel.symm add_step
      n + step d   ≃ _ := ‹n + step d ≃ m›
      m            ≃ _ := Rel.refl

/--
Useful result when needing to decrement the larger number in a _less than_
relation.
-/
theorem lt_split {n m : ℕ} : n < step m → n < m ∨ n ≃ m := by
  intro (_ : n < step m)
  show n < m ∨ n ≃ m
  have : step n ≤ step m := lt_step_le.mp ‹n < step m›
  have : n ≤ m := AA.inject ‹step n ≤ step m›
  exact le_split ‹n ≤ m›

/-- The _less than_ relation can be extended through intermediate values. -/
theorem lt_trans {n m k : ℕ} : n < m → m < k → n < k := by
  intro (_ : n < m) (_ : m < k)
  show n < k
  apply lt_step_le.mpr
  show step n ≤ k
  calc
    step n ≤ _ := lt_step_le.mp ‹n < m›
    m      ≤ _ := le_from_lt lt_step
    step m ≤ _ := lt_step_le.mp ‹m < k›
    k      ≤ _ := Rel.refl

instance lt_transitive : Relation.Transitive (α := ℕ) (· < ·) := {
  trans := lt_trans
}

/--
Very general property about ordering which often simplifies proofs that would
otherwise have had to use induction.
-/
theorem trichotomy (n m : ℕ)
    : AA.ExactlyOneOfThree (n < m) (n ≃ m) (n > m) := by
  constructor
  case atLeastOne =>
    let motive := λ n => AA.OneOfThree (n < m) (n ≃ m) (n > m)
    apply ind_on (motive := motive) n
    case zero =>
      show AA.OneOfThree (0 < m) (0 ≃ m) (0 > m)
      let motive := λ m : ℕ => AA.OneOfThree (0 < m) (0 ≃ m) (0 > m)
      apply cases_on (motive := motive) m
      case zero =>
        apply AA.OneOfThree.second
        show 0 ≃ 0
        exact Rel.refl
      case step =>
        intro m
        apply AA.OneOfThree.first
        show 0 < step m
        apply lt_defn.mpr
        apply And.intro
        · show 0 ≤ step m
          apply le_defn.mpr
          exists step m
          exact zero_add
        · show 0 ≄ step m
          exact Rel.symm Axioms.step_neq_zero
    case step =>
      intro n (ih : AA.OneOfThree (n < m) (n ≃ m) (n > m))
      show AA.OneOfThree (step n < m) (step n ≃ m) (step n > m)
      match ih with
      | AA.OneOfThree.first (_ : n < m) =>
        have : step n ≤ m := lt_step_le.mp ‹n < m›
        have : step n < m ∨ step n ≃ m := le_split ‹step n ≤ m›
        match ‹step n < m ∨ step n ≃ m› with
        | Or.inl (_ : step n < m) => exact AA.OneOfThree.first ‹step n < m›
        | Or.inr (_ : step n ≃ m) => exact AA.OneOfThree.second ‹step n ≃ m›
      | AA.OneOfThree.second (_ : n ≃ m) =>
        have : m ≃ n := Rel.symm ‹n ≃ m›
        have : m ≤ n := le_from_eqv ‹m ≃ n›
        have : step m ≤ step n := AA.subst₁ ‹m ≤ n›
        have : m < step n := lt_step_le.mpr ‹step m ≤ step n›
        apply AA.OneOfThree.third
        exact ‹m < step n›
      | AA.OneOfThree.third (_ : n > m) =>
        apply AA.OneOfThree.third
        show m < step n
        exact Rel.trans ‹m < n› lt_step
  case atMostOne =>
    show ¬ AA.TwoOfThree (n < m) (n ≃ m) (n > m)
    intro
    | AA.TwoOfThree.oneAndTwo (_ : n < m) (_ : n ≃ m) =>
      show False
      have ⟨_, (_ : n ≄ m)⟩ := lt_defn.mp ‹n < m›
      exact absurd ‹n ≃ m› ‹n ≄ m›
    | AA.TwoOfThree.oneAndThree (_ : n < m) (_ : n > m) =>
      show False
      have ⟨(_ : n ≤ m), (_ : n ≄ m)⟩ := lt_defn.mp ‹n < m›
      have ⟨(_ : m ≤ n), _⟩ := lt_defn.mp ‹n > m›
      have : n ≃ m := le_antisymm ‹n ≤ m› ‹m ≤ n›
      exact absurd ‹n ≃ m› ‹n ≄ m›
    | AA.TwoOfThree.twoAndThree (_ : n ≃ m) (_ : n > m) =>
      show False
      have ⟨_, (_ : m ≄ n)⟩ := lt_defn.mp ‹n > m›
      exact absurd ‹n ≃ m› (Rel.symm ‹m ≄ n›)

end Lean4Axiomatic.Natural
