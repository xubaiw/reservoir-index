import Lean4Axiomatic.Natural.Addition
import Lean4Axiomatic.Sign

/-!
# Natural number signedness

There are no negative natural numbers, so this file covers positive numbers and
zero.
-/

namespace Lean4Axiomatic.Natural

open Signed (Positive)

/-!
## Axioms
-/

/--
Definition of positive natural numbers.

All other properties of positive natural numbers can be derived from this.
-/
class Sign (ℕ : Type) [Core ℕ] :=
  /-- Definition, properties, and syntax for the `Positive` predicate. -/
  positivity : Signed.Positivity ℕ

attribute [instance] Sign.positivity

/-!
## Derived properties

These results follow from the generic definitions in `Sign` and don't depend on
a specific implementation of natural numbers.
-/

variable {ℕ : Type}
variable [Core ℕ]
variable [Axioms ℕ]
variable [Addition ℕ]
variable [Sign ℕ]

/--
The `Positive` predicate respects equivalence.

**Property intuition**: This must be true for `Positive` to make sense as a
predicate.

**Proof intuition**: From the definition of `Positive`, this is equivalent to
proving `n₁ ≄ 0 → n₂ ≄ 0`. Use substitution on `· ≄ ·` to complete the proof.
-/
theorem positive_subst {n₁ n₂ : ℕ} : n₁ ≃ n₂ → Positive n₁ → Positive n₂ := by
  intro (_ : n₁ ≃ n₂) (_ : Positive n₁)
  show Positive n₂
  have : n₁ ≄ 0 := Signed.positive_defn.mp ‹Positive n₁›
  apply Signed.positive_defn.mpr
  show n₂ ≄ 0
  exact AA.substL (f := (· ≄ ·)) (rβ := (· → ·)) ‹n₁ ≃ n₂› ‹n₁ ≄ 0›

instance positive_substitutive
    : AA.Substitutive₁ (α := ℕ) Positive (· ≃ ·) (· → ·) where
  subst₁ := positive_subst

/--
Every positive natural number is the successor of a natural number.

**Property and proof intuition**: The smallest positive natural number, `1`, is
the successor of `0`. Every other positive number is the successor of another
positive number.
-/
theorem positive_step {n : ℕ} : Positive n → ∃ m : ℕ, step m ≃ n := by
  apply cases_on (motive := λ n => Positive n → ∃ m, step m ≃ n) n
  case zero =>
    intro (_ : Positive (0 : ℕ))
    apply False.elim
    show False
    have : 0 ≄ 0 := Signed.positive_defn.mp ‹Positive (0 : ℕ)›
    apply this
    show 0 ≃ 0
    exact Rel.refl
  case step =>
    intro n (_ : Positive (step n))
    exists n
    show step n ≃ step n
    exact Rel.refl

/--
Addition to a positive number preserves its positivity.

**Property intuition**: The only non-positive natural number is zero. Adding to
a positive number can never decrease it, and thus can never make it zero, i.e.
non-positive.

**Proof intuition**: If adding zero, then we already know the result is
positive because it hasn't changed. Otherwise, we're adding a successor so the
result has at least one `step` in it, which cannot be equivalent to
zero and is thus positive.
-/
theorem positive_add {n m : ℕ} : Positive n → Positive (n + m) := by
  intro (_ : Positive n)
  show Positive (n + m)
  apply cases_on (motive := λ m => Positive (n + m)) m
  case zero =>
    show Positive (n + 0)
    apply AA.subst₁ (rβ := (· → ·)) (Rel.symm add_zero)
    exact ‹Positive n›
  case step =>
    intro m
    show Positive (n + step m)
    apply AA.subst₁ (rβ := (· → ·)) (Rel.symm add_step)
    show Positive (step (n + m))
    apply Signed.positive_defn.mpr
    show step (n + m) ≄ 0
    exact step_neq_zero

end Lean4Axiomatic.Natural
