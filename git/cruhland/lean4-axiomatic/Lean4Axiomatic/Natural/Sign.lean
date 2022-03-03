import Lean4Axiomatic.Natural.Addition

namespace Lean4Axiomatic.Natural

/-!
# Definition and properties of natural number signedness

There are no negative natural numbers, so this file covers positive numbers and
zero.
-/

/--
Definition of positive natural numbers.

All other properties of positive natural numbers can be derived from this.
-/
class Sign.Base (ℕ : Type) [Core ℕ] where
  /-- Predicate that holds of a natural number iff it is positive. -/
  Positive (n : ℕ) : Prop

  /-- A natural number is positive iff it is nonzero. -/
  positive_defn {n : ℕ} : Positive n ↔ n ≄ 0

/-- Properties that follow from those provided in `Sign.Base`. -/
class Sign.Derived (ℕ : Type) [Core ℕ] [Addition.Base ℕ]
    extends Sign.Base ℕ where
  /--
  Positivity respects equality: if two natural numbers are equal and one of
  them is positive, then the other one must be positive.
  -/
  positive_substitutive : AA.Substitutive Positive (· ≃ ·) (· → ·)

  /--
  Every positive natural number is the successor of another natural number.
  -/
  positive_step {n : ℕ} : Positive n → ∃ m : ℕ, step m ≃ n

  /--
  Addition preserves positivity: adding a natural number to a positive natural
  number yields a positive sum.
  -/
  positive_add {n m : ℕ} : Positive n → Positive (n + m)

namespace Sign
export Sign.Base (Positive positive_defn)
export Sign.Derived (positive_add positive_step)
end Sign

end Lean4Axiomatic.Natural
