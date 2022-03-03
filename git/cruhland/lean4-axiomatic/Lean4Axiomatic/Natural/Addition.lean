import Lean4Axiomatic.Natural.Core

namespace Lean4Axiomatic.Natural

/-!
# Definition and properties of natural number addition
-/

/--
Definition of addition, and properties that it must satisfy.

All other properties of addition can be derived from these.
-/
class Addition.Base (ℕ : Type) [Core ℕ] where
  /-- Definition of and syntax for addition. -/
  addOp : Add ℕ

  /-- Adding zero to any natural number (on the left) leaves it unchanged. -/
  zero_add {m : ℕ} : 0 + m ≃ m

  /-- Incrementing the left term in a sum increments the result. -/
  step_add {n m : ℕ} : step n + m ≃ step (n + m)

attribute [instance] Addition.Base.addOp

/-- Properties that follow from those provided in `Addition.Base`. -/
class Addition.Derived (ℕ : Type) [Core ℕ] extends Addition.Base ℕ where
  /-- Adding zero to any natural number (on the right) leaves it unchanged. -/
  add_zero {n : ℕ} : n + 0 ≃ n

  /-- Incrementing the right term in a sum increments the result. -/
  add_step {n m : ℕ} : n + step m ≃ step (n + m)

  /--
  Addition preserves equality of natural numbers; two equal natural numbers are
  still equal after the same quantity is added to both (on the left or right).
  -/
  add_substitutive : AA.Substitutive₂ (α := ℕ) (· + ·) (· ≃ ·) (· ≃ ·)

  /-- Adding one is the same as incrementing. -/
  add_one_step {n : ℕ} : n + 1 ≃ step n

  /-- Exchanging the operands of an addition does not change the result. -/
  add_commutative : AA.Commutative (α := ℕ) (· + ·)

  /--
  When three natural numbers are added together, the result is the same
  regardless of which two numbers are added first.
  -/
  add_assoc {n m k : ℕ} : (n + m) + k ≃ n + (m + k)

  /--
  If two equal sums of natural numbers have the same left operand, then their
  right operands are also equal.

  This is called the cancellation law because it allows the same quantity to be
  removed (cancelled) from both sides of an equality of sums.
  -/
  cancel_add {n m k : ℕ} : n + m ≃ n + k → m ≃ k

  /--
  Both operands in a sum of natural numbers must be zero if the result is zero.
  -/
  zero_sum_split {n m : ℕ} : n + m ≃ 0 → n ≃ 0 ∧ m ≃ 0

attribute [instance] Addition.Derived.add_commutative
attribute [instance] Addition.Derived.add_substitutive

namespace Addition
export Addition.Base (addOp step_add zero_add)
export Addition.Derived (
  add_assoc add_commutative add_one_step add_step add_substitutive add_zero cancel_add
  zero_sum_split
)
end Addition

export Addition (
  add_assoc add_commutative add_one_step addOp add_step add_substitutive
  add_zero cancel_add step_add zero_add zero_sum_split
)

end Lean4Axiomatic.Natural
