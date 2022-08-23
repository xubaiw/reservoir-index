import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Core

/-! # Integer addition -/

namespace Lean4Axiomatic.Integer

/-! ## Axioms -/

/--
Definition of addition, and properties that it must satisfy.

All other properties of addition can be derived from these.

**Named parameters**
- `ℤ`: The type of integers.

**Class parameters**
- `Core ℤ`: Required to express most properties of addition.
-/
class Addition (ℕ : Type) [Natural ℕ] (ℤ : Type) [Core ℕ ℤ] :=
  /-- Definition of and syntax for addition. -/
  addOp : Add ℤ

  /--
  Addition preserves equivalence of integers; two equivalent integers are still
  equivalent after the same quantity is added to both (on the left or right).
  -/
  add_substitutive : AA.Substitutive₂ (α := ℤ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·)

  /-- Exchanging the operands of an addition does not change the result. -/
  add_commutative : AA.Commutative (α := ℤ) (· + ·)

  /-- The grouping of the terms in a sum doesn't matter. -/
  add_associative : AA.Associative (α := ℤ) (· + ·)

  /-- Adding zero to an integer produces the same integer. -/
  add_identity : AA.Identity (α := ℤ) 0 (· + ·)

  /--
  Adding two natural numbers and then converting to an integer gives the same
  result as converting each number to an integer and then adding.
  -/
  add_compatible_from_natural
    : AA.Compatible₂ (α := ℕ) (β := ℤ) (↑·) (· + ·) (· + ·)

attribute [instance] Addition.addOp
attribute [instance] Addition.add_associative
attribute [instance] Addition.add_compatible_from_natural
attribute [instance] Addition.add_identity
attribute [instance] Addition.add_substitutive

export Addition (addOp)

end Lean4Axiomatic.Integer
