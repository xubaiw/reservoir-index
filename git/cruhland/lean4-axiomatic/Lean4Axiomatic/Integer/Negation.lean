import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Integer.Multiplication
import Lean4Axiomatic.Integer.Core

namespace Lean4Axiomatic.Integer

open Signed (Positive)

/-!
# Definition and properties of integer negation
-/

/--
Definition of negation, and properties that it must satisfy.

All other properties of negation can be derived from these.

**Named parameters**
- `ℕ`: The natural numbers.
- `ℤ`: The integers.

**Class parameters**
- `Natural ℕ`: Evidence that `ℕ` implements the natural numbers.
- All other class parameters provide the subset of integer properties necessary
  to define the fields of this class.
-/
class Negation.Base
    (ℕ : outParam Type) [outParam (Natural ℕ)]
    (ℤ : Type) [outParam (Core.Base ℕ ℤ)] [outParam (Addition.Base ℕ ℤ)]
    :=
  /-- Definition of and syntax for negation. -/
  negOp : Neg ℤ

  /--
  Negation preserves equality of integers; two equal integers are still equal
  after both are negated.
  -/
  neg_substitutive : AA.Substitutive₁ (α := ℤ) (-·) (· ≃ ·) (· ≃ ·)

  /-- Every integer is either positive, negative, or zero. -/
  trichotomy (a : ℤ)
    : AA.ExactlyOneOfThree
      (a ≃ ↑(0 : ℕ))
      (∃ (n : ℕ), Positive n ∧ a ≃ n)
      (∃ (n : ℕ), Positive n ∧ a ≃ -n)

  /-- An integer added to its negation is always zero. -/
  neg_inverse : AA.Inverse (α := ℤ) (-·) (· + ·)

attribute [instance] Negation.Base.negOp
attribute [instance] Negation.Base.neg_inverse
attribute [instance] Negation.Base.neg_substitutive

/--
Properties that follow from those provided in `Negation.Base`.

**Named parameters**
- `ℕ`: The natural numbers.
- `ℤ`: The integers.

**Class parameters**
- `Natural ℕ`: Evidence that `ℕ` implements the natural numbers.
- All other class parameters provide the subset of integer properties necessary
  to define the fields of this class.
-/
class Negation.Derived
    (ℕ : Type) [Natural ℕ]
    (ℤ : Type) [Core.Base ℕ ℤ] [Addition.Base ℕ ℤ] [Multiplication.Base ℕ ℤ]
    extends Negation.Base ℕ ℤ
    :=
  /-- Multiplying by zero always gives zero. -/
  mul_absorbing : AA.Absorbing (α := ℤ) 0 (· * ·)

  /-- Negation can be moved between a product and either one of its factors. -/
  neg_semicompatible_mul : AA.Semicompatible (α := ℤ) (-·) (· * ·)

  /-- Negation cancels out negation. -/
  neg_involutive {a : ℤ} : -(-a) ≃ a

namespace Negation
export Negation.Base (negOp trichotomy)
end Negation

end Lean4Axiomatic.Integer
