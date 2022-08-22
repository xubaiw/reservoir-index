import Lean4Axiomatic.Natural
import Lean4Axiomatic.Relation.Equivalence

/-! # Fundamental definitions and properties of integers -/

namespace Lean4Axiomatic.Integer

/-! ## Axioms -/

/--
Definitions pertaining to equivalence of integer values.

**Named parameters**
- `ℤ`: The integers.
-/
class Equivalence (ℤ : Type) :=
  /--
  The standard equivalence relation on integers, expressed with the syntax
  `a ≃ b`.
  -/
  eqvOp : Relation.Equivalence.EqvOp ℤ

attribute [instance] Equivalence.eqvOp

export Equivalence (eqvOp)

/--
Definitions pertaining to conversion of other types into or out of integers.

**Named parameters**
- `ℕ`: The natural numbers.
- `ℤ`: The integers.

**Class parameters**
- `Natural ℕ`: Evidence that `ℕ` implements the natural numbers.
- All other class parameters provide the subset of integer properties necessary
  to define the fields of this class.
-/
class Conversion
    (ℕ : outParam Type) [outParam (Natural ℕ)]
    (ℤ : outParam Type) [outParam (Equivalence ℤ)]
    :=
  /-- Every natural number has an integer representation. -/
  from_natural : Coe ℕ ℤ

  /-- Every natural number maps to a unique integer. -/
  from_natural_substitutive
    : AA.Substitutive₁ (α := ℕ) (β := ℤ) (↑·) (· ≃ ·) (· ≃ ·)

  /-- Every integer representation comes from a unique natural number. -/
  from_natural_injective : AA.Injective (α := ℕ) (β := ℤ) (↑·) (· ≃ ·) (· ≃ ·)

attribute [instance] Conversion.from_natural
attribute [instance] Conversion.from_natural_injective
attribute [instance] Conversion.from_natural_substitutive

/--
Bundles all core integer classes into one, to reduce the number of core
dependencies needed by other integer classes.

**Named parameters**
- `ℕ`: The natural numbers.
- `ℤ`: The integers.

**Class parameters**
- `Natural ℕ`: Evidence that `ℕ` implements the natural numbers.
-/
class Core (ℕ : outParam Type) [outParam (Natural ℕ)] (ℤ : outParam Type)
  extends Equivalence ℤ, Conversion ℕ ℤ

/-! ## Derived properties -/

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℕ ℤ]

/--
The integer one is not the same as the integer zero.

**Proof intuition**: All the laws of algebra for integers continue to hold if
`0 ≃ 1` (see [zero ring](https://en.wikipedia.org/wiki/Zero_ring)), so we need
to use a non-algebraic fact. This is provided by the mapping from natural
numbers to integers, specifically its injectivity which allows us to translate
the property that a successor is never the same as zero into the integers.
-/
theorem one_neqv_zero : (1 : ℤ) ≄ 0 := by
  intro (_ : (1 : ℤ) ≃ 0)
  show False
  have : ↑(1 : ℕ) ≃ ↑(0 : ℕ) := ‹(1 : ℤ) ≃ 0›
  have : (1 : ℕ) ≃ 0 := AA.inject ‹↑(1 : ℕ) ≃ ↑(0 : ℕ)›
  have : Natural.step (0 : ℕ) ≃ 0 :=
    Rel.trans (Rel.symm Natural.literal_step) ‹(1 : ℕ) ≃ 0›
  exact absurd ‹Natural.step (0 : ℕ) ≃ 0› Natural.step_neq_zero

end Lean4Axiomatic.Integer
