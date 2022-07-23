import Lean4Axiomatic.Natural
import Lean4Axiomatic.Relation.Equivalence

/-!
# Fundamental definitions and properties of integers
-/

namespace Lean4Axiomatic.Integer

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
class Core.Base (ℕ : outParam Type) [outParam (Natural ℕ)] (ℤ : outParam Type)
  extends Equivalence ℤ, Conversion ℕ ℤ

/--
Properties that follow from those provided by `Core.Base`.

**Named parameters**
- `ℕ`: The natural numbers.
- `ℤ`: The integers.

**Class parameters**
- `Natural ℕ`: Evidence that `ℕ` implements the natural numbers.
-/
class Core.Derived
    (ℕ : outParam Type) [outParam (Natural ℕ)] (ℤ : outParam Type)
    extends Core.Base ℕ ℤ
    :=
  /-- The integer values for zero and one are not equivalent. -/
  one_neqv_zero : (1 : ℤ) ≄ 0

namespace Core
export Core.Derived (one_neqv_zero)
export Equivalence (eqvOp)
end Core

end Lean4Axiomatic.Integer
