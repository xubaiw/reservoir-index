import Lean4Axiomatic.Natural
import Lean4Axiomatic.Relation.Equivalence

/-!
# Fundamental definitions and properties of integers
-/

namespace Lean4Axiomatic.Integer

/--
Definitions pertaining to equality of integer values.

**Named parameters**
- `ℤ`: The type of integers.
-/
class Equality (ℤ : Type) :=
  /-- The equality relation on integers, expressed with the syntax `a ≃ b`. -/
  eqvOp : Relation.Equivalence.EqvOp ℤ

attribute [instance] Equality.eqvOp

/--
Definitions pertaining to conversion of other types into or out of integers.

**Named parameters**
- `ℕ`: A type that implements the natural numbers.
- `ℤ`: The type of integers.

**Class parameters**
- `Natural ℕ`: Evidence that `ℕ` implements the natural numbers.
-/
class Conversion (ℕ : Type) [Natural ℕ] (ℤ : Type) :=
  /-- Every natural number has an integer representation. -/
  from_natural : Coe ℕ ℤ

attribute [instance] Conversion.from_natural

end Lean4Axiomatic.Integer
