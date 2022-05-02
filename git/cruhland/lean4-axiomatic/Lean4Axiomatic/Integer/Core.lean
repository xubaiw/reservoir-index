import Lean4Axiomatic.Operators

/-!
# Fundamental definitions and properties of integers
-/

namespace Lean4Axiomatic.Integer

/--
Definitions pertaining to equality of integer values.

**Named parameters**
- `ℤ`: the type of integers.
-/
class Equality (ℤ : Type) :=
  /-- The equality relation on integers, expressed with the syntax `a ≃ b`. -/
  tildeDash : Operators.TildeDash ℤ

attribute [instance] Equality.tildeDash

/--
Packages together the basic properties of integers, to reduce the amount of
class references needed for more advanced properties.

**Named parameters**
- `ℤ`: the type of integers.
-/
class Core (ℤ : Type) extends Equality ℤ

end Lean4Axiomatic.Integer
