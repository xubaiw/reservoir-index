import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Operators
import Lean4Axiomatic.Relation.Equivalence

/-! # Generic definitions and properties applicable to signed types -/

namespace Lean4Axiomatic

open Relation.Equivalence (EqvOp)

/--
Class for types that have positive values.

**Named parameters**
- `α`: The `Sort` having positive values.
-/
class Positivity.Base (α : Sort u) :=
  /-- Predicate that holds only for positive values. -/
  Positive : α → Prop

export Positivity.Base (Positive)

/--
Class providing additional properties of types that have positive values.

**Named parameters**
- `α`: The `Sort` having positive values.

**Class parameters**
- `EqvOp α`: Needed for expressing some properties.
-/
class Positivity.Properties
    (α : Sort u) [outParam (EqvOp α)] extends Positivity.Base α :=
  /--
  Positivity respects equivalence: if two values are equivalent and one of them
  is positive, then the other one must be positive.
  -/
  positive_substitutive : AA.Substitutive₁ (α := α) Positive (· ≃ ·) (· → ·)

attribute [instance] Positivity.Properties.positive_substitutive

end Lean4Axiomatic
