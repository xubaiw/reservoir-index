import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Operators
import Lean4Axiomatic.Relation.Equivalence

/-! # Generic definitions and properties applicable to signed types -/

namespace Lean4Axiomatic

open Relation.Equivalence (EqvOp)

namespace Signed

/--
Class that provides a canonical `Positive` predicate over a type `α`.

This class is separate from the other `Positivity` classes as a convenience:
when implementing the properties for `Positivity`, it's cleaner and more
consistent to be able to use the syntax for the "official" `Positive`
predicate, rather than a specific implementation.

While it's possible to define instances of this class whose `Positive`
predicates don't behave as expected, this shouldn't matter much in practice
because any code that requires correct behavior will depend on `Positivity`
instead.
-/
class Positivity.Ops (α : Type u) :=
  /-- Predicate that holds only for positive values. -/
  Positive : α → Prop

export Positivity.Ops (Positive)

/-- Class for types `α` that have positive values (but not negative values). -/
class Positivity
    (α : Type u) [outParam (EqvOp α)] [outParam (OfNat α 0)]
    extends Positivity.Ops α
    :=
  /-- All values other than zero are positive. -/
  positive_defn {a : α} : Positive a ↔ a ≄ 0

/--
Class that provides canonical `Positive` and `Negative` predicates over a type
`α`.

This class is separate from `Signed` as a convenience: when implementing
the properties for `Signed`, it's cleaner and more consistent to be able to
use the syntax for the "official" predicates, rather than specific
implementations.

While it's possible to define instances of this class whose predicates don't
behave as expected, this shouldn't matter much in practice because any code
that requires correct behavior will depend on `Signed` instead.
-/
class Ops (α : Type u) extends Positivity.Ops α :=
  /-- Predicate that holds only for negative values. -/
  Negative : α → Prop

export Ops (Negative)

end Signed

open Signed (Negative Positive)

/-- Class for types `α` that have positive and negative values. -/
class Signed
    (α : Type u) [outParam (EqvOp α)] [outParam (OfNat α 0)]
    extends Signed.Ops α
    :=
  /--
  Positivity respects equivalence: if two values are equivalent and one of them
  is positive, then the other one must be positive.
  -/
  positive_substitutive : AA.Substitutive₁ (α := α) Positive (· ≃ ·) (· → ·)

  /--
  Negativity respects equivalence: if two values are equivalent and one of them
  is negative, then the other one must be negative.
  -/
  negative_substitutive : AA.Substitutive₁ (α := α) Negative (· ≃ ·) (· → ·)

  /-- Every value is one, and only one, of zero, positive, or negative. -/
  trichotomy
    (a : α) : AA.ExactlyOneOfThree (a ≃ 0) (Positive a) (Negative a)

attribute [instance] Signed.negative_substitutive

namespace Signed
export Positivity (positive_defn)
end Signed

end Lean4Axiomatic
