import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Operators
import Lean4Axiomatic.Relation.Equivalence

/-! # Generic definitions and properties applicable to signed types -/

namespace Lean4Axiomatic.Signed

open Relation.Equivalence (EqvOp)

/-- Class for types `α` that have positive values. -/
class Positivity.Base
    (α : Type u) [outParam (EqvOp α)] [outParam (OfNat α 0)]
    :=
  /-- Predicate that holds only for positive values. -/
  Positive : α → Prop

  /-- Positive values are nonzero. -/
  positive_neqv_zero {a : α} : Positive a → a ≄ 0

export Positivity.Base (Positive)

/-- Class providing more properties of types `α` that have positive values. -/
class Positivity.Properties
    (α : Type u)
    [outParam (EqvOp α)] [outParam (OfNat α 0)] [outParam (Positivity.Base α)]
    :=
  /--
  Positivity respects equivalence: if two values are equivalent and one of them
  is positive, then the other one must be positive.
  -/
  positive_substitutive : AA.Substitutive₁ (α := α) Positive (· ≃ ·) (· → ·)

attribute [instance] Positivity.Properties.positive_substitutive

/-- Class for types `α` that have negative values. -/
class Base
    (α : Type u)
    [outParam (EqvOp α)] [outParam (OfNat α 0)] [outParam (Positivity.Base α)]
    :=
  /-- Predicate that holds only for negative values. -/
  Negative : α → Prop

  /-- Negative values are nonzero. -/
  negative_neqv_zero {a : α} : Negative a → a ≄ 0

  /-- Negative values aren't positive. -/
  negative_non_positive {a : α} : Negative a → ¬ Positive a

export Base (Negative)

/-- Class providing more properties of types `α` that have negative values. -/
class Properties
    (α : Type u) [outParam (EqvOp α)] [outParam (OfNat α 0)]
    [outParam (Positivity.Base α)] [outParam (Positivity.Properties α)]
    [outParam (Base α)]
    :=
  /--
  Negativity respects equivalence: if two values are equivalent and one of them
  is negative, then the other one must be negative.
  -/
  negative_substitutive : AA.Substitutive₁ (α := α) Negative (· ≃ ·) (· → ·)

  /-- Every value is one, and only one, of zero, positive, or negative. -/
  sign_trichotomy
    (a : α) : AA.ExactlyOneOfThree (a ≃ 0) (Positive a) (Negative a)

attribute [instance] Properties.negative_substitutive

end Lean4Axiomatic.Signed
