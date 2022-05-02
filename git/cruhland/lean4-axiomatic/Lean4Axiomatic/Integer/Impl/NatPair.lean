import Lean4Axiomatic.Integer
import Lean4Axiomatic.Natural
import Lean4Axiomatic.Operators

open Lean4Axiomatic

/-!
# Implementation of integers as pairs of natural numbers
-/

namespace Lean4Axiomatic.Integer.Impl.NatPair

/--
A pair of values of the same type that represents the concept of subtraction.

Given a type of natural numbers `ℕ`, integers can be defined as a
`PosNegPair ℕ` under an equivalence relation that identifies pairs denoting
subtraction operations that give the same result.

**Definition intuition**: Subtraction is the operation that reduces a quantity
by an amount specified by another quantity. The second quantity can thus be
viewed as having a "negative" value which "cancels" a corresponding amount of
the first, "positive" quantity.
-/
structure PosNegPair (α : Type) : Type :=
  pos : α
  neg : α

variable {ℕ : Type}
variable [Natural ℕ]

/--
The equivalence relation that partitions pairs of natural numbers into groups
denoting integers.

In other words, given two pairs `a` and `b`, they represent the same integer if
and only if `eqv a b` holds.

**Definition intuition**: Equating two pairs means that they represent the same
quantity after subtraction; i.e., after their negative values have been taken
away from their positive values. The negative values can be removed from the
equation without changing its correctness by adding each of them to both sides.
Doing that produces the expression that is the definition of this relation.
-/
def eqv : PosNegPair ℕ → PosNegPair ℕ → Prop
| ⟨ap, an⟩, ⟨bp, bn⟩ => ap + bn ≃ bp + an

def tildeDash : Operators.TildeDash (PosNegPair ℕ) := {
  tildeDash := eqv
}

def equality : Equality (PosNegPair ℕ) := {
  tildeDash := tildeDash
}

def core : Core (PosNegPair ℕ) := {
  toEquality := equality
}

instance integer : Integer (PosNegPair ℕ) := {
  toCore := core
}

end Lean4Axiomatic.Integer.Impl.NatPair
