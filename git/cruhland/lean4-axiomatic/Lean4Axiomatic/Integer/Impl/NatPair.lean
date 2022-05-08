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

-- This is an instance so the operator can be used in the rest of the file
instance tildeDash : Operators.TildeDash (PosNegPair ℕ) := {
  tildeDash := eqv
}

/--
The equivalence on pairs is reflexive.

**Proof intuition**: The underlying equality in the equivalence relation is
symmetric in terms of the two pairs; when both pairs are the same, the equality
is trivial.
-/
theorem refl {a : PosNegPair ℕ} : a ≃ a := by
  revert a; intro ⟨ap, an⟩
  show ap + an ≃ ap + an
  exact Eqv.refl

/--
The equivalence on pairs is symmetric.

**Proof intuition**: The underlying equality in the equivalence relation is
already symmetric in terms of the two pairs.
-/
theorem symm {a b : PosNegPair ℕ} : a ≃ b → b ≃ a := by
  revert a; intro ⟨ap, an⟩; revert b; intro ⟨bp, bn⟩
  intro (_ : ap + bn ≃ bp + an)
  show bp + an ≃ ap + bn
  exact Eqv.symm ‹ap + bn ≃ bp + an›

/--
The equivalence on pairs is transitive.

**Proof intuition**: Add the underlying equalities of the two hypotheses; this
nearly produces the goal equality, but both sides have an extra `bn + bp`. Use
the cancellation property of natural number addition to remove it.

The bulk of the proof is just the algebra needed to prepare for cancellation.
-/
theorem trans {a b c : PosNegPair ℕ} : a ≃ b → b ≃ c → a ≃ c := by
  revert a; intro ⟨ap, an⟩; revert b; intro ⟨bp, bn⟩; revert c; intro ⟨cp, cn⟩
  intro (_ : ap + bn ≃ bp + an) (_ : bp + cn ≃ cp + bn)
  show ap + cn ≃ cp + an
  have : (ap + cn) + (bn + bp) ≃ (cp + an) + (bn + bp) := calc
    (ap + cn) + (bn + bp) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (ap + bn) + (cn + bp) ≃ _ := AA.substL ‹ap + bn ≃ bp + an›
    (bp + an) + (cn + bp) ≃ _ := AA.substL AA.comm
    (an + bp) + (cn + bp) ≃ _ := AA.substR AA.comm
    (an + bp) + (bp + cn) ≃ _ := AA.substR ‹bp + cn ≃ cp + bn›
    (an + bp) + (cp + bn) ≃ _ := AA.comm
    (cp + bn) + (an + bp) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (cp + an) + (bn + bp) ≃ _ := Eqv.refl
  exact AA.cancelR ‹(ap + cn) + (bn + bp) ≃ (cp + an) + (bn + bp)›

def eqvOp : Relation.EqvOp (PosNegPair ℕ) := {
  toTildeDash := tildeDash
  refl := refl
  symm := symm
  trans := trans
}

def equality : Equality (PosNegPair ℕ) := {
  eqvOp := eqvOp
}

def core : Core (PosNegPair ℕ) := {
  toEquality := equality
}

instance integer : Integer (PosNegPair ℕ) := {
  toCore := core
}

end Lean4Axiomatic.Integer.Impl.NatPair
