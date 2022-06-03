import Lean4Axiomatic.Integer
import Lean4Axiomatic.Natural
import Lean4Axiomatic.Operators

open Lean4Axiomatic

/-!
# Implementation of integers as formal differences of natural numbers
-/

namespace Lean4Axiomatic.Integer.Impl

/--
The formal (as in "having the form of") difference between two values of the
same type.

The field names suggest an interpretation for this structure of a starting
value (`init`) that has a quantity (`take`) removed from it. The structure then
denotes the value of the result.

Equivalently, this structure can be viewed as measuring the "directed gap"
between the two values. Specifically, it denotes the value that, when combined
with `take`, gives the result `init`.

Given a type of natural numbers `ℕ`, integers can be defined as values of
`Difference ℕ` under an equivalence relation that considers two differences to
be equal when they denote the same value according to an interpretation above.
-/
structure Difference (α : Type) : Type :=
  init : α
  take : α

infixl:90 "——" => Difference.mk

namespace Difference

variable {ℕ : Type}
variable [Natural ℕ]

/--
The equivalence relation that separates all `Difference ℕ` values into buckets
denoting integers.

In other words, given two differences `d₁` and `d₂`, they represent the same
integer if and only if `eqv d₁ d₂` holds.

**Definition intuition**: Equating two differences means that they represent
the same quantity after subtraction; i.e., after their `take` values have been
removed from their `init` values. The subtracted values can be removed from the
equation without changing its correctness by adding each of them to both sides.
Doing that produces the expression that is the definition of this relation.
-/
def eqv : Difference ℕ → Difference ℕ → Prop
| a——b, c——d => a + d ≃ c + b

-- This is an instance so the operator can be used in the rest of the file
instance tildeDash : Operators.TildeDash (Difference ℕ) := {
  tildeDash := eqv
}

/--
The equivalence relation on differences is reflexive.

**Proof intuition**: The underlying equality in the equivalence relation is
symmetric in terms of the two differences; when both differences are the same,
the equality is trivial.
-/
theorem refl {a : Difference ℕ} : a ≃ a := by
  revert a; intro (a₁——a₂)
  show a₁ + a₂ ≃ a₁ + a₂
  exact Rel.refl

/--
The equivalence relation on differences is symmetric.

**Proof intuition**: The underlying equality in the equivalence relation is
already symmetric in terms of the two differences.
-/
theorem symm {a b : Difference ℕ} : a ≃ b → b ≃ a := by
  revert a; intro (a₁——a₂); revert b; intro (b₁——b₂)
  intro (_ : a₁ + b₂ ≃ b₁ + a₂)
  show b₁ + a₂ ≃ a₁ + b₂
  exact Rel.symm ‹a₁ + b₂ ≃ b₁ + a₂›

/--
The equivalence relation on differences is transitive.

**Proof intuition**: Add the underlying equalities of the two hypotheses; this
nearly produces the goal equality, but both sides have an extra `bn + bp`. Use
the cancellation property of natural number addition to remove it.

The bulk of the proof is just the algebra needed to prepare for cancellation.
-/
theorem trans {a b c : Difference ℕ} : a ≃ b → b ≃ c → a ≃ c := by
  revert a; intro (a₁——a₂); revert b; intro (b₁——b₂); revert c; intro (c₁——c₂)
  intro (_ : a₁ + b₂ ≃ b₁ + a₂) (_ : b₁ + c₂ ≃ c₁ + b₂)
  show a₁ + c₂ ≃ c₁ + a₂
  have : (a₁ + c₂) + (b₂ + b₁) ≃ (c₁ + a₂) + (b₂ + b₁) := calc
    (a₁ + c₂) + (b₂ + b₁) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (a₁ + b₂) + (c₂ + b₁) ≃ _ := AA.substL ‹a₁ + b₂ ≃ b₁ + a₂›
    (b₁ + a₂) + (c₂ + b₁) ≃ _ := AA.substL AA.comm
    (a₂ + b₁) + (c₂ + b₁) ≃ _ := AA.substR AA.comm
    (a₂ + b₁) + (b₁ + c₂) ≃ _ := AA.substR ‹b₁ + c₂ ≃ c₁ + b₂›
    (a₂ + b₁) + (c₁ + b₂) ≃ _ := AA.comm
    (c₁ + b₂) + (a₂ + b₁) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (c₁ + a₂) + (b₂ + b₁) ≃ _ := Rel.refl
  exact AA.cancelR ‹(a₁ + c₂) + (b₂ + b₁) ≃ (c₁ + a₂) + (b₂ + b₁)›

def eqvOp : Relation.Equivalence.EqvOp (Difference ℕ) := {
  toTildeDash := tildeDash
  refl := refl
  symm := symm
  trans := trans
}

def equality : Equality (Difference ℕ) := {
  eqvOp := eqvOp
}

def core : Core (Difference ℕ) := {
  toEquality := equality
}

/--
Addition of differences.

**Definition intuition**: the sum of two differences should be the net effect
of applying both of them.
-/
def add : Difference ℕ → Difference ℕ → Difference ℕ
| a——b, c——d => (a + c)——(b + d)

instance addOp : Add (Difference ℕ) := {
  add := add
}

def addition : Addition.Base (Difference ℕ) := {
  addOp := addOp
}

/--
Multiplication of differences.

**Definition intuition**: Geometry might be the best way to understand this
definition. Let's interpret each difference as the sum of a _positive_ value
(on the left) and a _negative_ value (on the right). Visualize this as a line
segment divided into two subsegments, colored black and red, with lengths
proportional to the positive and negative parts of the difference,
respectively.

The multiplication of two differences is then represented by a rectangle, where
each difference gets a dimension. The rectangle is divided into four smaller
rectangles, one for each combination of subsegments. The four regions are
colored according to the rules for multiplication of signs: if both sides of a
region are the same color, the region is colored black; if they are different
colors, the region is colored red. The difference in area between the black and
red regions is the result of the multiplication.
-/
def mul : Difference ℕ → Difference ℕ → Difference ℕ
| a——b, c——d => (a * c + b * d)——(a * d + b * c)

instance mulOp : Mul (Difference ℕ) := {
  mul := mul
}

def multiplication : Multiplication.Base (Difference ℕ) := {
  mulOp := mulOp
}

instance integer : Integer (Difference ℕ) := {
  toAddition := addition
  toCore := core
  toMultiplication := multiplication
}

end Lean4Axiomatic.Integer.Impl.Difference
