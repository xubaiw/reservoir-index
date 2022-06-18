import Lean4Axiomatic.Integer
import Lean4Axiomatic.Natural

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

/--
Create a `Difference` from an ordered pair of values.

**Named parameters**
- `α`: The type of both elements of the ordered pair.
-/
def from_prod {α : Type} : α × α → Difference α
| (x, y) => x——y

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
nearly produces the goal equality, but both sides have an extra `b₂ + b₁`. Use
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

instance eqvOp : Relation.Equivalence.EqvOp (Difference ℕ) := {
  toTildeDash := tildeDash
  refl := refl
  symm := symm
  trans := trans
}

/--
Conversion of ordered pairs into `Difference`s preserves equivalence.

**Proof intuition**: Equivalence of ordered pairs is stricter than equivalence
of differences. For ordered pairs, both the left and right elements must be
equivalent; for differences, any values representing the same gap are
equivalent. Thus one only needs to show that the former is strong enough to
imply the latter.
-/
instance from_prod_substitutive
    : AA.Substitutive₁ (α := ℕ × ℕ) from_prod (· ≃ ·) (· ≃ ·)
    := by
  apply AA.Substitutive₁.mk
  intro p q; revert p; intro ((n, m)); revert q; intro ((k, j))
  intro (_ : (n, m) ≃ (k, j))
  show from_prod (n, m) ≃ from_prod (k, j)
  show n——m ≃ k——j
  show n + j ≃ k + m
  have (And.intro (_ : n ≃ k) (_ : m ≃ j)) :=
    Relation.Equivalence.Impl.Prod.eqv_defn.mp ‹(n, m) ≃ (k, j)›
  calc
    n + j ≃ _ := AA.substL ‹n ≃ k›
    k + j ≃ _ := AA.substR (Rel.symm ‹m ≃ j›)
    k + m ≃ _ := Rel.refl

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

/--
Addition of natural number differences is commutative.

**Proof intuition**: Expand definitions to see that we need to show the
equivalence of two differences of natural number sums. The left and right
elements of the differences are directly equivalent via commutativity of
natural number addition, so convert the differences into ordered pairs and use
commutativity element-wise.
-/
theorem add_comm {a b : Difference ℕ} : a + b ≃ b + a := by
  revert a; intro (a₁——a₂); revert b; intro (b₁——b₂)
  show a₁——a₂ + b₁——b₂ ≃ b₁——b₂ + a₁——a₂
  show (a₁ + b₁)——(a₂ + b₂) ≃ (b₁ + a₁)——(b₂ + a₂)
  show from_prod (a₁ + b₁, a₂ + b₂) ≃ from_prod (b₁ + a₁, b₂ + a₂)
  apply AA.subst₁
  show (a₁ + b₁, a₂ + b₂) ≃ (b₁ + a₁, b₂ + a₂)
  calc
    (a₁ + b₁, a₂ + b₂) ≃ _ := AA.substL AA.comm
    (b₁ + a₁, a₂ + b₂) ≃ _ := AA.substR AA.comm
    (b₁ + a₁, b₂ + a₂) ≃ _ := Rel.refl

instance add_commutative : AA.Commutative (α := Difference ℕ) (· + ·) := {
  comm := add_comm
}

/--
Adding the same difference on the right of two equivalent differences preserves
their equivalence.

**Proof intuition**: The property is already intuitively true; imagine
extending two line segments of the same length by the same amount. So the proof
just expands all definitions into equalities of sums of natural numbers, and
performs algebra to obtain the desired result.
-/
theorem add_substL {a₁ a₂ b : Difference ℕ} : a₁ ≃ a₂ → a₁ + b ≃ a₂ + b := by
  revert a₁; intro (n——m); revert a₂; intro (k——j); revert b; intro (p——q)
  intro (_ : n——m ≃ k——j)
  have : n + j ≃ k + m := ‹n——m ≃ k——j›
  show n——m + p——q ≃ k——j + p——q
  show (n + p)——(m + q) ≃ (k + p)——(j + q)
  show (n + p) + (j + q) ≃ (k + p) + (m + q)
  calc
    (n + p) + (j + q) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (n + j) + (p + q) ≃ _ := AA.substL ‹n + j ≃ k + m›
    (k + m) + (p + q) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (k + p) + (m + q) ≃ _ := Rel.refl

def add_substitutiveL
    : AA.SubstitutiveOn Hand.L (α := Difference ℕ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  subst₂ := λ (_ : True) => add_substL
}

def add_substitutive
    : AA.Substitutive₂ (α := Difference ℕ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·) := {
  substitutiveL := add_substitutiveL
  substitutiveR := AA.substR_from_substL_swap (rS := (· ≃ ·)) add_substitutiveL
}

instance equality : Equality (Difference ℕ) := {
  eqvOp := eqvOp
}

/--
Every natural number can be represented as a difference.

**Definition intuition**: Taking nothing away from a natural number preserves
its value.
-/
def from_natural : Coe ℕ (Difference ℕ) := {
  coe := (·——0)
}

def conversion : Conversion ℕ (Difference ℕ) := {
  from_natural := from_natural
}

def addition : Addition.Base (Difference ℕ) := {
  addOp := addOp
  add_substitutive := add_substitutive
  add_commutative := add_commutative
}

/--
Negation of differences.

**Definition intuition**: It's easiest to use the "directed gap" interpretation
of differences to see this. If `a——b` represents the process of traveling from
`a` to `b`, then its negation should represent the opposite process: traveling
from `b` to `a`.
-/
def neg : Difference ℕ → Difference ℕ
| a——b => b——a

instance negOp : Neg (Difference ℕ) := {
  neg := neg
}

/--
Negating two equivalent differences preserves their equivalence.

**Property intuition**: For negation to make sense as an operation (i.e., have
a consistent definition as a function) on integers, this property must be true.

**Proof intuition**: Nothing too insightful here, it's just expanding the
definitions of negation and equality and performing some algebra.
-/
theorem neg_subst {a₁ a₂ : Difference ℕ} : a₁ ≃ a₂ → -a₁ ≃ -a₂ := by
  revert a₁; intro (n——m); revert a₂; intro (k——j)
  intro (_ : n——m ≃ k——j)
  show -(n——m) ≃ -(k——j)
  have : n + j ≃ k + m := ‹n——m ≃ k——j›
  show m——n ≃ j——k
  show m + k ≃ j + n
  calc
    m + k ≃ _ := AA.comm
    k + m ≃ _ := Rel.symm ‹n + j ≃ k + m›
    n + j ≃ _ := AA.comm
    j + n ≃ _ := Rel.refl

def neg_substitutive
    : AA.Substitutive₁ (α := Difference ℕ) (-·) (· ≃ ·) (· ≃ ·)
    := {
  subst₁ := neg_subst
}

def negation : Negation.Base (Difference ℕ) := {
  negOp := negOp
  neg_substitutive := neg_substitutive
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

/--
Multiplication of natural number differences is commutative.

**Proof intuition**: Expand definitions to see that we need to show the
equivalence of two differences of natural number sums of products. The left and
right elements of the differences are directly equivalent via commutativity of
natural number addition and multiplication, so convert the differences into
ordered pairs and use commutativity element-wise.
-/
theorem mul_comm {a b : Difference ℕ} : a * b ≃ b * a := by
  revert a; intro (n——m); revert b; intro (k——j)
  show n——m * k——j ≃ k——j * n——m
  show (n * k + m * j)——(n * j + m * k) ≃ (k * n + j * m)——(k * m + j * n)
  show from_prod (n * k + m * j, n * j + m * k)
     ≃ from_prod (k * n + j * m, k * m + j * n)
  apply AA.subst₁
  show (n * k + m * j, n * j + m * k) ≃ (k * n + j * m, k * m + j * n)
  calc
    (n * k + m * j, n * j + m * k) ≃ _ := AA.substL (AA.substL AA.comm)
    (k * n + m * j, n * j + m * k) ≃ _ := AA.substL (AA.substR AA.comm)
    (k * n + j * m, n * j + m * k) ≃ _ := AA.substR (AA.substL AA.comm)
    (k * n + j * m, j * n + m * k) ≃ _ := AA.substR (AA.substR AA.comm)
    (k * n + j * m, j * n + k * m) ≃ _ := AA.substR AA.comm
    (k * n + j * m, k * m + j * n) ≃ _ := Rel.refl

instance mul_commutative : AA.Commutative (α := Difference ℕ) (· * ·) := {
  comm := mul_comm
}

/--
Multiplying the same difference on the right of two equivalent differences
preserves their equivalence.

**Proof intuition**: The property is already intuitively true; imagine
stretching two line segments of the same length by the same amount. So the
proof just expands all definitions into equalities of sums of products of
natural numbers, and performs algebra to obtain the desired result.
-/
theorem mul_substL {a₁ a₂ b : Difference ℕ} : a₁ ≃ a₂ → a₁ * b ≃ a₂ * b := by
  revert a₁; intro (n——m); revert a₂; intro (k——j); revert b; intro (p——q)
  intro (_ : n——m ≃ k——j)
  have h : n + j ≃ k + m := ‹n——m ≃ k——j›
  show n——m * p——q ≃ k——j * p——q
  show (n * p + m * q)——(n * q + m * p) ≃ (k * p + j * q)——(k * q + j * p)
  show (n * p + m * q) + (k * q + j * p) ≃ (k * p + j * q) + (n * q + m * p)
  calc
    (n * p + m * q) + (k * q + j * p) ≃ _ := Rel.symm expand_swap
    (n + j) * p     + (k + m) * q     ≃ _ := AA.substL (AA.substL h)
    (k + m) * p     + (k + m) * q     ≃ _ := AA.substR (AA.substL (Rel.symm h))
    (k + m) * p     + (n + j) * q     ≃ _ := expand_swap
    (k * p + j * q) + (n * q + m * p) ≃ _ := Rel.refl
where
  expand_swap
      {u v w x y z : ℕ}
      : (w + x) * u + (y + z) * v ≃ (w * u + z * v) + (y * v + x * u)
      := calc
    (w + x) * u     + (y + z) * v     ≃ _ := AA.substL AA.distribR
    (w * u + x * u) + (y + z) * v     ≃ _ := AA.substR AA.distribR
    (w * u + x * u) + (y * v + z * v) ≃ _ := AA.expr_xxfxxff_lr_swap_rr
    (w * u + z * v) + (y * v + x * u) ≃ _ := Rel.refl

def mul_substitutiveL
    : AA.SubstitutiveOn
      Hand.L (α := Difference ℕ) (· * ·) AA.tc (· ≃ ·) (· ≃ ·) := {
  subst₂ := λ (_ : True) => mul_substL
}

def mul_substitutive
    : AA.Substitutive₂ (α := Difference ℕ) (· * ·) AA.tc (· ≃ ·) (· ≃ ·) := {
  substitutiveL := mul_substitutiveL
  substitutiveR := AA.substR_from_substL_swap (rS := (· ≃ ·)) mul_substitutiveL
}

def multiplication : Multiplication.Base (Difference ℕ) := {
  mulOp := mulOp
  mul_commutative := mul_commutative
  mul_substitutive := mul_substitutive
}

instance integer : Integer ℕ (Difference ℕ) := {
  toAddition := addition
  toConversion := conversion
  toEquality := equality
  toMultiplication := multiplication
  toNegation := negation
}

end Lean4Axiomatic.Integer.Impl.Difference
