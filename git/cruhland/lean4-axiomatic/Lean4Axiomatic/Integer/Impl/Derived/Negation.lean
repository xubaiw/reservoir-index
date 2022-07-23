import Lean4Axiomatic.Integer.Negation

namespace Lean4Axiomatic.Integer.Impl.Derived

variable {ℕ : Type}
variable [Natural ℕ]
variable {ℤ : Type}
variable [Core.Derived ℕ ℤ]
variable [Addition.Base ℕ ℤ]
variable [Multiplication.Base ℕ ℤ]
variable [Negation.Base ℕ ℤ]

namespace Base
export Negation (trichotomy)
end Base

/--
Zero is a left absorbing element for multiplication.

**Property intuition**: A sum of zero terms should produce the empty sum, i.e.
the additive identity, which is zero.

**Proof intuition**: The only way to produce zero by itself, given the
properties of integer addition and multiplication, is by adding a value to its
negation. So we somehow need to obtain `0 * a + -(0 * a)` from `0 * a`. We can
easily get `0 * a + (0 * a + -(0 * a))` from the additive identity and inverse
properties. The key is then using associativity, distributivity, and again
additive identity to merge the two instances of `0 * a` into one.
-/
def mul_absorbL {a : ℤ} : 0 * a ≃ 0 := calc
  0 * a                      ≃ _ := Rel.symm AA.identR
  0 * a + 0                  ≃ _ := AA.substR (Rel.symm AA.inverseR)
  0 * a + (0 * a + -(0 * a)) ≃ _ := Rel.symm AA.assoc
  (0 * a + 0 * a) + -(0 * a) ≃ _ := AA.substL (Rel.symm AA.distribR)
  (0 + 0) * a + -(0 * a)     ≃ _ := AA.substL (AA.substL AA.identL)
  0 * a + -(0 * a)           ≃ _ := AA.inverseR
  (0 : ℤ)                    ≃ _ := Rel.refl

def mul_absorbingL : AA.AbsorbingOn Hand.L (α := ℤ) 0 (· * ·) := {
  absorb := mul_absorbL
}

local instance mul_absorbing : AA.Absorbing (α := ℤ) 0 (· * ·) := {
  absorbingL := mul_absorbingL
  absorbingR := AA.absorbingR_from_absorbingL mul_absorbingL
}

/--
Negation is left-semicompatible with multiplication.

**Property intuition**: Negating the sum of `b` copies of `a` should be the
same as the sum of `b` copies of `-a`.

**Proof intuition**: We're showing how negation and multiplication interact, so
there's no preexisting property that tells us how to manipulate `-(a * b)`. The
next best thing is to try to introduce some new terms, one of which is our
desired result `(-a) * b`, but the other is `a * b` to cancel out `-(a * b)`.
And it turns out those new terms have a factor of `b` in common, so we can
produce them using distributivity and the additive inverse property.
-/
theorem neg_scompatL_mul {a b : ℤ} : -(a * b) ≃ (-a) * b := calc
  -(a * b)
    ≃ _ := Rel.symm AA.identL
  0 + -(a * b)
    ≃ _ := AA.substL (Rel.symm AA.absorbL)
  0 * b + -(a * b)
    ≃ _ := AA.substL (AA.substL (Rel.symm AA.inverseL))
  (-a + a) * b + -(a * b)
    ≃ _ := AA.substL AA.distribR
  (-a * b + a * b) + -(a * b)
    ≃ _ := AA.assoc
  (-a) * b + (a * b + -(a * b))
    ≃ _ := AA.substR AA.inverseR
  (-a) * b + 0
    ≃ _ := AA.identR
  (-a) * b
    ≃ _ := Rel.refl

def neg_semicompatibleL_mul
    : AA.SemicompatibleOn Hand.L (α := ℤ) (-·) (· * ·)
    := {
  scompat := neg_scompatL_mul
}

local instance neg_semicompatible_mul
    : AA.Semicompatible (α := ℤ) (-·) (· * ·)
    := {
  semicompatibleL :=
    neg_semicompatibleL_mul
  semicompatibleR :=
    AA.semicompatibleR_from_semicompatibleL neg_semicompatibleL_mul
}

/--
Negation is an involution; applying it twice is equivalent to not applying it
at all.

**Property intuition**: Negation transforms an integer into its "mirror image"
reflection across zero. Reflecting twice gives back the original integer.

**Proof intuition**: The value `-a` is the additive inverse of `-(-a)` and also
`a`. Thus, it can be used as an intermediate to replace one with the other.
-/
theorem neg_involutive {a : ℤ} : -(-a) ≃ a := calc
  -(-a)            ≃ _ := Rel.symm AA.identL
  0 + -(-a)        ≃ _ := AA.substL (Rel.symm AA.inverseR)
  (a + -a) + -(-a) ≃ _ := AA.assoc
  a + (-a + -(-a)) ≃ _ := AA.substR AA.inverseR
  a + 0            ≃ _ := AA.identR
  a                ≃ _ := Rel.refl

/--
A positive or negative integer of unit magnitude.

Only `1` and `-1` satisfy this property. It's formulated using multiplication
to be easy to use with algebra.

**Named parameters**
- `a`: The integer satisfying the property.
-/
def SquareRootOfUnity (a : ℤ) : Prop := a * a ≃ 1

/--
A positive or negative integer.

Represents nonzero integers as the product of a nonzero sign (`1` or `-1`) and
a positive magnitude. This is convenient for use in algebraic proofs.

**Named parameters**
- `a`: The integer satisfying the property.
-/
inductive Nonzero (a : ℤ) : Prop :=
| /--
  Construct evidence that the integer `a` is nonzero.

  **Named parameters**
  - `sign`: Has value `1` if `a` is positive, or `-1` if `a` is negative.
  - `magnitude`: The distance of `a` from zero, as a natural number.
  - `sqrt_1`: Evidence that `sign` is `1` or `-1`.
  - `pos`: Evidence that `magnitude` is positive.
  - `prod`: Evidence that `a` is a positive or negative value.
  -/
  intro
    (sign : ℤ)
    (magnitude : ℕ)
    (sqrt_1 : SquareRootOfUnity sign)
    (pos : Positive magnitude)
    (prod : a ≃ sign * ↑magnitude)

/--
Expresses that one of two propositions is true, but not both.

**Named parameters**
- `α`, `β`: The two propositions.
-/
def ExactlyOneOfTwo (α β : Prop) : Prop := (α ∨ β) ∧ ¬ (α ∧ β)

section

open Natural (step)

/--
Zero is the only natural number less than one.

This is a lemma to help with the proof of `natural_sqrt_1` below.
-/
theorem zero_lt_one {n : ℕ} : n < 1 ↔ n ≃ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : n < 1)
    show n ≃ 0
    have : n < step 0 := AA.substRFn Natural.literal_step ‹n < 1›
    have : n < 0 ∨ n ≃ 0 := Natural.lt_split ‹n < step 0›
    match ‹n < 0 ∨ n ≃ 0› with
    | Or.inl (_ : n < 0) => exact absurd ‹n < 0› Natural.lt_zero
    | Or.inr (_ : n ≃ 0) => exact ‹n ≃ 0›
  case mpr =>
    intro (_ : n ≃ 0)
    show n < 1
    have : (0 : ℕ) < step 0 := Natural.lt_step
    have : n < step 0 := AA.substLFn (Rel.symm ‹n ≃ 0›) ‹(0 : ℕ) < step 0›
    have : n < 1 := AA.substRFn (Rel.symm Natural.literal_step) ‹n < step 0›
    exact ‹n < 1›

/--
The only square root of unity in the natural numbers is `1`.

**Property and proof intuition**: It can only be one, because zero squared is
zero, and squaring any natural number greater than one always produces a larger
result.
-/
theorem natural_sqrt_1 {n : ℕ} : n * n ≃ 1 ↔ n ≃ 1 := by
  apply Iff.intro
  case mp =>
    intro (_ : n * n ≃ 1)
    show n ≃ 1
    have tri_n_1 : AA.ExactlyOneOfThree (n < 1) (n ≃ 1) (n > 1) :=
      Natural.trichotomy n 1
    match tri_n_1.atLeastOne with
    | AA.OneOfThree.first (_ : n < 1) =>
      apply False.elim
      show False
      have : n ≃ 0 := zero_lt_one.mp ‹n < 1›
      have : step 0 ≃ 0 := calc
        step 0  ≃ _ := Rel.symm Natural.literal_step
        1       ≃ _ := Rel.symm ‹n * n ≃ 1›
        n * n   ≃ _ := AA.substL ‹n ≃ 0›
        0 * n   ≃ _ := AA.absorbL
        0       ≃ _ := Rel.refl
      exact absurd ‹step (0 : ℕ) ≃ 0› Natural.step_neq_zero
    | AA.OneOfThree.second (_ : n ≃ 1) =>
      exact ‹n ≃ 1›
    | AA.OneOfThree.third (_ : n > 1) =>
      apply False.elim
      show False
      apply tri_n_1.atMostOne
      show AA.TwoOfThree (n < 1) (n ≃ 1) (n > 1)
      have : step 0 < n := AA.substLFn Natural.literal_step ‹1 < n›
      have : 0 < n := Rel.trans Natural.lt_step ‹step 0 < n›
      have : Positive n := Natural.lt_zero_pos.mpr ‹0 < n›
      have : 1 * n < n * n := AA.substLC ‹Positive n› ‹1 < n›
      have : n < n * n := AA.substLFn AA.identL ‹1 * n < n * n›
      have : n < 1 := AA.substRFn ‹n * n ≃ 1› ‹n < n * n›
      exact AA.TwoOfThree.oneAndThree ‹n < 1› ‹n > 1›
  case mpr =>
    intro (_ : n ≃ 1)
    show n * n ≃ 1
    calc
      n * n ≃ _ := AA.substL ‹n ≃ 1›
      1 * n ≃ _ := AA.identL
      n     ≃ _ := ‹n ≃ 1›
      1     ≃ _ := Rel.refl

end

/--
The only square roots of unity in the integers are `1` and `-1`.

**Property and proof intuition**: This follows from similar reasoning as
`natural_sqrt_1`. Zero squared is zero, and integers greater than one or less
than negative one all have squares that are greater than one.
-/
theorem sqrt_1_cases {a : ℤ} : SquareRootOfUnity a ↔ a ≃ 1 ∨ a ≃ -1 := by
  apply Iff.intro
  case mp =>
    intro (_ : a * a ≃ 1)
    show a ≃ 1 ∨ a ≃ -1
    have from_nat_subst :=
      @AA.subst₁ (self := Conversion.from_natural_substitutive)
    match (Base.trichotomy a).atLeastOne with
    | AA.OneOfThree.first
        (_ : a ≃ 0) =>
      apply False.elim
      show False
      have : 1 ≃ 0 := calc
        1       ≃ _ := Rel.symm ‹a * a ≃ 1›
        a * a   ≃ _ := AA.substL ‹a ≃ 0›
        0 * a   ≃ _ := AA.absorbL
        0       ≃ _ := Rel.refl
      exact absurd ‹(1 : ℤ) ≃ 0› Core.one_neqv_zero
    | AA.OneOfThree.second
        (Exists.intro n (And.intro (_ : Positive n) (_ : a ≃ ↑n))) =>
      apply Or.inl
      show a ≃ 1
      have : ↑(n * n) ≃ ↑(1 : ℕ) := calc
        ↑(n * n) ≃ _ := AA.compat₂ (f := (↑·))
        ↑n * ↑n  ≃ _ := AA.substL (Rel.symm ‹a ≃ ↑n›)
        a * ↑n   ≃ _ := AA.substR (Rel.symm ‹a ≃ ↑n›)
        a * a    ≃ _ := ‹a * a ≃ 1›
        1        ≃ _ := Rel.refl
      have : n * n ≃ 1 := AA.inject ‹↑(n * n) ≃ ↑(1 : ℕ)›
      have : n ≃ 1 := natural_sqrt_1.mp ‹n * n ≃ 1›
      calc
        a       ≃ _ := ‹a ≃ ↑n›
        ↑n      ≃ _ := from_nat_subst ‹n ≃ 1›
        ↑1      ≃ _ := Rel.refl
        (1 : ℤ) ≃ _ := Rel.refl
    | AA.OneOfThree.third
        (Exists.intro n (And.intro (_ : Positive n) (_ : a ≃ -↑n))) =>
      apply Or.inr
      show a ≃ -1
      have : ↑(n * n) ≃ ↑(1 : ℕ) := calc
        ↑(n * n)        ≃ _ := AA.compat₂ (f := (↑·))
        ↑n * ↑n         ≃ _ := Rel.symm neg_involutive
        (-(-(↑n * ↑n))) ≃ _ := AA.subst₁ AA.scompatR
        (-(↑n * -↑n))   ≃ _ := AA.scompatL
        (-↑n) * (-↑n)   ≃ _ := AA.substL (Rel.symm ‹a ≃ -↑n›)
        a * (-↑n)       ≃ _ := AA.substR (Rel.symm ‹a ≃ -↑n›)
        a * a           ≃ _ := ‹a * a ≃ 1›
        1               ≃ _ := Rel.refl
      have : n * n ≃ 1 := AA.inject ‹↑(n * n) ≃ ↑(1 : ℕ)›
      have : n ≃ 1 := natural_sqrt_1.mp ‹n * n ≃ 1›
      calc
        a     ≃ _ := ‹a ≃ -↑n›
        (-↑n) ≃ _ := AA.subst₁ (from_nat_subst ‹n ≃ 1›)
        (-↑1) ≃ _ := Rel.refl
        (-1)  ≃ _ := Rel.refl
  case mpr =>
    intro (_ : a ≃ 1 ∨ a ≃ -1)
    show a * a ≃ 1
    match ‹a ≃ 1 ∨ a ≃ -1› with
    | Or.inl (_ : a ≃ 1) => calc
      a * a ≃ _ := AA.substL ‹a ≃ 1›
      1 * a ≃ _ := AA.identL
      a     ≃ _ := ‹a ≃ 1›
      1     ≃ _ := Rel.refl
    | Or.inr (_ : a ≃ -1) => calc
      a * a      ≃ _ := AA.substR ‹a ≃ -1›
      a * -1     ≃ _ := Rel.symm AA.scompatR
      (-(a * 1)) ≃ _ := AA.subst₁ AA.identR
      (-a)       ≃ _ := AA.subst₁ ‹a ≃ -1›
      (-(-1))    ≃ _ := neg_involutive
      1          ≃ _ := Rel.refl

/--
Provide evidence that an integer is equivalent, or not equivalent, to zero.

**Property and proof intuition**: We already know from trichotomy of integers
that every integer is either zero, positive, or negative, and never more than
one of those at the same time. Combine the positive and negative categories to
obtain this result.
-/
theorem zero? (a : ℤ) : ExactlyOneOfTwo (a ≃ 0) (Nonzero a) := by
  have tri : AA.ExactlyOneOfThree
      (a ≃ 0)
      (∃ n, Positive n ∧ a ≃ ↑n)
      (∃ n, Positive n ∧ a ≃ -↑n)
      :=
    Base.trichotomy a
  apply And.intro
  case left =>
    show a ≃ 0 ∨ Nonzero a
    match tri.atLeastOne with
    | AA.OneOfThree.first (_ : a ≃ 0) =>
      exact Or.inl ‹a ≃ 0›
    | AA.OneOfThree.second (a_pos : ∃ n, Positive n ∧ a ≃ ↑n) =>
      have (Exists.intro n (And.intro (_ : Positive n) (_ : a ≃ ↑n))) := a_pos
      apply Or.inr
      show Nonzero a
      apply Nonzero.intro 1 n
      case h.sqrt_1 =>
        show SquareRootOfUnity 1
        exact sqrt_1_cases.mpr (Or.inl Rel.refl)
      case h.pos =>
        show Positive n
        exact ‹Positive n›
      case h.prod =>
        show a ≃ 1 * ↑n
        calc
          a      ≃ _ := ‹a ≃ ↑n›
          ↑n     ≃ _ := Rel.symm AA.identL
          1 * ↑n ≃ _ := Rel.refl
    | AA.OneOfThree.third (a_neg : ∃ n, Positive n ∧ a ≃ -↑n) =>
      have (Exists.intro n (And.intro (_ : Positive n) (_ : a ≃ -↑n))) := a_neg
      apply Or.inr
      show Nonzero a
      apply Nonzero.intro (-1) n
      case h.sqrt_1 =>
        show SquareRootOfUnity (-1)
        exact sqrt_1_cases.mpr (Or.inr Rel.refl)
      case h.pos =>
        show Positive n
        exact ‹Positive n›
      case h.prod =>
        show a ≃ -1 * ↑n
        calc
          a           ≃ _ := ‹a ≃ -↑n›
          (-↑n)       ≃ _ := AA.subst₁ (Rel.symm AA.identL)
          (-(1 * ↑n)) ≃ _ := AA.scompatL
          (-1) * ↑n   ≃ _ := Rel.refl
  case right =>
    intro (And.intro (_ : a ≃ 0) (_ : Nonzero a))
    show False
    apply tri.atMostOne
    show AA.TwoOfThree
      (a ≃ 0)
      (∃ n, Positive n ∧ a ≃ ↑n)
      (∃ n, Positive n ∧ a ≃ -↑n)
    have (Nonzero.intro s m
        (_ : SquareRootOfUnity s) (_ : Positive m) (_ : a ≃ s * ↑m))
      := ‹Nonzero a›
    have : s ≃ 1 ∨ s ≃ -1 := sqrt_1_cases.mp ‹SquareRootOfUnity s›
    match ‹s ≃ 1 ∨ s ≃ -1› with
    | Or.inl (_ : s ≃ 1) =>
      have : a ≃ ↑m := calc
        a      ≃ _ := ‹a ≃ s * ↑m›
        s * ↑m ≃ _ := AA.substL ‹s ≃ 1›
        1 * ↑m ≃ _ := AA.identL
        ↑m     ≃ _ := Rel.refl
      have : ∃ n, Positive n ∧ a ≃ ↑n :=
        Exists.intro m (And.intro ‹Positive m› ‹a ≃ ↑m›)
      exact AA.TwoOfThree.oneAndTwo ‹a ≃ 0› ‹∃ n, Positive n ∧ a ≃ ↑n›
    | Or.inr (_ : s ≃ -1) =>
      have : a ≃ -↑m := calc
        a           ≃ _ := ‹a ≃ s * ↑m›
        s * ↑m      ≃ _ := AA.substL ‹s ≃ -1›
        (-1) * ↑m   ≃ _ := Rel.symm AA.scompatL
        (-(1 * ↑m)) ≃ _ := AA.subst₁ AA.identL
        (-↑m)       ≃ _ := Rel.refl
      have : ∃ n, Positive n ∧ a ≃ -↑n :=
        Exists.intro m (And.intro ‹Positive m› ‹a ≃ -↑m›)
      exact
        AA.TwoOfThree.oneAndThree ‹a ≃ 0› ‹∃ n, Positive n ∧ a ≃ -↑n›

/--
The product of nonzero integers is nonzero.

**Property and proof intuition**: Integers can be viewed as natural numbers
(i.e. magnitudes) with signs (i.e. one-dimensional directions). We already
know that nonzero natural numbers are preserved under multiplication. The same
is true for signs: the sign of a product will never be zero if the factors also
have nonzero (i.e. positive or negative) signs. Thus there is no way for a
product of nonzero integers to become zero.
-/
theorem mul_preserves_nonzero
    {a b : ℤ} : Nonzero a → Nonzero b → Nonzero (a * b)
    := by
  intro (Nonzero.intro as am
      (_ : SquareRootOfUnity as) (_ : Positive am) (_ : a ≃ as * ↑am))
  intro (Nonzero.intro bs bm
      (_ : SquareRootOfUnity bs) (_ : Positive bm) (_ : b ≃ bs * ↑bm))
  show Nonzero (a * b)
  apply Nonzero.intro (as * bs) (am * bm)
  case sqrt_1 =>
    show SquareRootOfUnity (as * bs)
    have : as * as ≃ 1 := ‹SquareRootOfUnity as›
    have : bs * bs ≃ 1 := ‹SquareRootOfUnity bs›
    show (as * bs) * (as * bs) ≃ 1
    calc
      (as * bs) * (as * bs) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
      (as * as) * (bs * bs) ≃ _ := AA.substL ‹as * as ≃ 1›
      1 * (bs * bs)         ≃ _ := AA.substR ‹bs * bs ≃ 1›
      1 * 1                 ≃ _ := AA.identL
      1                     ≃ _ := Rel.refl
  case pos =>
    show Positive (am * bm)
    exact Natural.mul_positive ‹Positive am› ‹Positive bm›
  case prod =>
    show a * b ≃ (as * bs) * ↑(am * bm)
    calc
      a * b
        ≃ _ := AA.substL ‹a ≃ as * ↑am›
      (as * ↑am) * b
        ≃ _ := AA.substR ‹b ≃ bs * ↑bm›
      (as * ↑am) * (bs * ↑bm)
        ≃ _ := AA.expr_xxfxxff_lr_swap_rl
      (as * bs) * (↑am * ↑bm)
        ≃ _ := AA.substR (Rel.symm (AA.compat₂ (f := (↑·))))
      (as * bs) * ↑(am * bm)
        ≃ _ := Rel.refl

/--
For a product of integers to be zero, at least one of its factors must be zero.

**Property and proof intuition**: This property alone is not very intuitive, or
at least the forward direction isn't. But eliminating the obvious cases where
either `a` or `b` are zero reduces the problem to showing that if `a` and `b`
are both nonzero, then their product must be nonzero as well. And that has some
intuitive justification; see `mul_preserves_nonzero`.
-/
theorem mul_split_zero {a b : ℤ} : a * b ≃ 0 ↔ a ≃ 0 ∨ b ≃ 0 := by
  apply Iff.intro
  case mp =>
    intro (_ : a * b ≃ 0)
    show a ≃ 0 ∨ b ≃ 0
    have : a ≃ 0 ∨ Nonzero a := (zero? a).left
    match ‹a ≃ 0 ∨ Nonzero a› with
    | Or.inl (_ : a ≃ 0) =>
      exact Or.inl ‹a ≃ 0›
    | Or.inr (_ : Nonzero a) =>
      have : b ≃ 0 ∨ Nonzero b := (zero? b).left
      match ‹b ≃ 0 ∨ Nonzero b› with
      | Or.inl (_ : b ≃ 0) =>
        exact Or.inr ‹b ≃ 0›
      | Or.inr (_ : Nonzero b) =>
        apply False.elim
        show False
        have : ¬ (a * b ≃ 0 ∧ Nonzero (a * b)) := (zero? (a * b)).right
        apply this
        show a * b ≃ 0 ∧ Nonzero (a * b)
        apply And.intro
        · exact ‹a * b ≃ 0›
        · exact mul_preserves_nonzero ‹Nonzero a› ‹Nonzero b›
  case mpr =>
    intro (_ : a ≃ 0 ∨ b ≃ 0)
    show a * b ≃ 0
    match ‹a ≃ 0 ∨ b ≃ 0› with
    | Or.inl (_ : a ≃ 0) => calc
      a * b ≃ _ := AA.substL ‹a ≃ 0›
      0 * b ≃ _ := AA.absorbL
      0     ≃ _ := Rel.refl
    | Or.inr (_ : b ≃ 0) => calc
      a * b ≃ _ := AA.substR ‹b ≃ 0›
      a * 0 ≃ _ := AA.absorbR
      0     ≃ _ := Rel.refl

def negation : Negation.Derived ℕ ℤ := {
  mul_absorbing := mul_absorbing
  neg_semicompatible_mul := neg_semicompatible_mul
  neg_involutive := neg_involutive
}

end Lean4Axiomatic.Integer.Impl.Derived
