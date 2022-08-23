import Lean4Axiomatic.Integer.Negation
import Lean4Axiomatic.Sign

/-!
# Integer signedness
-/

namespace Lean4Axiomatic.Integer

open Signed (Negative Positive)

/-!
## Preliminary definitions and theorems
-/

section prelim

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℕ ℤ]
variable [Addition ℕ ℤ] [Multiplication ℕ ℤ] [Negation ℕ ℤ]

/--
A positive or negative integer of unit magnitude.

Only `1` and `-1` satisfy this property. It's formulated using multiplication
to be easy to use with algebra.

**Named parameters**
- `a`: The integer satisfying the property.
-/
def SquareRootOfUnity (a : ℤ) : Prop := a * a ≃ 1

/--
The `SquareRootOfUnity` predicate respects equivalence.

**Property intuition**: This must be true for `SquareRootOfUnity` to make sense
as a predicate.

**Proof intuition**: Expand the definition of `SquareRootOfUnity` to obtain an
equivalence involving multiplication. Since multiplication is substitutive, the
result follows easily.
-/
theorem sqrt1_subst
    {a₁ a₂ : ℤ} : a₁ ≃ a₂ → SquareRootOfUnity a₁ → SquareRootOfUnity a₂
    := by
  intro (_ : a₁ ≃ a₂) (_ : a₁ * a₁ ≃ 1)
  show a₂ * a₂ ≃ 1
  calc
    a₂ * a₂ ≃ _ := AA.substL (Rel.symm ‹a₁ ≃ a₂›)
    a₁ * a₂ ≃ _ := AA.substR (Rel.symm ‹a₁ ≃ a₂›)
    a₁ * a₁ ≃ _ := ‹a₁ * a₁ ≃ 1›
    1       ≃ _ := Rel.refl

instance sqrt1_substitutive
    : AA.Substitutive₁ SquareRootOfUnity (· ≃ ·) (· → ·)
    := {
  subst₁ := sqrt1_subst
}

/-- One is a square root of unity. -/
theorem sqrt1_one : SquareRootOfUnity 1 := by
  show 1 * 1 ≃ 1
  exact AA.identL

/--
Negative one is a square root of unity.

**Property and proof intuition**: Multiplying two negative numbers gives a
positive result, and if the magnitudes are `1`, the result will also be `1`.
-/
theorem sqrt1_neg_one : SquareRootOfUnity (-1) := by
  show (-1) * (-1) ≃ 1
  calc
    (-1) * (-1)   ≃ _ := Rel.symm AA.scompatL
    (-(1 * (-1))) ≃ _ := AA.subst₁ (Rel.symm AA.scompatR)
    (-(-(1 * 1))) ≃ _ := neg_involutive
    1 * 1         ≃ _ := sqrt1_one
    1             ≃ _ := Rel.refl

/--
The product of square roots of unity is also a square root of unity.

This is an important result; it means that positive and negative signs can be
represented by integers, allowing derivations using algebra.

**Property intuition**: A factor of `1` or `-1` in a product does not change
the magnitude of the result. Thus, regardless of the signs involved, a product
of two square roots of unity can only be `1` or `-1`.

**Proof intuition**: Rearrange factors with associativity to isolate `a` and
`b` into products with themselves. By the definition of `SquareRootOfUnity`,
those products must each be `1`; thus the product of the products is also `1`.
-/
theorem mul_preserves_sqrt1
    {a b : ℤ}
    : SquareRootOfUnity a → SquareRootOfUnity b → SquareRootOfUnity (a * b)
    := by
  intro (_ : a * a ≃ 1) (_ : b * b ≃ 1)
  show (a * b) * (a * b) ≃ 1
  calc
    (a * b) * (a * b) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (a * a) * (b * b) ≃ _ := AA.substL ‹a * a ≃ 1›
    1 * (b * b)       ≃ _ := AA.substR ‹b * b ≃ 1›
    1 * 1             ≃ _ := sqrt1_one
    1                 ≃ _ := Rel.refl

/--
Demonstrates that an integer can be factored into _sign_ and _magnitude_
components.

The sign value is either positive (represented by `1`) or negative (represented
by `-1`). The magnitude must be a positive natural number.

This data structure is a foundation for defining the `Positive`, `Negative`,
and `Nonzero` predicates on integers.

**Parameters**
- `a`: The integer to represent in signed-magnitude form.
- `s`: The sign value.
- `SquareRootOfUnity s`: Ensures that `s` is either `1` or `-1`.
-/
inductive SignedMagnitude (a : ℤ) {s : ℤ} (_ : SquareRootOfUnity s) : Prop
| /--
  `SignedMagnitude`'s only constructor.

  **Parameters**
  - `m`: The magnitude value.
  - `pos`: Ensures a positive magnitude.
  - `eqv`: Proof that `a` is a product of the sign and the magnitude.
  -/
  intro (m : ℕ) (pos : Positive m) (eqv : a ≃ s * m)

/-- Extract the `Positive` field from `SignedMagnitude`. -/
def SignedMagnitude.pos
    {a s : ℤ} {sqrt1 : SquareRootOfUnity s}
    : SignedMagnitude a sqrt1 → ∃ (n : ℕ), Positive n
    := by
  intro (SignedMagnitude.intro m (_ : Positive m) (_ : a ≃ s * ↑m))
  exists m
  exact ‹Positive m›

/-- Extract the underlying equivalence from `SignedMagnitude`. -/
def SignedMagnitude.eqv
    {a s : ℤ} {sqrt1 : SquareRootOfUnity s}
    : SignedMagnitude a sqrt1 → ∃ (n : ℕ), a ≃ s * ↑n
    := by
  intro (SignedMagnitude.intro m (_ : Positive m) (_ : a ≃ s * ↑m))
  exists m
  exact ‹a ≃ s * ↑m›

/--
`SignedMagnitude` respects equivalence of signs.

**Property intuition**: If signs `s₁` and `s₂` are equivalent, and we have a
`SignedMagnitude` for `s₁`, then that can be converted into a `SignedMagnitude`
for `s₂`. This _must_ be true for `SignedMagnitude` to be a valid predicate.

**Proof intuition**: Extract the equivalence for `s₁`, substitute `s₂` into it,
and build a new `SignedMagnitude` on `s₂`.
-/
theorem signedMagnitude_sqrt1_subst
    {a s₁ s₂ : ℤ} {_ : SquareRootOfUnity s₁} (_ : s₁ ≃ s₂)
    : SignedMagnitude a ‹SquareRootOfUnity s₁›
    → have : SquareRootOfUnity s₂ :=
        AA.subst₁ (rβ := (· → ·)) ‹s₁ ≃ s₂› ‹SquareRootOfUnity s₁›
      SignedMagnitude a ‹SquareRootOfUnity s₂›
    := by
  intro (SignedMagnitude.intro (m : ℕ) (_ : Positive m) (_ : a ≃ s₁ * ↑m))
  have : a ≃ s₂ * ↑m := Rel.trans ‹a ≃ s₁ * ↑m› (AA.substL ‹s₁ ≃ s₂›)
  exact SignedMagnitude.intro m ‹Positive m› ‹a ≃ s₂ * ↑m›

/--
Given two integers in signed-magnitude form, we can put their product in
signed-magnitude form as well.

**Property intuition**: This seems plausible, if only because every integer can
be put into signed-magnitude form.

**Proof intuition**: From previous results, we know that multiplication
preserves `SquareRootOfUnity`, and `Positive` on natural numbers. Then we just
need to show that the product of two signed-magnitude forms can itself be put
into signed-magnitude form; this follows mostly from algebra on multiplication.
-/
theorem mul_preserves_signedMagnitude
    {a b as bs : ℤ}
    {a_sqrt1 : SquareRootOfUnity as} {b_sqrt1 : SquareRootOfUnity bs}
    : SignedMagnitude a a_sqrt1 → SignedMagnitude b b_sqrt1
    → have : SquareRootOfUnity (as * bs) := mul_preserves_sqrt1 a_sqrt1 b_sqrt1
      SignedMagnitude (a * b) ‹SquareRootOfUnity (as * bs)›
    := by
  intro (SignedMagnitude.intro (am : ℕ) (_ : Positive am) (_ : a ≃ as * ↑am))
  intro (SignedMagnitude.intro (bm : ℕ) (_ : Positive bm) (_ : b ≃ bs * ↑bm))
  have : SquareRootOfUnity (as * bs) := mul_preserves_sqrt1 a_sqrt1 b_sqrt1
  show SignedMagnitude (a * b) ‹SquareRootOfUnity (as * bs)›
  have : Positive (am * bm) := Natural.mul_positive ‹Positive am› ‹Positive bm›
  have : a * b ≃ (as * bs) * ↑(am * bm) := calc
    a * b                   ≃ _ := AA.substL ‹a ≃ as * ↑am›
    (as * ↑am) * b          ≃ _ := AA.substR ‹b ≃ bs * ↑bm›
    (as * ↑am) * (bs * ↑bm) ≃ _ := AA.expr_xxfxxff_lr_swap_rl
    (as * bs) * (↑am * ↑bm) ≃ _ := AA.substR (Rel.symm (AA.compat₂ (f := (↑·))))
    (as * bs) * ↑(am * bm)  ≃ _ := Rel.refl
  exact SignedMagnitude.intro
    (am * bm) ‹Positive (am * bm)› ‹a * b ≃ (as * bs) * ↑(am * bm)›

/--
A positive or negative integer.

Represents nonzero integers as the product of a nonzero sign (`1` or `-1`) and
a positive magnitude. This is convenient for use in algebraic proofs.

**Parameters**
- `a`: The integer that is positive or negative.
-/
inductive Nonzero (a : ℤ) : Prop :=
| /--
  Construct evidence that the integer `a` is nonzero.

  **Parameters**
  - See `Nonzero` for the class-level parameters.
  - `sign`: Has value `1` if `a` is positive, or `-1` if `a` is negative.
  - `sqrt1`: Evidence that `sign` is `1` or `-1`.
  - `sm`: Evidence that `sign` denotes the sign of `a`.
  -/
  intro
    (sign : ℤ)
    (sqrt1 : SquareRootOfUnity sign)
    (sm : SignedMagnitude a sqrt1)

/--
Convenience constructor that infers early arguments of `Nonzero.intro` from the
last, `SignedMagnitude` argument.
-/
def Nonzero.mk
    {a s : ℤ} {sqrt1 : SquareRootOfUnity s}
    : SignedMagnitude a sqrt1 → Nonzero a :=
  Nonzero.intro s sqrt1

/-- Extract the proof of `SquareRootOfUnity` from `Nonzero`. -/
def Nonzero.sqrt1 {a : ℤ} : Nonzero a → ∃ (s : ℤ), SquareRootOfUnity s := by
  intro (Nonzero.intro (s : ℤ) (sqrt1 : SquareRootOfUnity s) _)
  exists s
  exact ‹SquareRootOfUnity s›

/--
The product of nonzero integers is nonzero.

**Property and proof intuition**: `Nonzero` can be decomposed into a sign value
and a `SignedMagnitude` value. Previous results have shown that both of those
components are preserved under multiplication, so a `Nonzero` value for the
product of `Nonzero` integers can always be constructed.
-/
theorem mul_preserves_nonzero
    {a b : ℤ} : Nonzero a → Nonzero b → Nonzero (a * b)
    := by
  intro (Nonzero.intro as
      (a_sqrt1 : SquareRootOfUnity as) (a_sm : SignedMagnitude a a_sqrt1))
  intro (Nonzero.intro bs
      (b_sqrt1 : SquareRootOfUnity bs) (b_sm : SignedMagnitude b b_sqrt1))
  show Nonzero (a * b)
  have : SquareRootOfUnity (as * bs) :=
    mul_preserves_sqrt1 ‹SquareRootOfUnity as› ‹SquareRootOfUnity bs›
  have : SignedMagnitude (a * b) ‹SquareRootOfUnity (as * bs)› :=
    mul_preserves_signedMagnitude a_sm b_sm
  exact Nonzero.mk ‹SignedMagnitude (a * b) ‹SquareRootOfUnity (as * bs)››

end prelim

/-!
## Axioms
-/

/-- Class defining integer signedness, and properties that it must satisfy. -/
class Sign
    (ℕ : Type) [outParam (Natural ℕ)]
    (ℤ : Type)
      [outParam (Core ℕ ℤ)] [outParam (Addition ℕ ℤ)]
      [outParam (Multiplication ℕ ℤ)] [outParam (Negation ℕ ℤ)]
    :=
  /-- Definitions of `Positive` and `Negative`, and their basic properties. -/
  signed : Signed ℤ

  /-- An integer is positive iff it has sign `1` in signed-magnitude form. -/
  positive_defn {a : ℤ} : Positive a ↔ SignedMagnitude a sqrt1_one

  /-- An integer is negative iff it has sign `-1` in signed-magnitude form. -/
  negative_defn {a : ℤ} : Negative a ↔ SignedMagnitude a sqrt1_neg_one

attribute [instance] Sign.signed

export Sign (negative_defn positive_defn)

/-!
## Derived properties
-/

variable {ℕ : Type} [Natural ℕ]
variable {ℤ : Type} [Core ℕ ℤ] [Addition ℕ ℤ] [Multiplication ℕ ℤ]
variable [Negation ℕ ℤ] [Sign ℕ ℤ]

/-- Extract and simplify the underlying equivalence from `Positive`. -/
theorem positive_eqv {a : ℤ} : Positive a → ∃ (n : ℕ), a ≃ ↑n := by
  intro (_ : Positive a)
  show ∃ n, a ≃ ↑n
  have : SignedMagnitude a sqrt1_one := positive_defn.mp ‹Positive a›
  have (Exists.intro (n : ℕ) (_ : a ≃ 1 * ↑n)) := this.eqv
  exists n
  show a ≃ ↑n
  exact Rel.trans ‹a ≃ 1 * ↑n› AA.identL

/-- Extract and simplify the underlying equivalence from `Negative`. -/
theorem negative_eqv {a : ℤ} : Negative a → ∃ (n : ℕ), a ≃ -↑n := by
  intro (_ : Negative a)
  show ∃ n, a ≃ -↑n
  have : SignedMagnitude a sqrt1_neg_one := negative_defn.mp ‹Negative a›
  have (Exists.intro (n : ℕ) (_ : a ≃ -1 * ↑n)) := this.eqv
  exists n
  show a ≃ -↑n
  exact Rel.trans ‹a ≃ -1 * ↑n› mul_neg_one

/--
The only square roots of unity in the integers are `1` and `-1`.

**Property and proof intuition**: This follows from similar reasoning as
`Natural.sqrt1`. Zero squared is zero, and integers greater than one or less
than negative one all have squares that are greater than one.
-/
theorem sqrt1_cases {a : ℤ} : SquareRootOfUnity a ↔ a ≃ 1 ∨ a ≃ -1 := by
  apply Iff.intro
  case mp =>
    intro (_ : a * a ≃ 1)
    show a ≃ 1 ∨ a ≃ -1
    match (Signed.trichotomy a).atLeastOne with
    | AA.OneOfThree.first (_ : a ≃ 0) =>
      apply False.elim
      show False
      have : 1 ≃ 0 := calc
        1     ≃ _ := Rel.symm ‹a * a ≃ 1›
        a * a ≃ _ := AA.substL ‹a ≃ 0›
        0 * a ≃ _ := AA.absorbL
        0     ≃ _ := Rel.refl
      exact absurd ‹(1 : ℤ) ≃ 0› one_neqv_zero
    | AA.OneOfThree.second (_ : Positive a) =>
      apply Or.inl
      show a ≃ 1
      have (Exists.intro (n : ℕ) (_ : a ≃ ↑n)) := positive_eqv ‹Positive a›
      have : ↑(n * n) ≃ ↑(1 : ℕ) := calc
        ↑(n * n) ≃ _ := AA.compat₂ (f := (↑·))
        ↑n * ↑n  ≃ _ := AA.substL (Rel.symm ‹a ≃ ↑n›)
        a * ↑n   ≃ _ := AA.substR (Rel.symm ‹a ≃ ↑n›)
        a * a    ≃ _ := ‹a * a ≃ 1›
        1        ≃ _ := Rel.refl
      have : n * n ≃ 1 := AA.inject ‹↑(n * n) ≃ ↑(1 : ℕ)›
      have : n ≃ 1 := Natural.sqrt1.mp ‹n * n ≃ 1›
      show a ≃ 1
      calc
        a       ≃ _ := ‹a ≃ ↑n›
        ↑n      ≃ _ := AA.subst₁ (f := (↑·)) ‹n ≃ 1›
        ↑1      ≃ _ := Rel.refl
        (1 : ℤ) ≃ _ := Rel.refl
    | AA.OneOfThree.third (_ : Negative a) =>
      apply Or.inr
      show a ≃ -1
      have (Exists.intro (n : ℕ) (_ : a ≃ -↑n)) := negative_eqv ‹Negative a›
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
      have : n ≃ 1 := Natural.sqrt1.mp ‹n * n ≃ 1›
      show a ≃ -1
      calc
        a     ≃ _ := ‹a ≃ -↑n›
        (-↑n) ≃ _ := AA.subst₁ (AA.subst₁ (f := (↑·)) ‹n ≃ 1›)
        (-↑1) ≃ _ := Rel.refl
        (-1)  ≃ _ := Rel.refl
  case mpr =>
    intro (_ : a ≃ 1 ∨ a ≃ -1)
    show SquareRootOfUnity a
    match ‹a ≃ 1 ∨ a ≃ -1› with
    | Or.inl (_ : a ≃ 1) =>
      have : SquareRootOfUnity 1 := sqrt1_one
      exact AA.subst₁ (rβ := (· → ·)) (Rel.symm ‹a ≃ 1›) this
    | Or.inr (_ : a ≃ -1) =>
      have : SquareRootOfUnity (-1) := sqrt1_neg_one
      exact AA.subst₁ (rβ := (· → ·)) (Rel.symm ‹a ≃ -1›) this

/--
Every `SignedMagnitude` has a sign value that's either `1` or `-1`.

This is a lemma that's useful for the proof of `nonzero_defn`.

**Property and proof intuition**: We already know from `sqrt1_cases` that sign
values can only be `1` or `-1`. So this result just uses that fact to show what
the precise type of `SignedMagnitude` is allowed to be.
-/
theorem signedMagnitude_cases
    {a s : ℤ} {sqrt1 : SquareRootOfUnity s}
    : SignedMagnitude a sqrt1 →
    SignedMagnitude a sqrt1_one ∨ SignedMagnitude a sqrt1_neg_one
    := by
  intro (_ : SignedMagnitude a sqrt1)
  show SignedMagnitude a sqrt1_one ∨ SignedMagnitude a sqrt1_neg_one
  have : s ≃ 1 ∨ s ≃ -1 := sqrt1_cases.mp ‹SquareRootOfUnity s›
  match ‹s ≃ 1 ∨ s ≃ -1› with
  | Or.inl (_ : s ≃ 1) =>
    apply Or.inl
    show SignedMagnitude a sqrt1_one
    exact signedMagnitude_sqrt1_subst ‹s ≃ 1› ‹SignedMagnitude a sqrt1›
  | Or.inr (_ : s ≃ -1) =>
    apply Or.inr
    show SignedMagnitude a sqrt1_neg_one
    exact signedMagnitude_sqrt1_subst ‹s ≃ -1› ‹SignedMagnitude a sqrt1›

/--
Nonzero integers are either, and only, positive or negative.

**Property intuition**: As the name `nonzero_defn` implies, this captures our
intuitive notion of what a nonzero integer is.

**Proof intuition**: Converts `Nonzero`, `Positive`, and `Negative` to and from
their `SignedMagnitude` representations via `signedMagnitude_cases`,
`positive_defn`, and `negative_defn`.
-/
theorem nonzero_defn {a : ℤ} : Nonzero a ↔ Positive a ∨ Negative a := by
  apply Iff.intro
  case mp =>
    intro (_ : Nonzero a)
    show Positive a ∨ Negative a
    have (Nonzero.intro
        (s : ℤ) (sqrt1 : SquareRootOfUnity s) (_ : SignedMagnitude a sqrt1)) :=
      ‹Nonzero a›
    have : SignedMagnitude a sqrt1_one ∨ SignedMagnitude a sqrt1_neg_one :=
      signedMagnitude_cases ‹SignedMagnitude a sqrt1›
    match ‹SignedMagnitude a sqrt1_one ∨ SignedMagnitude a sqrt1_neg_one› with
    | Or.inl (_ : SignedMagnitude a sqrt1_one) =>
      have : Positive a := positive_defn.mpr ‹SignedMagnitude a sqrt1_one›
      exact Or.inl ‹Positive a›
    | Or.inr (_ : SignedMagnitude a sqrt1_neg_one) =>
      have : Negative a := negative_defn.mpr ‹SignedMagnitude a sqrt1_neg_one›
      exact Or.inr ‹Negative a›
  case mpr =>
    intro (_ : Positive a ∨ Negative a)
    show Nonzero a
    match ‹Positive a ∨ Negative a› with
    | Or.inl (_ : Positive a) =>
      have : SignedMagnitude a sqrt1_one := positive_defn.mp ‹Positive a›
      exact Nonzero.mk ‹SignedMagnitude a sqrt1_one›
    | Or.inr (_ : Negative a) =>
      have : SignedMagnitude a sqrt1_neg_one := negative_defn.mp ‹Negative a›
      exact Nonzero.mk ‹SignedMagnitude a sqrt1_neg_one›

/--
Provide evidence that an integer is equivalent, or not equivalent, to zero.

**Property and proof intuition**: We already know from trichotomy of integers
that every integer is either zero, positive, or negative, and never more than
one of those at the same time. Combine the positive and negative categories to
obtain this result.
-/
theorem zero? (a : ℤ) : AA.ExactlyOneOfTwo (a ≃ 0) (Nonzero a) := by
  have tri : AA.ExactlyOneOfThree (a ≃ 0) (Positive a) (Negative a) :=
    Signed.trichotomy a
  apply And.intro
  case left =>
    show a ≃ 0 ∨ Nonzero a
    match tri.atLeastOne with
    | AA.OneOfThree.first (_ : a ≃ 0) =>
      exact Or.inl ‹a ≃ 0›
    | AA.OneOfThree.second (_ : Positive a) =>
      have : Nonzero a := nonzero_defn.mpr (Or.inl ‹Positive a›)
      exact Or.inr ‹Nonzero a›
    | AA.OneOfThree.third (_ : Negative a) =>
      have : Nonzero a := nonzero_defn.mpr (Or.inr ‹Negative a›)
      exact Or.inr ‹Nonzero a›
  case right =>
    intro (And.intro (_ : a ≃ 0) (_ : Nonzero a))
    show False
    apply tri.atMostOne
    show AA.TwoOfThree (a ≃ 0) (Positive a) (Negative a)
    have : Positive a ∨ Negative a := nonzero_defn.mp ‹Nonzero a›
    match ‹Positive a ∨ Negative a› with
    | Or.inl (_ : Positive a) =>
      exact AA.TwoOfThree.oneAndTwo ‹a ≃ 0› ‹Positive a›
    | Or.inr (_ : Negative a) =>
      exact AA.TwoOfThree.oneAndThree ‹a ≃ 0› ‹Negative a›

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

end Lean4Axiomatic.Integer
