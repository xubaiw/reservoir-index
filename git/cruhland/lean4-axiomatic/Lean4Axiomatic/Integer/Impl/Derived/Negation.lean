import Lean4Axiomatic.Integer.Negation

namespace Lean4Axiomatic.Integer.Impl.Derived

variable {ℕ : Type}
variable [Natural ℕ]
variable {ℤ : Type}
variable [Equality ℤ]
variable [Conversion ℕ ℤ]
variable [Addition.Base ℕ ℤ]
variable [Multiplication.Base ℕ ℤ]
variable [Negation.Base ℕ ℤ]

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

def neg_semicompatible_mul : AA.Semicompatible (α := ℤ) (-·) (· * ·) := {
  semicompatibleL :=
    neg_semicompatibleL_mul
  semicompatibleR :=
    AA.semicompatibleR_from_semicompatibleL neg_semicompatibleL_mul
}

def negation_derived : Negation.Derived ℕ ℤ := {
  mul_absorbing := mul_absorbing
  neg_semicompatible_mul := neg_semicompatible_mul
}

end Lean4Axiomatic.Integer.Impl.Derived
