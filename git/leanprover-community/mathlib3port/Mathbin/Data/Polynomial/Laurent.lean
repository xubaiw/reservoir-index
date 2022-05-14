/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.Data.Polynomial.AlgebraMap

/-!  # Laurent polynomials

We introduce Laurent polynomials over a semiring `R`.  Mathematically, they are expressions of the
form
$$
\sum_{i \in \mathbb{Z}} a_i T ^ i
$$
where the sum extends over a finite subset of `ℤ`.  Thus, negative exponents are allowed.  The
coefficients come from the semiring `R` and the variable `T` commutes with everything.

Since we are going to convert back and forth between polynomials and Laurent polynomials, we
decided to maintain some distinction by using the symbol `T`, rather than `X`, as the variable for
Laurent polynomials

## Notation
The symbol `R[T;T⁻¹]` stands for `laurent_polynomial R`.  We also define

* `C : R →+* R[T;T⁻¹]` the inclusion of constant polynomials, analogous to the one for `R[X]`;
* `T : ℤ → R[T;T⁻¹]` the sequence of powers of the variable `T`.

## Implementation notes

We define Laurent polynomials as `add_monoid_algebra R ℤ`.
Thus, they are essentially `finsupp`s `ℤ →₀ R`.
This choice differs from the current irreducible design of `polynomial`, that instead shields away
the implementation via `finsupp`s.  It is closer to the original definition of polynomials.

As a consequence, `laurent_polynomial` plays well with polynomials, but there is a little roughness
in establishing the API, since the `finsupp` implementation of `polynomial R` is well-shielded.

Unlike the case of polynomials, I felt that the exponent notation was not too easy to use, as only
natural exponents would be allowed.  Moreover, in the end, it seems likely that we should aim to
perform computations on exponents in `ℤ` anyway and separating this via the symbol `T` seems
convenient.

I made a *heavy* use of `simp` lemmas, aiming to bring Laurent polynomials to the form `C a * T n`.
Any comments or suggestions for improvements is greatly appreciated!

##  Future work
Lots is missing!  I would certainly like to show that `R[T;T⁻¹]` is the localization of `R[X]`
inverting `X`.  This should be mostly in place, given `exists_T_pow` (which is part of PR #13415).
(Riccardo) add inclusion into Laurent series.
(Riccardo) giving a morphism (as `R`-alg, so in the commutative case)
from `R[T,T⁻¹]` to `S` is the same as choosing a unit of `S`.
-/


open Polynomial BigOperators

open Polynomial AddMonoidAlgebra Finsupp

noncomputable section

variable {R : Type _}

/-- The semiring of Laurent polynomials with coefficients in the semiring `R`.
We denote it by `R[T;T⁻¹]`.
The ring homomorphism `C : R →+* R[T;T⁻¹]` includes `R` as the constant polynomials. -/
abbrev LaurentPolynomial (R : Type _) [Semiringₓ R] :=
  AddMonoidAlgebra R ℤ

-- mathport name: «expr [T;T⁻¹]»
local notation:9000 R "[T;T⁻¹]" => LaurentPolynomial R

/-- The ring homomorphism, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def Polynomial.toLaurent [Semiringₓ R] : R[X] →+* R[T;T⁻¹] :=
  (mapDomainRingHom R Int.ofNatHom).comp (toFinsuppIso R)

/-- This is not a simp lemma, as it is usually preferable to use the lemmas about `C` and `X`
instead. -/
theorem Polynomial.to_laurent_apply [Semiringₓ R] (p : R[X]) : p.toLaurent = p.toFinsupp.mapDomain coe :=
  rfl

/-- The `R`-algebra map, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def Polynomial.toLaurentAlg [CommSemiringₓ R] : R[X] →ₐ[R] R[T;T⁻¹] := by
  refine' AlgHom.comp _ (to_finsupp_iso_alg R).toAlgHom
  exact map_domain_alg_hom R R Int.ofNatHom

@[simp]
theorem Polynomial.to_laurent_alg_apply [CommSemiringₓ R] (f : R[X]) : f.toLaurentAlg = f.toLaurent :=
  rfl

namespace LaurentPolynomial

section Semiringₓ

variable [Semiringₓ R]

theorem single_zero_one_eq_one : (single 0 1 : R[T;T⁻¹]) = (1 : R[T;T⁻¹]) :=
  rfl

/-!  ### The functions `C` and `T`. -/


/-- The ring homomorphism `C`, including `R` into the ring of Laurent polynomials over `R` as
the constant Laurent polynomials. -/
def c : R →+* R[T;T⁻¹] :=
  single_zero_ring_hom

theorem algebra_map_apply {R A : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] (r : R) :
    algebraMap R (LaurentPolynomial A) r = c (algebraMap R A r) :=
  rfl

/-- When we have `[comm_semiring R]`, the function `C` is the same as `algebra_map R R[T;T⁻¹]`.
(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebra_map` is not available.)
-/
theorem C_eq_algebra_map {R : Type _} [CommSemiringₓ R] (r : R) : c r = algebraMap R R[T;T⁻¹] r :=
  rfl

theorem single_eq_C (r : R) : single 0 r = c r :=
  rfl

/-- The function `n ↦ T ^ n`, implemented as a sequence `ℤ → R[T;T⁻¹]`.

Using directly `T ^ n` does not work, since we want the exponents to be of Type `ℤ` and there
is no `ℤ`-power defined on `R[T;T⁻¹]`.  Using that `T` is a unit introduces extra coercions.
For these reasons, the definition of `T` is as a sequence. -/
def t (n : ℤ) : R[T;T⁻¹] :=
  single n 1

@[simp]
theorem T_zero : (t 0 : R[T;T⁻¹]) = 1 :=
  rfl

theorem T_add (m n : ℤ) : (t (m + n) : R[T;T⁻¹]) = t m * t n := by
  convert single_mul_single.symm
  simp [T]

@[simp]
theorem T_pow (m : ℤ) (n : ℕ) : (t m ^ n : R[T;T⁻¹]) = t (n * m) := by
  rw [T, T, single_pow n, one_pow, nsmul_eq_mul, Int.nat_cast_eq_coe_nat]

/-- The `simp` version of `mul_assoc`, in the presence of `T`'s. -/
@[simp]
theorem mul_T_assoc (f : R[T;T⁻¹]) (m n : ℤ) : f * t m * t n = f * t (m + n) := by
  simp [← T_add, mul_assoc]

@[simp]
theorem single_eq_C_mul_T (r : R) (n : ℤ) : (single n r : R[T;T⁻¹]) = (c r * t n : R[T;T⁻¹]) := by
  convert single_mul_single.symm <;> simp

-- This lemma locks in the right changes and is what Lean proved directly.
-- The actual `simp`-normal form of a Laurent monomial is `C a * T n`, whenever it can be reached.
@[simp]
theorem _root_.polynomial.to_laurent_C_mul_T (n : ℕ) (r : R) :
    ((Polynomial.monomial n r).toLaurent : R[T;T⁻¹]) = c r * t n :=
  show mapDomain coe (monomial n r).toFinsupp = (c r * t n : R[T;T⁻¹]) by
    rw [to_finsupp_monomial, map_domain_single, single_eq_C_mul_T]

@[simp]
theorem _root_.polynomial.to_laurent_C (r : R) : (Polynomial.c r).toLaurent = c r := by
  convert Polynomial.to_laurent_C_mul_T 0 r
  simp only [Int.coe_nat_zero, T_zero, mul_oneₓ]

@[simp]
theorem _root_.polynomial.to_laurent_X : (Polynomial.x.toLaurent : R[T;T⁻¹]) = t 1 := by
  have : (Polynomial.x : R[X]) = monomial 1 1 := by
    simp [monomial_eq_C_mul_X]
  simp [this, Polynomial.to_laurent_C_mul_T]

@[simp]
theorem _root_.polynomial.to_laurent_one : (Polynomial.toLaurent : R[X] → R[T;T⁻¹]) 1 = 1 :=
  map_one Polynomial.toLaurent

@[simp]
theorem _root_.polynomial.to_laurent_C_mul_eq (r : R) (f : R[X]) : (Polynomial.c r * f).toLaurent = c r * f.toLaurent :=
  by
  simp only [_root_.map_mul, Polynomial.to_laurent_C]

@[simp]
theorem _root_.polynomial.to_laurent_X_pow (n : ℕ) : (X ^ n : R[X]).toLaurent = t n := by
  simp only [map_pow, Polynomial.to_laurent_X, T_pow, mul_oneₓ]

@[simp]
theorem _root_.polynomial.to_laurent_C_mul_X_pow (n : ℕ) (r : R) : (Polynomial.c r * X ^ n).toLaurent = c r * t n := by
  simp only [_root_.map_mul, Polynomial.to_laurent_C, Polynomial.to_laurent_X_pow]

instance invertibleT (n : ℤ) : Invertible (t n : R[T;T⁻¹]) where
  invOf := t (-n)
  inv_of_mul_self := by
    rw [← T_add, add_left_negₓ, T_zero]
  mul_inv_of_self := by
    rw [← T_add, add_right_negₓ, T_zero]

@[simp]
theorem inv_of_T (n : ℤ) : ⅟ (t n : R[T;T⁻¹]) = t (-n) :=
  rfl

theorem is_unit_T (n : ℤ) : IsUnit (t n : R[T;T⁻¹]) :=
  is_unit_of_invertible _

@[elab_as_eliminator]
protected theorem induction_on {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹]) (h_C : ∀ a, M (c a))
    (h_add : ∀ {p q}, M p → M q → M (p + q)) (h_C_mul_T : ∀ n : ℕ a : R, M (c a * t n) → M (c a * t (n + 1)))
    (h_C_mul_T_Z : ∀ n : ℕ a : R, M (c a * t (-n)) → M (c a * t (-n - 1))) : M p := by
  have A : ∀ {n : ℤ} {a : R}, M (C a * T n) := by
    intro n a
    apply n.induction_on
    · simpa only [T_zero, mul_oneₓ] using h_C a
      
    · exact fun m => h_C_mul_T m a
      
    · exact fun m => h_C_mul_T_Z m a
      
  have B : ∀ s : Finset ℤ, M (s.Sum fun n : ℤ => C (p.to_fun n) * T n) := by
    apply Finset.induction
    · convert h_C 0
      simp only [Finset.sum_empty, _root_.map_zero]
      
    · intro n s ns ih
      rw [Finset.sum_insert ns]
      exact h_add A ih
      
  convert B p.support
  ext a
  simp_rw [← single_eq_C_mul_T, Finset.sum_apply', single_apply, Finset.sum_ite_eq']
  split_ifs with h h
  · rfl
    
  · exact finsupp.not_mem_support_iff.mp h
    

/-- To prove something about Laurent polynomials, it suffices to show that
* the condition is closed under taking sums, and
* it holds for monomials.
-/
@[elab_as_eliminator]
protected theorem induction_on' {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹]) (h_add : ∀ p q, M p → M q → M (p + q))
    (h_C_mul_T : ∀ n : ℤ a : R, M (c a * t n)) : M p := by
  refine' p.induction_on (fun a => _) h_add _ _ <;>
    try
      exact fun n f _ => h_C_mul_T _ f
  convert h_C_mul_T 0 a
  exact (mul_oneₓ _).symm

theorem commute_T (n : ℤ) (f : R[T;T⁻¹]) : Commute (t n) f :=
  (f.induction_on' fun p q Tp Tq => Commute.add_right Tp Tq) fun m a =>
    show t n * _ = _ by
      rw [T, T, ← single_eq_C, single_mul_single, single_mul_single, single_mul_single]
      simp [add_commₓ]

@[simp]
theorem T_mul (n : ℤ) (f : R[T;T⁻¹]) : t n * f = f * t n :=
  (commute_T n f).Eq

/-- `trunc : R[T;T⁻¹] →+ R[X]` maps a Laurent polynomial `f` to the polynomial whose terms of
nonnegative degree coincide with the ones of `f`.  The terms of negative degree of `f` "vanish".
`trunc` is a left-inverse to `polynomial.to_laurent`. -/
def trunc : R[T;T⁻¹] →+ R[X] :=
  (toFinsuppIso R).symm.toAddMonoidHom.comp <| comap_domain.add_monoid_hom fun a b => Int.ofNat.injₓ

@[simp]
theorem trunc_C_mul_T (n : ℤ) (r : R) : trunc (c r * t n) = ite (0 ≤ n) (monomial n.toNat r) 0 := by
  apply (to_finsupp_iso R).Injective
  rw [← single_eq_C_mul_T, Trunc, AddMonoidHom.coe_comp, Function.comp_app, comap_domain.add_monoid_hom_apply,
    to_finsupp_iso_apply]
  by_cases' n0 : 0 ≤ n
  · lift n to ℕ using n0
    erw [comap_domain_single, to_finsupp_iso_symm_apply]
    simp only [Int.coe_nat_nonneg, Int.to_nat_coe_nat, if_true, to_finsupp_iso_apply, to_finsupp_monomial]
    
  · lift -n to ℕ using (neg_pos.mpr (not_le.mp n0)).le with m
    rw [to_finsupp_iso_apply, to_finsupp_inj, if_neg n0]
    erw [to_finsupp_iso_symm_apply]
    ext a
    have := ((not_le.mp n0).trans_le (Int.coe_zero_le a)).ne'
    simp only [coeff, comap_domain_apply, Int.of_nat_eq_coe, coeff_zero, single_apply_eq_zero, this, forall_false_left]
    

@[simp]
theorem left_inverse_trunc_to_laurent : Function.LeftInverse (trunc : R[T;T⁻¹] → R[X]) Polynomial.toLaurent := by
  refine' fun f => f.induction_on' _ _
  · exact fun f g hf hg => by
      simp only [hf, hg, _root_.map_add]
    
  · exact fun n r => by
      simp only [Polynomial.to_laurent_C_mul_T, trunc_C_mul_T, Int.coe_nat_nonneg, Int.to_nat_coe_nat, if_true]
    

@[simp]
theorem _root_.polynomial.trunc_to_laurent (f : R[X]) : trunc f.toLaurent = f :=
  left_inverse_trunc_to_laurent _

theorem _root_.polynomial.to_laurent_injective : Function.Injective (Polynomial.toLaurent : R[X] → R[T;T⁻¹]) :=
  left_inverse_trunc_to_laurent.Injective

@[simp]
theorem _root_.polynomial.to_laurent_inj (f g : R[X]) : f.toLaurent = g.toLaurent ↔ f = g :=
  ⟨fun h => Polynomial.to_laurent_injective h, congr_argₓ _⟩

end Semiringₓ

end LaurentPolynomial

