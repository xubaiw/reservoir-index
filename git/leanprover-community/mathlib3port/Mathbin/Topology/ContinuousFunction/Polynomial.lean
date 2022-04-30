/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Topology.Algebra.Polynomial
import Mathbin.Topology.ContinuousFunction.Algebra
import Mathbin.Topology.ContinuousFunction.Compact
import Mathbin.Topology.UnitInterval

/-!
# Constructions relating polynomial functions and continuous functions.

## Main definitions

* `polynomial.to_continuous_map_on p X`: for `X : set R`, interprets a polynomial `p`
  as a bundled continuous function in `C(X, R)`.
* `polynomial.to_continuous_map_on_alg_hom`: the same, as an `R`-algebra homomorphism.
* `polynomial_functions (X : set R) : subalgebra R C(X, R)`: polynomial functions as a subalgebra.
* `polynomial_functions_separates_points (X : set R) : (polynomial_functions X).separates_points`:
  the polynomial functions separate points.

-/


variable {R : Type _}

open Polynomial

namespace Polynomial

section

variable [Semiringₓ R] [TopologicalSpace R] [TopologicalSemiring R]

/-- Every polynomial with coefficients in a topological semiring gives a (bundled) continuous function.
-/
@[simps]
def toContinuousMap (p : R[X]) : C(R, R) :=
  ⟨fun x : R => p.eval x, by
    continuity⟩

/-- A polynomial as a continuous function,
with domain restricted to some subset of the semiring of coefficients.

(This is particularly useful when restricting to compact sets, e.g. `[0,1]`.)
-/
@[simps]
def toContinuousMapOn (p : R[X]) (X : Set R) : C(X, R) :=
  ⟨fun x : X => p.toContinuousMap x, by
    continuity⟩

-- TODO some lemmas about when `to_continuous_map_on` is injective?
end

section

variable {α : Type _} [TopologicalSpace α] [CommSemiringₓ R] [TopologicalSpace R] [TopologicalSemiring R]

@[simp]
theorem aeval_continuous_map_apply (g : R[X]) (f : C(α, R)) (x : α) : ((Polynomial.aeval f) g) x = g.eval (f x) := by
  apply Polynomial.induction_on' g
  · intro p q hp hq
    simp [hp, hq]
    
  · intro n a
    simp [Pi.pow_apply f x n]
    

end

section

noncomputable section

variable [CommSemiringₓ R] [TopologicalSpace R] [TopologicalSemiring R]

/-- The algebra map from `polynomial R` to continuous functions `C(R, R)`.
-/
@[simps]
def toContinuousMapAlgHom : R[X] →ₐ[R] C(R, R) where
  toFun := fun p => p.toContinuousMap
  map_zero' := by
    ext
    simp
  map_add' := by
    intros
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' := by
    intros
    ext
    simp
  commutes' := by
    intros
    ext
    simp [Algebra.algebra_map_eq_smul_one]

/-- The algebra map from `polynomial R` to continuous functions `C(X, R)`, for any subset `X` of `R`.
-/
@[simps]
def toContinuousMapOnAlgHom (X : Set R) : R[X] →ₐ[R] C(X, R) where
  toFun := fun p => p.toContinuousMapOn X
  map_zero' := by
    ext
    simp
  map_add' := by
    intros
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' := by
    intros
    ext
    simp
  commutes' := by
    intros
    ext
    simp [Algebra.algebra_map_eq_smul_one]

end

end Polynomial

section

variable [CommSemiringₓ R] [TopologicalSpace R] [TopologicalSemiring R]

/-- The subalgebra of polynomial functions in `C(X, R)`, for `X` a subset of some topological semiring
`R`.
-/
def polynomialFunctions (X : Set R) : Subalgebra R C(X, R) :=
  (⊤ : Subalgebra R R[X]).map (Polynomial.toContinuousMapOnAlgHom X)

@[simp]
theorem polynomial_functions_coe (X : Set R) :
    (polynomialFunctions X : Set C(X, R)) = Set.Range (Polynomial.toContinuousMapOnAlgHom X) := by
  ext
  simp [polynomialFunctions]

-- TODO:
-- if `f : R → R` is an affine equivalence, then pulling back along `f`
-- induces a normed algebra isomorphism between `polynomial_functions X` and
-- `polynomial_functions (f ⁻¹' X)`, intertwining the pullback along `f` of `C(R, R)` to itself.
theorem polynomial_functions_separates_points (X : Set R) : (polynomialFunctions X).SeparatesPoints := fun x y h => by
  -- We use `polynomial.X`, then clean up.
  refine' ⟨_, ⟨⟨_, ⟨⟨Polynomial.x, ⟨Algebra.mem_top, rfl⟩⟩, rfl⟩⟩, _⟩⟩
  dsimp
  simp only [Polynomial.eval_X]
  exact fun h' => h (Subtype.ext h')

open UnitInterval

open ContinuousMap

/-- The preimage of polynomials on `[0,1]` under the pullback map by `x ↦ (b-a) * x + a`
is the polynomials on `[a,b]`. -/
theorem polynomialFunctions.comap'_comp_right_alg_hom_Icc_homeo_I (a b : ℝ) (h : a < b) :
    (polynomialFunctions I).comap' (compRightAlgHom ℝ (iccHomeoI a b h).symm.toContinuousMap) =
      polynomialFunctions (Set.Icc a b) :=
  by
  ext f
  fconstructor
  · rintro ⟨p, ⟨-, w⟩⟩
    rw [FunLike.ext_iff] at w
    dsimp  at w
    let q := p.comp ((b - a)⁻¹ • Polynomial.x + Polynomial.c (-a * (b - a)⁻¹))
    refine' ⟨q, ⟨_, _⟩⟩
    · simp
      
    · ext x
      simp only [neg_mul, RingHom.map_neg, RingHom.map_mul, AlgHom.coe_to_ring_hom, Polynomial.eval_X,
        Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.coe_aeval_eq_eval, Polynomial.eval_comp,
        Polynomial.to_continuous_map_on_alg_hom_apply, Polynomial.to_continuous_map_on_to_fun,
        Polynomial.to_continuous_map_to_fun]
      convert w ⟨_, _⟩ <;> clear w
      · -- why does `comm_ring.add` appear here!?
        change x = (iccHomeoI a b h).symm ⟨_ + _, _⟩
        ext
        simp only [Icc_homeo_I_symm_apply_coe, Subtype.coe_mk]
        replace h : b - a ≠ 0 := sub_ne_zero_of_ne h.ne.symm
        simp only [mul_addₓ]
        field_simp
        ring
        
      · change _ + _ ∈ I
        rw [mul_comm (b - a)⁻¹, ← neg_mul, ← add_mulₓ, ← sub_eq_add_neg]
        have w₁ : 0 < (b - a)⁻¹ := inv_pos.mpr (sub_pos.mpr h)
        have w₂ : 0 ≤ (x : ℝ) - a := sub_nonneg.mpr x.2.1
        have w₃ : (x : ℝ) - a ≤ b - a := sub_le_sub_right x.2.2 a
        fconstructor
        · exact mul_nonneg w₂ (le_of_ltₓ w₁)
          
        · rw [← div_eq_mul_inv, div_le_one (sub_pos.mpr h)]
          exact w₃
          
        
      
    
  · rintro ⟨p, ⟨-, rfl⟩⟩
    let q := p.comp ((b - a) • Polynomial.x + Polynomial.c a)
    refine' ⟨q, ⟨_, _⟩⟩
    · simp
      
    · ext x
      simp [mul_comm]
      
    

end

