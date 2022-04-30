/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Algebra.Quaternion
import Mathbin.Analysis.InnerProductSpace.Basic

/-!
# Quaternions as a normed algebra

In this file we define the following structures on the space `ℍ := ℍ[ℝ]` of quaternions:

* inner product space;
* normed ring;
* normed space over `ℝ`.

## Notation

The following notation is available with `open_locale quaternion`:

* `ℍ` : quaternions

## Tags

quaternion, normed ring, normed space, normed algebra
-/


-- mathport name: «exprℍ»
localized [Quaternion] notation "ℍ" => Quaternion ℝ

open RealInnerProductSpace

noncomputable section

namespace Quaternion

instance : HasInner ℝ ℍ :=
  ⟨fun a b => (a * b.conj).re⟩

theorem inner_self (a : ℍ) : ⟪a, a⟫ = normSq a :=
  rfl

theorem inner_def (a b : ℍ) : ⟪a, b⟫ = (a * b.conj).re :=
  rfl

instance : InnerProductSpace ℝ ℍ :=
  InnerProductSpace.ofCore
    { inner := HasInner.inner,
      conj_sym := fun x y => by
        simp [inner_def, mul_comm],
      nonneg_re := fun x => norm_sq_nonneg, definite := fun x => norm_sq_eq_zero.1,
      add_left := fun x y z => by
        simp only [inner_def, add_mulₓ, add_re],
      smul_left := fun x y r => by
        simp [inner_def] }

theorem norm_sq_eq_norm_sq (a : ℍ) : normSq a = ∥a∥ * ∥a∥ := by
  rw [← inner_self, real_inner_self_eq_norm_mul_norm]

instance : NormOneClass ℍ :=
  ⟨by
    rw [norm_eq_sqrt_real_inner, inner_self, norm_sq.map_one, Real.sqrt_one]⟩

@[simp, norm_cast]
theorem norm_coe (a : ℝ) : ∥(a : ℍ)∥ = ∥a∥ := by
  rw [norm_eq_sqrt_real_inner, inner_self, norm_sq_coe, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

@[simp, norm_cast]
theorem nnnorm_coe (a : ℝ) : ∥(a : ℍ)∥₊ = ∥a∥₊ :=
  Subtype.ext <| norm_coe a

noncomputable instance : NormedDivisionRing ℍ where
  dist_eq := fun _ _ => rfl
  norm_mul' := fun a b => by
    simp only [norm_eq_sqrt_real_inner, inner_self, norm_sq.map_mul]
    exact Real.sqrt_mul norm_sq_nonneg _

noncomputable instance : NormedAlgebra ℝ ℍ where
  norm_smul_le := fun a x => (norm_smul a x).le
  toAlgebra := Quaternion.algebra

instance : Coe ℂ ℍ :=
  ⟨fun z => ⟨z.re, z.im, 0, 0⟩⟩

@[simp, norm_cast]
theorem coe_complex_re (z : ℂ) : (z : ℍ).re = z.re :=
  rfl

@[simp, norm_cast]
theorem coe_complex_im_i (z : ℂ) : (z : ℍ).imI = z.im :=
  rfl

@[simp, norm_cast]
theorem coe_complex_im_j (z : ℂ) : (z : ℍ).imJ = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_complex_im_k (z : ℂ) : (z : ℍ).imK = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_complex_add (z w : ℂ) : ↑(z + w) = (z + w : ℍ) := by
  ext <;> simp

@[simp, norm_cast]
theorem coe_complex_mul (z w : ℂ) : ↑(z * w) = (z * w : ℍ) := by
  ext <;> simp

@[simp, norm_cast]
theorem coe_complex_zero : ((0 : ℂ) : ℍ) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_complex_one : ((1 : ℂ) : ℍ) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_real_complex_mul (r : ℝ) (z : ℂ) : (r • z : ℍ) = ↑r * ↑z := by
  ext <;> simp

@[simp, norm_cast]
theorem coe_complex_coe (r : ℝ) : ((r : ℂ) : ℍ) = r :=
  rfl

/-- Coercion `ℂ →ₐ[ℝ] ℍ` as an algebra homomorphism. -/
def ofComplex : ℂ →ₐ[ℝ] ℍ where
  toFun := coe
  map_one' := rfl
  map_zero' := rfl
  map_add' := coe_complex_add
  map_mul' := coe_complex_mul
  commutes' := fun x => rfl

@[simp]
theorem coe_of_complex : ⇑of_complex = coe :=
  rfl

end Quaternion

