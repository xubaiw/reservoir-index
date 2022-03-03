/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathbin.LinearAlgebra.Charpoly.Basic
import Mathbin.LinearAlgebra.Matrix.Basis

/-!

# Characteristic polynomial

## Main result

* `linear_map.charpoly_to_matrix f` : `charpoly f` is the characteristic polynomial of the matrix
of `f` in any basis.

-/


universe u v w

variable {R : Type u} {M : Type v} [CommRingₓ R] [Nontrivial R]

variable [AddCommGroupₓ M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)

open_locale Classical Matrix

noncomputable section

open Module.Free Polynomial Matrix

namespace LinearMap

section Basic

/-- `charpoly f` is the characteristic polynomial of the matrix of `f` in any basis. -/
@[simp]
theorem charpoly_to_matrix {ι : Type w} [Fintype ι] (b : Basis ι R M) : (toMatrix b b f).charpoly = f.charpoly := by
  set A := to_matrix b b f
  set b' := choose_basis R M
  set ι' := choose_basis_index R M
  set A' := to_matrix b' b' f
  set e := Basis.indexEquiv b b'
  set φ := reindex_linear_equiv R R e e
  set φ₁ := reindex_linear_equiv R R e (Equivₓ.refl ι')
  set φ₂ := reindex_linear_equiv R R (Equivₓ.refl ι') (Equivₓ.refl ι')
  set φ₃ := reindex_linear_equiv R R (Equivₓ.refl ι') e
  set P := b.to_matrix b'
  set Q := b'.to_matrix b
  have hPQ : C.map_matrix (φ₁ P) ⬝ C.map_matrix (φ₃ Q) = 1 := by
    rw [RingHom.map_matrix_apply, RingHom.map_matrix_apply, ← Matrix.map_mul,
      @reindex_linear_equiv_mul _ ι' _ _ _ _ R R, Basis.to_matrix_mul_to_matrix_flip, reindex_linear_equiv_one, ←
      RingHom.map_matrix_apply, RingHom.map_one]
  calc A.charpoly = (reindex e e A).charpoly :=
      (charpoly_reindex _ _).symm _ = (scalar ι' X - C.map_matrix (φ A)).det :=
      rfl _ = (scalar ι' X - C.map_matrix (φ (P ⬝ A' ⬝ Q))).det := by
      rw
        [basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix]_ =
        (scalar ι' X - C.map_matrix (φ₁ P ⬝ φ₂ A' ⬝ φ₃ Q)).det :=
      by
      rw [reindex_linear_equiv_mul,
        reindex_linear_equiv_mul]_ = (scalar ι' X - C.map_matrix (φ₁ P) ⬝ C.map_matrix A' ⬝ C.map_matrix (φ₃ Q)).det :=
      by
      simp
        _ =
        (scalar ι' X ⬝ C.map_matrix (φ₁ P) ⬝ C.map_matrix (φ₃ Q) -
            C.map_matrix (φ₁ P) ⬝ C.map_matrix A' ⬝ C.map_matrix (φ₃ Q)).det :=
      by
      rw [Matrix.mul_assoc ((scalar ι') X), hPQ,
        Matrix.mul_one]_ =
        (C.map_matrix (φ₁ P) ⬝ scalar ι' X ⬝ C.map_matrix (φ₃ Q) -
            C.map_matrix (φ₁ P) ⬝ C.map_matrix A' ⬝ C.map_matrix (φ₃ Q)).det :=
      by
      simp _ = (C.map_matrix (φ₁ P) ⬝ (scalar ι' X - C.map_matrix A') ⬝ C.map_matrix (φ₃ Q)).det := by
      rw [← Matrix.sub_mul, ←
        Matrix.mul_sub]_ =
        (C.map_matrix (φ₁ P)).det * (scalar ι' X - C.map_matrix A').det * (C.map_matrix (φ₃ Q)).det :=
      by
      rw [det_mul,
        det_mul]_ = (C.map_matrix (φ₁ P)).det * (C.map_matrix (φ₃ Q)).det * (scalar ι' X - C.map_matrix A').det :=
      by
      ring _ = (scalar ι' X - C.map_matrix A').det := by
      rw [← det_mul, hPQ, det_one, one_mulₓ]_ = f.charpoly := rfl

end Basic

end LinearMap

