/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Eric Wieser
-/
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Analysis.NormedSpace.PiLp
import Mathbin.Analysis.InnerProductSpace.PiL2

/-!
# Matrices as a normed space

In this file we provide the following non-instances for norms on matrices:

* The elementwise norm:

  * `matrix.seminormed_add_comm_group`
  * `matrix.normed_add_comm_group`
  * `matrix.normed_space`

* The Frobenius norm:

  * `matrix.frobenius_seminormed_add_comm_group`
  * `matrix.frobenius_normed_add_comm_group`
  * `matrix.frobenius_normed_space`
  * `matrix.frobenius_normed_ring`
  * `matrix.frobenius_normed_algebra`

* The $L^\infty$ operator norm:

  * `matrix.linfty_op_seminormed_add_comm_group`
  * `matrix.linfty_op_normed_add_comm_group`
  * `matrix.linfty_op_normed_space`
  * `matrix.linfty_op_non_unital_semi_normed_ring`
  * `matrix.linfty_op_semi_normed_ring`
  * `matrix.linfty_op_non_unital_normed_ring`
  * `matrix.linfty_op_normed_ring`
  * `matrix.linfty_op_normed_algebra`

These are not declared as instances because there are several natural choices for defining the norm
of a matrix.
-/


noncomputable section

open BigOperators Nnreal Matrix

namespace Matrix

variable {R l m n α β : Type _} [Fintype l] [Fintype m] [Fintype n]

/-! ### The elementwise supremum norm -/


section LinfLinf

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

/-- Seminormed group instance (using sup norm of sup norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def seminormedAddCommGroup : SeminormedAddCommGroup (Matrix m n α) :=
  Pi.seminormedAddCommGroup

attribute [local instance] Matrix.seminormedAddCommGroup

theorem norm_le_iff {r : ℝ} (hr : 0 ≤ r) {A : Matrix m n α} : ∥A∥ ≤ r ↔ ∀ i j, ∥A i j∥ ≤ r := by
  simp [pi_norm_le_iff hr]

theorem nnnorm_le_iff {r : ℝ≥0 } {A : Matrix m n α} : ∥A∥₊ ≤ r ↔ ∀ i j, ∥A i j∥₊ ≤ r := by
  simp [pi_nnnorm_le_iff]

theorem norm_lt_iff {r : ℝ} (hr : 0 < r) {A : Matrix m n α} : ∥A∥ < r ↔ ∀ i j, ∥A i j∥ < r := by
  simp [pi_norm_lt_iff hr]

theorem nnnorm_lt_iff {r : ℝ≥0 } (hr : 0 < r) {A : Matrix m n α} : ∥A∥₊ < r ↔ ∀ i j, ∥A i j∥₊ < r := by
  simp [pi_nnnorm_lt_iff hr]

theorem norm_entry_le_entrywise_sup_norm (A : Matrix m n α) {i : m} {j : n} : ∥A i j∥ ≤ ∥A∥ :=
  (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

theorem nnnorm_entry_le_entrywise_sup_nnnorm (A : Matrix m n α) {i : m} {j : n} : ∥A i j∥₊ ≤ ∥A∥₊ :=
  (nnnorm_le_pi_nnnorm (A i) j).trans (nnnorm_le_pi_nnnorm A i)

@[simp]
theorem nnnorm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ∥f a∥₊ = ∥a∥₊) : ∥A.map f∥₊ = ∥A∥₊ := by
  simp_rw [Pi.nnnorm_def, Matrix.map_apply, hf]

@[simp]
theorem norm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ∥f a∥ = ∥a∥) : ∥A.map f∥ = ∥A∥ :=
  (congr_arg (coe : ℝ≥0 → ℝ) <| (nnnorm_map_eq A f) fun a => Subtype.ext <| hf a : _)

@[simp]
theorem nnnorm_transpose (A : Matrix m n α) : ∥Aᵀ∥₊ = ∥A∥₊ := by
  simp_rw [Pi.nnnorm_def]
  exact Finset.sup_comm _ _ _

@[simp]
theorem norm_transpose (A : Matrix m n α) : ∥Aᵀ∥ = ∥A∥ :=
  congr_arg coe <| nnnorm_transpose A

@[simp]
theorem nnnorm_conj_transpose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) : ∥Aᴴ∥₊ = ∥A∥₊ :=
  (nnnorm_map_eq _ _ nnnorm_star).trans A.nnnorm_transpose

@[simp]
theorem norm_conj_transpose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) : ∥Aᴴ∥ = ∥A∥ :=
  congr_arg coe <| nnnorm_conj_transpose A

instance [StarAddMonoid α] [NormedStarGroup α] : NormedStarGroup (Matrix m m α) :=
  ⟨norm_conj_transpose⟩

@[simp]
theorem nnnorm_col (v : m → α) : ∥colₓ v∥₊ = ∥v∥₊ := by
  simp [Pi.nnnorm_def]

@[simp]
theorem norm_col (v : m → α) : ∥colₓ v∥ = ∥v∥ :=
  congr_arg coe <| nnnorm_col v

@[simp]
theorem nnnorm_row (v : n → α) : ∥rowₓ v∥₊ = ∥v∥₊ := by
  simp [Pi.nnnorm_def]

@[simp]
theorem norm_row (v : n → α) : ∥rowₓ v∥ = ∥v∥ :=
  congr_arg coe <| nnnorm_row v

@[simp]
theorem nnnorm_diagonal [DecidableEq n] (v : n → α) : ∥diagonalₓ v∥₊ = ∥v∥₊ := by
  simp_rw [Pi.nnnorm_def]
  congr 1 with i : 1
  refine' le_antisymmₓ (Finset.sup_le fun j hj => _) _
  · obtain rfl | hij := eq_or_ne i j
    · rw [diagonal_apply_eq]
      
    · rw [diagonal_apply_ne _ hij, nnnorm_zero]
      exact zero_le _
      
    
  · refine' Eq.trans_leₓ _ (Finset.le_sup (Finset.mem_univ i))
    rw [diagonal_apply_eq]
    

@[simp]
theorem norm_diagonal [DecidableEq n] (v : n → α) : ∥diagonalₓ v∥ = ∥v∥ :=
  congr_arg coe <| nnnorm_diagonal v

/-- Note this is safe as an instance as it carries no data. -/
instance [Nonempty n] [DecidableEq n] [One α] [NormOneClass α] : NormOneClass (Matrix n n α) :=
  ⟨(norm_diagonal _).trans <| norm_one⟩

end SeminormedAddCommGroup

/-- Normed group instance (using sup norm of sup norm) for matrices over a normed group.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (Matrix m n α) :=
  Pi.normedAddCommGroup

section NormedSpace

attribute [local instance] Matrix.seminormedAddCommGroup

variable [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α]

/-- Normed space instance (using sup norm of sup norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normedSpace : NormedSpace R (Matrix m n α) :=
  Pi.normedSpace

end NormedSpace

end LinfLinf

/-! ### The $L_\infty$ operator norm

This section defines the matrix norm $\|A\|_\infty = \operatorname{sup}_i (\sum_j \|A_{ij}\|)$.

Note that this is equivalent to the operator norm, considering $A$ as a linear map between two
$L^\infty$ spaces.
-/


section LinftyOp

/-- Seminormed group instance (using sup norm of L1 norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpSeminormedAddCommGroup [SeminormedAddCommGroup α] : SeminormedAddCommGroup (Matrix m n α) :=
  (by
    infer_instance : SeminormedAddCommGroup (m → PiLp 1 fun j : n => α))

/-- Normed group instance (using sup norm of L1 norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpNormedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (Matrix m n α) :=
  (by
    infer_instance : NormedAddCommGroup (m → PiLp 1 fun j : n => α))

/-- Normed space instance (using sup norm of L1 norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpNormedSpace [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α] :
    NormedSpace R (Matrix m n α) :=
  (by
    infer_instance : NormedSpace R (m → PiLp 1 fun j : n => α))

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α]

theorem linfty_op_norm_def (A : Matrix m n α) :
    ∥A∥ = ((Finset.univ : Finset m).sup fun i : m => ∑ j : n, ∥A i j∥₊ : ℝ≥0 ) := by
  simp [Pi.norm_def, PiLp.nnnorm_eq_sum Ennreal.one_ne_top]

theorem linfty_op_nnnorm_def (A : Matrix m n α) : ∥A∥₊ = (Finset.univ : Finset m).sup fun i : m => ∑ j : n, ∥A i j∥₊ :=
  Subtype.ext <| linfty_op_norm_def A

@[simp]
theorem linfty_op_nnnorm_col (v : m → α) : ∥colₓ v∥₊ = ∥v∥₊ := by
  rw [linfty_op_nnnorm_def, Pi.nnnorm_def]
  simp

@[simp]
theorem linfty_op_norm_col (v : m → α) : ∥colₓ v∥ = ∥v∥ :=
  congr_arg coe <| linfty_op_nnnorm_col v

@[simp]
theorem linfty_op_nnnorm_row (v : n → α) : ∥rowₓ v∥₊ = ∑ i, ∥v i∥₊ := by
  simp [linfty_op_nnnorm_def]

@[simp]
theorem linfty_op_norm_row (v : n → α) : ∥rowₓ v∥ = ∑ i, ∥v i∥ :=
  (congr_arg coe <| linfty_op_nnnorm_row v).trans <| by
    simp [Nnreal.coe_sum]

@[simp]
theorem linfty_op_nnnorm_diagonal [DecidableEq m] (v : m → α) : ∥diagonalₓ v∥₊ = ∥v∥₊ := by
  rw [linfty_op_nnnorm_def, Pi.nnnorm_def]
  congr 1 with i : 1
  refine' ((Finset.sum_eq_single_of_mem _ (Finset.mem_univ i)) fun j hj hij => _).trans _
  · rw [diagonal_apply_ne' _ hij, nnnorm_zero]
    
  · rw [diagonal_apply_eq]
    

@[simp]
theorem linfty_op_norm_diagonal [DecidableEq m] (v : m → α) : ∥diagonalₓ v∥ = ∥v∥ :=
  congr_arg coe <| linfty_op_nnnorm_diagonal v

end SeminormedAddCommGroup

section NonUnitalSemiNormedRing

variable [NonUnitalSemiNormedRing α]

-- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (k j)
theorem linfty_op_nnnorm_mul (A : Matrix l m α) (B : Matrix m n α) : ∥A ⬝ B∥₊ ≤ ∥A∥₊ * ∥B∥₊ := by
  simp_rw [linfty_op_nnnorm_def, Matrix.mul_apply]
  calc
    (finset.univ.sup fun i => ∑ k, ∥∑ j, A i j * B j k∥₊) ≤ finset.univ.sup fun i => ∑ (k) (j), ∥A i j∥₊ * ∥B j k∥₊ :=
      Finset.sup_mono_fun fun i hi =>
        Finset.sum_le_sum fun k hk => (nnnorm_sum_le_of_le _) fun j hj => nnnorm_mul_le _ _
    _ = finset.univ.sup fun i => ∑ j, ∥A i j∥₊ * ∑ k, ∥B j k∥₊ := by
      simp_rw [@Finset.sum_comm _ m n, Finset.mul_sum]
    _ ≤ finset.univ.sup fun i => ∑ j, ∥A i j∥₊ * finset.univ.sup fun i => ∑ j, ∥B i j∥₊ :=
      Finset.sup_mono_fun fun i hi =>
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (Finset.le_sup hj) (zero_le _)
    _ ≤ (finset.univ.sup fun i => ∑ j, ∥A i j∥₊) * finset.univ.sup fun i => ∑ j, ∥B i j∥₊ := by
      simp_rw [← Finset.sum_mul, ← Nnreal.finset_sup_mul]
    

theorem linfty_op_norm_mul (A : Matrix l m α) (B : Matrix m n α) : ∥A ⬝ B∥ ≤ ∥A∥ * ∥B∥ :=
  linfty_op_nnnorm_mul _ _

theorem linfty_op_nnnorm_mul_vec (A : Matrix l m α) (v : m → α) : ∥A.mulVec v∥₊ ≤ ∥A∥₊ * ∥v∥₊ := by
  rw [← linfty_op_nnnorm_col (A.mul_vec v), ← linfty_op_nnnorm_col v]
  exact linfty_op_nnnorm_mul A (col v)

theorem linfty_op_norm_mul_vec (A : Matrix l m α) (v : m → α) : ∥Matrix.mulVecₓ A v∥ ≤ ∥A∥ * ∥v∥ :=
  linfty_op_nnnorm_mul_vec _ _

end NonUnitalSemiNormedRing

/-- Seminormed non-unital ring instance (using sup norm of L1 norm) for matrices over a semi normed
non-unital ring. Not declared as an instance because there are several natural choices for defining
the norm of a matrix. -/
@[local instance]
protected def linftyOpNonUnitalSemiNormedRing [NonUnitalSemiNormedRing α] : NonUnitalSemiNormedRing (Matrix n n α) :=
  { Matrix.linftyOpSeminormedAddCommGroup, Matrix.nonUnitalRing with norm_mul := linfty_op_norm_mul }

/-- The `L₁-L∞` norm preserves one on non-empty matrices. Note this is safe as an instance, as it
carries no data. -/
instance linfty_op_norm_one_class [SemiNormedRing α] [NormOneClass α] [DecidableEq n] [Nonempty n] :
    NormOneClass (Matrix n n α) where norm_one := (linfty_op_norm_diagonal _).trans norm_one

/-- Seminormed ring instance (using sup norm of L1 norm) for matrices over a semi normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpSemiNormedRing [SemiNormedRing α] [DecidableEq n] : SemiNormedRing (Matrix n n α) :=
  { Matrix.linftyOpNonUnitalSemiNormedRing, Matrix.ring with }

/-- Normed non-unital ring instance (using sup norm of L1 norm) for matrices over a normed
non-unital ring. Not declared as an instance because there are several natural choices for defining
the norm of a matrix. -/
@[local instance]
protected def linftyOpNonUnitalNormedRing [NonUnitalNormedRing α] : NonUnitalNormedRing (Matrix n n α) :=
  { Matrix.linftyOpNonUnitalSemiNormedRing with }

/-- Normed ring instance (using sup norm of L1 norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpNormedRing [NormedRing α] [DecidableEq n] : NormedRing (Matrix n n α) :=
  { Matrix.linftyOpSemiNormedRing with }

/-- Normed algebra instance (using sup norm of L1 norm) for matrices over a normed algebra. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpNormedAlgebra [NormedField R] [SemiNormedRing α] [NormedAlgebra R α] [DecidableEq n] :
    NormedAlgebra R (Matrix n n α) :=
  { Matrix.linftyOpNormedSpace with }

end LinftyOp

/-! ### The Frobenius norm

This is defined as $\|A\| = \sqrt{\sum_{i,j} \|A_{ij}\|^2}$.
When the matrix is over the real or complex numbers, this norm is submultiplicative.
-/


section frobenius

open Matrix BigOperators

/-- Seminormed group instance (using frobenius norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusSeminormedAddCommGroup [SeminormedAddCommGroup α] : SeminormedAddCommGroup (Matrix m n α) :=
  (by
    infer_instance : SeminormedAddCommGroup (PiLp 2 fun i : m => PiLp 2 fun j : n => α))

/-- Normed group instance (using frobenius norm) for matrices over a normed group.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusNormedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (Matrix m n α) :=
  (by
    infer_instance : NormedAddCommGroup (PiLp 2 fun i : m => PiLp 2 fun j : n => α))

/-- Normed space instance (using frobenius norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusNormedSpace [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α] : NormedSpace R (Matrix m n α) :=
  (by
    infer_instance : NormedSpace R (PiLp 2 fun i : m => PiLp 2 fun j : n => α))

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

-- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j)
theorem frobenius_nnnorm_def (A : Matrix m n α) : ∥A∥₊ = (∑ (i) (j), ∥A i j∥₊ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  simp_rw [PiLp.nnnorm_eq_of_L2, Nnreal.sq_sqrt, Nnreal.sqrt_eq_rpow, Nnreal.rpow_two]

-- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j)
theorem frobenius_norm_def (A : Matrix m n α) : ∥A∥ = (∑ (i) (j), ∥A i j∥ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
  (congr_arg coe (frobenius_nnnorm_def A)).trans <| by
    simp [Nnreal.coe_sum]

@[simp]
theorem frobenius_nnnorm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ∥f a∥₊ = ∥a∥₊) : ∥A.map f∥₊ = ∥A∥₊ := by
  simp_rw [frobenius_nnnorm_def, Matrix.map_apply, hf]

@[simp]
theorem frobenius_norm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ∥f a∥ = ∥a∥) : ∥A.map f∥ = ∥A∥ :=
  (congr_arg (coe : ℝ≥0 → ℝ) <| (frobenius_nnnorm_map_eq A f) fun a => Subtype.ext <| hf a : _)

@[simp]
theorem frobenius_nnnorm_transpose (A : Matrix m n α) : ∥Aᵀ∥₊ = ∥A∥₊ := by
  rw [frobenius_nnnorm_def, frobenius_nnnorm_def, Finset.sum_comm]
  rfl

@[simp]
theorem frobenius_norm_transpose (A : Matrix m n α) : ∥Aᵀ∥ = ∥A∥ :=
  congr_arg coe <| frobenius_nnnorm_transpose A

@[simp]
theorem frobenius_nnnorm_conj_transpose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) : ∥Aᴴ∥₊ = ∥A∥₊ :=
  (frobenius_nnnorm_map_eq _ _ nnnorm_star).trans A.frobenius_nnnorm_transpose

@[simp]
theorem frobenius_norm_conj_transpose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) : ∥Aᴴ∥ = ∥A∥ :=
  congr_arg coe <| frobenius_nnnorm_conj_transpose A

instance frobenius_normed_star_group [StarAddMonoid α] [NormedStarGroup α] : NormedStarGroup (Matrix m m α) :=
  ⟨frobenius_norm_conj_transpose⟩

@[simp]
theorem frobenius_norm_row (v : m → α) : ∥rowₓ v∥ = ∥(PiLp.equiv 2 _).symm v∥ := by
  rw [frobenius_norm_def, Fintype.sum_unique, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
  simp only [row_apply, Real.rpow_two, PiLp.equiv_symm_apply']

@[simp]
theorem frobenius_nnnorm_row (v : m → α) : ∥rowₓ v∥₊ = ∥(PiLp.equiv 2 _).symm v∥₊ :=
  Subtype.ext <| frobenius_norm_row v

@[simp]
theorem frobenius_norm_col (v : n → α) : ∥colₓ v∥ = ∥(PiLp.equiv 2 _).symm v∥ := by
  simp_rw [frobenius_norm_def, Fintype.sum_unique, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
  simp only [col_apply, Real.rpow_two, PiLp.equiv_symm_apply']

@[simp]
theorem frobenius_nnnorm_col (v : n → α) : ∥colₓ v∥₊ = ∥(PiLp.equiv 2 _).symm v∥₊ :=
  Subtype.ext <| frobenius_norm_col v

@[simp]
theorem frobenius_nnnorm_diagonal [DecidableEq n] (v : n → α) : ∥diagonalₓ v∥₊ = ∥(PiLp.equiv 2 _).symm v∥₊ := by
  simp_rw [frobenius_nnnorm_def, ← Finset.sum_product', Finset.univ_product_univ, PiLp.nnnorm_eq_of_L2]
  let s := (Finset.univ : Finset n).map ⟨fun i : n => (i, i), fun i j h => congr_arg Prod.fst h⟩
  rw [← Finset.sum_subset (Finset.subset_univ s) fun i hi his => _]
  · rw [Finset.sum_map, Nnreal.sqrt_eq_rpow]
    dsimp'
    simp_rw [diagonal_apply_eq, Nnreal.rpow_two]
    
  · suffices i.1 ≠ i.2 by
      rw [diagonal_apply_ne _ this, nnnorm_zero, Nnreal.zero_rpow two_ne_zero]
    intro h
    exact finset.mem_map.not.mp his ⟨i.1, Finset.mem_univ _, Prod.extₓ rfl h⟩
    

@[simp]
theorem frobenius_norm_diagonal [DecidableEq n] (v : n → α) : ∥diagonalₓ v∥ = ∥(PiLp.equiv 2 _).symm v∥ :=
  (congr_arg coe <| frobenius_nnnorm_diagonal v : _).trans rfl

end SeminormedAddCommGroup

theorem frobenius_nnnorm_one [DecidableEq n] [SeminormedAddCommGroup α] [One α] :
    ∥(1 : Matrix n n α)∥₊ = Nnreal.sqrt (Fintype.card n) * ∥(1 : α)∥₊ := by
  refine' (frobenius_nnnorm_diagonal _).trans _
  simp_rw [PiLp.nnnorm_equiv_symm_const Ennreal.two_ne_top, Nnreal.sqrt_eq_rpow]
  simp only [Ennreal.to_real_div, Ennreal.one_to_real, Ennreal.to_real_bit0]

section IsROrC

variable [IsROrC α]

theorem frobenius_nnnorm_mul (A : Matrix l m α) (B : Matrix m n α) : ∥A ⬝ B∥₊ ≤ ∥A∥₊ * ∥B∥₊ := by
  simp_rw [frobenius_nnnorm_def, Matrix.mul_apply]
  rw [← Nnreal.mul_rpow, @Finset.sum_comm _ n m, Finset.sum_mul_sum, Finset.sum_product]
  refine' Nnreal.rpow_le_rpow _ one_half_pos.le
  refine' Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => _
  rw [← Nnreal.rpow_le_rpow_iff one_half_pos, ← Nnreal.rpow_mul, mul_div_cancel' (1 : ℝ) two_ne_zero, Nnreal.rpow_one,
    Nnreal.mul_rpow]
  dsimp' only
  have :=
    @nnnorm_inner_le_nnnorm α _ _ _ ((PiLp.equiv 2 fun i => α).symm fun j => star (A i j))
      ((PiLp.equiv 2 fun i => α).symm fun k => B k j)
  simpa only [PiLp.equiv_symm_apply, PiLp.inner_apply, IsROrC.inner_apply, star_ring_end_apply, Pi.nnnorm_def,
    PiLp.nnnorm_eq_of_L2, star_star, nnnorm_star, Nnreal.sqrt_eq_rpow, Nnreal.rpow_two] using this

theorem frobenius_norm_mul (A : Matrix l m α) (B : Matrix m n α) : ∥A ⬝ B∥ ≤ ∥A∥ * ∥B∥ :=
  frobenius_nnnorm_mul A B

/-- Normed ring instance (using frobenius norm) for matrices over `ℝ` or `ℂ`.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusNormedRing [DecidableEq m] : NormedRing (Matrix m m α) :=
  { Matrix.frobeniusSeminormedAddCommGroup with norm := HasNorm.norm, norm_mul := frobenius_norm_mul }

/-- Normed algebra instance (using frobenius norm) for matrices over `ℝ` or `ℂ`.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusNormedAlgebra [DecidableEq m] [NormedField R] [NormedAlgebra R α] : NormedAlgebra R (Matrix m m α) :=
  { Matrix.frobeniusNormedSpace with }

end IsROrC

end frobenius

end Matrix

