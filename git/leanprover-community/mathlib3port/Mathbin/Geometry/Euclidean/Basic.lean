/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathbin.Algebra.QuadraticDiscriminant
import Mathbin.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathbin.Analysis.Calculus.Conformal.NormedSpace

/-!
# Euclidean spaces

This file makes some definitions and proves very basic geometrical
results about real inner product spaces and Euclidean affine spaces.
Results about real inner product spaces that involve the norm and
inner product but not angles generally go in
`analysis.normed_space.inner_product`.  Results with longer
proofs or more geometrical content generally go in separate files.

## Main definitions

* `inner_product_geometry.angle` is the undirected angle between two
  vectors.

* `euclidean_geometry.angle`, with notation `∠`, is the undirected
  angle determined by three points.

* `euclidean_geometry.orthogonal_projection` is the orthogonal
  projection of a point onto an affine subspace.

* `euclidean_geometry.reflection` is the reflection of a point in an
  affine subspace.

## Implementation notes

To declare `P` as the type of points in a Euclidean affine space with
`V` as the type of vectors, use `[inner_product_space ℝ V] [metric_space P]
[normed_add_torsor V P]`.  This works better with `out_param` to make
`V` implicit in most cases than having a separate type alias for
Euclidean affine spaces.

Rather than requiring Euclidean affine spaces to be finite-dimensional
(as in the definition on Wikipedia), this is specified only for those
theorems that need it.

## References

* https://en.wikipedia.org/wiki/Euclidean_space

-/


noncomputable section

open_locale BigOperators

open_locale Classical

open_locale Real

open_locale RealInnerProductSpace

namespace InnerProductGeometry

/-!
### Geometrical results on real inner product spaces

This section develops some geometrical definitions and results on real
inner product spaces, where those definitions and results can most
conveniently be developed in terms of vectors and then used to deduce
corresponding results for Euclidean affine spaces.
-/


variable {V : Type _} [InnerProductSpace ℝ V]

/-- The undirected angle between two vectors. If either vector is 0,
this is π/2. See `orientation.oangle` for the corresponding oriented angle
definition. -/
def angle (x y : V) : ℝ :=
  Real.arccos (inner x y / (∥x∥ * ∥y∥))

theorem IsConformalMap.preserves_angle {E F : Type _} [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] {f' : E →L[ℝ] F}
    (h : IsConformalMap f') (u v : E) : angle (f' u) (f' v) = angle u v := by
  obtain ⟨c, hc, li, hcf⟩ := h
  suffices c * (c * inner u v) / (∥c∥ * ∥u∥ * (∥c∥ * ∥v∥)) = inner u v / (∥u∥ * ∥v∥) by
    simp [this, angle, hcf, norm_smul, inner_smul_left, inner_smul_right]
  by_cases' hu : ∥u∥ = 0
  · simp [norm_eq_zero.mp hu]
    
  by_cases' hv : ∥v∥ = 0
  · simp [norm_eq_zero.mp hv]
    
  have hc : ∥c∥ ≠ 0 := fun w => hc (norm_eq_zero.mp w)
  field_simp
  have : c * c = ∥c∥ * ∥c∥ := by
    simp [Real.norm_eq_abs, abs_mul_abs_self]
  convert congr_argₓ (fun x => x * ⟪u, v⟫ * ∥u∥ * ∥v∥) this using 1 <;> ring

/-- If a real differentiable map `f` is conformal at a point `x`,
    then it preserves the angles at that point. -/
theorem ConformalAt.preserves_angle {E F : Type _} [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] {f : E → F} {x : E}
    {f' : E →L[ℝ] F} (h : HasFderivAt f f' x) (H : ConformalAt f x) (u v : E) : angle (f' u) (f' v) = angle u v :=
  let ⟨f₁, h₁, c⟩ := H
  h₁.unique h ▸ IsConformalMap.preserves_angle c u v

/-- The cosine of the angle between two vectors. -/
theorem cos_angle (x y : V) : Real.cos (angle x y) = inner x y / (∥x∥ * ∥y∥) :=
  Real.cos_arccos (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
    (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2

/-- The angle between two vectors does not depend on their order. -/
theorem angle_comm (x y : V) : angle x y = angle y x := by
  unfold angle
  rw [real_inner_comm, mul_comm]

/-- The angle between the negation of two vectors. -/
@[simp]
theorem angle_neg_neg (x y : V) : angle (-x) (-y) = angle x y := by
  unfold angle
  rw [inner_neg_neg, norm_neg, norm_neg]

/-- The angle between two vectors is nonnegative. -/
theorem angle_nonneg (x y : V) : 0 ≤ angle x y :=
  Real.arccos_nonneg _

/-- The angle between two vectors is at most π. -/
theorem angle_le_pi (x y : V) : angle x y ≤ π :=
  Real.arccos_le_pi _

/-- The angle between a vector and the negation of another vector. -/
theorem angle_neg_right (x y : V) : angle x (-y) = π - angle x y := by
  unfold angle
  rw [← Real.arccos_neg, norm_neg, inner_neg_right, neg_div]

/-- The angle between the negation of a vector and another vector. -/
theorem angle_neg_left (x y : V) : angle (-x) y = π - angle x y := by
  rw [← angle_neg_neg, neg_negₓ, angle_neg_right]

/-- The angle between the zero vector and a vector. -/
@[simp]
theorem angle_zero_left (x : V) : angle 0 x = π / 2 := by
  unfold angle
  rw [inner_zero_left, zero_div, Real.arccos_zero]

/-- The angle between a vector and the zero vector. -/
@[simp]
theorem angle_zero_right (x : V) : angle x 0 = π / 2 := by
  unfold angle
  rw [inner_zero_right, zero_div, Real.arccos_zero]

/-- The angle between a nonzero vector and itself. -/
@[simp]
theorem angle_self {x : V} (hx : x ≠ 0) : angle x x = 0 := by
  unfold angle
  rw [← real_inner_self_eq_norm_mul_norm, div_self fun h => hx (inner_self_eq_zero.1 h), Real.arccos_one]

/-- The angle between a nonzero vector and its negation. -/
@[simp]
theorem angle_self_neg_of_nonzero {x : V} (hx : x ≠ 0) : angle x (-x) = π := by
  rw [angle_neg_right, angle_self hx, sub_zero]

/-- The angle between the negation of a nonzero vector and that
vector. -/
@[simp]
theorem angle_neg_self_of_nonzero {x : V} (hx : x ≠ 0) : angle (-x) x = π := by
  rw [angle_comm, angle_self_neg_of_nonzero hx]

/-- The angle between a vector and a positive multiple of a vector. -/
@[simp]
theorem angle_smul_right_of_pos (x y : V) {r : ℝ} (hr : 0 < r) : angle x (r • y) = angle x y := by
  unfold angle
  rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_ltₓ hr), ← mul_assoc, mul_comm _ r, mul_assoc,
    mul_div_mul_left _ _ (ne_of_gtₓ hr)]

/-- The angle between a positive multiple of a vector and a vector. -/
@[simp]
theorem angle_smul_left_of_pos (x y : V) {r : ℝ} (hr : 0 < r) : angle (r • x) y = angle x y := by
  rw [angle_comm, angle_smul_right_of_pos y x hr, angle_comm]

/-- The angle between a vector and a negative multiple of a vector. -/
@[simp]
theorem angle_smul_right_of_neg (x y : V) {r : ℝ} (hr : r < 0) : angle x (r • y) = angle x (-y) := by
  rw [← neg_negₓ r, neg_smul, angle_neg_right, angle_smul_right_of_pos x y (neg_pos_of_neg hr), angle_neg_right]

/-- The angle between a negative multiple of a vector and a vector. -/
@[simp]
theorem angle_smul_left_of_neg (x y : V) {r : ℝ} (hr : r < 0) : angle (r • x) y = angle (-x) y := by
  rw [angle_comm, angle_smul_right_of_neg y x hr, angle_comm]

/-- The cosine of the angle between two vectors, multiplied by the
product of their norms. -/
theorem cos_angle_mul_norm_mul_norm (x y : V) : Real.cos (angle x y) * (∥x∥ * ∥y∥) = inner x y := by
  rw [cos_angle, div_mul_cancel_of_imp]
  simp (config := { contextual := true })[or_imp_distrib]

/-- The sine of the angle between two vectors, multiplied by the
product of their norms. -/
theorem sin_angle_mul_norm_mul_norm (x y : V) :
    Real.sin (angle x y) * (∥x∥ * ∥y∥) = Real.sqrt (inner x x * inner y y - inner x y * inner x y) := by
  unfold angle
  rw
    [Real.sin_arccos (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1
      (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2,
    ← Real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)), ← Real.sqrt_mul' _ (mul_self_nonneg _), sq,
    Real.sqrt_mul_self (mul_nonneg (norm_nonneg x) (norm_nonneg y)), real_inner_self_eq_norm_mul_norm,
    real_inner_self_eq_norm_mul_norm]
  by_cases' h : ∥x∥ * ∥y∥ = 0
  · rw
      [show ∥x∥ * ∥x∥ * (∥y∥ * ∥y∥) = ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥) by
        ring,
      h, mul_zero, mul_zero, zero_sub]
    cases' eq_zero_or_eq_zero_of_mul_eq_zero h with hx hy
    · rw [norm_eq_zero] at hx
      rw [hx, inner_zero_left, zero_mul, neg_zero]
      
    · rw [norm_eq_zero] at hy
      rw [hy, inner_zero_right, zero_mul, neg_zero]
      
    
  · field_simp [h]
    ring_nf
    

/-- The angle between two vectors is zero if and only if they are
nonzero and one is a positive multiple of the other. -/
theorem angle_eq_zero_iff {x y : V} : angle x y = 0 ↔ x ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • x := by
  rw [angle, ← real_inner_div_norm_mul_norm_eq_one_iff, Real.arccos_eq_zero, LE.le.le_iff_eq, eq_comm]
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).2

/-- The angle between two vectors is π if and only if they are nonzero
and one is a negative multiple of the other. -/
theorem angle_eq_pi_iff {x y : V} : angle x y = π ↔ x ≠ 0 ∧ ∃ r : ℝ, r < 0 ∧ y = r • x := by
  rw [angle, ← real_inner_div_norm_mul_norm_eq_neg_one_iff, Real.arccos_eq_pi, LE.le.le_iff_eq]
  exact (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x y)).1

/-- If the angle between two vectors is π, the angles between those
vectors and a third vector add to π. -/
theorem angle_add_angle_eq_pi_of_angle_eq_pi {x y : V} (z : V) (h : angle x y = π) : angle x z + angle y z = π := by
  rcases angle_eq_pi_iff.1 h with ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
  rw [angle_smul_left_of_neg x z hr, angle_neg_left, add_sub_cancel'_right]

/-- Two vectors have inner product 0 if and only if the angle between
them is π/2. -/
theorem inner_eq_zero_iff_angle_eq_pi_div_two (x y : V) : ⟪x, y⟫ = 0 ↔ angle x y = π / 2 :=
  Iff.symm <| by
    simp (config := { contextual := true })[angle, or_imp_distrib]

/-- If the angle between two vectors is π, the inner product equals the negative product
of the norms. -/
theorem inner_eq_neg_mul_norm_of_angle_eq_pi {x y : V} (h : angle x y = π) : ⟪x, y⟫ = -(∥x∥ * ∥y∥) := by
  simp [← cos_angle_mul_norm_mul_norm, h]

/-- If the angle between two vectors is 0, the inner product equals the product of the norms. -/
theorem inner_eq_mul_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) : ⟪x, y⟫ = ∥x∥ * ∥y∥ := by
  simp [← cos_angle_mul_norm_mul_norm, h]

/-- The inner product of two non-zero vectors equals the negative product of their norms
if and only if the angle between the two vectors is π. -/
theorem inner_eq_neg_mul_norm_iff_angle_eq_pi {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ⟪x, y⟫ = -(∥x∥ * ∥y∥) ↔ angle x y = π := by
  refine' ⟨fun h => _, inner_eq_neg_mul_norm_of_angle_eq_pi⟩
  have h₁ : ∥x∥ * ∥y∥ ≠ 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  rw [angle, h, neg_div, div_self h₁, Real.arccos_neg_one]

/-- The inner product of two non-zero vectors equals the product of their norms
if and only if the angle between the two vectors is 0. -/
theorem inner_eq_mul_norm_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : ⟪x, y⟫ = ∥x∥ * ∥y∥ ↔ angle x y = 0 :=
  by
  refine' ⟨fun h => _, inner_eq_mul_norm_of_angle_eq_zero⟩
  have h₁ : ∥x∥ * ∥y∥ ≠ 0 := (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)).ne'
  rw [angle, h, div_self h₁, Real.arccos_one]

/-- If the angle between two vectors is π, the norm of their difference equals
the sum of their norms. -/
theorem norm_sub_eq_add_norm_of_angle_eq_pi {x y : V} (h : angle x y = π) : ∥x - y∥ = ∥x∥ + ∥y∥ := by
  rw [← sq_eq_sq (norm_nonneg (x - y)) (add_nonneg (norm_nonneg x) (norm_nonneg y))]
  rw [norm_sub_pow_two_real, inner_eq_neg_mul_norm_of_angle_eq_pi h]
  ring

/-- If the angle between two vectors is 0, the norm of their sum equals
the sum of their norms. -/
theorem norm_add_eq_add_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) : ∥x + y∥ = ∥x∥ + ∥y∥ := by
  rw [← sq_eq_sq (norm_nonneg (x + y)) (add_nonneg (norm_nonneg x) (norm_nonneg y))]
  rw [norm_add_pow_two_real, inner_eq_mul_norm_of_angle_eq_zero h]
  ring

/-- If the angle between two vectors is 0, the norm of their difference equals
the absolute value of the difference of their norms. -/
theorem norm_sub_eq_abs_sub_norm_of_angle_eq_zero {x y : V} (h : angle x y = 0) : ∥x - y∥ = abs (∥x∥ - ∥y∥) := by
  rw [← sq_eq_sq (norm_nonneg (x - y)) (abs_nonneg (∥x∥ - ∥y∥)), norm_sub_pow_two_real,
    inner_eq_mul_norm_of_angle_eq_zero h, sq_abs (∥x∥ - ∥y∥)]
  ring

/-- The norm of the difference of two non-zero vectors equals the sum of their norms
if and only the angle between the two vectors is π. -/
theorem norm_sub_eq_add_norm_iff_angle_eq_pi {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∥x - y∥ = ∥x∥ + ∥y∥ ↔ angle x y = π := by
  refine' ⟨fun h => _, norm_sub_eq_add_norm_of_angle_eq_pi⟩
  rw [← inner_eq_neg_mul_norm_iff_angle_eq_pi hx hy]
  obtain ⟨hxy₁, hxy₂⟩ := norm_nonneg (x - y), add_nonneg (norm_nonneg x) (norm_nonneg y)
  rw [← sq_eq_sq hxy₁ hxy₂, norm_sub_pow_two_real] at h
  calc inner x y = (∥x∥ ^ 2 + ∥y∥ ^ 2 - (∥x∥ + ∥y∥) ^ 2) / 2 := by
      linarith _ = -(∥x∥ * ∥y∥) := by
      ring

/-- The norm of the sum of two non-zero vectors equals the sum of their norms
if and only the angle between the two vectors is 0. -/
theorem norm_add_eq_add_norm_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∥x + y∥ = ∥x∥ + ∥y∥ ↔ angle x y = 0 := by
  refine' ⟨fun h => _, norm_add_eq_add_norm_of_angle_eq_zero⟩
  rw [← inner_eq_mul_norm_iff_angle_eq_zero hx hy]
  obtain ⟨hxy₁, hxy₂⟩ := norm_nonneg (x + y), add_nonneg (norm_nonneg x) (norm_nonneg y)
  rw [← sq_eq_sq hxy₁ hxy₂, norm_add_pow_two_real] at h
  calc inner x y = ((∥x∥ + ∥y∥) ^ 2 - ∥x∥ ^ 2 - ∥y∥ ^ 2) / 2 := by
      linarith _ = ∥x∥ * ∥y∥ := by
      ring

/-- The norm of the difference of two non-zero vectors equals the absolute value
of the difference of their norms if and only the angle between the two vectors is 0. -/
theorem norm_sub_eq_abs_sub_norm_iff_angle_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∥x - y∥ = abs (∥x∥ - ∥y∥) ↔ angle x y = 0 := by
  refine' ⟨fun h => _, norm_sub_eq_abs_sub_norm_of_angle_eq_zero⟩
  rw [← inner_eq_mul_norm_iff_angle_eq_zero hx hy]
  have h1 : ∥x - y∥ ^ 2 = (∥x∥ - ∥y∥) ^ 2 := by
    rw [h]
    exact sq_abs (∥x∥ - ∥y∥)
  rw [norm_sub_pow_two_real] at h1
  calc inner x y = ((∥x∥ + ∥y∥) ^ 2 - ∥x∥ ^ 2 - ∥y∥ ^ 2) / 2 := by
      linarith _ = ∥x∥ * ∥y∥ := by
      ring

/-- The norm of the sum of two vectors equals the norm of their difference if and only if
the angle between them is π/2. -/
theorem norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (x y : V) : ∥x + y∥ = ∥x - y∥ ↔ angle x y = π / 2 := by
  rw [← sq_eq_sq (norm_nonneg (x + y)) (norm_nonneg (x - y)), ← inner_eq_zero_iff_angle_eq_pi_div_two x y,
    norm_add_pow_two_real, norm_sub_pow_two_real]
  constructor <;> intro h <;> linarith

end InnerProductGeometry

namespace EuclideanGeometry

/-!
### Geometrical results on Euclidean affine spaces

This section develops some geometrical definitions and results on
Euclidean affine spaces.
-/


open InnerProductGeometry

variable {V : Type _} {P : Type _} [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner ℝ V _ x y

include V

/-- The undirected angle at `p2` between the line segments to `p1` and
`p3`. If either of those points equals `p2`, this is π/2. Use
`open_locale euclidean_geometry` to access the `∠ p1 p2 p3`
notation. -/
def angle (p1 p2 p3 : P) : ℝ :=
  angle (p1 -ᵥ p2 : V) (p3 -ᵥ p2)

-- mathport name: «expr∠»
localized [EuclideanGeometry] notation "∠" => EuclideanGeometry.angle

/-- The angle at a point does not depend on the order of the other two
points. -/
theorem angle_comm (p1 p2 p3 : P) : ∠ p1 p2 p3 = ∠ p3 p2 p1 :=
  angle_comm _ _

/-- The angle at a point is nonnegative. -/
theorem angle_nonneg (p1 p2 p3 : P) : 0 ≤ ∠ p1 p2 p3 :=
  angle_nonneg _ _

/-- The angle at a point is at most π. -/
theorem angle_le_pi (p1 p2 p3 : P) : ∠ p1 p2 p3 ≤ π :=
  angle_le_pi _ _

/-- The angle ∠AAB at a point. -/
theorem angle_eq_left (p1 p2 : P) : ∠ p1 p1 p2 = π / 2 := by
  unfold angle
  rw [vsub_self]
  exact angle_zero_left _

/-- The angle ∠ABB at a point. -/
theorem angle_eq_right (p1 p2 : P) : ∠ p1 p2 p2 = π / 2 := by
  rw [angle_comm, angle_eq_left]

/-- The angle ∠ABA at a point. -/
theorem angle_eq_of_ne {p1 p2 : P} (h : p1 ≠ p2) : ∠ p1 p2 p1 = 0 :=
  angle_self fun he => h (vsub_eq_zero_iff_eq.1 he)

/-- If the angle ∠ABC at a point is π, the angle ∠BAC is 0. -/
theorem angle_eq_zero_of_angle_eq_pi_left {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : ∠ p2 p1 p3 = 0 := by
  unfold angle  at h
  rw [angle_eq_pi_iff] at h
  rcases h with ⟨hp1p2, ⟨r, ⟨hr, hpr⟩⟩⟩
  unfold angle
  rw [angle_eq_zero_iff]
  rw [← neg_vsub_eq_vsub_rev, neg_ne_zero] at hp1p2
  use hp1p2, -r + 1, add_pos (neg_pos_of_neg hr) zero_lt_one
  rw [add_smul, ← neg_vsub_eq_vsub_rev p1 p2, smul_neg]
  simp [← hpr]

/-- If the angle ∠ABC at a point is π, the angle ∠BCA is 0. -/
theorem angle_eq_zero_of_angle_eq_pi_right {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : ∠ p2 p3 p1 = 0 := by
  rw [angle_comm] at h
  exact angle_eq_zero_of_angle_eq_pi_left h

/-- If ∠BCD = π, then ∠ABC = ∠ABD. -/
theorem angle_eq_angle_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) : ∠ p1 p2 p3 = ∠ p1 p2 p4 := by
  unfold angle  at *
  rcases angle_eq_pi_iff.1 h with ⟨hp2p3, ⟨r, ⟨hr, hpr⟩⟩⟩
  rw [eq_comm]
  convert angle_smul_right_of_pos (p1 -ᵥ p2) (p3 -ᵥ p2) (add_pos (neg_pos_of_neg hr) zero_lt_one)
  rw [add_smul, ← neg_vsub_eq_vsub_rev p2 p3, smul_neg, neg_smul, ← hpr]
  simp

/-- If ∠BCD = π, then ∠ACB + ∠ACD = π. -/
theorem angle_add_angle_eq_pi_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
    ∠ p1 p3 p2 + ∠ p1 p3 p4 = π := by
  unfold angle  at h
  rw [angle_comm p1 p3 p2, angle_comm p1 p3 p4]
  unfold angle
  exact angle_add_angle_eq_pi_of_angle_eq_pi _ h

/-- Vertical Angles Theorem: angles opposite each other, formed by two intersecting straight
lines, are equal. -/
theorem angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi {p1 p2 p3 p4 p5 : P} (hapc : ∠ p1 p5 p3 = π)
    (hbpd : ∠ p2 p5 p4 = π) : ∠ p1 p5 p2 = ∠ p3 p5 p4 := by
  linarith [angle_add_angle_eq_pi_of_angle_eq_pi p1 hbpd, angle_comm p4 p5 p1,
    angle_add_angle_eq_pi_of_angle_eq_pi p4 hapc, angle_comm p4 p5 p3]

/-- If ∠ABC = π then dist A B ≠ 0. -/
theorem left_dist_ne_zero_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : dist p1 p2 ≠ 0 := by
  by_contra heq
  rw [dist_eq_zero] at heq
  rw [HEq, angle_eq_left] at h
  exact
    Real.pi_ne_zero
      (by
        linarith)

/-- If ∠ABC = π then dist C B ≠ 0. -/
theorem right_dist_ne_zero_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : dist p3 p2 ≠ 0 :=
  left_dist_ne_zero_of_angle_eq_pi <| (angle_comm _ _ _).trans h

/-- If ∠ABC = π, then (dist A C) = (dist A B) + (dist B C). -/
theorem dist_eq_add_dist_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : dist p1 p3 = dist p1 p2 + dist p3 p2 := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_add_norm_of_angle_eq_pi h

/-- If A ≠ B and C ≠ B then ∠ABC = π if and only if (dist A C) = (dist A B) + (dist B C). -/
theorem dist_eq_add_dist_iff_angle_eq_pi {p1 p2 p3 : P} (hp1p2 : p1 ≠ p2) (hp3p2 : p3 ≠ p2) :
    dist p1 p3 = dist p1 p2 + dist p3 p2 ↔ ∠ p1 p2 p3 = π := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_add_norm_iff_angle_eq_pi (fun he => hp1p2 (vsub_eq_zero_iff_eq.1 he)) fun he =>
      hp3p2 (vsub_eq_zero_iff_eq.1 he)

/-- If ∠ABC = 0, then (dist A C) = abs ((dist A B) - (dist B C)). -/
theorem dist_eq_abs_sub_dist_of_angle_eq_zero {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = 0) :
    dist p1 p3 = abs (dist p1 p2 - dist p3 p2) := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact norm_sub_eq_abs_sub_norm_of_angle_eq_zero h

/-- If A ≠ B and C ≠ B then ∠ABC = 0 if and only if (dist A C) = abs ((dist A B) - (dist B C)). -/
theorem dist_eq_abs_sub_dist_iff_angle_eq_zero {p1 p2 p3 : P} (hp1p2 : p1 ≠ p2) (hp3p2 : p3 ≠ p2) :
    dist p1 p3 = abs (dist p1 p2 - dist p3 p2) ↔ ∠ p1 p2 p3 = 0 := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right]
  exact
    norm_sub_eq_abs_sub_norm_iff_angle_eq_zero (fun he => hp1p2 (vsub_eq_zero_iff_eq.1 he)) fun he =>
      hp3p2 (vsub_eq_zero_iff_eq.1 he)

/-- The midpoint of the segment AB is the same distance from A as it is from B. -/
theorem dist_left_midpoint_eq_dist_right_midpoint (p1 p2 : P) :
    dist p1 (midpoint ℝ p1 p2) = dist p2 (midpoint ℝ p1 p2) := by
  rw [dist_left_midpoint p1 p2, dist_right_midpoint p1 p2]

/-- If M is the midpoint of the segment AB, then ∠AMB = π. -/
theorem angle_midpoint_eq_pi (p1 p2 : P) (hp1p2 : p1 ≠ p2) : ∠ p1 (midpoint ℝ p1 p2) p2 = π := by
  have : p2 -ᵥ midpoint ℝ p1 p2 = -(p1 -ᵥ midpoint ℝ p1 p2) := by
    rw [neg_vsub_eq_vsub_rev]
    simp
  simp [angle, this, hp1p2, -zero_lt_one]

/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMA = π / 2. -/
theorem angle_left_midpoint_eq_pi_div_two_of_dist_eq {p1 p2 p3 : P} (h : dist p3 p1 = dist p3 p2) :
    ∠ p3 (midpoint ℝ p1 p2) p1 = π / 2 := by
  let m : P := midpoint ℝ p1 p2
  have h1 : p3 -ᵥ p1 = p3 -ᵥ m - (p1 -ᵥ m) := (vsub_sub_vsub_cancel_right p3 p1 m).symm
  have h2 : p3 -ᵥ p2 = p3 -ᵥ m + (p1 -ᵥ m) := by
    rw [left_vsub_midpoint, ← midpoint_vsub_right, vsub_add_vsub_cancel]
  rw [dist_eq_norm_vsub V p3 p1, dist_eq_norm_vsub V p3 p2, h1, h2] at h
  exact (norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (p3 -ᵥ m) (p1 -ᵥ m)).mp h.symm

/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMB = π / 2. -/
theorem angle_right_midpoint_eq_pi_div_two_of_dist_eq {p1 p2 p3 : P} (h : dist p3 p1 = dist p3 p2) :
    ∠ p3 (midpoint ℝ p1 p2) p2 = π / 2 := by
  rw [midpoint_comm p1 p2, angle_left_midpoint_eq_pi_div_two_of_dist_eq h.symm]

/-- The inner product of two vectors given with `weighted_vsub`, in
terms of the pairwise distances. -/
theorem inner_weighted_vsub {ι₁ : Type _} {s₁ : Finset ι₁} {w₁ : ι₁ → ℝ} (p₁ : ι₁ → P) (h₁ : (∑ i in s₁, w₁ i) = 0)
    {ι₂ : Type _} {s₂ : Finset ι₂} {w₂ : ι₂ → ℝ} (p₂ : ι₂ → P) (h₂ : (∑ i in s₂, w₂ i) = 0) :
    inner (s₁.weightedVsub p₁ w₁) (s₂.weightedVsub p₂ w₂) =
      (-∑ i₁ in s₁, ∑ i₂ in s₂, w₁ i₁ * w₂ i₂ * (dist (p₁ i₁) (p₂ i₂) * dist (p₁ i₁) (p₂ i₂))) / 2 :=
  by
  rw [Finset.weighted_vsub_apply, Finset.weighted_vsub_apply, inner_sum_smul_sum_smul_of_sum_eq_zero _ h₁ _ h₂]
  simp_rw [vsub_sub_vsub_cancel_right]
  rcongr i₁ i₂ <;> rw [dist_eq_norm_vsub V (p₁ i₁) (p₂ i₂)]

/-- The distance between two points given with `affine_combination`,
in terms of the pairwise distances between the points in that
combination. -/
theorem dist_affine_combination {ι : Type _} {s : Finset ι} {w₁ w₂ : ι → ℝ} (p : ι → P) (h₁ : (∑ i in s, w₁ i) = 1)
    (h₂ : (∑ i in s, w₂ i) = 1) :
    dist (s.affineCombination p w₁) (s.affineCombination p w₂) *
        dist (s.affineCombination p w₁) (s.affineCombination p w₂) =
      (-∑ i₁ in s, ∑ i₂ in s, (w₁ - w₂) i₁ * (w₁ - w₂) i₂ * (dist (p i₁) (p i₂) * dist (p i₁) (p i₂))) / 2 :=
  by
  rw [dist_eq_norm_vsub V (s.affine_combination p w₁) (s.affine_combination p w₂), ← inner_self_eq_norm_mul_norm,
    Finset.affine_combination_vsub]
  have h : (∑ i in s, (w₁ - w₂) i) = 0 := by
    simp_rw [Pi.sub_apply, Finset.sum_sub_distrib, h₁, h₂, sub_self]
  exact inner_weighted_vsub p h p h

/-- Suppose that `c₁` is equidistant from `p₁` and `p₂`, and the same
applies to `c₂`.  Then the vector between `c₁` and `c₂` is orthogonal
to that between `p₁` and `p₂`.  (In two dimensions, this says that the
diagonals of a kite are orthogonal.) -/
theorem inner_vsub_vsub_of_dist_eq_of_dist_eq {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁)
    (hc₂ : dist p₁ c₂ = dist p₂ c₂) : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 := by
  have h : ⟪c₂ -ᵥ c₁ + (c₂ -ᵥ c₁), p₂ -ᵥ p₁⟫ = 0 := by
    conv_lhs => congr congr rw [← vsub_sub_vsub_cancel_right c₂ c₁ p₁]skip rw [← vsub_sub_vsub_cancel_right c₂ c₁ p₂]
    rw [← add_sub_comm, inner_sub_left]
    conv_lhs => congr rw [← vsub_sub_vsub_cancel_right p₂ p₁ c₂]skip rw [← vsub_sub_vsub_cancel_right p₂ p₁ c₁]
    rw [dist_comm p₁, dist_comm p₂, dist_eq_norm_vsub V _ p₁, dist_eq_norm_vsub V _ p₂, ←
      real_inner_add_sub_eq_zero_iff] at hc₁ hc₂
    simp_rw [← neg_vsub_eq_vsub_rev c₁, ← neg_vsub_eq_vsub_rev c₂, sub_neg_eq_add, neg_add_eq_sub, hc₁, hc₂, sub_zero]
  simpa [inner_add_left, ← mul_two,
    (by
      norm_num : (2 : ℝ) ≠ 0)] using
    h

/-- The squared distance between points on a line (expressed as a
multiple of a fixed vector added to a point) and another point,
expressed as a quadratic. -/
theorem dist_smul_vadd_sq (r : ℝ) (v : V) (p₁ p₂ : P) :
    dist (r • v +ᵥ p₁) p₂ * dist (r • v +ᵥ p₁) p₂ = ⟪v, v⟫ * r * r + 2 * ⟪v, p₁ -ᵥ p₂⟫ * r + ⟪p₁ -ᵥ p₂, p₁ -ᵥ p₂⟫ := by
  rw [dist_eq_norm_vsub V _ p₂, ← real_inner_self_eq_norm_mul_norm, vadd_vsub_assoc, real_inner_add_add_self,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The condition for two points on a line to be equidistant from
another point. -/
theorem dist_smul_vadd_eq_dist {v : V} (p₁ p₂ : P) (hv : v ≠ 0) (r : ℝ) :
    dist (r • v +ᵥ p₁) p₂ = dist p₁ p₂ ↔ r = 0 ∨ r = -2 * ⟪v, p₁ -ᵥ p₂⟫ / ⟪v, v⟫ := by
  conv_lhs =>
    rw [← mul_self_inj_of_nonneg dist_nonneg dist_nonneg, dist_smul_vadd_sq, ← sub_eq_zero, add_sub_assoc,
      dist_eq_norm_vsub V p₁ p₂, ← real_inner_self_eq_norm_mul_norm, sub_self]
  have hvi : ⟪v, v⟫ ≠ 0 := by
    simpa using hv
  have hd : discrim ⟪v, v⟫ (2 * ⟪v, p₁ -ᵥ p₂⟫) 0 = 2 * inner v (p₁ -ᵥ p₂) * (2 * inner v (p₁ -ᵥ p₂)) := by
    rw [discrim]
    ring
  rw [quadratic_eq_zero_iff hvi hd, add_left_negₓ, zero_div, neg_mul_eq_neg_mulₓ, ← mul_sub_right_distrib,
    sub_eq_add_neg, ← mul_two, mul_assoc, mul_div_assoc, mul_div_mul_left, mul_div_assoc]
  norm_num

open AffineSubspace FiniteDimensional

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
/-- Distances `r₁` `r₂` of `p` from two different points `c₁` `c₂` determine at
most two points `p₁` `p₂` in a two-dimensional subspace containing those points
(two circles intersect in at most two points). -/
theorem eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two {s : AffineSubspace ℝ P} [FiniteDimensional ℝ s.direction]
    (hd : finrank ℝ s.direction = 2) {c₁ c₂ p₁ p₂ p : P} (hc₁s : c₁ ∈ s) (hc₂s : c₂ ∈ s) (hp₁s : p₁ ∈ s) (hp₂s : p₂ ∈ s)
    (hps : p ∈ s) {r₁ r₂ : ℝ} (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁) (hp₂c₁ : dist p₂ c₁ = r₁)
    (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂) (hp₂c₂ : dist p₂ c₂ = r₂) (hpc₂ : dist p c₂ = r₂) :
    p = p₁ ∨ p = p₂ := by
  have ho : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hp₂c₁.symm) (hp₁c₂.trans hp₂c₂.symm)
  have hop : ⟪c₂ -ᵥ c₁, p -ᵥ p₁⟫ = 0 :=
    inner_vsub_vsub_of_dist_eq_of_dist_eq (hp₁c₁.trans hpc₁.symm) (hp₁c₂.trans hpc₂.symm)
  let b : Finₓ 2 → V := ![c₂ -ᵥ c₁, p₂ -ᵥ p₁]
  have hb : LinearIndependent ℝ b := by
    refine' linear_independent_of_ne_zero_of_inner_eq_zero _ _
    · intro i
      fin_cases i <;> simp [b, hc.symm, hp.symm]
      
    · intro i j hij
      fin_cases i <;>
        fin_cases j <;>
          try
            exact False.elim (hij rfl)
      · exact ho
        
      · rw [real_inner_comm]
        exact ho
        
      
  have hbs : Submodule.span ℝ (Set.Range b) = s.direction := by
    refine' eq_of_le_of_finrank_eq _ _
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · exact vsub_mem_direction hc₂s hc₁s
        
      · exact vsub_mem_direction hp₂s hp₁s
        
      
    · rw [finrank_span_eq_card hb, Fintype.card_fin, hd]
      
  have hv : ∀, ∀ v ∈ s.direction, ∀, ∃ t₁ t₂ : ℝ, v = t₁ • (c₂ -ᵥ c₁) + t₂ • (p₂ -ᵥ p₁) := by
    intro v hv
    have hr : Set.Range b = {c₂ -ᵥ c₁, p₂ -ᵥ p₁} := by
      have hu : (Finset.univ : Finset (Finₓ 2)) = {0, 1} := by
        decide
      rw [← Fintype.coe_image_univ, hu]
      simp
      rfl
    rw [← hbs, hr, Submodule.mem_span_insert] at hv
    rcases hv with ⟨t₁, v', hv', hv⟩
    rw [Submodule.mem_span_singleton] at hv'
    rcases hv' with ⟨t₂, rfl⟩
    exact ⟨t₁, t₂, hv⟩
  rcases hv (p -ᵥ p₁) (vsub_mem_direction hps hp₁s) with ⟨t₁, t₂, hpt⟩
  simp only [hpt, inner_add_right, inner_smul_right, ho, mul_zero, add_zeroₓ, mul_eq_zero, inner_self_eq_zero,
    vsub_eq_zero_iff_eq, hc.symm, or_falseₓ] at hop
  rw [hop, zero_smul, zero_addₓ, ← eq_vadd_iff_vsub_eq] at hpt
  subst hpt
  have hp' : (p₂ -ᵥ p₁ : V) ≠ 0 := by
    simp [hp.symm]
  have hp₂ : dist ((1 : ℝ) • (p₂ -ᵥ p₁) +ᵥ p₁) c₁ = r₁ := by
    simp [hp₂c₁]
  rw [← hp₁c₁, dist_smul_vadd_eq_dist _ _ hp'] at hpc₁ hp₂
  simp only [one_ne_zero, false_orₓ] at hp₂
  rw [hp₂.symm] at hpc₁
  cases hpc₁ <;> simp [hpc₁]

/-- Distances `r₁` `r₂` of `p` from two different points `c₁` `c₂` determine at
most two points `p₁` `p₂` in two-dimensional space (two circles intersect in at
most two points). -/
theorem eq_of_dist_eq_of_dist_eq_of_finrank_eq_two [FiniteDimensional ℝ V] (hd : finrank ℝ V = 2) {c₁ c₂ p₁ p₂ p : P}
    {r₁ r₂ : ℝ} (hc : c₁ ≠ c₂) (hp : p₁ ≠ p₂) (hp₁c₁ : dist p₁ c₁ = r₁) (hp₂c₁ : dist p₂ c₁ = r₁)
    (hpc₁ : dist p c₁ = r₁) (hp₁c₂ : dist p₁ c₂ = r₂) (hp₂c₂ : dist p₂ c₂ = r₂) (hpc₂ : dist p c₂ = r₂) :
    p = p₁ ∨ p = p₂ :=
  have hd' : finrank ℝ (⊤ : AffineSubspace ℝ P).direction = 2 := by
    rw [direction_top, finrank_top]
    exact hd
  eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd' (mem_top ℝ V _) (mem_top ℝ V _) (mem_top ℝ V _) (mem_top ℝ V _)
    (mem_top ℝ V _) hc hp hp₁c₁ hp₂c₁ hpc₁ hp₁c₂ hp₂c₂ hpc₂

variable {V}

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete, as an unbundled function.  This
definition is only intended for use in setting up the bundled version
`orthogonal_projection` and should not be used once that is
defined. -/
def orthogonalProjectionFn (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] (p : P) : P :=
  Classical.some <|
    inter_eq_singleton_of_nonempty_of_is_compl (nonempty_subtype.mp ‹_›) (mk'_nonempty p s.directionᗮ)
      (by
        rw [direction_mk' p s.directionᗮ]
        exact Submodule.is_compl_orthogonal_of_complete_space)

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonal_projection_fn` of that
point onto the subspace.  This lemma is only intended for use in
setting up the bundled version and should not be used once that is
defined. -/
theorem inter_eq_singleton_orthogonal_projection_fn {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
    (p : P) : (s : Set P) ∩ mk' p s.directionᗮ = {orthogonalProjectionFn s p} :=
  Classical.some_spec <|
    inter_eq_singleton_of_nonempty_of_is_compl (nonempty_subtype.mp ‹_›) (mk'_nonempty p s.directionᗮ)
      (by
        rw [direction_mk' p s.directionᗮ]
        exact Submodule.is_compl_orthogonal_of_complete_space)

/-- The `orthogonal_projection_fn` lies in the given subspace.  This
lemma is only intended for use in setting up the bundled version and
should not be used once that is defined. -/
theorem orthogonal_projection_fn_mem {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction] (p : P) :
    orthogonalProjectionFn s p ∈ s := by
  rw [← mem_coe, ← Set.singleton_subset_iff, ← inter_eq_singleton_orthogonal_projection_fn]
  exact Set.inter_subset_left _ _

/-- The `orthogonal_projection_fn` lies in the orthogonal
subspace.  This lemma is only intended for use in setting up the
bundled version and should not be used once that is defined. -/
theorem orthogonal_projection_fn_mem_orthogonal {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
    (p : P) : orthogonalProjectionFn s p ∈ mk' p s.directionᗮ := by
  rw [← mem_coe, ← Set.singleton_subset_iff, ← inter_eq_singleton_orthogonal_projection_fn]
  exact Set.inter_subset_right _ _

/-- Subtracting `p` from its `orthogonal_projection_fn` produces a
result in the orthogonal direction.  This lemma is only intended for
use in setting up the bundled version and should not be used once that
is defined. -/
theorem orthogonal_projection_fn_vsub_mem_direction_orthogonal {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] (p : P) : orthogonalProjectionFn s p -ᵥ p ∈ s.directionᗮ :=
  direction_mk' p s.directionᗮ ▸ vsub_mem_direction (orthogonal_projection_fn_mem_orthogonal p) (self_mem_mk' _ _)

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete. The corresponding linear map
(mapping a vector to the difference between the projections of two
points whose difference is that vector) is the `orthogonal_projection`
for real inner product spaces, onto the direction of the affine
subspace being projected onto. -/
def orthogonalProjection (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] : P →ᵃ[ℝ] s where
  toFun := fun p => ⟨orthogonalProjectionFn s p, orthogonal_projection_fn_mem p⟩
  linear := orthogonalProjection s.direction
  map_vadd' := fun p v => by
    have hs : ((orthogonalProjection s.direction) v : V) +ᵥ orthogonalProjectionFn s p ∈ s :=
      vadd_mem_of_mem_direction (orthogonalProjection s.direction v).2 (orthogonal_projection_fn_mem p)
    have ho : ((orthogonalProjection s.direction) v : V) +ᵥ orthogonalProjectionFn s p ∈ mk' (v +ᵥ p) s.directionᗮ := by
      rw [← vsub_right_mem_direction_iff_mem (self_mem_mk' _ _) _, direction_mk', vsub_vadd_eq_vsub_sub,
        vadd_vsub_assoc, add_commₓ, add_sub_assoc]
      refine' Submodule.add_mem _ (orthogonal_projection_fn_vsub_mem_direction_orthogonal p) _
      rw [Submodule.mem_orthogonal']
      intro w hw
      rw [← neg_sub, inner_neg_left, orthogonal_projection_inner_eq_zero _ w hw, neg_zero]
    have hm :
      ((orthogonalProjection s.direction) v : V) +ᵥ orthogonalProjectionFn s p ∈
        ({orthogonalProjectionFn s (v +ᵥ p)} : Set P) :=
      by
      rw [← inter_eq_singleton_orthogonal_projection_fn (v +ᵥ p)]
      exact Set.mem_inter hs ho
    rw [Set.mem_singleton_iff] at hm
    ext
    exact hm.symm

@[simp]
theorem orthogonal_projection_fn_eq {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction] (p : P) :
    orthogonalProjectionFn s p = orthogonalProjection s p :=
  rfl

/-- The linear map corresponding to `orthogonal_projection`. -/
@[simp]
theorem orthogonal_projection_linear {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction] :
    (orthogonalProjection s).linear = orthogonalProjection s.direction :=
  rfl

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonal_projection` of that point
onto the subspace. -/
theorem inter_eq_singleton_orthogonal_projection {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
    (p : P) : (s : Set P) ∩ mk' p s.directionᗮ = {orthogonalProjection s p} := by
  rw [← orthogonal_projection_fn_eq]
  exact inter_eq_singleton_orthogonal_projection_fn p

/-- The `orthogonal_projection` lies in the given subspace. -/
theorem orthogonal_projection_mem {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction] (p : P) :
    ↑(orthogonalProjection s p) ∈ s :=
  (orthogonalProjection s p).2

/-- The `orthogonal_projection` lies in the orthogonal subspace. -/
theorem orthogonal_projection_mem_orthogonal (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] (p : P) :
    ↑(orthogonalProjection s p) ∈ mk' p s.directionᗮ :=
  orthogonal_projection_fn_mem_orthogonal p

/-- Subtracting a point in the given subspace from the
`orthogonal_projection` produces a result in the direction of the
given subspace. -/
theorem orthogonal_projection_vsub_mem_direction {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
    {p1 : P} (p2 : P) (hp1 : p1 ∈ s) : ↑(orthogonalProjection s p2 -ᵥ ⟨p1, hp1⟩ : s.direction) ∈ s.direction :=
  (orthogonalProjection s p2 -ᵥ ⟨p1, hp1⟩ : s.direction).2

/-- Subtracting the `orthogonal_projection` from a point in the given
subspace produces a result in the direction of the given subspace. -/
theorem vsub_orthogonal_projection_mem_direction {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
    {p1 : P} (p2 : P) (hp1 : p1 ∈ s) : ↑((⟨p1, hp1⟩ : s) -ᵥ orthogonalProjection s p2 : s.direction) ∈ s.direction :=
  ((⟨p1, hp1⟩ : s) -ᵥ orthogonalProjection s p2 : s.direction).2

/-- A point equals its orthogonal projection if and only if it lies in
the subspace. -/
theorem orthogonal_projection_eq_self_iff {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction] {p : P} :
    ↑(orthogonalProjection s p) = p ↔ p ∈ s := by
  constructor
  · exact fun h => h ▸ orthogonal_projection_mem p
    
  · intro h
    have hp : p ∈ (s : Set P) ∩ mk' p s.directionᗮ := ⟨h, self_mem_mk' p _⟩
    rw [inter_eq_singleton_orthogonal_projection p] at hp
    symm
    exact hp
    

@[simp]
theorem orthogonal_projection_mem_subspace_eq_self {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
    (p : s) : orthogonalProjection s p = p := by
  ext
  rw [orthogonal_projection_eq_self_iff]
  exact p.2

/-- Orthogonal projection is idempotent. -/
@[simp]
theorem orthogonal_projection_orthogonal_projection (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction]
    (p : P) : orthogonalProjection s (orthogonalProjection s p) = orthogonalProjection s p := by
  ext
  rw [orthogonal_projection_eq_self_iff]
  exact orthogonal_projection_mem p

theorem eq_orthogonal_projection_of_eq_subspace {s s' : AffineSubspace ℝ P} [Nonempty s] [Nonempty s']
    [CompleteSpace s.direction] [CompleteSpace s'.direction] (h : s = s') (p : P) :
    (orthogonalProjection s p : P) = (orthogonalProjection s' p : P) := by
  change orthogonalProjectionFn s p = orthogonalProjectionFn s' p
  congr
  exact h

/-- The distance to a point's orthogonal projection is 0 iff it lies in the subspace. -/
theorem dist_orthogonal_projection_eq_zero_iff {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
    {p : P} : dist p (orthogonalProjection s p) = 0 ↔ p ∈ s := by
  rw [dist_comm, dist_eq_zero, orthogonal_projection_eq_self_iff]

/-- The distance between a point and its orthogonal projection is
nonzero if it does not lie in the subspace. -/
theorem dist_orthogonal_projection_ne_zero_of_not_mem {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
    {p : P} (hp : p ∉ s) : dist p (orthogonalProjection s p) ≠ 0 :=
  mt dist_orthogonal_projection_eq_zero_iff.mp hp

/-- Subtracting `p` from its `orthogonal_projection` produces a result
in the orthogonal direction. -/
theorem orthogonal_projection_vsub_mem_direction_orthogonal (s : AffineSubspace ℝ P) [Nonempty s]
    [CompleteSpace s.direction] (p : P) : (orthogonalProjection s p : P) -ᵥ p ∈ s.directionᗮ :=
  orthogonal_projection_fn_vsub_mem_direction_orthogonal p

/-- Subtracting the `orthogonal_projection` from `p` produces a result
in the orthogonal direction. -/
theorem vsub_orthogonal_projection_mem_direction_orthogonal (s : AffineSubspace ℝ P) [Nonempty s]
    [CompleteSpace s.direction] (p : P) : p -ᵥ orthogonalProjection s p ∈ s.directionᗮ :=
  direction_mk' p s.directionᗮ ▸ vsub_mem_direction (self_mem_mk' _ _) (orthogonal_projection_mem_orthogonal s p)

/-- Subtracting the `orthogonal_projection` from `p` produces a result in the kernel of the linear
part of the orthogonal projection. -/
theorem orthogonal_projection_vsub_orthogonal_projection (s : AffineSubspace ℝ P) [Nonempty s]
    [CompleteSpace s.direction] (p : P) : orthogonalProjection s.direction (p -ᵥ orthogonalProjection s p) = 0 := by
  apply orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero
  intro c hc
  rw [← neg_vsub_eq_vsub_rev, inner_neg_right, orthogonal_projection_vsub_mem_direction_orthogonal s p c hc, neg_zero]

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector was
in the orthogonal direction. -/
theorem orthogonal_projection_vadd_eq_self {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction] {p : P}
    (hp : p ∈ s) {v : V} (hv : v ∈ s.directionᗮ) : orthogonalProjection s (v +ᵥ p) = ⟨p, hp⟩ := by
  have h := vsub_orthogonal_projection_mem_direction_orthogonal s (v +ᵥ p)
  rw [vadd_vsub_assoc, Submodule.add_mem_iff_right _ hv] at h
  refine' (eq_of_vsub_eq_zero _).symm
  ext
  refine' Submodule.disjoint_def.1 s.direction.orthogonal_disjoint _ _ h
  exact (_ : s.direction).2

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
theorem orthogonal_projection_vadd_smul_vsub_orthogonal_projection {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] {p1 : P} (p2 : P) (r : ℝ) (hp : p1 ∈ s) :
    orthogonalProjection s (r • (p2 -ᵥ orthogonalProjection s p2 : V) +ᵥ p1) = ⟨p1, hp⟩ :=
  orthogonal_projection_vadd_eq_self hp
    (Submodule.smul_mem _ _ (vsub_orthogonal_projection_mem_direction_orthogonal s _))

/-- The square of the distance from a point in `s` to `p2` equals the
sum of the squares of the distances of the two points to the
`orthogonal_projection`. -/
theorem dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] {p1 : P} (p2 : P) (hp1 : p1 ∈ s) :
    dist p1 p2 * dist p1 p2 =
      dist p1 (orthogonalProjection s p2) * dist p1 (orthogonalProjection s p2) +
        dist p2 (orthogonalProjection s p2) * dist p2 (orthogonalProjection s p2) :=
  by
  rw [PseudoMetricSpace.dist_comm p2 _, dist_eq_norm_vsub V p1 _, dist_eq_norm_vsub V p1 _, dist_eq_norm_vsub V _ p2, ←
    vsub_add_vsub_cancel p1 (orthogonalProjection s p2) p2, norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact
    Submodule.inner_right_of_mem_orthogonal (vsub_orthogonal_projection_mem_direction p2 hp1)
      (orthogonal_projection_vsub_mem_direction_orthogonal s p2)

/-- The square of the distance between two points constructed by
adding multiples of the same orthogonal vector to points in the same
subspace. -/
theorem dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd {s : AffineSubspace ℝ P} {p1 p2 : P} (hp1 : p1 ∈ s)
    (hp2 : p2 ∈ s) (r1 r2 : ℝ) {v : V} (hv : v ∈ s.directionᗮ) :
    dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) * dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) =
      dist p1 p2 * dist p1 p2 + (r1 - r2) * (r1 - r2) * (∥v∥ * ∥v∥) :=
  calc
    dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) * dist (r1 • v +ᵥ p1) (r2 • v +ᵥ p2) =
        ∥p1 -ᵥ p2 + (r1 - r2) • v∥ * ∥p1 -ᵥ p2 + (r1 - r2) • v∥ :=
      by
      rw [dist_eq_norm_vsub V (r1 • v +ᵥ p1), vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, sub_smul, add_commₓ,
        add_sub_assoc]
    _ = ∥p1 -ᵥ p2∥ * ∥p1 -ᵥ p2∥ + ∥(r1 - r2) • v∥ * ∥(r1 - r2) • v∥ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_real
        (Submodule.inner_right_of_mem_orthogonal (vsub_mem_direction hp1 hp2) (Submodule.smul_mem _ _ hv))
    _ = ∥(p1 -ᵥ p2 : V)∥ * ∥(p1 -ᵥ p2 : V)∥ + abs (r1 - r2) * abs (r1 - r2) * ∥v∥ * ∥v∥ := by
      rw [norm_smul, Real.norm_eq_abs]
      ring
    _ = dist p1 p2 * dist p1 p2 + (r1 - r2) * (r1 - r2) * (∥v∥ * ∥v∥) := by
      rw [dist_eq_norm_vsub V p1, abs_mul_abs_self, mul_assoc]
    

/-- Reflection in an affine subspace, which is expected to be nonempty
and complete.  The word "reflection" is sometimes understood to mean
specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point.  The
definition here, of reflection in an affine subspace, is a more
general sense of the word that includes both those common cases. -/
def reflection (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] : P ≃ᵃⁱ[ℝ] P :=
  AffineIsometryEquiv.mk' (fun p => ↑(orthogonalProjection s p) -ᵥ p +ᵥ orthogonalProjection s p)
    (reflection s.direction) (↑(Classical.arbitrary s))
    (by
      intro p
      let v := p -ᵥ ↑(Classical.arbitrary s)
      let a : V := _root_.orthogonal_projection s.direction v
      let b : P := ↑(Classical.arbitrary s)
      have key : a +ᵥ b -ᵥ (v +ᵥ b) +ᵥ (a +ᵥ b) = a + a - v +ᵥ (b -ᵥ b +ᵥ b) := by
        rw [← add_vadd, vsub_vadd_eq_vsub_sub, vsub_vadd, vadd_vsub]
        congr 1
        abel
      have : p = v +ᵥ ↑(Classical.arbitrary s) := (vsub_vadd p ↑(Classical.arbitrary s)).symm
      simpa only [coe_vadd, reflection_apply, AffineMap.map_vadd, orthogonal_projection_linear,
        orthogonal_projection_mem_subspace_eq_self, vadd_vsub, ContinuousLinearMap.coe_coe,
        ContinuousLinearEquiv.coe_coe, this] using key)

/-- The result of reflecting. -/
theorem reflection_apply (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] (p : P) :
    reflection s p = ↑(orthogonalProjection s p) -ᵥ p +ᵥ orthogonalProjection s p :=
  rfl

theorem eq_reflection_of_eq_subspace {s s' : AffineSubspace ℝ P} [Nonempty s] [Nonempty s'] [CompleteSpace s.direction]
    [CompleteSpace s'.direction] (h : s = s') (p : P) : (reflection s p : P) = (reflection s' p : P) := by
  subst h

/-- Reflecting twice in the same subspace. -/
@[simp]
theorem reflection_reflection (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] (p : P) :
    reflection s (reflection s p) = p := by
  have :
    ∀ a : s,
      ∀ b : V, (_root_.orthogonal_projection s.direction) b = 0 → reflection s (reflection s (b +ᵥ a)) = b +ᵥ a :=
    by
    intro a b h
    have : (a : P) -ᵥ (b +ᵥ a) = -b := by
      rw [vsub_vadd_eq_vsub_sub, vsub_self, zero_sub]
    simp [reflection, h, this]
  rw [← vsub_vadd p (orthogonalProjection s p)]
  exact this (orthogonalProjection s p) _ (orthogonal_projection_vsub_orthogonal_projection s p)

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_symm (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] :
    (reflection s).symm = reflection s := by
  ext
  rw [← (reflection s).Injective.eq_iff]
  simp

/-- Reflection is involutive. -/
theorem reflection_involutive (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] :
    Function.Involutive (reflection s) :=
  reflection_reflection s

/-- A point is its own reflection if and only if it is in the
subspace. -/
theorem reflection_eq_self_iff {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction] (p : P) :
    reflection s p = p ↔ p ∈ s := by
  rw [← orthogonal_projection_eq_self_iff, reflection_apply]
  constructor
  · intro h
    rw [← @vsub_eq_zero_iff_eq V, vadd_vsub_assoc, ← two_smul ℝ (↑(orthogonalProjection s p) -ᵥ p), smul_eq_zero] at h
    norm_num  at h
    exact h
    
  · intro h
    simp [h]
    

/-- Reflecting a point in two subspaces produces the same result if
and only if the point has the same orthogonal projection in each of
those subspaces. -/
theorem reflection_eq_iff_orthogonal_projection_eq (s₁ s₂ : AffineSubspace ℝ P) [Nonempty s₁] [Nonempty s₂]
    [CompleteSpace s₁.direction] [CompleteSpace s₂.direction] (p : P) :
    reflection s₁ p = reflection s₂ p ↔ (orthogonalProjection s₁ p : P) = orthogonalProjection s₂ p := by
  rw [reflection_apply, reflection_apply]
  constructor
  · intro h
    rw [← @vsub_eq_zero_iff_eq V, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_commₓ, add_sub_assoc,
      vsub_sub_vsub_cancel_right, ← two_smul ℝ ((orthogonalProjection s₁ p : P) -ᵥ orthogonalProjection s₂ p),
      smul_eq_zero] at h
    norm_num  at h
    exact h
    
  · intro h
    rw [h]
    

/-- The distance between `p₁` and the reflection of `p₂` equals that
between the reflection of `p₁` and `p₂`. -/
theorem dist_reflection (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] (p₁ p₂ : P) :
    dist p₁ (reflection s p₂) = dist (reflection s p₁) p₂ := by
  conv_lhs => rw [← reflection_reflection s p₁]
  exact (reflection s).dist_map _ _

/-- A point in the subspace is equidistant from another point and its
reflection. -/
theorem dist_reflection_eq_of_mem (s : AffineSubspace ℝ P) [Nonempty s] [CompleteSpace s.direction] {p₁ : P}
    (hp₁ : p₁ ∈ s) (p₂ : P) : dist p₁ (reflection s p₂) = dist p₁ p₂ := by
  rw [← reflection_eq_self_iff p₁] at hp₁
  convert (reflection s).dist_map p₁ p₂
  rw [hp₁]

/-- The reflection of a point in a subspace is contained in any larger
subspace containing both the point and the subspace reflected in. -/
theorem reflection_mem_of_le_of_mem {s₁ s₂ : AffineSubspace ℝ P} [Nonempty s₁] [CompleteSpace s₁.direction]
    (hle : s₁ ≤ s₂) {p : P} (hp : p ∈ s₂) : reflection s₁ p ∈ s₂ := by
  rw [reflection_apply]
  have ho : ↑(orthogonalProjection s₁ p) ∈ s₂ := hle (orthogonal_projection_mem p)
  exact vadd_mem_of_mem_direction (vsub_mem_direction ho hp) ho

/-- Reflecting an orthogonal vector plus a point in the subspace
produces the negation of that vector plus the point. -/
theorem reflection_orthogonal_vadd {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction] {p : P}
    (hp : p ∈ s) {v : V} (hv : v ∈ s.directionᗮ) : reflection s (v +ᵥ p) = -v +ᵥ p := by
  rw [reflection_apply, orthogonal_projection_vadd_eq_self hp hv, vsub_vadd_eq_vsub_sub]
  simp

/-- Reflecting a vector plus a point in the subspace produces the
negation of that vector plus the point if the vector is a multiple of
the result of subtracting a point's orthogonal projection from that
point. -/
theorem reflection_vadd_smul_vsub_orthogonal_projection {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] {p₁ : P} (p₂ : P) (r : ℝ) (hp₁ : p₁ ∈ s) :
    reflection s (r • (p₂ -ᵥ orthogonalProjection s p₂) +ᵥ p₁) = -(r • (p₂ -ᵥ orthogonalProjection s p₂)) +ᵥ p₁ :=
  reflection_orthogonal_vadd hp₁ (Submodule.smul_mem _ _ (vsub_orthogonal_projection_mem_direction_orthogonal s _))

omit V

/-- A set of points is cospherical if they are equidistant from some
point.  In two dimensions, this is the same thing as being
concyclic. -/
def Cospherical (ps : Set P) : Prop :=
  ∃ (center : P)(radius : ℝ), ∀, ∀ p ∈ ps, ∀, dist p center = radius

/-- The definition of `cospherical`. -/
theorem cospherical_def (ps : Set P) :
    Cospherical ps ↔ ∃ (center : P)(radius : ℝ), ∀, ∀ p ∈ ps, ∀, dist p center = radius :=
  Iff.rfl

/-- A subset of a cospherical set is cospherical. -/
theorem cospherical_subset {ps₁ ps₂ : Set P} (hs : ps₁ ⊆ ps₂) (hc : Cospherical ps₂) : Cospherical ps₁ := by
  rcases hc with ⟨c, r, hcr⟩
  exact ⟨c, r, fun p hp => hcr p (hs hp)⟩

include V

/-- The empty set is cospherical. -/
theorem cospherical_empty : Cospherical (∅ : Set P) := by
  use add_torsor.nonempty.some
  simp

omit V

/-- A single point is cospherical. -/
theorem cospherical_singleton (p : P) : Cospherical ({p} : Set P) := by
  use p
  simp

include V

/-- Two points are cospherical. -/
theorem cospherical_insert_singleton (p₁ p₂ : P) : Cospherical ({p₁, p₂} : Set P) := by
  use (2⁻¹ : ℝ) • (p₂ -ᵥ p₁) +ᵥ p₁, (2⁻¹ : ℝ) * dist p₂ p₁
  intro p
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro ⟨_ | _⟩
  · rw [dist_eq_norm_vsub V p₁, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, norm_neg, norm_smul, dist_eq_norm_vsub V p₂]
    simp
    
  · rw [H, dist_eq_norm_vsub V p₂, vsub_vadd_eq_vsub_sub, dist_eq_norm_vsub V p₂]
    conv_lhs => congr congr rw [← one_smul ℝ (p₂ -ᵥ p₁ : V)]
    rw [← sub_smul, norm_smul]
    norm_num
    

/-- Any three points in a cospherical set are affinely independent. -/
theorem Cospherical.affine_independent {s : Set P} (hs : Cospherical s) {p : Finₓ 3 → P} (hps : Set.Range p ⊆ s)
    (hpi : Function.Injective p) : AffineIndependent ℝ p := by
  rw [affine_independent_iff_not_collinear]
  intro hc
  rw [collinear_iff_of_mem ℝ (Set.mem_range_self (0 : Finₓ 3))] at hc
  rcases hc with ⟨v, hv⟩
  rw [Set.forall_range_iff] at hv
  have hv0 : v ≠ 0 := by
    intro h
    have he : p 1 = p 0 := by
      simpa [h] using hv 1
    exact
      (by
          decide : (1 : Finₓ 3) ≠ 0)
        (hpi he)
  rcases hs with ⟨c, r, hs⟩
  have hs' := fun i => hs (p i) (Set.mem_of_mem_of_subset (Set.mem_range_self _) hps)
  choose f hf using hv
  have hsd : ∀ i, dist (f i • v +ᵥ p 0) c = r := by
    intro i
    rw [← hf]
    exact hs' i
  have hf0 : f 0 = 0 := by
    have hf0' := hf 0
    rw [eq_comm, ← @vsub_eq_zero_iff_eq V, vadd_vsub, smul_eq_zero] at hf0'
    simpa [hv0] using hf0'
  have hfi : Function.Injective f := by
    intro i j h
    have hi := hf i
    rw [h, ← hf j] at hi
    exact hpi hi
  simp_rw [← hsd 0, hf0, zero_smul, zero_vadd, dist_smul_vadd_eq_dist (p 0) c hv0]  at hsd
  have hfn0 : ∀ i, i ≠ 0 → f i ≠ 0 := fun i => (hfi.ne_iff' hf0).2
  have hfn0' : ∀ i, i ≠ 0 → f i = -2 * ⟪v, p 0 -ᵥ c⟫ / ⟪v, v⟫ := by
    intro i hi
    have hsdi := hsd i
    simpa [hfn0, hi] using hsdi
  have hf12 : f 1 = f 2 := by
    rw
      [hfn0' 1
        (by
          decide),
      hfn0' 2
        (by
          decide)]
  exact
    (by
        decide : (1 : Finₓ 3) ≠ 2)
      (hfi hf12)

end EuclideanGeometry

