/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.Geometry.Euclidean.Basic
import Mathbin.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathbin.Tactic.DeriveFintype

/-!
# Circumcenter and circumradius

This file proves some lemmas on points equidistant from a set of
points, and defines the circumradius and circumcenter of a simplex.
There are also some definitions for use in calculations where it is
convenient to work with affine combinations of vertices together with
the circumcenter.

## Main definitions

* `circumcenter` and `circumradius` are the circumcenter and
  circumradius of a simplex.

## References

* https://en.wikipedia.org/wiki/Circumscribed_circle

-/


noncomputable section

open BigOperators

open Classical

open Real

open RealInnerProductSpace

namespace EuclideanGeometry

open InnerProductGeometry

variable {V : Type _} {P : Type _} [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

include V

open AffineSubspace

/-- `p` is equidistant from two points in `s` if and only if its
`orthogonal_projection` is. -/
theorem dist_eq_iff_dist_orthogonal_projection_eq {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
    {p1 p2 : P} (p3 : P) (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) :
    dist p1 p3 = dist p2 p3 ↔ dist p1 (orthogonalProjection s p3) = dist p2 (orthogonalProjection s p3) := by
  rw [← mul_self_inj_of_nonneg dist_nonneg dist_nonneg, ← mul_self_inj_of_nonneg dist_nonneg dist_nonneg,
    dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq p3 hp1,
    dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq p3 hp2]
  simp

/-- `p` is equidistant from a set of points in `s` if and only if its
`orthogonal_projection` is. -/
theorem dist_set_eq_iff_dist_orthogonal_projection_eq {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
    {ps : Set P} (hps : ps ⊆ s) (p : P) :
    (Set.Pairwise ps fun p1 p2 => dist p1 p = dist p2 p) ↔
      Set.Pairwise ps fun p1 p2 => dist p1 (orthogonalProjection s p) = dist p2 (orthogonalProjection s p) :=
  ⟨fun h p1 hp1 p2 hp2 hne => (dist_eq_iff_dist_orthogonal_projection_eq p (hps hp1) (hps hp2)).1 (h hp1 hp2 hne),
    fun h p1 hp1 p2 hp2 hne => (dist_eq_iff_dist_orthogonal_projection_eq p (hps hp1) (hps hp2)).2 (h hp1 hp2 hne)⟩

/-- There exists `r` such that `p` has distance `r` from all the
points of a set of points in `s` if and only if there exists (possibly
different) `r` such that its `orthogonal_projection` has that distance
from all the points in that set. -/
theorem exists_dist_eq_iff_exists_dist_orthogonal_projection_eq {s : AffineSubspace ℝ P} [Nonempty s]
    [CompleteSpace s.direction] {ps : Set P} (hps : ps ⊆ s) (p : P) :
    (∃ r, ∀ p1 ∈ ps, dist p1 p = r) ↔ ∃ r, ∀ p1 ∈ ps, dist p1 ↑(orthogonalProjection s p) = r := by
  have h := dist_set_eq_iff_dist_orthogonal_projection_eq hps p
  simp_rw [Set.pairwise_eq_iff_exists_eq] at h
  exact h

/-- The induction step for the existence and uniqueness of the
circumcenter.  Given a nonempty set of points in a nonempty affine
subspace whose direction is complete, such that there is a unique
(circumcenter, circumradius) pair for those points in that subspace,
and a point `p` not in that subspace, there is a unique (circumcenter,
circumradius) pair for the set with `p` added, in the span of the
subspace with `p` added. -/
theorem exists_unique_dist_eq_of_insert {s : AffineSubspace ℝ P} [CompleteSpace s.direction] {ps : Set P}
    (hnps : ps.Nonempty) {p : P} (hps : ps ⊆ s) (hp : p ∉ s)
    (hu : ∃! cccr : P × ℝ, cccr.fst ∈ s ∧ ∀ p1 ∈ ps, dist p1 cccr.fst = cccr.snd) :
    ∃! cccr₂ : P × ℝ,
      cccr₂.fst ∈ affineSpan ℝ (insert p (s : Set P)) ∧ ∀ p1 ∈ insert p ps, dist p1 cccr₂.fst = cccr₂.snd :=
  by
  haveI : Nonempty s := Set.Nonempty.to_subtype (hnps.mono hps)
  rcases hu with ⟨⟨cc, cr⟩, ⟨hcc, hcr⟩, hcccru⟩
  simp only [Prod.fst, Prod.snd] at hcc hcr hcccru
  let x := dist cc (orthogonalProjection s p)
  let y := dist p (orthogonalProjection s p)
  have hy0 : y ≠ 0 := dist_orthogonal_projection_ne_zero_of_not_mem hp
  let ycc₂ := (x * x + y * y - cr * cr) / (2 * y)
  let cc₂ := (ycc₂ / y) • (p -ᵥ orthogonalProjection s p : V) +ᵥ cc
  let cr₂ := Real.sqrt (cr * cr + ycc₂ * ycc₂)
  use (cc₂, cr₂)
  simp only [Prod.fst, Prod.snd]
  have hpo : p = (1 : ℝ) • (p -ᵥ orthogonalProjection s p : V) +ᵥ orthogonalProjection s p := by
    simp
  constructor
  · constructor
    · refine' vadd_mem_of_mem_direction _ (mem_affine_span ℝ (Set.mem_insert_of_mem _ hcc))
      rw [direction_affine_span]
      exact
        Submodule.smul_mem _ _
          (vsub_mem_vector_span ℝ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (orthogonal_projection_mem _)))
      
    · intro p1 hp1
      rw [← mul_self_inj_of_nonneg dist_nonneg (Real.sqrt_nonneg _),
        Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))]
      cases hp1
      · rw [hp1]
        rw [hpo,
          dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd (orthogonal_projection_mem p) hcc _ _
            (vsub_orthogonal_projection_mem_direction_orthogonal s p),
          ← dist_eq_norm_vsub V p, dist_comm _ cc]
        field_simp [hy0]
        ring
        
      · rw [dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq _ (hps hp1),
          orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ hcc, Subtype.coe_mk, hcr _ hp1,
          dist_eq_norm_vsub V cc₂ cc, vadd_vsub, norm_smul, ← dist_eq_norm_vsub V, Real.norm_eq_abs, abs_div,
          abs_of_nonneg dist_nonneg, div_mul_cancel _ hy0, abs_mul_abs_self]
        
      
    
  · rintro ⟨cc₃, cr₃⟩ ⟨hcc₃, hcr₃⟩
    simp only [Prod.fst, Prod.snd] at hcc₃ hcr₃
    obtain ⟨t₃, cc₃', hcc₃', hcc₃''⟩ :
      ∃ (r : ℝ)(p0 : P)(hp0 : p0 ∈ s), cc₃ = r • (p -ᵥ ↑((orthogonalProjection s) p)) +ᵥ p0 := by
      rwa [mem_affine_span_insert_iff (orthogonal_projection_mem p)] at hcc₃
    have hcr₃' : ∃ r, ∀ p1 ∈ ps, dist p1 cc₃ = r := ⟨cr₃, fun p1 hp1 => hcr₃ p1 (Set.mem_insert_of_mem _ hp1)⟩
    rw [exists_dist_eq_iff_exists_dist_orthogonal_projection_eq hps cc₃, hcc₃'',
      orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ hcc₃'] at hcr₃'
    cases' hcr₃' with cr₃' hcr₃'
    have hu := hcccru (cc₃', cr₃')
    simp only [Prod.fst, Prod.snd] at hu
    replace hu := hu ⟨hcc₃', hcr₃'⟩
    rw [Prod.ext_iff] at hu
    simp only [Prod.fst, Prod.snd] at hu
    cases' hu with hucc hucr
    substs hucc hucr
    have hcr₃val : cr₃ = Real.sqrt (cr₃' * cr₃' + t₃ * y * (t₃ * y)) := by
      cases' hnps with p0 hp0
      have h' : ↑(⟨cc₃', hcc₃'⟩ : s) = cc₃' := rfl
      rw [← hcr₃ p0 (Set.mem_insert_of_mem _ hp0), hcc₃'', ← mul_self_inj_of_nonneg dist_nonneg (Real.sqrt_nonneg _),
        Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)),
        dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq _ (hps hp0),
        orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ hcc₃', h', hcr p0 hp0,
        dist_eq_norm_vsub V _ cc₃', vadd_vsub, norm_smul, ← dist_eq_norm_vsub V p, Real.norm_eq_abs, ← mul_assoc,
        mul_comm _ (abs t₃), ← mul_assoc, abs_mul_abs_self]
      ring
    replace hcr₃ := hcr₃ p (Set.mem_insert _ _)
    rw [hpo, hcc₃'', hcr₃val, ← mul_self_inj_of_nonneg dist_nonneg (Real.sqrt_nonneg _),
      dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd (orthogonal_projection_mem p) hcc₃' _ _
        (vsub_orthogonal_projection_mem_direction_orthogonal s p),
      dist_comm, ← dist_eq_norm_vsub V p, Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))] at
      hcr₃
    change x * x + _ * (y * y) = _ at hcr₃
    rw
      [show x * x + (1 - t₃) * (1 - t₃) * (y * y) = x * x + y * y - 2 * y * (t₃ * y) + t₃ * y * (t₃ * y) by
        ring,
      add_left_injₓ] at hcr₃
    have ht₃ : t₃ = ycc₂ / y := by
      field_simp [← hcr₃, hy0]
      ring
    subst ht₃
    change cc₃ = cc₂ at hcc₃''
    congr
    rw [hcr₃val]
    congr 2
    field_simp [hy0]
    ring
    

/-- Given a finite nonempty affinely independent family of points,
there is a unique (circumcenter, circumradius) pair for those points
in the affine subspace they span. -/
theorem _root_.affine_independent.exists_unique_dist_eq {ι : Type _} [hne : Nonempty ι] [Fintype ι] {p : ι → P}
    (ha : AffineIndependent ℝ p) :
    ∃! cccr : P × ℝ, cccr.fst ∈ affineSpan ℝ (Set.Range p) ∧ ∀ i, dist (p i) cccr.fst = cccr.snd := by
  induction' hn : Fintype.card ι with m hm generalizing ι
  · exfalso
    have h := Fintype.card_pos_iff.2 hne
    rw [hn] at h
    exact lt_irreflₓ 0 h
    
  · cases m
    · rw [Fintype.card_eq_one_iff] at hn
      cases' hn with i hi
      haveI : Unique ι := ⟨⟨i⟩, hi⟩
      use (p i, 0)
      simp only [Prod.fst, Prod.snd, Set.range_unique, AffineSubspace.mem_affine_span_singleton]
      constructor
      · simp_rw [hi default]
        use rfl
        intro i1
        rw [hi i1]
        exact dist_self _
        
      · rintro ⟨cc, cr⟩
        simp only [Prod.fst, Prod.snd]
        rintro ⟨rfl, hdist⟩
        rw [hi default]
        congr
        rw [← hdist default]
        exact dist_self _
        
      
    · have i := hne.some
      let ι2 := { x // x ≠ i }
      have hc : Fintype.card ι2 = m + 1 := by
        rw [Fintype.card_of_subtype (finset.univ.filter fun x => x ≠ i)]
        · rw [Finset.filter_not]
          simp_rw [eq_comm]
          rw [Finset.filter_eq, if_pos (Finset.mem_univ _), Finset.card_sdiff (Finset.subset_univ _),
            Finset.card_singleton, Finset.card_univ, hn]
          simp
          
        · simp
          
      haveI : Nonempty ι2 := Fintype.card_pos_iff.1 (hc.symm ▸ Nat.zero_lt_succₓ _)
      have ha2 : AffineIndependent ℝ fun i2 : ι2 => p i2 := ha.subtype _
      replace hm := hm ha2 hc
      have hr : Set.Range p = insert (p i) (Set.Range fun i2 : ι2 => p i2) := by
        change _ = insert _ (Set.Range fun i2 : { x | x ≠ i } => p i2)
        rw [← Set.image_eq_range, ← Set.image_univ, ← Set.image_insert_eq]
        congr with j
        simp [Classical.em]
      change ∃! cccr : P × ℝ, _ ∧ ∀ i2, (fun q => dist q cccr.fst = cccr.snd) (p i2)
      conv => congr ext conv => congr skip rw [← Set.forall_range_iff]
      dsimp' only
      rw [hr]
      change ∃! cccr : P × ℝ, _ ∧ ∀ i2 : ι2, (fun q => dist q cccr.fst = cccr.snd) (p i2) at hm
      conv at hm => congr ext conv => congr skip rw [← Set.forall_range_iff]
      rw [← affine_span_insert_affine_span]
      refine' exists_unique_dist_eq_of_insert (Set.range_nonempty _) (subset_span_points ℝ _) _ hm
      convert ha.not_mem_affine_span_diff i Set.Univ
      change (Set.Range fun i2 : { x | x ≠ i } => p i2) = _
      rw [← Set.image_eq_range]
      congr with j
      simp
      rfl
      
    

end EuclideanGeometry

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry

variable {V : Type _} {P : Type _} [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

include V

/-- The pair (circumcenter, circumradius) of a simplex. -/
def circumcenterCircumradius {n : ℕ} (s : Simplex ℝ P n) : P × ℝ :=
  s.Independent.exists_unique_dist_eq.some

/-- The property satisfied by the (circumcenter, circumradius) pair. -/
theorem circumcenter_circumradius_unique_dist_eq {n : ℕ} (s : Simplex ℝ P n) :
    (s.circumcenterCircumradius.fst ∈ affineSpan ℝ (Set.Range s.points) ∧
        ∀ i, dist (s.points i) s.circumcenterCircumradius.fst = s.circumcenterCircumradius.snd) ∧
      ∀ cccr : P × ℝ,
        (cccr.fst ∈ affineSpan ℝ (Set.Range s.points) ∧ ∀ i, dist (s.points i) cccr.fst = cccr.snd) →
          cccr = s.circumcenterCircumradius :=
  s.Independent.exists_unique_dist_eq.some_spec

/-- The circumcenter of a simplex. -/
def circumcenter {n : ℕ} (s : Simplex ℝ P n) : P :=
  s.circumcenterCircumradius.fst

/-- The circumradius of a simplex. -/
def circumradius {n : ℕ} (s : Simplex ℝ P n) : ℝ :=
  s.circumcenterCircumradius.snd

/-- The circumcenter lies in the affine span. -/
theorem circumcenter_mem_affine_span {n : ℕ} (s : Simplex ℝ P n) : s.circumcenter ∈ affineSpan ℝ (Set.Range s.points) :=
  s.circumcenter_circumradius_unique_dist_eq.1.1

/-- All points have distance from the circumcenter equal to the
circumradius. -/
@[simp]
theorem dist_circumcenter_eq_circumradius {n : ℕ} (s : Simplex ℝ P n) :
    ∀ i, dist (s.points i) s.circumcenter = s.circumradius :=
  s.circumcenter_circumradius_unique_dist_eq.1.2

/-- All points have distance to the circumcenter equal to the
circumradius. -/
@[simp]
theorem dist_circumcenter_eq_circumradius' {n : ℕ} (s : Simplex ℝ P n) :
    ∀ i, dist s.circumcenter (s.points i) = s.circumradius := by
  intro i
  rw [dist_comm]
  exact dist_circumcenter_eq_circumradius _ _

/-- Given a point in the affine span from which all the points are
equidistant, that point is the circumcenter. -/
theorem eq_circumcenter_of_dist_eq {n : ℕ} (s : Simplex ℝ P n) {p : P} (hp : p ∈ affineSpan ℝ (Set.Range s.points))
    {r : ℝ} (hr : ∀ i, dist (s.points i) p = r) : p = s.circumcenter := by
  have h := s.circumcenter_circumradius_unique_dist_eq.2 (p, r)
  simp only [hp, hr, forall_const, eq_self_iff_true, and_selfₓ, Prod.ext_iff] at h
  exact h.1

/-- Given a point in the affine span from which all the points are
equidistant, that distance is the circumradius. -/
theorem eq_circumradius_of_dist_eq {n : ℕ} (s : Simplex ℝ P n) {p : P} (hp : p ∈ affineSpan ℝ (Set.Range s.points))
    {r : ℝ} (hr : ∀ i, dist (s.points i) p = r) : r = s.circumradius := by
  have h := s.circumcenter_circumradius_unique_dist_eq.2 (p, r)
  simp only [hp, hr, forall_const, eq_self_iff_true, and_selfₓ, Prod.ext_iff] at h
  exact h.2

/-- The circumradius is non-negative. -/
theorem circumradius_nonneg {n : ℕ} (s : Simplex ℝ P n) : 0 ≤ s.circumradius :=
  s.dist_circumcenter_eq_circumradius 0 ▸ dist_nonneg

/-- The circumradius of a simplex with at least two points is
positive. -/
theorem circumradius_pos {n : ℕ} (s : Simplex ℝ P (n + 1)) : 0 < s.circumradius := by
  refine' lt_of_le_of_neₓ s.circumradius_nonneg _
  intro h
  have hr := s.dist_circumcenter_eq_circumradius
  simp_rw [← h, dist_eq_zero] at hr
  have h01 :=
    s.independent.injective.ne
      (by
        decide : (0 : Finₓ (n + 2)) ≠ 1)
  simpa [hr] using h01

/-- The circumcenter of a 0-simplex equals its unique point. -/
theorem circumcenter_eq_point (s : Simplex ℝ P 0) (i : Finₓ 1) : s.circumcenter = s.points i := by
  have h := s.circumcenter_mem_affine_span
  rw [Set.range_unique, mem_affine_span_singleton] at h
  rw [h]
  congr

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
/-- The circumcenter of a 1-simplex equals its centroid. -/
theorem circumcenter_eq_centroid (s : Simplex ℝ P 1) : s.circumcenter = Finset.univ.centroid ℝ s.points := by
  have hr :
    Set.Pairwise Set.Univ fun i j : Finₓ 2 =>
      dist (s.points i) (finset.univ.centroid ℝ s.points) = dist (s.points j) (finset.univ.centroid ℝ s.points) :=
    by
    intro i hi j hj hij
    rw [Finset.centroid_pair_fin, dist_eq_norm_vsub V (s.points i), dist_eq_norm_vsub V (s.points j),
      vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, ← one_smul ℝ (s.points i -ᵥ s.points 0), ←
      one_smul ℝ (s.points j -ᵥ s.points 0)]
    fin_cases i <;> fin_cases j <;> simp [-one_smul, ← sub_smul] <;> norm_num
  rw [Set.pairwise_eq_iff_exists_eq] at hr
  cases' hr with r hr
  exact
    (s.eq_circumcenter_of_dist_eq (centroid_mem_affine_span_of_card_eq_add_one ℝ _ (Finset.card_fin 2)) fun i =>
        hr i (Set.mem_univ _)).symm

/-- The orthogonal projection of a point `p` onto the hyperplane spanned by the simplex's points. -/
def orthogonalProjectionSpan {n : ℕ} (s : Simplex ℝ P n) : P →ᵃ[ℝ] affineSpan ℝ (Set.Range s.points) :=
  orthogonalProjection (affineSpan ℝ (Set.Range s.points))

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
theorem orthogonal_projection_vadd_smul_vsub_orthogonal_projection {n : ℕ} (s : Simplex ℝ P n) {p1 : P} (p2 : P) (r : ℝ)
    (hp : p1 ∈ affineSpan ℝ (Set.Range s.points)) :
    s.orthogonalProjectionSpan (r • (p2 -ᵥ s.orthogonalProjectionSpan p2 : V) +ᵥ p1) = ⟨p1, hp⟩ :=
  orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ _

theorem coe_orthogonal_projection_vadd_smul_vsub_orthogonal_projection {n : ℕ} {r₁ : ℝ} (s : Simplex ℝ P n) {p p₁o : P}
    (hp₁o : p₁o ∈ affineSpan ℝ (Set.Range s.points)) :
    ↑(s.orthogonalProjectionSpan (r₁ • (p -ᵥ ↑(s.orthogonalProjectionSpan p)) +ᵥ p₁o)) = p₁o :=
  congr_arg coe (orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ _ hp₁o)

theorem dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq {n : ℕ} (s : Simplex ℝ P n) {p1 : P}
    (p2 : P) (hp1 : p1 ∈ affineSpan ℝ (Set.Range s.points)) :
    dist p1 p2 * dist p1 p2 =
      dist p1 (s.orthogonalProjectionSpan p2) * dist p1 (s.orthogonalProjectionSpan p2) +
        dist p2 (s.orthogonalProjectionSpan p2) * dist p2 (s.orthogonalProjectionSpan p2) :=
  by
  rw [PseudoMetricSpace.dist_comm p2 _, dist_eq_norm_vsub V p1 _, dist_eq_norm_vsub V p1 _, dist_eq_norm_vsub V _ p2, ←
    vsub_add_vsub_cancel p1 (s.orthogonal_projection_span p2) p2,
    norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact
    Submodule.inner_right_of_mem_orthogonal (vsub_orthogonal_projection_mem_direction p2 hp1)
      (orthogonal_projection_vsub_mem_direction_orthogonal _ p2)

theorem dist_circumcenter_sq_eq_sq_sub_circumradius {n : ℕ} {r : ℝ} (s : Simplex ℝ P n) {p₁ : P}
    (h₁ : ∀ i : Finₓ (n + 1), dist (s.points i) p₁ = r) (h₁' : ↑(s.orthogonalProjectionSpan p₁) = s.circumcenter)
    (h : s.points 0 ∈ affineSpan ℝ (Set.Range s.points)) :
    dist p₁ s.circumcenter * dist p₁ s.circumcenter = r * r - s.circumradius * s.circumradius := by
  rw [dist_comm, ← h₁ 0, s.dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq p₁ h]
  simp only [h₁', dist_comm p₁, add_sub_cancel', simplex.dist_circumcenter_eq_circumradius]

/-- If there exists a distance that a point has from all vertices of a
simplex, the orthogonal projection of that point onto the subspace
spanned by that simplex is its circumcenter.  -/
theorem orthogonal_projection_eq_circumcenter_of_exists_dist_eq {n : ℕ} (s : Simplex ℝ P n) {p : P}
    (hr : ∃ r, ∀ i, dist (s.points i) p = r) : ↑(s.orthogonalProjectionSpan p) = s.circumcenter := by
  change ∃ r : ℝ, ∀ i, (fun x => dist x p = r) (s.points i) at hr
  conv at hr => congr ext rw [← Set.forall_range_iff]
  rw [exists_dist_eq_iff_exists_dist_orthogonal_projection_eq (subset_affine_span ℝ _) p] at hr
  cases' hr with r hr
  exact s.eq_circumcenter_of_dist_eq (orthogonal_projection_mem p) fun i => hr _ (Set.mem_range_self i)

/-- If a point has the same distance from all vertices of a simplex,
the orthogonal projection of that point onto the subspace spanned by
that simplex is its circumcenter.  -/
theorem orthogonal_projection_eq_circumcenter_of_dist_eq {n : ℕ} (s : Simplex ℝ P n) {p : P} {r : ℝ}
    (hr : ∀ i, dist (s.points i) p = r) : ↑(s.orthogonalProjectionSpan p) = s.circumcenter :=
  s.orthogonal_projection_eq_circumcenter_of_exists_dist_eq ⟨r, hr⟩

/-- The orthogonal projection of the circumcenter onto a face is the
circumcenter of that face. -/
theorem orthogonal_projection_circumcenter {n : ℕ} (s : Simplex ℝ P n) {fs : Finset (Finₓ (n + 1))} {m : ℕ}
    (h : fs.card = m + 1) : ↑((s.face h).orthogonalProjectionSpan s.circumcenter) = (s.face h).circumcenter := by
  have hr : ∃ r, ∀ i, dist ((s.face h).points i) s.circumcenter = r := by
    use s.circumradius
    simp [face_points]
  exact orthogonal_projection_eq_circumcenter_of_exists_dist_eq _ hr

/-- Two simplices with the same points have the same circumcenter. -/
theorem circumcenter_eq_of_range_eq {n : ℕ} {s₁ s₂ : Simplex ℝ P n} (h : Set.Range s₁.points = Set.Range s₂.points) :
    s₁.circumcenter = s₂.circumcenter := by
  have hs : s₁.circumcenter ∈ affineSpan ℝ (Set.Range s₂.points) := h ▸ s₁.circumcenter_mem_affine_span
  have hr : ∀ i, dist (s₂.points i) s₁.circumcenter = s₁.circumradius := by
    intro i
    have hi : s₂.points i ∈ Set.Range s₂.points := Set.mem_range_self _
    rw [← h, Set.mem_range] at hi
    rcases hi with ⟨j, hj⟩
    rw [← hj, s₁.dist_circumcenter_eq_circumradius j]
  exact s₂.eq_circumcenter_of_dist_eq hs hr

omit V

/-- An index type for the vertices of a simplex plus its circumcenter.
This is for use in calculations where it is convenient to work with
affine combinations of vertices together with the circumcenter.  (An
equivalent form sometimes used in the literature is placing the
circumcenter at the origin and working with vectors for the vertices.) -/
inductive PointsWithCircumcenterIndex (n : ℕ)
  | point_index : Finₓ (n + 1) → points_with_circumcenter_index
  | circumcenter_index : points_with_circumcenter_index
  deriving Fintype

open PointsWithCircumcenterIndex

instance pointsWithCircumcenterIndexInhabited (n : ℕ) : Inhabited (PointsWithCircumcenterIndex n) :=
  ⟨circumcenter_index⟩

/-- `point_index` as an embedding. -/
def pointIndexEmbedding (n : ℕ) : Finₓ (n + 1) ↪ PointsWithCircumcenterIndex n :=
  ⟨fun i => point_index i, fun _ _ h => by
    injection h⟩

/-- The sum of a function over `points_with_circumcenter_index`. -/
theorem sum_points_with_circumcenter {α : Type _} [AddCommMonoidₓ α] {n : ℕ} (f : PointsWithCircumcenterIndex n → α) :
    (∑ i, f i) = (∑ i : Finₓ (n + 1), f (point_index i)) + f circumcenter_index := by
  have h : univ = insert circumcenter_index (univ.map (point_index_embedding n)) := by
    ext x
    refine' ⟨fun h => _, fun _ => mem_univ _⟩
    cases' x with i
    · exact mem_insert_of_mem (mem_map_of_mem _ (mem_univ i))
      
    · exact mem_insert_self _ _
      
  change _ = (∑ i, f (point_index_embedding n i)) + _
  rw [add_commₓ, h, ← sum_map, sum_insert]
  simp_rw [Finset.mem_map, not_exists]
  intro x hx h
  injection h

include V

/-- The vertices of a simplex plus its circumcenter. -/
def pointsWithCircumcenter {n : ℕ} (s : Simplex ℝ P n) : PointsWithCircumcenterIndex n → P
  | point_index i => s.points i
  | circumcenter_index => s.circumcenter

/-- `points_with_circumcenter`, applied to a `point_index` value,
equals `points` applied to that value. -/
@[simp]
theorem points_with_circumcenter_point {n : ℕ} (s : Simplex ℝ P n) (i : Finₓ (n + 1)) :
    s.pointsWithCircumcenter (point_index i) = s.points i :=
  rfl

/-- `points_with_circumcenter`, applied to `circumcenter_index`, equals the
circumcenter. -/
@[simp]
theorem points_with_circumcenter_eq_circumcenter {n : ℕ} (s : Simplex ℝ P n) :
    s.pointsWithCircumcenter circumcenter_index = s.circumcenter :=
  rfl

omit V

/-- The weights for a single vertex of a simplex, in terms of
`points_with_circumcenter`. -/
def pointWeightsWithCircumcenter {n : ℕ} (i : Finₓ (n + 1)) : PointsWithCircumcenterIndex n → ℝ
  | point_index j => if j = i then 1 else 0
  | circumcenter_index => 0

/-- `point_weights_with_circumcenter` sums to 1. -/
@[simp]
theorem sum_point_weights_with_circumcenter {n : ℕ} (i : Finₓ (n + 1)) : (∑ j, pointWeightsWithCircumcenter i j) = 1 :=
  by
  convert sum_ite_eq' univ (point_index i) (Function.const _ (1 : ℝ))
  · ext j
    cases j <;> simp [point_weights_with_circumcenter]
    
  · simp
    

include V

/-- A single vertex, in terms of `points_with_circumcenter`. -/
theorem point_eq_affine_combination_of_points_with_circumcenter {n : ℕ} (s : Simplex ℝ P n) (i : Finₓ (n + 1)) :
    s.points i =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination s.pointsWithCircumcenter
        (pointWeightsWithCircumcenter i) :=
  by
  rw [← points_with_circumcenter_point]
  symm
  refine'
    affine_combination_of_eq_one_of_eq_zero _ _ _ (mem_univ _)
      (by
        simp [point_weights_with_circumcenter])
      _
  intro i hi hn
  cases i
  · have h : i_1 ≠ i := fun h => hn (h ▸ rfl)
    simp [point_weights_with_circumcenter, h]
    
  · rfl
    

omit V

/-- The weights for the centroid of some vertices of a simplex, in
terms of `points_with_circumcenter`. -/
def centroidWeightsWithCircumcenter {n : ℕ} (fs : Finset (Finₓ (n + 1))) : PointsWithCircumcenterIndex n → ℝ
  | point_index i => if i ∈ fs then (card fs : ℝ)⁻¹ else 0
  | circumcenter_index => 0

/-- `centroid_weights_with_circumcenter` sums to 1, if the `finset` is
nonempty. -/
@[simp]
theorem sum_centroid_weights_with_circumcenter {n : ℕ} {fs : Finset (Finₓ (n + 1))} (h : fs.Nonempty) :
    (∑ i, centroidWeightsWithCircumcenter fs i) = 1 := by
  simp_rw [sum_points_with_circumcenter, centroid_weights_with_circumcenter, add_zeroₓ, ←
    fs.sum_centroid_weights_eq_one_of_nonempty ℝ h, Set.sum_indicator_subset _ fs.subset_univ]
  rcongr

include V

/-- The centroid of some vertices of a simplex, in terms of
`points_with_circumcenter`. -/
theorem centroid_eq_affine_combination_of_points_with_circumcenter {n : ℕ} (s : Simplex ℝ P n)
    (fs : Finset (Finₓ (n + 1))) :
    fs.centroid ℝ s.points =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination s.pointsWithCircumcenter
        (centroidWeightsWithCircumcenter fs) :=
  by
  simp_rw [centroid_def, affine_combination_apply, weighted_vsub_of_point_apply, sum_points_with_circumcenter,
    centroid_weights_with_circumcenter, points_with_circumcenter_point, zero_smul, add_zeroₓ, centroid_weights,
    Set.sum_indicator_subset_of_eq_zero (Function.const (Finₓ (n + 1)) (card fs : ℝ)⁻¹)
      (fun i wi => wi • (s.points i -ᵥ Classical.choice AddTorsor.nonempty)) fs.subset_univ fun i => zero_smul ℝ _,
    Set.indicator_apply]
  congr

omit V

/-- The weights for the circumcenter of a simplex, in terms of
`points_with_circumcenter`. -/
def circumcenterWeightsWithCircumcenter (n : ℕ) : PointsWithCircumcenterIndex n → ℝ
  | point_index i => 0
  | circumcenter_index => 1

/-- `circumcenter_weights_with_circumcenter` sums to 1. -/
@[simp]
theorem sum_circumcenter_weights_with_circumcenter (n : ℕ) : (∑ i, circumcenterWeightsWithCircumcenter n i) = 1 := by
  convert sum_ite_eq' univ circumcenter_index (Function.const _ (1 : ℝ))
  · ext ⟨j⟩ <;> simp [circumcenter_weights_with_circumcenter]
    
  · simp
    

include V

/-- The circumcenter of a simplex, in terms of
`points_with_circumcenter`. -/
theorem circumcenter_eq_affine_combination_of_points_with_circumcenter {n : ℕ} (s : Simplex ℝ P n) :
    s.circumcenter =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination s.pointsWithCircumcenter
        (circumcenterWeightsWithCircumcenter n) :=
  by
  rw [← points_with_circumcenter_eq_circumcenter]
  symm
  refine' affine_combination_of_eq_one_of_eq_zero _ _ _ (mem_univ _) rfl _
  rintro ⟨i⟩ hi hn <;> tauto

omit V

/-- The weights for the reflection of the circumcenter in an edge of a
simplex.  This definition is only valid with `i₁ ≠ i₂`. -/
def reflectionCircumcenterWeightsWithCircumcenter {n : ℕ} (i₁ i₂ : Finₓ (n + 1)) : PointsWithCircumcenterIndex n → ℝ
  | point_index i => if i = i₁ ∨ i = i₂ then 1 else 0
  | circumcenter_index => -1

/-- `reflection_circumcenter_weights_with_circumcenter` sums to 1. -/
@[simp]
theorem sum_reflection_circumcenter_weights_with_circumcenter {n : ℕ} {i₁ i₂ : Finₓ (n + 1)} (h : i₁ ≠ i₂) :
    (∑ i, reflectionCircumcenterWeightsWithCircumcenter i₁ i₂ i) = 1 := by
  simp_rw [sum_points_with_circumcenter, reflection_circumcenter_weights_with_circumcenter, sum_ite, sum_const,
    filter_or, filter_eq']
  rw [card_union_eq]
  · simp
    
  · simpa only [if_true, mem_univ, disjoint_singleton] using h
    

include V

/-- The reflection of the circumcenter of a simplex in an edge, in
terms of `points_with_circumcenter`. -/
theorem reflection_circumcenter_eq_affine_combination_of_points_with_circumcenter {n : ℕ} (s : Simplex ℝ P n)
    {i₁ i₂ : Finₓ (n + 1)} (h : i₁ ≠ i₂) :
    reflection (affineSpan ℝ (s.points '' {i₁, i₂})) s.circumcenter =
      (univ : Finset (PointsWithCircumcenterIndex n)).affineCombination s.pointsWithCircumcenter
        (reflectionCircumcenterWeightsWithCircumcenter i₁ i₂) :=
  by
  have hc : card ({i₁, i₂} : Finset (Finₓ (n + 1))) = 2 := by
    simp [h]
  -- Making the next line a separate definition helps the elaborator:
  set W : AffineSubspace ℝ P := affineSpan ℝ (s.points '' {i₁, i₂}) with W_def
  have h_faces : ↑(orthogonalProjection W s.circumcenter) = ↑((s.face hc).orthogonalProjectionSpan s.circumcenter) := by
    apply eq_orthogonal_projection_of_eq_subspace
    simp
  rw [EuclideanGeometry.reflection_apply, h_faces, s.orthogonal_projection_circumcenter hc, circumcenter_eq_centroid,
    s.face_centroid_eq_centroid hc, centroid_eq_affine_combination_of_points_with_circumcenter,
    circumcenter_eq_affine_combination_of_points_with_circumcenter, ← @vsub_eq_zero_iff_eq V, affine_combination_vsub,
    weighted_vsub_vadd_affine_combination, affine_combination_vsub, weighted_vsub_apply, sum_points_with_circumcenter]
  simp_rw [Pi.sub_apply, Pi.add_apply, Pi.sub_apply, sub_smul, add_smul, sub_smul, centroid_weights_with_circumcenter,
    circumcenter_weights_with_circumcenter, reflection_circumcenter_weights_with_circumcenter, ite_smul, zero_smul,
    sub_zero, apply_ite2 (· + ·), add_zeroₓ, ← add_smul, hc, zero_sub, neg_smul, sub_self, add_zeroₓ]
  convert sum_const_zero
  norm_num

end Simplex

end Affine

namespace EuclideanGeometry

open Affine AffineSubspace FiniteDimensional

variable {V : Type _} {P : Type _} [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

include V

/-- Given a nonempty affine subspace, whose direction is complete,
that contains a set of points, those points are cospherical if and
only if they are equidistant from some point in that subspace. -/
theorem cospherical_iff_exists_mem_of_complete {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s) [Nonempty s]
    [CompleteSpace s.direction] : Cospherical ps ↔ ∃ center ∈ s, ∃ radius : ℝ, ∀ p ∈ ps, dist p center = radius := by
  constructor
  · rintro ⟨c, hcr⟩
    rw [exists_dist_eq_iff_exists_dist_orthogonal_projection_eq h c] at hcr
    exact ⟨orthogonalProjection s c, orthogonal_projection_mem _, hcr⟩
    
  · exact fun ⟨c, hc, hd⟩ => ⟨c, hd⟩
    

/-- Given a nonempty affine subspace, whose direction is
finite-dimensional, that contains a set of points, those points are
cospherical if and only if they are equidistant from some point in
that subspace. -/
theorem cospherical_iff_exists_mem_of_finite_dimensional {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s) [Nonempty s]
    [FiniteDimensional ℝ s.direction] : Cospherical ps ↔ ∃ center ∈ s, ∃ radius : ℝ, ∀ p ∈ ps, dist p center = radius :=
  cospherical_iff_exists_mem_of_complete h

/-- All n-simplices among cospherical points in an n-dimensional
subspace have the same circumradius. -/
theorem exists_circumradius_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s) [Nonempty s]
    {n : ℕ} [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = n) (hc : Cospherical ps) :
    ∃ r : ℝ, ∀ sx : Simplex ℝ P n, Set.Range sx.points ⊆ ps → sx.circumradius = r := by
  rw [cospherical_iff_exists_mem_of_finite_dimensional h] at hc
  rcases hc with ⟨c, hc, r, hcr⟩
  use r
  intro sx hsxps
  have hsx : affineSpan ℝ (Set.Range sx.points) = s := by
    refine'
      sx.independent.affine_span_eq_of_le_of_card_eq_finrank_add_one
        (span_points_subset_coe_of_subset_coe (hsxps.trans h)) _
    simp [hd]
  have hc : c ∈ affineSpan ℝ (Set.Range sx.points) := hsx.symm ▸ hc
  exact (sx.eq_circumradius_of_dist_eq hc fun i => hcr (sx.points i) (hsxps (Set.mem_range_self i))).symm

/-- Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumradius. -/
theorem circumradius_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s) [Nonempty s] {n : ℕ}
    [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n}
    (hsx₁ : Set.Range sx₁.points ⊆ ps) (hsx₂ : Set.Range sx₂.points ⊆ ps) : sx₁.circumradius = sx₂.circumradius := by
  rcases exists_circumradius_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

/-- All n-simplices among cospherical points in n-space have the same
circumradius. -/
theorem exists_circumradius_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V] (hd : finrank ℝ V = n)
    (hc : Cospherical ps) : ∃ r : ℝ, ∀ sx : Simplex ℝ P n, Set.Range sx.points ⊆ ps → sx.circumradius = r := by
  haveI : Nonempty (⊤ : AffineSubspace ℝ P) := Set.Univ.nonempty
  rw [← finrank_top, ← direction_top ℝ V P] at hd
  refine' exists_circumradius_eq_of_cospherical_subset _ hd hc
  exact Set.subset_univ _

/-- Two n-simplices among cospherical points in n-space have the same
circumradius. -/
theorem circumradius_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V] (hd : finrank ℝ V = n)
    (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n} (hsx₁ : Set.Range sx₁.points ⊆ ps)
    (hsx₂ : Set.Range sx₂.points ⊆ ps) : sx₁.circumradius = sx₂.circumradius := by
  rcases exists_circumradius_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

/-- All n-simplices among cospherical points in an n-dimensional
subspace have the same circumcenter. -/
theorem exists_circumcenter_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s) [Nonempty s]
    {n : ℕ} [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = n) (hc : Cospherical ps) :
    ∃ c : P, ∀ sx : Simplex ℝ P n, Set.Range sx.points ⊆ ps → sx.circumcenter = c := by
  rw [cospherical_iff_exists_mem_of_finite_dimensional h] at hc
  rcases hc with ⟨c, hc, r, hcr⟩
  use c
  intro sx hsxps
  have hsx : affineSpan ℝ (Set.Range sx.points) = s := by
    refine'
      sx.independent.affine_span_eq_of_le_of_card_eq_finrank_add_one
        (span_points_subset_coe_of_subset_coe (hsxps.trans h)) _
    simp [hd]
  have hc : c ∈ affineSpan ℝ (Set.Range sx.points) := hsx.symm ▸ hc
  exact (sx.eq_circumcenter_of_dist_eq hc fun i => hcr (sx.points i) (hsxps (Set.mem_range_self i))).symm

/-- Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumcenter. -/
theorem circumcenter_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s) [Nonempty s] {n : ℕ}
    [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = n) (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n}
    (hsx₁ : Set.Range sx₁.points ⊆ ps) (hsx₂ : Set.Range sx₂.points ⊆ ps) : sx₁.circumcenter = sx₂.circumcenter := by
  rcases exists_circumcenter_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

/-- All n-simplices among cospherical points in n-space have the same
circumcenter. -/
theorem exists_circumcenter_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V] (hd : finrank ℝ V = n)
    (hc : Cospherical ps) : ∃ c : P, ∀ sx : Simplex ℝ P n, Set.Range sx.points ⊆ ps → sx.circumcenter = c := by
  haveI : Nonempty (⊤ : AffineSubspace ℝ P) := Set.Univ.nonempty
  rw [← finrank_top, ← direction_top ℝ V P] at hd
  refine' exists_circumcenter_eq_of_cospherical_subset _ hd hc
  exact Set.subset_univ _

/-- Two n-simplices among cospherical points in n-space have the same
circumcenter. -/
theorem circumcenter_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V] (hd : finrank ℝ V = n)
    (hc : Cospherical ps) {sx₁ sx₂ : Simplex ℝ P n} (hsx₁ : Set.Range sx₁.points ⊆ ps)
    (hsx₂ : Set.Range sx₂.points ⊆ ps) : sx₁.circumcenter = sx₂.circumcenter := by
  rcases exists_circumcenter_eq_of_cospherical hd hc with ⟨r, hr⟩
  rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

/-- Suppose all distances from `p₁` and `p₂` to the points of a
simplex are equal, and that `p₁` and `p₂` lie in the affine span of
`p` with the vertices of that simplex.  Then `p₁` and `p₂` are equal
or reflections of each other in the affine span of the vertices of the
simplex. -/
theorem eq_or_eq_reflection_of_dist_eq {n : ℕ} {s : Simplex ℝ P n} {p p₁ p₂ : P} {r : ℝ}
    (hp₁ : p₁ ∈ affineSpan ℝ (insert p (Set.Range s.points))) (hp₂ : p₂ ∈ affineSpan ℝ (insert p (Set.Range s.points)))
    (h₁ : ∀ i, dist (s.points i) p₁ = r) (h₂ : ∀ i, dist (s.points i) p₂ = r) :
    p₁ = p₂ ∨ p₁ = reflection (affineSpan ℝ (Set.Range s.points)) p₂ := by
  let span_s := affineSpan ℝ (Set.Range s.points)
  have h₁' := s.orthogonal_projection_eq_circumcenter_of_dist_eq h₁
  have h₂' := s.orthogonal_projection_eq_circumcenter_of_dist_eq h₂
  rw [← affine_span_insert_affine_span, mem_affine_span_insert_iff (orthogonal_projection_mem p)] at hp₁ hp₂
  obtain ⟨r₁, p₁o, hp₁o, hp₁⟩ := hp₁
  obtain ⟨r₂, p₂o, hp₂o, hp₂⟩ := hp₂
  obtain rfl : ↑(s.orthogonal_projection_span p₁) = p₁o := by
    subst hp₁
    exact s.coe_orthogonal_projection_vadd_smul_vsub_orthogonal_projection hp₁o
  rw [h₁'] at hp₁
  obtain rfl : ↑(s.orthogonal_projection_span p₂) = p₂o := by
    subst hp₂
    exact s.coe_orthogonal_projection_vadd_smul_vsub_orthogonal_projection hp₂o
  rw [h₂'] at hp₂
  have h : s.points 0 ∈ span_s := mem_affine_span ℝ (Set.mem_range_self _)
  have hd₁ : dist p₁ s.circumcenter * dist p₁ s.circumcenter = r * r - s.circumradius * s.circumradius :=
    s.dist_circumcenter_sq_eq_sq_sub_circumradius h₁ h₁' h
  have hd₂ : dist p₂ s.circumcenter * dist p₂ s.circumcenter = r * r - s.circumradius * s.circumradius :=
    s.dist_circumcenter_sq_eq_sq_sub_circumradius h₂ h₂' h
  rw [← hd₂, hp₁, hp₂, dist_eq_norm_vsub V _ s.circumcenter, dist_eq_norm_vsub V _ s.circumcenter, vadd_vsub, vadd_vsub,
    ← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_right, ← mul_assoc, ← mul_assoc] at hd₁
  by_cases' hp : p = s.orthogonal_projection_span p
  · rw [simplex.orthogonal_projection_span] at hp
    rw [hp₁, hp₂, ← hp]
    simp only [true_orₓ, eq_self_iff_true, smul_zero, vsub_self]
    
  · have hz : ⟪p -ᵥ orthogonalProjection span_s p, p -ᵥ orthogonalProjection span_s p⟫ ≠ 0 := by
      simpa only [Ne.def, vsub_eq_zero_iff_eq, inner_self_eq_zero] using hp
    rw [mul_left_inj' hz, mul_self_eq_mul_self_iff] at hd₁
    rw [hp₁, hp₂]
    cases hd₁
    · left
      rw [hd₁]
      
    · right
      rw [hd₁, reflection_vadd_smul_vsub_orthogonal_projection p r₂ s.circumcenter_mem_affine_span, neg_smul]
      
    

end EuclideanGeometry

