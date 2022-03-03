/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Analysis.Convex.Basic
import Mathbin.Topology.Algebra.Order.Basic

/-!
# Strictly convex sets

This file defines strictly convex sets.

A set is strictly convex if the open segment between any two distinct points lies in its interior.

## TODO

Define strictly convex spaces.
-/


open Set

open_locale Convex Pointwise

variable {𝕜 E F β : Type _}

open Function Set

open_locale Convex

section OrderedSemiring

variable [OrderedSemiring 𝕜] [TopologicalSpace E] [TopologicalSpace F]

section AddCommMonoidₓ

variable [AddCommMonoidₓ E] [AddCommMonoidₓ F]

section HasScalar

variable (𝕜) [HasScalar 𝕜 E] [HasScalar 𝕜 F] (s : Set E)

/-- A set is strictly convex if the open segment between any two distinct points lies is in its
interior. This basically means "convex and not flat on the boundary". -/
def StrictConvex : Prop :=
  s.Pairwise fun x y => ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ Interior s

variable {𝕜 s} {x y : E}

theorem strict_convex_iff_open_segment_subset :
    StrictConvex 𝕜 s ↔ s.Pairwise fun x y => OpenSegment 𝕜 x y ⊆ Interior s :=
  forall₅_congr fun x hx y hy hxy => (open_segment_subset_iff 𝕜).symm

theorem StrictConvex.open_segment_subset (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) (h : x ≠ y) :
    OpenSegment 𝕜 x y ⊆ Interior s :=
  strict_convex_iff_open_segment_subset.1 hs hx hy h

theorem strict_convex_empty : StrictConvex 𝕜 (∅ : Set E) :=
  pairwise_empty _

theorem strict_convex_univ : StrictConvex 𝕜 (Univ : Set E) := by
  intro x hx y hy hxy a b ha hb hab
  rw [interior_univ]
  exact mem_univ _

protected theorem StrictConvex.inter {t : Set E} (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) :
    StrictConvex 𝕜 (s ∩ t) := by
  intro x hx y hy hxy a b ha hb hab
  rw [interior_inter]
  exact ⟨hs hx.1 hy.1 hxy ha hb hab, ht hx.2 hy.2 hxy ha hb hab⟩

theorem Directed.strict_convex_Union {ι : Sort _} {s : ι → Set E} (hdir : Directed (· ⊆ ·) s)
    (hs : ∀ ⦃i : ι⦄, StrictConvex 𝕜 (s i)) : StrictConvex 𝕜 (⋃ i, s i) := by
  rintro x hx y hy hxy a b ha hb hab
  rw [mem_Union] at hx hy
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact interior_mono (subset_Union s k) (hs (hik hx) (hjk hy) hxy ha hb hab)

theorem DirectedOn.strict_convex_sUnion {S : Set (Set E)} (hdir : DirectedOn (· ⊆ ·) S)
    (hS : ∀, ∀ s ∈ S, ∀, StrictConvex 𝕜 s) : StrictConvex 𝕜 (⋃₀S) := by
  rw [sUnion_eq_Union]
  exact (directed_on_iff_directed.1 hdir).strict_convex_Union fun s => hS _ s.2

end HasScalar

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

protected theorem StrictConvex.convex (hs : StrictConvex 𝕜 s) : Convex 𝕜 s :=
  convex_iff_pairwise_pos.2 fun x hx y hy hxy a b ha hb hab => interior_subset <| hs hx hy hxy ha hb hab

/-- An open convex set is strictly convex. -/
protected theorem Convex.strict_convex (h : IsOpen s) (hs : Convex 𝕜 s) : StrictConvex 𝕜 s :=
  fun x hx y hy _ a b ha hb hab => h.interior_eq.symm ▸ hs hx hy ha.le hb.le hab

theorem IsOpen.strict_convex_iff (h : IsOpen s) : StrictConvex 𝕜 s ↔ Convex 𝕜 s :=
  ⟨StrictConvex.convex, Convex.strict_convex h⟩

theorem strict_convex_singleton (c : E) : StrictConvex 𝕜 ({c} : Set E) :=
  pairwise_singleton _ _

theorem Set.Subsingleton.strict_convex (hs : s.Subsingleton) : StrictConvex 𝕜 s :=
  hs.Pairwise _

theorem StrictConvex.linear_image (hs : StrictConvex 𝕜 s) (f : E →ₗ[𝕜] F) (hf : IsOpenMap f) :
    StrictConvex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  exact
    hf.image_interior_subset _
      ⟨a • x + b • y, hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, by
        rw [f.map_add, f.map_smul, f.map_smul]⟩

theorem StrictConvex.is_linear_image (hs : StrictConvex 𝕜 s) {f : E → F} (h : IsLinearMap 𝕜 f) (hf : IsOpenMap f) :
    StrictConvex 𝕜 (f '' s) :=
  hs.linear_image (h.mk' f) hf

theorem StrictConvex.linear_preimage {s : Set F} (hs : StrictConvex 𝕜 s) (f : E →ₗ[𝕜] F) (hf : Continuous f)
    (hfinj : Injective f) : StrictConvex 𝕜 (s.Preimage f) := by
  intro x hx y hy hxy a b ha hb hab
  refine' preimage_interior_subset_interior_preimage hf _
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul]
  exact hs hx hy (hfinj.ne hxy) ha hb hab

theorem StrictConvex.is_linear_preimage {s : Set F} (hs : StrictConvex 𝕜 s) {f : E → F} (h : IsLinearMap 𝕜 f)
    (hf : Continuous f) (hfinj : Injective f) : StrictConvex 𝕜 (s.Preimage f) :=
  hs.linear_preimage (h.mk' f) hf hfinj

section LinearOrderedCancelAddCommMonoid

variable [TopologicalSpace β] [LinearOrderedCancelAddCommMonoid β] [OrderTopology β] [Module 𝕜 β] [OrderedSmul 𝕜 β]

theorem strict_convex_Iic (r : β) : StrictConvex 𝕜 (Iic r) := by
  rintro x (hx : x ≤ r) y (hy : y ≤ r) hxy a b ha hb hab
  refine' (subset_interior_iff_subset_of_open is_open_Iio).2 Iio_subset_Iic_self _
  rw [← Convex.combo_self hab r]
  obtain rfl | hx := hx.eq_or_lt
  · exact add_lt_add_left (smul_lt_smul_of_pos (hy.lt_of_ne hxy.symm) hb) _
    
  obtain rfl | hy := hy.eq_or_lt
  · exact add_lt_add_right (smul_lt_smul_of_pos hx ha) _
    
  · exact add_lt_add (smul_lt_smul_of_pos hx ha) (smul_lt_smul_of_pos hy hb)
    

theorem strict_convex_Ici (r : β) : StrictConvex 𝕜 (Ici r) :=
  @strict_convex_Iic 𝕜 (OrderDual β) _ _ _ _ _ _ r

theorem strict_convex_Icc (r s : β) : StrictConvex 𝕜 (Icc r s) :=
  (strict_convex_Ici r).inter <| strict_convex_Iic s

theorem strict_convex_Iio (r : β) : StrictConvex 𝕜 (Iio r) :=
  (convex_Iio r).StrictConvex is_open_Iio

theorem strict_convex_Ioi (r : β) : StrictConvex 𝕜 (Ioi r) :=
  (convex_Ioi r).StrictConvex is_open_Ioi

theorem strict_convex_Ioo (r s : β) : StrictConvex 𝕜 (Ioo r s) :=
  (strict_convex_Ioi r).inter <| strict_convex_Iio s

theorem strict_convex_Ico (r s : β) : StrictConvex 𝕜 (Ico r s) :=
  (strict_convex_Ici r).inter <| strict_convex_Iio s

theorem strict_convex_Ioc (r s : β) : StrictConvex 𝕜 (Ioc r s) :=
  (strict_convex_Ioi r).inter <| strict_convex_Iic s

theorem strict_convex_interval (r s : β) : StrictConvex 𝕜 (Interval r s) :=
  strict_convex_Icc _ _

end LinearOrderedCancelAddCommMonoid

end Module

end AddCommMonoidₓ

section AddCancelCommMonoid

variable [AddCancelCommMonoid E] [HasContinuousAdd E] [Module 𝕜 E] {s : Set E}

/-- The translation of a strict_convex set is also strict_convex. -/
theorem StrictConvex.preimage_add_right (hs : StrictConvex 𝕜 s) (z : E) : StrictConvex 𝕜 ((fun x => z + x) ⁻¹' s) := by
  intro x hx y hy hxy a b ha hb hab
  refine' preimage_interior_subset_interior_preimage (continuous_add_left _) _
  have h := hs hx hy ((add_right_injective _).Ne hxy) ha hb hab
  rwa [smul_add, smul_add, add_add_add_commₓ, ← add_smul, hab, one_smul] at h

/-- The translation of a strict_convex set is also strict_convex. -/
theorem StrictConvex.preimage_add_left (hs : StrictConvex 𝕜 s) (z : E) : StrictConvex 𝕜 ((fun x => x + z) ⁻¹' s) := by
  simpa only [add_commₓ] using hs.preimage_add_right z

end AddCancelCommMonoid

section AddCommGroupₓ

variable [AddCommGroupₓ E] [Module 𝕜 E] {s t : Set E}

theorem StrictConvex.add_left [HasContinuousAdd E] (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => z + x) '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  refine' (is_open_map_add_left _).image_interior_subset _ _
  refine' ⟨a • x + b • y, hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, _⟩
  rw [smul_add, smul_add, add_add_add_commₓ, ← add_smul, hab, one_smul]

theorem StrictConvex.add_right [HasContinuousAdd E] (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => x + z) '' s) := by
  simpa only [add_commₓ] using hs.add_left z

theorem StrictConvex.add [HasContinuousAdd E] {t : Set E} (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) :
    StrictConvex 𝕜 (s + t) := by
  rintro _ ⟨v, w, hv, hw, rfl⟩ _ ⟨x, y, hx, hy, rfl⟩ h a b ha hb hab
  rw [smul_add, smul_add, add_add_add_commₓ]
  obtain rfl | hvx := eq_or_ne v x
  · rw [Convex.combo_self hab]
    suffices v + (a • w + b • y) ∈ Interior ({v} + t) by
      exact interior_mono (add_subset_add (singleton_subset_iff.2 hv) (subset.refl _)) this
    rw [singleton_add]
    exact
      (is_open_map_add_left _).image_interior_subset _ (mem_image_of_mem _ <| ht hw hy (ne_of_apply_ne _ h) ha hb hab)
    
  obtain rfl | hwy := eq_or_ne w y
  · rw [Convex.combo_self hab]
    suffices a • v + b • x + w ∈ Interior (s + {w}) by
      exact interior_mono (add_subset_add (subset.refl _) (singleton_subset_iff.2 hw)) this
    rw [add_singleton]
    exact (is_open_map_add_right _).image_interior_subset _ (mem_image_of_mem _ <| hs hv hx hvx ha hb hab)
    
  exact subset_interior_add (add_mem_add (hs hv hx hvx ha hb hab) <| ht hw hy hwy ha hb hab)

end AddCommGroupₓ

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜] [TopologicalSpace E]

section AddCommGroupₓ

variable [AddCommGroupₓ E] [Module 𝕜 E] [NoZeroSmulDivisors 𝕜 E] [HasContinuousConstSmul 𝕜 E] {s : Set E}

theorem StrictConvex.preimage_smul (hs : StrictConvex 𝕜 s) (c : 𝕜) : StrictConvex 𝕜 ((fun z => c • z) ⁻¹' s) := by
  classical
  obtain rfl | hc := eq_or_ne c 0
  · simp_rw [zero_smul, preimage_const]
    split_ifs
    · exact strict_convex_univ
      
    · exact strict_convex_empty
      
    
  refine' hs.linear_preimage (LinearMap.lsmul _ _ c) _ (smul_right_injective E hc)
  unfold LinearMap.lsmul LinearMap.mk₂ LinearMap.mk₂' LinearMap.mk₂'ₛₗ
  exact continuous_const_smul _

end AddCommGroupₓ

end OrderedCommSemiring

section OrderedRing

variable [OrderedRing 𝕜] [TopologicalSpace E] [TopologicalSpace F]

section AddCommGroupₓ

variable [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E} {x y : E}

theorem StrictConvex.eq_of_open_segment_subset_frontier [Nontrivial 𝕜] [DenselyOrdered 𝕜] (hs : StrictConvex 𝕜 s)
    (hx : x ∈ s) (hy : y ∈ s) (h : OpenSegment 𝕜 x y ⊆ Frontier s) : x = y := by
  obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
  classical
  by_contra hxy
  exact
    (h ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel'_right _ _, rfl⟩).2
      (hs hx hy hxy ha₀ (sub_pos_of_lt ha₁) <| add_sub_cancel'_right _ _)

theorem StrictConvex.add_smul_mem (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hxy : x + y ∈ s) (hy : y ≠ 0) {t : 𝕜}
    (ht₀ : 0 < t) (ht₁ : t < 1) : x + t • y ∈ Interior s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by
    rw [smul_add, ← add_assocₓ, ← add_smul, sub_add_cancel, one_smul]
  rw [h]
  refine' hs hx hxy (fun h => hy <| add_left_cancelₓ _) (sub_pos_of_lt ht₁) ht₀ (sub_add_cancel _ _)
  exact x
  rw [← h, add_zeroₓ]

theorem StrictConvex.smul_mem_of_zero_mem (hs : StrictConvex 𝕜 s) (zero_mem : (0 : E) ∈ s) (hx : x ∈ s) (hx₀ : x ≠ 0)
    {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : t • x ∈ Interior s := by
  simpa using
    hs.add_smul_mem zero_mem
      (by
        simpa using hx)
      hx₀ ht₀ ht₁

theorem StrictConvex.add_smul_sub_mem (h : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) {t : 𝕜}
    (ht₀ : 0 < t) (ht₁ : t < 1) : x + t • (y - x) ∈ Interior s := by
  apply h.open_segment_subset hx hy hxy
  rw [open_segment_eq_image']
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩

/-- The preimage of a strict_convex set under an affine map is strict_convex. -/
theorem StrictConvex.affine_preimage {s : Set F} (hs : StrictConvex 𝕜 s) {f : E →ᵃ[𝕜] F} (hf : Continuous f)
    (hfinj : Injective f) : StrictConvex 𝕜 (f ⁻¹' s) := by
  intro x hx y hy hxy a b ha hb hab
  refine' preimage_interior_subset_interior_preimage hf _
  rw [mem_preimage, Convex.combo_affine_apply hab]
  exact hs hx hy (hfinj.ne hxy) ha hb hab

/-- The image of a strict_convex set under an affine map is strict_convex. -/
theorem StrictConvex.affine_image (hs : StrictConvex 𝕜 s) {f : E →ᵃ[𝕜] F} (hf : IsOpenMap f) :
    StrictConvex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  exact
    hf.image_interior_subset _
      ⟨a • x + b • y, ⟨hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, Convex.combo_affine_apply hab⟩⟩

theorem StrictConvex.neg [TopologicalAddGroup E] (hs : StrictConvex 𝕜 s) : StrictConvex 𝕜 ((fun z => -z) '' s) :=
  hs.is_linear_image IsLinearMap.is_linear_map_neg (Homeomorph.neg E).IsOpenMap

theorem StrictConvex.neg_preimage [TopologicalAddGroup E] (hs : StrictConvex 𝕜 s) :
    StrictConvex 𝕜 ((fun z => -z) ⁻¹' s) :=
  hs.is_linear_preimage IsLinearMap.is_linear_map_neg continuous_id.neg neg_injective

end AddCommGroupₓ

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField 𝕜] [TopologicalSpace E]

section AddCommGroupₓ

variable [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E} {x : E}

theorem StrictConvex.smul [HasContinuousConstSmul 𝕜 E] (hs : StrictConvex 𝕜 s) (c : 𝕜) : StrictConvex 𝕜 (c • s) := by
  obtain rfl | hc := eq_or_ne c 0
  · exact (subsingleton_zero_smul_set _).StrictConvex
    
  · exact hs.linear_image (LinearMap.lsmul _ _ c) (is_open_map_smul₀ hc)
    

theorem StrictConvex.affinity [HasContinuousAdd E] [HasContinuousConstSmul 𝕜 E] (hs : StrictConvex 𝕜 s) (z : E)
    (c : 𝕜) : StrictConvex 𝕜 ((fun x => z + c • x) '' s) := by
  have h := (hs.smul c).add_left z
  rwa [← image_smul, image_image] at h

/-- Alternative definition of set strict_convexity, using division. -/
theorem strict_convex_iff_div :
    StrictConvex 𝕜 s ↔
      s.Pairwise fun x y => ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → (a / (a + b)) • x + (b / (a + b)) • y ∈ Interior s :=
  ⟨fun h x hx y hy hxy a b ha hb => by
    apply h hx hy hxy (div_pos ha <| add_pos ha hb) (div_pos hb <| add_pos ha hb)
    rw [← add_div]
    exact div_self (add_pos ha hb).ne', fun h x hx y hy hxy a b ha hb hab => by
    convert h hx hy hxy ha hb <;> rw [hab, div_one]⟩

theorem StrictConvex.mem_smul_of_zero_mem (hs : StrictConvex 𝕜 s) (zero_mem : (0 : E) ∈ s) (hx : x ∈ s) (hx₀ : x ≠ 0)
    {t : 𝕜} (ht : 1 < t) : x ∈ t • Interior s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans ht).ne']
  exact hs.smul_mem_of_zero_mem zero_mem hx hx₀ (inv_pos.2 <| zero_lt_one.trans ht) (inv_lt_one ht)

end AddCommGroupₓ

end LinearOrderedField

/-!
#### Convex sets in an ordered space

Relates `convex` and `set.ord_connected`.
-/


section

variable [TopologicalSpace E]

/-- A set in a linear ordered field is strictly convex if and only if it is convex. -/
@[simp]
theorem strict_convex_iff_convex [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {s : Set 𝕜} :
    StrictConvex 𝕜 s ↔ Convex 𝕜 s := by
  refine' ⟨StrictConvex.convex, fun hs => strict_convex_iff_open_segment_subset.2 fun x hx y hy hxy => _⟩
  obtain h | h := hxy.lt_or_lt
  · refine' (open_segment_subset_Ioo h).trans _
    rw [← interior_Icc]
    exact interior_mono (Icc_subset_segment.trans <| hs.segment_subset hx hy)
    
  · rw [open_segment_symm]
    refine' (open_segment_subset_Ioo h).trans _
    rw [← interior_Icc]
    exact interior_mono (Icc_subset_segment.trans <| hs.segment_subset hy hx)
    

theorem strict_convex_iff_ord_connected [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {s : Set 𝕜} :
    StrictConvex 𝕜 s ↔ s.OrdConnected :=
  strict_convex_iff_convex.trans convex_iff_ord_connected

alias strict_convex_iff_ord_connected ↔ StrictConvex.ord_connected _

end

