/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Bhavik Mehta, Yaël Dillies
-/
import Mathbin.Analysis.NormedSpace.Basic

/-!
# Local convexity

This file defines absorbent and balanced sets.

An absorbent set is one that "surrounds" the origin. The idea is made precise by requiring that any
point belongs to all large enough scalings of the set. This is the vector world analog of a
topological neighborhood of the origin.

A balanced set is one that is everywhere around the origin. This means that `a • s ⊆ s` for all `a`
of norm less than `1`.

## Main declarations

For a module over a normed ring:
* `absorbs`: A set `s` absorbs a set `t` if all large scalings of `s` contain `t`.
* `absorbent`: A set `s` is absorbent if every point eventually belongs to all large scalings of
  `s`.
* `balanced`: A set `s` is balanced if `a • s ⊆ s` for all `a` of norm less than `1`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

absorbent, balanced, locally convex, LCTVS
-/


open Set

open Pointwise TopologicalSpace

variable {𝕜 𝕝 E ι : Type _}

section SemiNormedRing

variable [SemiNormedRing 𝕜]

section HasScalar

variable (𝕜) [HasScalar 𝕜 E]

/-- A set `A` absorbs another set `B` if `B` is contained in all scalings of `A` by elements of
sufficiently large norm. -/
def Absorbs (A B : Set E) :=
  ∃ r, 0 < r ∧ ∀ a : 𝕜, r ≤ ∥a∥ → B ⊆ a • A

variable {𝕜} {s t u v A B : Set E}

@[simp]
theorem absorbs_empty {s : Set E} : Absorbs 𝕜 s (∅ : Set E) :=
  ⟨1, one_pos, fun a ha => Set.empty_subset _⟩

theorem Absorbs.mono (hs : Absorbs 𝕜 s u) (hst : s ⊆ t) (hvu : v ⊆ u) : Absorbs 𝕜 t v :=
  let ⟨r, hr, h⟩ := hs
  ⟨r, hr, fun a ha => hvu.trans <| (h _ ha).trans <| smul_set_mono hst⟩

theorem Absorbs.mono_left (hs : Absorbs 𝕜 s u) (h : s ⊆ t) : Absorbs 𝕜 t u :=
  hs.mono h Subset.rfl

theorem Absorbs.mono_right (hs : Absorbs 𝕜 s u) (h : v ⊆ u) : Absorbs 𝕜 s v :=
  hs.mono Subset.rfl h

theorem Absorbs.union (hu : Absorbs 𝕜 s u) (hv : Absorbs 𝕜 s v) : Absorbs 𝕜 s (u ∪ v) := by
  obtain ⟨a, ha, hu⟩ := hu
  obtain ⟨b, hb, hv⟩ := hv
  exact
    ⟨max a b, lt_max_of_lt_left ha, fun c hc =>
      union_subset (hu _ <| le_of_max_le_left hc) (hv _ <| le_of_max_le_right hc)⟩

@[simp]
theorem absorbs_union : Absorbs 𝕜 s (u ∪ v) ↔ Absorbs 𝕜 s u ∧ Absorbs 𝕜 s v :=
  ⟨fun h => ⟨h.mono_right <| subset_union_left _ _, h.mono_right <| subset_union_right _ _⟩, fun h => h.1.union h.2⟩

theorem absorbs_Union_finset {s : Set E} {t : Finset ι} {f : ι → Set E} :
    Absorbs 𝕜 s (⋃ i ∈ t, f i) ↔ ∀, ∀ i ∈ t, ∀, Absorbs 𝕜 s (f i) := by
  classical
  induction' t using Finset.induction_on with i t ht hi
  · simp only [Finset.not_mem_empty, Set.Union_false, Set.Union_empty, absorbs_empty, forall_false_left,
      implies_true_iff]
    
  rw [Finset.set_bUnion_insert, absorbs_union, hi]
  constructor <;> intro h
  · refine' fun _ hi' => (finset.mem_insert.mp hi').elim _ (h.2 _)
    exact fun hi'' => by
      rw [hi'']
      exact h.1
    
  exact ⟨h i (Finset.mem_insert_self i t), fun i' hi' => h i' (Finset.mem_insert_of_mem hi')⟩

theorem Set.Finite.absorbs_Union {s : Set E} {t : Set ι} {f : ι → Set E} (hi : t.Finite) :
    Absorbs 𝕜 s (⋃ (i : ι) (hy : i ∈ t), f i) ↔ ∀, ∀ i ∈ t, ∀, Absorbs 𝕜 s (f i) := by
  lift t to Finset ι using hi
  simp only [Finset.mem_coe]
  exact absorbs_Union_finset

variable (𝕜)

/-- A set is absorbent if it absorbs every singleton. -/
def Absorbent (A : Set E) :=
  ∀ x, ∃ r, 0 < r ∧ ∀ a : 𝕜, r ≤ ∥a∥ → x ∈ a • A

variable {𝕜}

theorem Absorbent.subset (hA : Absorbent 𝕜 A) (hAB : A ⊆ B) : Absorbent 𝕜 B := by
  refine' forall_imp (fun x => _) hA
  exact Exists.imp fun r => And.imp_right <| forall₂_imp fun a ha hx => Set.smul_set_mono hAB hx

theorem absorbent_iff_forall_absorbs_singleton : Absorbent 𝕜 A ↔ ∀ x, Absorbs 𝕜 A {x} := by
  simp_rw [Absorbs, Absorbent, singleton_subset_iff]

theorem Absorbent.absorbs (hs : Absorbent 𝕜 s) {x : E} : Absorbs 𝕜 s {x} :=
  absorbent_iff_forall_absorbs_singleton.1 hs _

theorem absorbent_iff_nonneg_lt : Absorbent 𝕜 A ↔ ∀ x, ∃ r, 0 ≤ r ∧ ∀ ⦃a : 𝕜⦄, r < ∥a∥ → x ∈ a • A :=
  forall_congrₓ fun x =>
    ⟨fun ⟨r, hr, hx⟩ => ⟨r, hr.le, fun a ha => hx a ha.le⟩, fun ⟨r, hr, hx⟩ =>
      ⟨r + 1, add_pos_of_nonneg_of_pos hr zero_lt_one, fun a ha =>
        hx ((lt_add_of_pos_right r zero_lt_one).trans_le ha)⟩⟩

theorem Absorbent.absorbs_finite {s : Set E} (hs : Absorbent 𝕜 s) {v : Set E} (hv : v.Finite) : Absorbs 𝕜 s v := by
  rw [← Set.bUnion_of_singleton v]
  exact hv.absorbs_Union.mpr fun _ _ => hs.absorbs

variable (𝕜)

/-- A set `A` is balanced if `a • A` is contained in `A` whenever `a` has norm at most `1`. -/
def Balanced (A : Set E) :=
  ∀ a : 𝕜, ∥a∥ ≤ 1 → a • A ⊆ A

variable {𝕜}

theorem balanced_mem {s : Set E} (hs : Balanced 𝕜 s) {x : E} (hx : x ∈ s) {a : 𝕜} (ha : ∥a∥ ≤ 1) : a • x ∈ s :=
  mem_of_subset_of_mem (hs a ha) (smul_mem_smul_set hx)

theorem balanced_univ : Balanced 𝕜 (Univ : Set E) := fun a ha => subset_univ _

theorem Balanced.union (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A ∪ B) := by
  intro a ha t ht
  rw [smul_set_union] at ht
  exact ht.imp (fun x => hA _ ha x) fun x => hB _ ha x

theorem Balanced.inter (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A ∩ B) := by
  rintro a ha _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
  exact ⟨hA _ ha ⟨_, hx₁, rfl⟩, hB _ ha ⟨_, hx₂, rfl⟩⟩

end HasScalar

section AddCommMonoidₓ

variable [AddCommMonoidₓ E] [Module 𝕜 E] {s s' t t' u v A B : Set E}

theorem Absorbs.add (h : Absorbs 𝕜 s t) (h' : Absorbs 𝕜 s' t') : Absorbs 𝕜 (s + s') (t + t') := by
  rcases h with ⟨r, hr, h⟩
  rcases h' with ⟨r', hr', h'⟩
  refine' ⟨max r r', lt_max_of_lt_left hr, fun a ha => _⟩
  rw [smul_add]
  exact Set.add_subset_add (h a (le_of_max_le_left ha)) (h' a (le_of_max_le_right ha))

theorem Balanced.add (hA₁ : Balanced 𝕜 A) (hA₂ : Balanced 𝕜 B) : Balanced 𝕜 (A + B) := by
  rintro a ha _ ⟨_, ⟨x, y, hx, hy, rfl⟩, rfl⟩
  rw [smul_add]
  exact add_mem_add (hA₁ _ ha ⟨_, hx, rfl⟩) (hA₂ _ ha ⟨_, hy, rfl⟩)

theorem zero_singleton_balanced : Balanced 𝕜 ({0} : Set E) := fun a ha => by
  simp only [smul_set_singleton, smul_zero]

end AddCommMonoidₓ

end SemiNormedRing

section NormedCommRing

variable [NormedCommRing 𝕜] [AddCommMonoidₓ E] [Module 𝕜 E] {A B : Set E} (a : 𝕜)

theorem Balanced.smul (hA : Balanced 𝕜 A) : Balanced 𝕜 (a • A) := by
  rintro b hb _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨b • x, hA _ hb ⟨_, hx, rfl⟩, smul_comm _ _ _⟩

end NormedCommRing

section NormedField

variable [NormedField 𝕜] [NormedRing 𝕝] [NormedSpace 𝕜 𝕝] [AddCommGroupₓ E] [Module 𝕜 E] [SmulWithZero 𝕝 E]
  [IsScalarTower 𝕜 𝕝 E] {s t u v A B : Set E} {a b : 𝕜}

/-- Scalar multiplication (by possibly different types) of a balanced set is monotone. -/
theorem Balanced.smul_mono (hs : Balanced 𝕝 s) {a : 𝕝} {b : 𝕜} (h : ∥a∥ ≤ ∥b∥) : a • s ⊆ b • s := by
  obtain rfl | hb := eq_or_ne b 0
  · rw [norm_zero] at h
    rw [norm_eq_zero.1 (h.antisymm <| norm_nonneg _)]
    obtain rfl | h := s.eq_empty_or_nonempty
    · simp_rw [smul_set_empty]
      
    · simp_rw [zero_smul_set h]
      
    
  rintro _ ⟨x, hx, rfl⟩
  refine' ⟨b⁻¹ • a • x, _, smul_inv_smul₀ hb _⟩
  rw [← smul_assoc]
  refine' hs _ _ (smul_mem_smul_set hx)
  rw [norm_smul, norm_inv, ← div_eq_inv_mul]
  exact div_le_one_of_le h (norm_nonneg _)

/-- A balanced set absorbs itself. -/
theorem Balanced.absorbs_self (hA : Balanced 𝕜 A) : Absorbs 𝕜 A A := by
  refine' ⟨1, zero_lt_one, fun a ha x hx => _⟩
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.1 <| zero_lt_one.trans_le ha)]
  refine' hA a⁻¹ _ (smul_mem_smul_set hx)
  rw [norm_inv]
  exact inv_le_one ha

theorem Balanced.subset_smul (hA : Balanced 𝕜 A) (ha : 1 ≤ ∥a∥) : A ⊆ a • A := by
  refine' (subset_set_smul_iff₀ _).2 (hA a⁻¹ _)
  · rintro rfl
    rw [norm_zero] at ha
    exact zero_lt_one.not_le ha
    
  · rw [norm_inv]
    exact inv_le_one ha
    

theorem Balanced.smul_eq (hA : Balanced 𝕜 A) (ha : ∥a∥ = 1) : a • A = A :=
  (hA _ ha.le).antisymm <| hA.subset_smul ha.Ge

theorem Absorbs.inter (hs : Absorbs 𝕜 s u) (ht : Absorbs 𝕜 t u) : Absorbs 𝕜 (s ∩ t) u := by
  obtain ⟨a, ha, hs⟩ := hs
  obtain ⟨b, hb, ht⟩ := ht
  have h : 0 < max a b := lt_max_of_lt_left ha
  refine' ⟨max a b, lt_max_of_lt_left ha, fun c hc => _⟩
  rw [smul_set_inter₀ (norm_pos_iff.1 <| h.trans_le hc)]
  exact subset_inter (hs _ <| le_of_max_le_left hc) (ht _ <| le_of_max_le_right hc)

@[simp]
theorem absorbs_inter : Absorbs 𝕜 (s ∩ t) u ↔ Absorbs 𝕜 s u ∧ Absorbs 𝕜 t u :=
  ⟨fun h => ⟨h.mono_left <| inter_subset_left _ _, h.mono_left <| inter_subset_right _ _⟩, fun h => h.1.inter h.2⟩

theorem absorbent_univ : Absorbent 𝕜 (Univ : Set E) := by
  refine' fun x => ⟨1, zero_lt_one, fun a ha => _⟩
  rw [smul_set_univ₀ (norm_pos_iff.1 <| zero_lt_one.trans_le ha)]
  exact trivialₓ

variable [TopologicalSpace E] [HasContinuousSmul 𝕜 E]

/-- Every neighbourhood of the origin is absorbent. -/
theorem absorbent_nhds_zero (hA : A ∈ 𝓝 (0 : E)) : Absorbent 𝕜 A := by
  intro x
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := mem_nhds_iff.mp hA
  have hc : Continuous fun t : 𝕜 => t • x := continuous_id.smul continuous_const
  obtain ⟨r, hr₁, hr₂⟩ :=
    metric.is_open_iff.mp (hw₂.preimage hc) 0
      (by
        rwa [mem_preimage, zero_smul])
  have hr₃ := inv_pos.mpr (half_pos hr₁)
  refine' ⟨(r / 2)⁻¹, hr₃, fun a ha₁ => _⟩
  have ha₂ : 0 < ∥a∥ := hr₃.trans_le ha₁
  refine' (mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp ha₂) _ _).2 (hw₁ <| hr₂ _)
  rw [Metric.mem_ball, dist_zero_right, norm_inv]
  calc ∥a∥⁻¹ ≤ r / 2 := (inv_le (half_pos hr₁) ha₂).mp ha₁ _ < r := half_lt_self hr₁

/-- The union of `{0}` with the interior of a balanced set is balanced. -/
theorem balanced_zero_union_interior (hA : Balanced 𝕜 A) : Balanced 𝕜 ((0 : Set E) ∪ Interior A) := by
  intro a ha
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_smul_set]
    exacts[subset_union_left _ _, ⟨0, Or.inl rfl⟩]
    
  · rw [← image_smul, image_union]
    apply union_subset_union
    · rw [image_zero, smul_zero]
      rfl
      
    · calc a • Interior A ⊆ Interior (a • A) := (is_open_map_smul₀ h).image_interior_subset A _ ⊆ Interior A :=
          interior_mono (hA _ ha)
      
    

/-- The interior of a balanced set is balanced if it contains the origin. -/
theorem Balanced.interior (hA : Balanced 𝕜 A) (h : (0 : E) ∈ Interior A) : Balanced 𝕜 (Interior A) := by
  rw [← union_eq_self_of_subset_left (singleton_subset_iff.2 h)]
  exact balanced_zero_union_interior hA

theorem Balanced.closure (hA : Balanced 𝕜 A) : Balanced 𝕜 (Closure A) := fun a ha =>
  (image_closure_subset_closure_image <| continuous_id.const_smul _).trans <| closure_mono <| hA _ ha

end NormedField

section NondiscreteNormedField

variable [NondiscreteNormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] {s : Set E}

theorem absorbs_zero_iff : Absorbs 𝕜 s 0 ↔ (0 : E) ∈ s := by
  refine' ⟨_, fun h => ⟨1, zero_lt_one, fun a _ => zero_subset.2 <| zero_mem_smul_set h⟩⟩
  rintro ⟨r, hr, h⟩
  obtain ⟨a, ha⟩ := NormedSpace.exists_lt_norm 𝕜 𝕜 r
  have := h _ ha.le
  rwa [zero_subset, zero_mem_smul_set_iff] at this
  exact norm_ne_zero_iff.1 (hr.trans ha).ne'

theorem Absorbent.zero_mem (hs : Absorbent 𝕜 s) : (0 : E) ∈ s :=
  absorbs_zero_iff.1 <| absorbent_iff_forall_absorbs_singleton.1 hs _

end NondiscreteNormedField

