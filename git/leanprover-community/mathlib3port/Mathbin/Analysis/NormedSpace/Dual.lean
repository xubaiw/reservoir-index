/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathbin.Analysis.NormedSpace.HahnBanach
import Mathbin.Analysis.NormedSpace.IsROrC

/-!
# The topological dual of a normed space

In this file we define the topological dual `normed_space.dual` of a normed space, and the
continuous linear map `normed_space.inclusion_in_double_dual` from a normed space into its double
dual.

For base field `𝕜 = ℝ` or `𝕜 = ℂ`, this map is actually an isometric embedding; we provide a
version `normed_space.inclusion_in_double_dual_li` of the map which is of type a bundled linear
isometric embedding, `E →ₗᵢ[𝕜] (dual 𝕜 (dual 𝕜 E))`.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `semi_normed_group` and we specialize to `normed_group` when needed.

## Main definitions

* `inclusion_in_double_dual` and `inclusion_in_double_dual_li` are the inclusion of a normed space
  in its double dual, considered as a bounded linear map and as a linear isometry, respectively.
* `polar 𝕜 s` is the subset of `dual 𝕜 E` consisting of those functionals `x'` for which
  `∥x' z∥ ≤ 1` for every `z ∈ s`.

## Tags

dual
-/


noncomputable section

open_locale Classical TopologicalSpace

universe u v

namespace NormedSpace

section General

variable (𝕜 : Type _) [NondiscreteNormedField 𝕜]

variable (E : Type _) [SemiNormedGroup E] [NormedSpace 𝕜 E]

variable (F : Type _) [NormedGroup F] [NormedSpace 𝕜 F]

-- ././Mathport/Syntax/Translate/Basic.lean:980:9: unsupported derive handler normed_space 𝕜
/-- The topological dual of a seminormed space `E`. -/
def Dual :=
  E →L[𝕜] 𝕜 deriving Inhabited, SemiNormedGroup, [anonymous]

instance : AddMonoidHomClass (Dual 𝕜 E) E 𝕜 :=
  ContinuousLinearMap.addMonoidHomClass

instance : CoeFun (Dual 𝕜 E) fun _ => E → 𝕜 :=
  ContinuousLinearMap.toFun

instance : NormedGroup (Dual 𝕜 F) :=
  ContinuousLinearMap.toNormedGroup

instance [FiniteDimensional 𝕜 E] : FiniteDimensional 𝕜 (Dual 𝕜 E) :=
  ContinuousLinearMap.finite_dimensional

/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusionInDoubleDual : E →L[𝕜] Dual 𝕜 (Dual 𝕜 E) :=
  ContinuousLinearMap.apply 𝕜 𝕜

@[simp]
theorem dual_def (x : E) (f : Dual 𝕜 E) : inclusionInDoubleDual 𝕜 E x f = f x :=
  rfl

theorem inclusion_in_double_dual_norm_eq : ∥inclusionInDoubleDual 𝕜 E∥ = ∥ContinuousLinearMap.id 𝕜 (Dual 𝕜 E)∥ :=
  ContinuousLinearMap.op_norm_flip _

theorem inclusion_in_double_dual_norm_le : ∥inclusionInDoubleDual 𝕜 E∥ ≤ 1 := by
  rw [inclusion_in_double_dual_norm_eq]
  exact ContinuousLinearMap.norm_id_le

theorem double_dual_bound (x : E) : ∥(inclusionInDoubleDual 𝕜 E) x∥ ≤ ∥x∥ := by
  simpa using ContinuousLinearMap.le_of_op_norm_le _ (inclusion_in_double_dual_norm_le 𝕜 E) x

end General

section BidualIsometry

variable (𝕜 : Type v) [IsROrC 𝕜] {E : Type u} [NormedGroup E] [NormedSpace 𝕜 E]

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
    Compare `continuous_linear_map.op_norm_le_bound`. -/
theorem norm_le_dual_bound (x : E) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ f : Dual 𝕜 E, ∥f x∥ ≤ M * ∥f∥) : ∥x∥ ≤ M := by
  classical
  by_cases' h : x = 0
  · simp only [h, hMp, norm_zero]
    
  · obtain ⟨f, hf₁, hfx⟩ : ∃ f : E →L[𝕜] 𝕜, ∥f∥ = 1 ∧ f x = ∥x∥ := exists_dual_vector 𝕜 x h
    calc ∥x∥ = ∥(∥x∥ : 𝕜)∥ := is_R_or_C.norm_coe_norm.symm _ = ∥f x∥ := by
        rw [hfx]_ ≤ M * ∥f∥ := hM f _ = M := by
        rw [hf₁, mul_oneₓ]
    

theorem eq_zero_of_forall_dual_eq_zero {x : E} (h : ∀ f : Dual 𝕜 E, f x = (0 : 𝕜)) : x = 0 :=
  norm_le_zero_iff.mp
    (norm_le_dual_bound 𝕜 x le_rfl fun f => by
      simp [h f])

theorem eq_zero_iff_forall_dual_eq_zero (x : E) : x = 0 ↔ ∀ g : Dual 𝕜 E, g x = 0 :=
  ⟨fun hx => by
    simp [hx], fun h => eq_zero_of_forall_dual_eq_zero 𝕜 h⟩

theorem eq_iff_forall_dual_eq {x y : E} : x = y ↔ ∀ g : Dual 𝕜 E, g x = g y := by
  rw [← sub_eq_zero, eq_zero_iff_forall_dual_eq_zero 𝕜 (x - y)]
  simp [sub_eq_zero]

/-- The inclusion of a normed space in its double dual is an isometry onto its image.-/
def inclusionInDoubleDualLi : E →ₗᵢ[𝕜] Dual 𝕜 (Dual 𝕜 E) :=
  { inclusionInDoubleDual 𝕜 E with
    norm_map' := by
      intro x
      apply le_antisymmₓ
      · exact double_dual_bound 𝕜 E x
        
      rw [ContinuousLinearMap.norm_def]
      refine' le_cInf ContinuousLinearMap.bounds_nonempty _
      rintro c ⟨hc1, hc2⟩
      exact norm_le_dual_bound 𝕜 x hc1 hc2 }

end BidualIsometry

end NormedSpace

section PolarSets

open Metric Set NormedSpace

/-- Given a subset `s` in a normed space `E` (over a field `𝕜`), the polar
`polar 𝕜 s` is the subset of `dual 𝕜 E` consisting of those functionals which
evaluate to something of norm at most one at all points `z ∈ s`. -/
def Polar (𝕜 : Type _) [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] (s : Set E) :
    Set (Dual 𝕜 E) :=
  { x' : Dual 𝕜 E | ∀, ∀ z ∈ s, ∀, ∥x' z∥ ≤ 1 }

variable (𝕜 : Type _) [NondiscreteNormedField 𝕜]

variable {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]

@[simp]
theorem zero_mem_polar (s : Set E) : (0 : Dual 𝕜 E) ∈ Polar 𝕜 s := fun _ _ => by
  simp only [zero_le_one, ContinuousLinearMap.zero_apply, norm_zero]

theorem polar_eq_Inter (s : Set E) : Polar 𝕜 s = ⋂ z ∈ s, { x' : Dual 𝕜 E | ∥x' z∥ ≤ 1 } := by
  simp only [Polar, set_of_forall]

@[simp]
theorem polar_univ : Polar 𝕜 (Univ : Set E) = {(0 : dual 𝕜 E)} := by
  refine' eq_singleton_iff_unique_mem.2 ⟨zero_mem_polar _ _, fun x' hx' => _⟩
  ext x
  refine' norm_le_zero_iff.1 (le_of_forall_le_of_dense fun ε hε => _)
  rcases NormedField.exists_norm_lt 𝕜 hε with ⟨c, hc, hcε⟩
  calc ∥x' x∥ = ∥c∥ * ∥x' (c⁻¹ • x)∥ := by
      rw [x'.map_smul, norm_smul, norm_inv, mul_inv_cancel_left₀ hc.ne']_ ≤ ε * 1 :=
      mul_le_mul hcε.le (hx' _ trivialₓ) (norm_nonneg _) hε.le _ = ε := mul_oneₓ _

theorem is_closed_polar (s : Set E) : IsClosed (Polar 𝕜 s) := by
  simp only [polar_eq_Inter, ← ContinuousLinearMap.apply_apply _ (_ : dual 𝕜 E)]
  refine' is_closed_bInter fun z hz => _
  exact is_closed_Iic.preimage (ContinuousLinearMap.apply 𝕜 𝕜 z).Continuous.norm

variable (E)

/-- `polar 𝕜 : set E → set (normed_space.dual 𝕜 E)` forms an order-reversing Galois connection with
a similarly defined map `set (normed_space.dual 𝕜 E) → set E`. We use `order_dual.to_dual` and
`order_dual.of_dual` to express that `polar` is order-reversing. Instead of defining the dual
operation `unpolar s := {x : E | ∀ x' ∈ s, ∥x' x∥ ≤ 1}` we apply `polar 𝕜` again, then pull the set
from the double dual space to the original space using `normed_space.inclusion_in_double_dual`. -/
theorem polar_gc :
    GaloisConnection (OrderDual.toDual ∘ Polar 𝕜) fun s =>
      inclusionInDoubleDual 𝕜 E ⁻¹' (Polar 𝕜 <| OrderDual.ofDual s) :=
  fun s t => ⟨fun H x hx x' hx' => H hx' x hx, fun H x' hx' x hx => H hx x' hx'⟩

variable {E}

@[simp]
theorem polar_Union {ι} (s : ι → Set E) : Polar 𝕜 (⋃ i, s i) = ⋂ i, Polar 𝕜 (s i) :=
  (polar_gc 𝕜 E).l_supr

@[simp]
theorem polar_union (s t : Set E) : Polar 𝕜 (s ∪ t) = Polar 𝕜 s ∩ Polar 𝕜 t :=
  (polar_gc 𝕜 E).l_sup

theorem polar_antitone : Antitone (Polar 𝕜 : Set E → Set (Dual 𝕜 E)) :=
  (polar_gc 𝕜 E).monotone_l

@[simp]
theorem polar_empty : Polar 𝕜 (∅ : Set E) = univ :=
  (polar_gc 𝕜 E).l_bot

@[simp]
theorem polar_zero : Polar 𝕜 ({0} : Set E) = univ :=
  eq_univ_of_forall fun x' =>
    forall_eq.2 <| by
      rw [map_zero, norm_zero]
      exact zero_le_one

@[simp]
theorem polar_closure (s : Set E) : Polar 𝕜 (Closure s) = Polar 𝕜 s :=
  (polar_antitone 𝕜 subset_closure).antisymm <|
    (polar_gc 𝕜 E).l_le <|
      closure_minimal ((polar_gc 𝕜 E).le_u_l s) <| (is_closed_polar _ _).Preimage (inclusionInDoubleDual 𝕜 E).Continuous

variable {𝕜}

/-- If `x'` is a dual element such that the norms `∥x' z∥` are bounded for `z ∈ s`, then a
small scalar multiple of `x'` is in `polar 𝕜 s`. -/
theorem smul_mem_polar {s : Set E} {x' : Dual 𝕜 E} {c : 𝕜} (hc : ∀ z, z ∈ s → ∥x' z∥ ≤ ∥c∥) : c⁻¹ • x' ∈ Polar 𝕜 s := by
  by_cases' c_zero : c = 0
  · simp [c_zero]
    
  have eq : ∀ z, ∥c⁻¹ • x' z∥ = ∥c⁻¹∥ * ∥x' z∥ := fun z => norm_smul c⁻¹ _
  have le : ∀ z, z ∈ s → ∥c⁻¹ • x' z∥ ≤ ∥c⁻¹∥ * ∥c∥ := by
    intro z hzs
    rw [Eq z]
    apply mul_le_mul (le_of_eqₓ rfl) (hc z hzs) (norm_nonneg _) (norm_nonneg _)
  have cancel : ∥c⁻¹∥ * ∥c∥ = 1 := by
    simp only [c_zero, norm_eq_zero, Ne.def, not_false_iff, inv_mul_cancel, norm_inv]
  rwa [cancel] at le

theorem polar_ball_subset_closed_ball_div {c : 𝕜} (hc : 1 < ∥c∥) {r : ℝ} (hr : 0 < r) :
    Polar 𝕜 (Ball (0 : E) r) ⊆ ClosedBall (0 : Dual 𝕜 E) (∥c∥ / r) := by
  intro x' hx'
  simp only [Polar, mem_set_of_eq, mem_closed_ball_zero_iff, mem_ball_zero_iff] at *
  have hcr : 0 < ∥c∥ / r := div_pos (zero_lt_one.trans hc) hr
  refine' ContinuousLinearMap.op_norm_le_of_shell hr hcr.le hc fun x h₁ h₂ => _
  calc ∥x' x∥ ≤ 1 := hx' _ h₂ _ ≤ ∥c∥ / r * ∥x∥ :=
      (inv_pos_le_iff_one_le_mul' hcr).1
        (by
          rwa [inv_div])

variable (𝕜)

theorem closed_ball_inv_subset_polar_closed_ball {r : ℝ} :
    ClosedBall (0 : Dual 𝕜 E) r⁻¹ ⊆ Polar 𝕜 (ClosedBall (0 : E) r) := fun x' hx' x hx =>
  calc
    ∥x' x∥ ≤ ∥x'∥ * ∥x∥ := x'.le_op_norm x
    _ ≤ r⁻¹ * r :=
      mul_le_mul (mem_closed_ball_zero_iff.1 hx') (mem_closed_ball_zero_iff.1 hx) (norm_nonneg _)
        (dist_nonneg.trans hx')
    _ = r / r := div_eq_inv_mul.symm
    _ ≤ 1 := div_self_le_one r
    

/-- The `polar` of closed ball in a normed space `E` is the closed ball of the dual with
inverse radius. -/
theorem polar_closed_ball {𝕜 : Type _} [IsROrC 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {r : ℝ} (hr : 0 < r) :
    Polar 𝕜 (ClosedBall (0 : E) r) = ClosedBall (0 : Dual 𝕜 E) r⁻¹ := by
  refine' subset.antisymm _ (closed_ball_inv_subset_polar_closed_ball _)
  intro x' h
  simp only [mem_closed_ball_zero_iff]
  refine' ContinuousLinearMap.op_norm_le_of_ball hr (inv_nonneg.mpr hr.le) fun z hz => _
  simpa only [one_div] using LinearMap.bound_of_ball_bound' hr 1 x'.to_linear_map h z

/-- Given a neighborhood `s` of the origin in a normed space `E`, the dual norms
of all elements of the polar `polar 𝕜 s` are bounded by a constant. -/
theorem bounded_polar_of_mem_nhds_zero {s : Set E} (s_nhd : s ∈ 𝓝 (0 : E)) : Bounded (Polar 𝕜 s) := by
  obtain ⟨a, ha⟩ : ∃ a : 𝕜, 1 < ∥a∥ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨r, r_pos, r_ball⟩ : ∃ (r : ℝ)(hr : 0 < r), ball 0 r ⊆ s := Metric.mem_nhds_iff.1 s_nhd
  exact bounded_closed_ball.mono ((polar_antitone 𝕜 r_ball).trans <| polar_ball_subset_closed_ball_div ha r_pos)

end PolarSets

