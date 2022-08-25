/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.MeasureTheory.Integral.SetIntegral

/-! # `L^2` space

If `E` is an inner product space over `𝕜` (`ℝ` or `ℂ`), then `Lp E 2 μ` (defined in `lp_space.lean`)
is also an inner product space, with inner product defined as `inner f g = ∫ a, ⟪f a, g a⟫ ∂μ`.

### Main results

* `mem_L1_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `λ x, ⟪f x, g x⟫`
  belongs to `Lp 𝕜 1 μ`.
* `integrable_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `λ x, ⟪f x, g x⟫`
  is integrable.
* `L2.inner_product_space` : `Lp E 2 μ` is an inner product space.

-/


noncomputable section

open TopologicalSpace MeasureTheory MeasureTheory.lp

open Nnreal Ennreal MeasureTheory

namespace MeasureTheory

section

variable {α F : Type _} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup F]

theorem Memℒp.integrable_sq {f : α → ℝ} (h : Memℒp f 2 μ) : Integrable (fun x => f x ^ 2) μ := by
  simpa [← mem_ℒp_one_iff_integrable] using h.norm_rpow Ennreal.two_ne_zero Ennreal.two_ne_top

theorem mem_ℒp_two_iff_integrable_sq_norm {f : α → F} (hf : AeStronglyMeasurable f μ) :
    Memℒp f 2 μ ↔ Integrable (fun x => ∥f x∥ ^ 2) μ := by
  rw [← mem_ℒp_one_iff_integrable]
  convert (mem_ℒp_norm_rpow_iff hf Ennreal.two_ne_zero Ennreal.two_ne_top).symm
  · simp
    
  · rw [div_eq_mul_inv, Ennreal.mul_inv_cancel Ennreal.two_ne_zero Ennreal.two_ne_top]
    

theorem mem_ℒp_two_iff_integrable_sq {f : α → ℝ} (hf : AeStronglyMeasurable f μ) :
    Memℒp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ := by
  convert mem_ℒp_two_iff_integrable_sq_norm hf
  ext x
  simp

end

namespace L2

variable {α E F 𝕜 : Type _} [IsROrC 𝕜] [MeasurableSpace α] {μ : Measure α} [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

theorem snorm_rpow_two_norm_lt_top (f : lp F 2 μ) : snorm (fun x => ∥f x∥ ^ (2 : ℝ)) 1 μ < ∞ := by
  have h_two : Ennreal.ofReal (2 : ℝ) = 2 := by
    simp [zero_le_one]
  rw [snorm_norm_rpow f zero_lt_two, one_mulₓ, h_two]
  exact Ennreal.rpow_lt_top_of_nonneg zero_le_two (Lp.snorm_ne_top f)

theorem snorm_inner_lt_top (f g : α →₂[μ] E) : snorm (fun x : α => ⟪f x, g x⟫) 1 μ < ∞ := by
  have h : ∀ x, IsROrC.abs ⟪f x, g x⟫ ≤ ∥f x∥ * ∥g x∥ := fun x => abs_inner_le_norm _ _
  have h' : ∀ x, IsROrC.abs ⟪f x, g x⟫ ≤ IsROrC.abs (∥f x∥ ^ 2 + ∥g x∥ ^ 2) := by
    refine' fun x => le_transₓ (h x) _
    rw [IsROrC.abs_to_real, abs_eq_self.mpr]
    swap
    · exact
        add_nonneg
          (by
            simp )
          (by
            simp )
      
    refine' le_transₓ _ (half_le_self (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    refine' (le_div_iff (@zero_lt_two ℝ _ _)).mpr ((le_of_eqₓ _).trans (two_mul_le_add_sq _ _))
    ring
  simp_rw [← IsROrC.norm_eq_abs, ← Real.rpow_nat_cast] at h'
  refine' (snorm_mono_ae (ae_of_all _ h')).trans_lt ((snorm_add_le _ _ le_rflₓ).trans_lt _)
  · exact ((Lp.ae_strongly_measurable f).norm.AeMeasurable.pow_const _).AeStronglyMeasurable
    
  · exact ((Lp.ae_strongly_measurable g).norm.AeMeasurable.pow_const _).AeStronglyMeasurable
    
  simp only [Nat.cast_bit0, Ennreal.add_lt_top, Nat.cast_oneₓ]
  exact ⟨snorm_rpow_two_norm_lt_top f, snorm_rpow_two_norm_lt_top g⟩

section InnerProductSpace

open ComplexConjugate

include 𝕜

instance : HasInner 𝕜 (α →₂[μ] E) :=
  ⟨fun f g => ∫ a, ⟪f a, g a⟫ ∂μ⟩

theorem inner_def (f g : α →₂[μ] E) : ⟪f, g⟫ = ∫ a : α, ⟪f a, g a⟫ ∂μ :=
  rfl

theorem integral_inner_eq_sq_snorm (f : α →₂[μ] E) :
    (∫ a, ⟪f a, f a⟫ ∂μ) = Ennreal.toReal (∫⁻ a, (∥f a∥₊ : ℝ≥0∞) ^ (2 : ℝ) ∂μ) := by
  simp_rw [inner_self_eq_norm_sq_to_K]
  norm_cast
  rw [integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact Filter.eventually_of_forall fun x => sq_nonneg _
    
  · exact ((Lp.ae_strongly_measurable f).norm.AeMeasurable.pow_const _).AeStronglyMeasurable
    
  congr
  ext1 x
  have h_two : (2 : ℝ) = ((2 : ℕ) : ℝ) := by
    simp
  rw [← Real.rpow_nat_cast _ 2, ← h_two, ← Ennreal.of_real_rpow_of_nonneg (norm_nonneg _) zero_le_two,
    of_real_norm_eq_coe_nnnorm]
  norm_cast

private theorem norm_sq_eq_inner' (f : α →₂[μ] E) : ∥f∥ ^ 2 = IsROrC.re ⟪f, f⟫ := by
  have h_two : (2 : ℝ≥0∞).toReal = 2 := by
    simp
  rw [inner_def, integral_inner_eq_sq_snorm, norm_def, ← Ennreal.to_real_pow, IsROrC.of_real_re,
    Ennreal.to_real_eq_to_real (Ennreal.pow_ne_top (Lp.snorm_ne_top f)) _]
  · rw [← Ennreal.rpow_nat_cast, snorm_eq_snorm' Ennreal.two_ne_zero Ennreal.two_ne_top, snorm', ← Ennreal.rpow_mul,
      one_div, h_two]
    simp
    
  · refine' (lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top zero_lt_two _).Ne
    rw [← h_two, ← snorm_eq_snorm' Ennreal.two_ne_zero Ennreal.two_ne_top]
    exact Lp.snorm_lt_top f
    

theorem mem_L1_inner (f g : α →₂[μ] E) :
    AeEqFun.mk (fun x => ⟪f x, g x⟫) ((lp.ae_strongly_measurable f).inner (lp.ae_strongly_measurable g)) ∈ lp 𝕜 1 μ :=
  by
  simp_rw [mem_Lp_iff_snorm_lt_top, snorm_ae_eq_fun]
  exact snorm_inner_lt_top f g

theorem integrable_inner (f g : α →₂[μ] E) : Integrable (fun x : α => ⟪f x, g x⟫) μ :=
  (integrable_congr
        (AeEqFun.coe_fn_mk (fun x => ⟪f x, g x⟫)
          ((lp.ae_strongly_measurable f).inner (lp.ae_strongly_measurable g)))).mp
    (AeEqFun.integrable_iff_mem_L1.mpr (mem_L1_inner f g))

private theorem add_left' (f f' g : α →₂[μ] E) : ⟪f + f', g⟫ = inner f g + inner f' g := by
  simp_rw [inner_def, ← integral_add (integrable_inner f g) (integrable_inner f' g), ← inner_add_left]
  refine' integral_congr_ae ((coe_fn_add f f').mono fun x hx => _)
  congr
  rwa [Pi.add_apply] at hx

private theorem smul_left' (f g : α →₂[μ] E) (r : 𝕜) : ⟪r • f, g⟫ = conj r * inner f g := by
  rw [inner_def, inner_def, ← smul_eq_mul, ← integral_smul]
  refine' integral_congr_ae ((coe_fn_smul r f).mono fun x hx => _)
  rw [smul_eq_mul, ← inner_smul_left]
  congr
  rwa [Pi.smul_apply] at hx

instance innerProductSpace : InnerProductSpace 𝕜 (α →₂[μ] E) where
  norm_sq_eq_inner := norm_sq_eq_inner'
  conj_sym := fun _ _ => by
    simp_rw [inner_def, ← integral_conj, inner_conj_sym]
  add_left := add_left'
  smul_left := smul_left'

end InnerProductSpace

section IndicatorConstLp

variable (𝕜) {s : Set α}

/-- The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs c` and `f` is
equal to the integral of the inner product over `s`: `∫ x in s, ⟪c, f x⟫ ∂μ`. -/
theorem inner_indicator_const_Lp_eq_set_integral_inner (f : lp E 2 μ) (hs : MeasurableSet s) (c : E) (hμs : μ s ≠ ∞) :
    (⟪indicatorConstLp 2 hs hμs c, f⟫ : 𝕜) = ∫ x in s, ⟪c, f x⟫ ∂μ := by
  rw [inner_def, ← integral_add_compl hs (L2.integrable_inner _ f)]
  have h_left : (∫ x in s, ⟪(indicator_const_Lp 2 hs hμs c) x, f x⟫ ∂μ) = ∫ x in s, ⟪c, f x⟫ ∂μ := by
    suffices h_ae_eq : ∀ᵐ x ∂μ, x ∈ s → ⟪indicator_const_Lp 2 hs hμs c x, f x⟫ = ⟪c, f x⟫
    exact set_integral_congr_ae hs h_ae_eq
    have h_indicator : ∀ᵐ x : α ∂μ, x ∈ s → indicator_const_Lp 2 hs hμs c x = c := indicator_const_Lp_coe_fn_mem
    refine' h_indicator.mono fun x hx hxs => _
    congr
    exact hx hxs
  have h_right : (∫ x in sᶜ, ⟪(indicator_const_Lp 2 hs hμs c) x, f x⟫ ∂μ) = 0 := by
    suffices h_ae_eq : ∀ᵐ x ∂μ, x ∉ s → ⟪indicator_const_Lp 2 hs hμs c x, f x⟫ = 0
    · simp_rw [← Set.mem_compl_iff] at h_ae_eq
      suffices h_int_zero : (∫ x in sᶜ, inner (indicator_const_Lp 2 hs hμs c x) (f x) ∂μ) = ∫ x in sᶜ, (0 : 𝕜) ∂μ
      · rw [h_int_zero]
        simp
        
      exact set_integral_congr_ae hs.compl h_ae_eq
      
    have h_indicator : ∀ᵐ x : α ∂μ, x ∉ s → indicator_const_Lp 2 hs hμs c x = 0 := indicator_const_Lp_coe_fn_nmem
    refine' h_indicator.mono fun x hx hxs => _
    rw [hx hxs]
    exact inner_zero_left
  rw [h_left, h_right, add_zeroₓ]

/-- The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs c` and `f` is
equal to the inner product of the constant `c` and the integral of `f` over `s`. -/
theorem inner_indicator_const_Lp_eq_inner_set_integral [CompleteSpace E] [NormedSpace ℝ E] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : E) (f : lp E 2 μ) : (⟪indicatorConstLp 2 hs hμs c, f⟫ : 𝕜) = ⟪c, ∫ x in s, f x ∂μ⟫ := by
  rw [← integral_inner (integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs),
    L2.inner_indicator_const_Lp_eq_set_integral_inner]

variable {𝕜}

/-- The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs (1 : 𝕜)` and
a real or complex function `f` is equal to the integral of `f` over `s`. -/
theorem inner_indicator_const_Lp_one (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (f : lp 𝕜 2 μ) :
    ⟪indicatorConstLp 2 hs hμs (1 : 𝕜), f⟫ = ∫ x in s, f x ∂μ := by
  rw [L2.inner_indicator_const_Lp_eq_inner_set_integral 𝕜 hs hμs (1 : 𝕜) f]
  simp

end IndicatorConstLp

end L2

section InnerContinuous

variable {α : Type _} [TopologicalSpace α] [MeasureSpace α] [BorelSpace α] {𝕜 : Type _} [IsROrC 𝕜]

variable (μ : Measure α) [IsFiniteMeasure μ]

open BoundedContinuousFunction ComplexConjugate

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 (α →₂[μ] 𝕜) _ x y

/-- For bounded continuous functions `f`, `g` on a finite-measure topological space `α`, the L^2
inner product is the integral of their pointwise inner product. -/
theorem BoundedContinuousFunction.inner_to_Lp (f g : α →ᵇ 𝕜) :
    ⟪BoundedContinuousFunction.toLp 2 μ 𝕜 f, BoundedContinuousFunction.toLp 2 μ 𝕜 g⟫ = ∫ x, conj (f x) * g x ∂μ := by
  apply integral_congr_ae
  have hf_ae := f.coe_fn_to_Lp μ
  have hg_ae := g.coe_fn_to_Lp μ
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf, hg]
  simp

variable [CompactSpace α]

/-- For continuous functions `f`, `g` on a compact, finite-measure topological space `α`, the L^2
inner product is the integral of their pointwise inner product. -/
theorem ContinuousMap.inner_to_Lp (f g : C(α, 𝕜)) :
    ⟪ContinuousMap.toLp 2 μ 𝕜 f, ContinuousMap.toLp 2 μ 𝕜 g⟫ = ∫ x, conj (f x) * g x ∂μ := by
  apply integral_congr_ae
  have hf_ae := f.coe_fn_to_Lp μ
  have hg_ae := g.coe_fn_to_Lp μ
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf, hg]
  simp

end InnerContinuous

end MeasureTheory

