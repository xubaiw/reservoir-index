/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathbin.MeasureTheory.Function.LpSpace

/-!
# Integrable functions and `L¹` space

In the first part of this file, the predicate `integrable` is defined and basic properties of
integrable functions are proved.

Such a predicate is already available under the name `mem_ℒp 1`. We give a direct definition which
is easier to use, and show that it is equivalent to `mem_ℒp 1`

In the second part, we establish an API between `integrable` and the space `L¹` of equivalence
classes of integrable functions, already defined as a special case of `L^p` spaces for `p = 1`.

## Notation

* `α →₁[μ] β` is the type of `L¹` space, where `α` is a `measure_space` and `β` is a `normed_group`
  with a `second_countable_topology`. `f : α →ₘ β` is a "function" in `L¹`. In comments, `[f]` is
  also used to denote an `L¹` function.

  `₁` can be typed as `\1`.

## Main definitions

* Let `f : α → β` be a function, where `α` is a `measure_space` and `β` a `normed_group`.
  Then `has_finite_integral f` means `(∫⁻ a, nnnorm (f a)) < ∞`.

* If `β` is moreover a `measurable_space` then `f` is called `integrable` if
  `f` is `measurable` and `has_finite_integral f` holds.

## Implementation notes

To prove something for an arbitrary integrable function, a useful theorem is
`integrable.induction` in the file `set_integral`.

## Tags

integrable, function space, l1

-/


noncomputable section

open_locale Classical TopologicalSpace BigOperators Ennreal MeasureTheory Nnreal

open Set Filter TopologicalSpace Ennreal Emetric MeasureTheory

variable {α β γ δ : Type _} {m : MeasurableSpace α} {μ ν : Measureₓ α}

variable [NormedGroup β]

variable [NormedGroup γ]

namespace MeasureTheory

/-! ### Some results about the Lebesgue integral involving a normed group -/


theorem lintegral_nnnorm_eq_lintegral_edist (f : α → β) : (∫⁻ a, nnnorm (f a) ∂μ) = ∫⁻ a, edist (f a) 0 ∂μ := by
  simp only [edist_eq_coe_nnnorm]

theorem lintegral_norm_eq_lintegral_edist (f : α → β) : (∫⁻ a, Ennreal.ofReal ∥f a∥ ∂μ) = ∫⁻ a, edist (f a) 0 ∂μ := by
  simp only [of_real_norm_eq_coe_nnnorm, edist_eq_coe_nnnorm]

theorem lintegral_edist_triangle [SecondCountableTopology β] [MeasurableSpace β] [OpensMeasurableSpace β]
    {f g h : α → β} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) (hh : AeMeasurable h μ) :
    (∫⁻ a, edist (f a) (g a) ∂μ) ≤ (∫⁻ a, edist (f a) (h a) ∂μ) + ∫⁻ a, edist (g a) (h a) ∂μ := by
  rw [← lintegral_add' (hf.edist hh) (hg.edist hh)]
  refine' lintegral_mono fun a => _
  apply edist_triangle_right

theorem lintegral_nnnorm_zero : (∫⁻ a : α, nnnorm (0 : β) ∂μ) = 0 := by
  simp

theorem lintegral_nnnorm_add [MeasurableSpace β] [OpensMeasurableSpace β] [MeasurableSpace γ] [OpensMeasurableSpace γ]
    {f : α → β} {g : α → γ} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    (∫⁻ a, nnnorm (f a) + nnnorm (g a) ∂μ) = (∫⁻ a, nnnorm (f a) ∂μ) + ∫⁻ a, nnnorm (g a) ∂μ :=
  lintegral_add' hf.ennnorm hg.ennnorm

theorem lintegral_nnnorm_neg {f : α → β} : (∫⁻ a, nnnorm ((-f) a) ∂μ) = ∫⁻ a, nnnorm (f a) ∂μ := by
  simp only [Pi.neg_apply, nnnorm_neg]

/-! ### The predicate `has_finite_integral` -/


/-- `has_finite_integral f μ` means that the integral `∫⁻ a, ∥f a∥ ∂μ` is finite.
  `has_finite_integral f` means `has_finite_integral f volume`. -/
def HasFiniteIntegral {m : MeasurableSpace α} (f : α → β)
    (μ : Measure α := by
      run_tac
        volume_tac) :
    Prop :=
  (∫⁻ a, nnnorm (f a) ∂μ) < ∞

theorem has_finite_integral_iff_norm (f : α → β) : HasFiniteIntegral f μ ↔ (∫⁻ a, Ennreal.ofReal ∥f a∥ ∂μ) < ∞ := by
  simp only [has_finite_integral, of_real_norm_eq_coe_nnnorm]

theorem has_finite_integral_iff_edist (f : α → β) : HasFiniteIntegral f μ ↔ (∫⁻ a, edist (f a) 0 ∂μ) < ∞ := by
  simp only [has_finite_integral_iff_norm, edist_dist, dist_zero_right]

theorem has_finite_integral_iff_of_real {f : α → ℝ} (h : 0 ≤ᵐ[μ] f) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, Ennreal.ofReal (f a) ∂μ) < ∞ := by
  have lintegral_eq : (∫⁻ a, Ennreal.ofReal ∥f a∥ ∂μ) = ∫⁻ a, Ennreal.ofReal (f a) ∂μ := by
    refine' lintegral_congr_ae (h.mono fun a h => _)
    rwa [Real.norm_eq_abs, abs_of_nonneg]
  rw [has_finite_integral_iff_norm, lintegral_eq]

theorem has_finite_integral_iff_of_nnreal {f : α → ℝ≥0 } :
    HasFiniteIntegral (fun x => (f x : ℝ)) μ ↔ (∫⁻ a, f a ∂μ) < ∞ := by
  simp [has_finite_integral_iff_norm]

theorem HasFiniteIntegral.mono {f : α → β} {g : α → γ} (hg : HasFiniteIntegral g μ) (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ ∥g a∥) :
    HasFiniteIntegral f μ := by
  simp only [has_finite_integral_iff_norm] at *
  calc (∫⁻ a, Ennreal.ofReal ∥f a∥ ∂μ) ≤ ∫⁻ a : α, Ennreal.ofReal ∥g a∥ ∂μ :=
      lintegral_mono_ae (h.mono fun a h => of_real_le_of_real h)_ < ∞ := hg

theorem HasFiniteIntegral.mono' {f : α → β} {g : α → ℝ} (hg : HasFiniteIntegral g μ) (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ g a) :
    HasFiniteIntegral f μ :=
  hg.mono <| h.mono fun x hx => le_transₓ hx (le_abs_self _)

theorem HasFiniteIntegral.congr' {f : α → β} {g : α → γ} (hf : HasFiniteIntegral f μ) (h : ∀ᵐ a ∂μ, ∥f a∥ = ∥g a∥) :
    HasFiniteIntegral g μ :=
  hf.mono <| eventually_eq.le <| EventuallyEq.symm h

theorem has_finite_integral_congr' {f : α → β} {g : α → γ} (h : ∀ᵐ a ∂μ, ∥f a∥ = ∥g a∥) :
    HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ :=
  ⟨fun hf => hf.congr' h, fun hg => hg.congr' <| EventuallyEq.symm h⟩

theorem HasFiniteIntegral.congr {f g : α → β} (hf : HasFiniteIntegral f μ) (h : f =ᵐ[μ] g) : HasFiniteIntegral g μ :=
  hf.congr' <| h.fun_comp norm

theorem has_finite_integral_congr {f g : α → β} (h : f =ᵐ[μ] g) : HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ :=
  has_finite_integral_congr' <| h.fun_comp norm

theorem has_finite_integral_const_iff {c : β} : HasFiniteIntegral (fun x : α => c) μ ↔ c = 0 ∨ μ Univ < ∞ := by
  simp [has_finite_integral, lintegral_const, lt_top_iff_ne_top, or_iff_not_imp_left]

theorem has_finite_integral_const [IsFiniteMeasure μ] (c : β) : HasFiniteIntegral (fun x : α => c) μ :=
  has_finite_integral_const_iff.2 (Or.inr <| measure_lt_top _ _)

theorem has_finite_integral_of_bounded [IsFiniteMeasure μ] {f : α → β} {C : ℝ} (hC : ∀ᵐ a ∂μ, ∥f a∥ ≤ C) :
    HasFiniteIntegral f μ :=
  (has_finite_integral_const C).mono' hC

theorem HasFiniteIntegral.mono_measure {f : α → β} (h : HasFiniteIntegral f ν) (hμ : μ ≤ ν) : HasFiniteIntegral f μ :=
  lt_of_le_of_ltₓ (lintegral_mono' hμ le_rfl) h

theorem HasFiniteIntegral.add_measure {f : α → β} (hμ : HasFiniteIntegral f μ) (hν : HasFiniteIntegral f ν) :
    HasFiniteIntegral f (μ + ν) := by
  simp only [has_finite_integral, lintegral_add_measure] at *
  exact add_lt_top.2 ⟨hμ, hν⟩

theorem HasFiniteIntegral.left_of_add_measure {f : α → β} (h : HasFiniteIntegral f (μ + ν)) : HasFiniteIntegral f μ :=
  h.mono_measure <| measure.le_add_right <| le_rfl

theorem HasFiniteIntegral.right_of_add_measure {f : α → β} (h : HasFiniteIntegral f (μ + ν)) : HasFiniteIntegral f ν :=
  h.mono_measure <| measure.le_add_left <| le_rfl

@[simp]
theorem has_finite_integral_add_measure {f : α → β} :
    HasFiniteIntegral f (μ + ν) ↔ HasFiniteIntegral f μ ∧ HasFiniteIntegral f ν :=
  ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

theorem HasFiniteIntegral.smul_measure {f : α → β} (h : HasFiniteIntegral f μ) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    HasFiniteIntegral f (c • μ) := by
  simp only [has_finite_integral, lintegral_smul_measure] at *
  exact mul_lt_top hc h.ne

@[simp]
theorem has_finite_integral_zero_measure {m : MeasurableSpace α} (f : α → β) : HasFiniteIntegral f (0 : Measure α) := by
  simp only [has_finite_integral, lintegral_zero_measure, WithTop.zero_lt_top]

variable (α β μ)

@[simp]
theorem has_finite_integral_zero : HasFiniteIntegral (fun a : α => (0 : β)) μ := by
  simp [has_finite_integral]

variable {α β μ}

theorem HasFiniteIntegral.neg {f : α → β} (hfi : HasFiniteIntegral f μ) : HasFiniteIntegral (-f) μ := by
  simpa [has_finite_integral] using hfi

@[simp]
theorem has_finite_integral_neg_iff {f : α → β} : HasFiniteIntegral (-f) μ ↔ HasFiniteIntegral f μ :=
  ⟨fun h => neg_negₓ f ▸ h.neg, HasFiniteIntegral.neg⟩

theorem HasFiniteIntegral.norm {f : α → β} (hfi : HasFiniteIntegral f μ) : HasFiniteIntegral (fun a => ∥f a∥) μ := by
  have eq : (fun a => (nnnorm ∥f a∥ : ℝ≥0∞)) = fun a => (nnnorm (f a) : ℝ≥0∞) := by
    funext
    rw [nnnorm_norm]
  rwa [has_finite_integral, Eq]

theorem has_finite_integral_norm_iff (f : α → β) : HasFiniteIntegral (fun a => ∥f a∥) μ ↔ HasFiniteIntegral f μ :=
  has_finite_integral_congr' <| eventually_of_forall fun x => norm_norm (f x)

theorem has_finite_integral_to_real_of_lintegral_ne_top {f : α → ℝ≥0∞} (hf : (∫⁻ x, f x ∂μ) ≠ ∞) :
    HasFiniteIntegral (fun x => (f x).toReal) μ := by
  have : ∀ x, (∥(f x).toReal∥₊ : ℝ≥0∞) = @coe ℝ≥0 ℝ≥0∞ _ (⟨(f x).toReal, Ennreal.to_real_nonneg⟩ : ℝ≥0 ) := by
    intro x
    rw [Real.nnnorm_of_nonneg]
  simp_rw [has_finite_integral, this]
  refine' lt_of_le_of_ltₓ (lintegral_mono fun x => _) (lt_top_iff_ne_top.2 hf)
  by_cases' hfx : f x = ∞
  · simp [hfx]
    
  · lift f x to ℝ≥0 using hfx with fx
    simp [← h]
    

theorem is_finite_measure_with_density_of_real {f : α → ℝ} (hfi : HasFiniteIntegral f μ) :
    IsFiniteMeasure (μ.withDensity fun x => Ennreal.ofReal <| f x) := by
  refine' is_finite_measure_with_density ((lintegral_mono fun x => _).trans_lt hfi).Ne
  exact Real.of_real_le_ennnorm (f x)

section DominatedConvergence

variable {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}

theorem all_ae_of_real_F_le_bound (h : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a) :
    ∀ n, ∀ᵐ a ∂μ, Ennreal.ofReal ∥F n a∥ ≤ Ennreal.ofReal (bound a) := fun n =>
  (h n).mono fun a h => Ennreal.of_real_le_of_real h

theorem all_ae_tendsto_of_real_norm (h : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop <| 𝓝 <| f a) :
    ∀ᵐ a ∂μ, Tendsto (fun n => Ennreal.ofReal ∥F n a∥) atTop <| 𝓝 <| Ennreal.ofReal ∥f a∥ :=
  h.mono fun a h => tendsto_of_real <| Tendsto.comp (Continuous.tendsto continuous_norm _) h

theorem all_ae_of_real_f_le_bound (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    ∀ᵐ a ∂μ, Ennreal.ofReal ∥f a∥ ≤ Ennreal.ofReal (bound a) := by
  have F_le_bound := all_ae_of_real_F_le_bound h_bound
  rw [← ae_all_iff] at F_le_bound
  apply F_le_bound.mp ((all_ae_tendsto_of_real_norm h_lim).mono _)
  intro a tendsto_norm F_le_bound
  exact le_of_tendsto' tendsto_norm F_le_bound

theorem has_finite_integral_of_dominated_convergence {F : ℕ → α → β} {f : α → β} {bound : α → ℝ}
    (bound_has_finite_integral : HasFiniteIntegral bound μ) (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : HasFiniteIntegral f μ := by
  /- `∥F n a∥ ≤ bound a` and `∥F n a∥ --> ∥f a∥` implies `∥f a∥ ≤ bound a`,
    and so `∫ ∥f∥ ≤ ∫ bound < ∞` since `bound` is has_finite_integral -/
  rw [has_finite_integral_iff_norm]
  calc (∫⁻ a, Ennreal.ofReal ∥f a∥ ∂μ) ≤ ∫⁻ a, Ennreal.ofReal (bound a) ∂μ :=
      lintegral_mono_ae <| all_ae_of_real_f_le_bound h_bound h_lim _ < ∞ := by
      rw [← has_finite_integral_iff_of_real]
      · exact bound_has_finite_integral
        
      exact (h_bound 0).mono fun a h => le_transₓ (norm_nonneg _) h

theorem tendsto_lintegral_norm_of_dominated_convergence [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
    {F : ℕ → α → β} {f : α → β} {bound : α → ℝ} (F_measurable : ∀ n, AeMeasurable (F n) μ)
    (bound_has_finite_integral : HasFiniteIntegral bound μ) (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, Ennreal.ofReal ∥F n a - f a∥ ∂μ) atTop (𝓝 0) := by
  have f_measurable : AeMeasurable f μ := ae_measurable_of_tendsto_metric_ae' F_measurable h_lim
  let b := fun a => 2 * Ennreal.ofReal (bound a)
  /- `∥F n a∥ ≤ bound a` and `F n a --> f a` implies `∥f a∥ ≤ bound a`, and thus by the
    triangle inequality, have `∥F n a - f a∥ ≤ 2 * (bound a). -/
  have hb : ∀ n, ∀ᵐ a ∂μ, Ennreal.ofReal ∥F n a - f a∥ ≤ b a := by
    intro n
    filter_upwards [all_ae_of_real_F_le_bound h_bound n, all_ae_of_real_f_le_bound h_bound h_lim] with a h₁ h₂
    calc Ennreal.ofReal ∥F n a - f a∥ ≤ Ennreal.ofReal ∥F n a∥ + Ennreal.ofReal ∥f a∥ := by
        rw [← Ennreal.of_real_add]
        apply of_real_le_of_real
        · apply norm_sub_le
          
        · exact norm_nonneg _
          
        · exact norm_nonneg _
          _ ≤ Ennreal.ofReal (bound a) + Ennreal.ofReal (bound a) :=
        add_le_add h₁ h₂ _ = b a := by
        rw [← two_mul]
  -- On the other hand, `F n a --> f a` implies that `∥F n a - f a∥ --> 0`
  have h : ∀ᵐ a ∂μ, Tendsto (fun n => Ennreal.ofReal ∥F n a - f a∥) atTop (𝓝 0) := by
    rw [← Ennreal.of_real_zero]
    refine' h_lim.mono fun a h => (continuous_of_real.tendsto _).comp _
    rwa [← tendsto_iff_norm_tendsto_zero]
  /- Therefore, by the dominated convergence theorem for nonnegative integration, have
    ` ∫ ∥f a - F n a∥ --> 0 ` -/
  suffices h : tendsto (fun n => ∫⁻ a, Ennreal.ofReal ∥F n a - f a∥ ∂μ) at_top (𝓝 (∫⁻ a : α, 0 ∂μ))
  · rwa [lintegral_zero] at h
    
  -- Using the dominated convergence theorem.
  refine' tendsto_lintegral_of_dominated_convergence' _ _ hb _ _
  -- Show `λa, ∥f a - F n a∥` is almost everywhere measurable for all `n`
  · exact fun n => measurable_of_real.comp_ae_measurable ((F_measurable n).sub f_measurable).norm
    
  -- Show `2 * bound` is has_finite_integral
  · rw [has_finite_integral_iff_of_real] at bound_has_finite_integral
    · calc (∫⁻ a, b a ∂μ) = 2 * ∫⁻ a, Ennreal.ofReal (bound a) ∂μ := by
          rw [lintegral_const_mul']
          exact coe_ne_top _ ≠ ∞ := mul_ne_top coe_ne_top bound_has_finite_integral.ne
      
    filter_upwards [h_bound 0] with _ h using le_transₓ (norm_nonneg _) h
    
  -- Show `∥f a - F n a∥ --> 0`
  · exact h
    

end DominatedConvergence

section PosPart

/-! Lemmas used for defining the positive part of a `L¹` function -/


theorem HasFiniteIntegral.max_zero {f : α → ℝ} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => max (f a) 0) μ :=
  hf.mono <|
    eventually_of_forall fun x => by
      simp [Real.norm_eq_abs, abs_le, abs_nonneg, le_abs_self]

theorem HasFiniteIntegral.min_zero {f : α → ℝ} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => min (f a) 0) μ :=
  hf.mono <|
    eventually_of_forall fun x => by
      simp [Real.norm_eq_abs, abs_le, abs_nonneg, neg_le, neg_le_abs_self, abs_eq_max_neg, le_totalₓ]

end PosPart

section NormedSpace

variable {𝕜 : Type _} [NormedField 𝕜] [NormedSpace 𝕜 β]

theorem HasFiniteIntegral.smul (c : 𝕜) {f : α → β} : HasFiniteIntegral f μ → HasFiniteIntegral (c • f) μ := by
  simp only [has_finite_integral]
  intro hfi
  calc (∫⁻ a : α, nnnorm (c • f a) ∂μ) = ∫⁻ a : α, nnnorm c * nnnorm (f a) ∂μ := by
      simp only [nnnorm_smul, Ennreal.coe_mul]_ < ∞ := by
      rw [lintegral_const_mul']
      exacts[mul_lt_top coe_ne_top hfi.ne, coe_ne_top]

theorem has_finite_integral_smul_iff {c : 𝕜} (hc : c ≠ 0) (f : α → β) :
    HasFiniteIntegral (c • f) μ ↔ HasFiniteIntegral f μ := by
  constructor
  · intro h
    simpa only [smul_smul, inv_mul_cancel hc, one_smul] using h.smul c⁻¹
    
  exact has_finite_integral.smul _

theorem HasFiniteIntegral.const_mul {f : α → ℝ} (h : HasFiniteIntegral f μ) (c : ℝ) :
    HasFiniteIntegral (fun x => c * f x) μ :=
  (HasFiniteIntegral.smul c h : _)

theorem HasFiniteIntegral.mul_const {f : α → ℝ} (h : HasFiniteIntegral f μ) (c : ℝ) :
    HasFiniteIntegral (fun x => f x * c) μ := by
  simp_rw [mul_comm, h.const_mul _]

end NormedSpace

/-! ### The predicate `integrable` -/


variable [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- `integrable f μ` means that `f` is measurable and that the integral `∫⁻ a, ∥f a∥ ∂μ` is finite.
  `integrable f` means `integrable f volume`. -/
def Integrable {α} {m : MeasurableSpace α} (f : α → β)
    (μ : Measure α := by
      run_tac
        volume_tac) :
    Prop :=
  AeMeasurable f μ ∧ HasFiniteIntegral f μ

theorem mem_ℒp_one_iff_integrable {f : α → β} : Memℒp f 1 μ ↔ Integrable f μ := by
  simp_rw [integrable, has_finite_integral, mem_ℒp, snorm_one_eq_lintegral_nnnorm]

theorem Integrable.ae_measurable {f : α → β} (hf : Integrable f μ) : AeMeasurable f μ :=
  hf.1

theorem Integrable.has_finite_integral {f : α → β} (hf : Integrable f μ) : HasFiniteIntegral f μ :=
  hf.2

theorem Integrable.mono {f : α → β} {g : α → γ} (hg : Integrable g μ) (hf : AeMeasurable f μ)
    (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ ∥g a∥) : Integrable f μ :=
  ⟨hf, hg.HasFiniteIntegral.mono h⟩

theorem Integrable.mono' {f : α → β} {g : α → ℝ} (hg : Integrable g μ) (hf : AeMeasurable f μ)
    (h : ∀ᵐ a ∂μ, ∥f a∥ ≤ g a) : Integrable f μ :=
  ⟨hf, hg.HasFiniteIntegral.mono' h⟩

theorem Integrable.congr' {f : α → β} {g : α → γ} (hf : Integrable f μ) (hg : AeMeasurable g μ)
    (h : ∀ᵐ a ∂μ, ∥f a∥ = ∥g a∥) : Integrable g μ :=
  ⟨hg, hf.HasFiniteIntegral.congr' h⟩

theorem integrable_congr' {f : α → β} {g : α → γ} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ)
    (h : ∀ᵐ a ∂μ, ∥f a∥ = ∥g a∥) : Integrable f μ ↔ Integrable g μ :=
  ⟨fun h2f => h2f.congr' hg h, fun h2g => h2g.congr' hf <| EventuallyEq.symm h⟩

theorem Integrable.congr {f g : α → β} (hf : Integrable f μ) (h : f =ᵐ[μ] g) : Integrable g μ :=
  ⟨hf.1.congr h, hf.2.congr h⟩

theorem integrable_congr {f g : α → β} (h : f =ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

theorem integrable_const_iff {c : β} : Integrable (fun x : α => c) μ ↔ c = 0 ∨ μ Univ < ∞ := by
  have : AeMeasurable (fun x : α => c) μ := measurable_const.ae_measurable
  rw [integrable, and_iff_right this, has_finite_integral_const_iff]

theorem integrable_const [IsFiniteMeasure μ] (c : β) : Integrable (fun x : α => c) μ :=
  integrable_const_iff.2 <| Or.inr <| measure_lt_top _ _

theorem Integrable.mono_measure {f : α → β} (h : Integrable f ν) (hμ : μ ≤ ν) : Integrable f μ :=
  ⟨h.AeMeasurable.mono_measure hμ, h.HasFiniteIntegral.mono_measure hμ⟩

theorem Integrable.of_measure_le_smul {μ' : Measure α} (c : ℝ≥0∞) (hc : c ≠ ∞) (hμ'_le : μ' ≤ c • μ) {f : α → β}
    (hf : Integrable f μ) : Integrable f μ' := by
  rw [← mem_ℒp_one_iff_integrable] at hf⊢
  exact hf.of_measure_le_smul c hc hμ'_le

theorem Integrable.add_measure {f : α → β} (hμ : Integrable f μ) (hν : Integrable f ν) : Integrable f (μ + ν) := by
  simp_rw [← mem_ℒp_one_iff_integrable]  at hμ hν⊢
  refine' ⟨hμ.ae_measurable.add_measure hν.ae_measurable, _⟩
  rw [snorm_one_add_measure, Ennreal.add_lt_top]
  exact ⟨hμ.snorm_lt_top, hν.snorm_lt_top⟩

theorem Integrable.left_of_add_measure {f : α → β} (h : Integrable f (μ + ν)) : Integrable f μ := by
  rw [← mem_ℒp_one_iff_integrable] at h⊢
  exact h.left_of_add_measure

theorem Integrable.right_of_add_measure {f : α → β} (h : Integrable f (μ + ν)) : Integrable f ν := by
  rw [← mem_ℒp_one_iff_integrable] at h⊢
  exact h.right_of_add_measure

@[simp]
theorem integrable_add_measure {f : α → β} : Integrable f (μ + ν) ↔ Integrable f μ ∧ Integrable f ν :=
  ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

@[simp]
theorem integrable_zero_measure {m : MeasurableSpace α} {f : α → β} : Integrable f (0 : Measure α) :=
  ⟨ae_measurable_zero_measure, has_finite_integral_zero_measure f⟩

theorem integrable_finset_sum_measure {ι} {m : MeasurableSpace α} {f : α → β} {μ : ι → Measure α} {s : Finset ι} :
    Integrable f (∑ i in s, μ i) ↔ ∀, ∀ i ∈ s, ∀, Integrable f (μ i) := by
  induction s using Finset.induction_on <;> simp [*]

theorem Integrable.smul_measure {f : α → β} (h : Integrable f μ) {c : ℝ≥0∞} (hc : c ≠ ∞) : Integrable f (c • μ) := by
  rw [← mem_ℒp_one_iff_integrable] at h⊢
  exact h.smul_measure hc

theorem Integrable.to_average {f : α → β} (h : Integrable f μ) : Integrable f ((μ Univ)⁻¹ • μ) := by
  rcases eq_or_ne μ 0 with (rfl | hne)
  · rwa [smul_zero]
    
  · apply h.smul_measure
    simpa
    

theorem integrable_map_measure [OpensMeasurableSpace β] {f : α → δ} {g : δ → β} (hg : AeMeasurable g (Measure.map f μ))
    (hf : Measurable f) : Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← mem_ℒp_one_iff_integrable]
  exact mem_ℒp_map_measure_iff hg hf

theorem Integrable.comp_measurable [OpensMeasurableSpace β] {f : α → δ} {g : δ → β}
    (hg : Integrable g (Measure.map f μ)) (hf : Measurable f) : Integrable (g ∘ f) μ :=
  (integrable_map_measure hg.AeMeasurable hf).mp hg

theorem _root_.measurable_embedding.integrable_map_iff {f : α → δ} (hf : MeasurableEmbedding f) {g : δ → β} :
    Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← mem_ℒp_one_iff_integrable]
  exact hf.mem_ℒp_map_measure_iff

theorem integrable_map_equiv (f : α ≃ᵐ δ) (g : δ → β) : Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← mem_ℒp_one_iff_integrable]
  exact f.mem_ℒp_map_measure_iff

theorem MeasurePreserving.integrable_comp [OpensMeasurableSpace β] {ν : Measure δ} {g : δ → β} {f : α → δ}
    (hf : MeasurePreserving f μ ν) (hg : AeMeasurable g ν) : Integrable (g ∘ f) μ ↔ Integrable g ν := by
  rw [← hf.map_eq] at hg⊢
  exact (integrable_map_measure hg hf.measurable).symm

theorem MeasurePreserving.integrable_comp_emb {f : α → δ} {ν} (h₁ : MeasurePreserving f μ ν)
    (h₂ : MeasurableEmbedding f) {g : δ → β} : Integrable (g ∘ f) μ ↔ Integrable g ν :=
  h₁.map_eq ▸ Iff.symm h₂.integrable_map_iff

theorem lintegral_edist_lt_top [SecondCountableTopology β] [OpensMeasurableSpace β] {f g : α → β} (hf : Integrable f μ)
    (hg : Integrable g μ) : (∫⁻ a, edist (f a) (g a) ∂μ) < ∞ :=
  lt_of_le_of_ltₓ
    (lintegral_edist_triangle hf.AeMeasurable hg.AeMeasurable
      (measurable_const.AeMeasurable : AeMeasurable (fun a => (0 : β)) μ))
    (Ennreal.add_lt_top.2 <| by
      simp_rw [← has_finite_integral_iff_edist]
      exact ⟨hf.has_finite_integral, hg.has_finite_integral⟩)

variable (α β μ)

@[simp]
theorem integrable_zero : Integrable (fun _ => (0 : β)) μ := by
  simp [integrable, measurable_const.ae_measurable]

variable {α β μ}

theorem Integrable.add' [OpensMeasurableSpace β] {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    HasFiniteIntegral (f + g) μ :=
  calc
    (∫⁻ a, nnnorm (f a + g a) ∂μ) ≤ ∫⁻ a, nnnorm (f a) + nnnorm (g a) ∂μ :=
      lintegral_mono fun a => by
        exact_mod_cast nnnorm_add_le _ _
    _ = _ := lintegral_nnnorm_add hf.AeMeasurable hg.AeMeasurable
    _ < ∞ := add_lt_top.2 ⟨hf.HasFiniteIntegral, hg.HasFiniteIntegral⟩
    

theorem Integrable.add [BorelSpace β] [SecondCountableTopology β] {f g : α → β} (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (f + g) μ :=
  ⟨hf.AeMeasurable.add hg.AeMeasurable, hf.add' hg⟩

theorem integrable_finset_sum {ι} [BorelSpace β] [SecondCountableTopology β] (s : Finset ι) {f : ι → α → β}
    (hf : ∀, ∀ i ∈ s, ∀, Integrable (f i) μ) : Integrable (fun a => ∑ i in s, f i a) μ := by
  simp only [← Finset.sum_apply]
  exact Finset.sum_induction f (fun g => integrable g μ) (fun _ _ => integrable.add) (integrable_zero _ _ _) hf

theorem Integrable.neg [BorelSpace β] {f : α → β} (hf : Integrable f μ) : Integrable (-f) μ :=
  ⟨hf.AeMeasurable.neg, hf.HasFiniteIntegral.neg⟩

@[simp]
theorem integrable_neg_iff [BorelSpace β] {f : α → β} : Integrable (-f) μ ↔ Integrable f μ :=
  ⟨fun h => neg_negₓ f ▸ h.neg, Integrable.neg⟩

theorem Integrable.sub' [OpensMeasurableSpace β] {f g : α → β} (hf : Integrable f μ) (hg : Integrable g μ) :
    HasFiniteIntegral (f - g) μ :=
  calc
    (∫⁻ a, nnnorm (f a - g a) ∂μ) ≤ ∫⁻ a, nnnorm (f a) + nnnorm (-g a) ∂μ :=
      lintegral_mono fun a => by
        simp only [sub_eq_add_neg]
        exact_mod_cast nnnorm_add_le _ _
    _ = _ := by
      simp only [nnnorm_neg]
      exact lintegral_nnnorm_add hf.ae_measurable hg.ae_measurable
    _ < ∞ := add_lt_top.2 ⟨hf.HasFiniteIntegral, hg.HasFiniteIntegral⟩
    

theorem Integrable.sub [BorelSpace β] [SecondCountableTopology β] {f g : α → β} (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (f - g) μ := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem Integrable.norm [OpensMeasurableSpace β] {f : α → β} (hf : Integrable f μ) : Integrable (fun a => ∥f a∥) μ :=
  ⟨hf.AeMeasurable.norm, hf.HasFiniteIntegral.norm⟩

theorem integrable_norm_iff [OpensMeasurableSpace β] {f : α → β} (hf : AeMeasurable f μ) :
    Integrable (fun a => ∥f a∥) μ ↔ Integrable f μ := by
  simp_rw [integrable, and_iff_right hf, and_iff_right hf.norm, has_finite_integral_norm_iff]

theorem integrable_of_norm_sub_le [OpensMeasurableSpace β] {f₀ f₁ : α → β} {g : α → ℝ} (hf₁_m : AeMeasurable f₁ μ)
    (hf₀_i : Integrable f₀ μ) (hg_i : Integrable g μ) (h : ∀ᵐ a ∂μ, ∥f₀ a - f₁ a∥ ≤ g a) : Integrable f₁ μ :=
  have : ∀ᵐ a ∂μ, ∥f₁ a∥ ≤ ∥f₀ a∥ + g a := by
    apply h.mono
    intro a ha
    calc ∥f₁ a∥ ≤ ∥f₀ a∥ + ∥f₀ a - f₁ a∥ := norm_le_insert _ _ _ ≤ ∥f₀ a∥ + g a := add_le_add_left ha _
  integrable.mono' (hf₀_i.norm.add hg_i) hf₁_m this

theorem Integrable.prod_mk [OpensMeasurableSpace β] [OpensMeasurableSpace γ] {f : α → β} {g : α → γ}
    (hf : Integrable f μ) (hg : Integrable g μ) : Integrable (fun x => (f x, g x)) μ :=
  ⟨hf.AeMeasurable.prod_mk hg.AeMeasurable,
    (hf.norm.add' hg.norm).mono <|
      eventually_of_forall fun x =>
        calc
          max ∥f x∥ ∥g x∥ ≤ ∥f x∥ + ∥g x∥ := max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
          _ ≤ ∥∥f x∥ + ∥g x∥∥ := le_abs_self _
          ⟩

theorem Memℒp.integrable [BorelSpace β] {q : ℝ≥0∞} (hq1 : 1 ≤ q) {f : α → β} [IsFiniteMeasure μ] (hfq : Memℒp f q μ) :
    Integrable f μ :=
  mem_ℒp_one_iff_integrable.mp (hfq.mem_ℒp_of_exponent_le hq1)

theorem LipschitzWith.integrable_comp_iff_of_antilipschitz [CompleteSpace β] [BorelSpace β] [BorelSpace γ] {K K'}
    {f : α → β} {g : β → γ} (hg : LipschitzWith K g) (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) :
    Integrable (g ∘ f) μ ↔ Integrable f μ := by
  simp [← mem_ℒp_one_iff_integrable, hg.mem_ℒp_comp_iff_of_antilipschitz hg' g0]

theorem Integrable.real_to_nnreal {f : α → ℝ} (hf : Integrable f μ) : Integrable (fun x => ((f x).toNnreal : ℝ)) μ := by
  refine' ⟨hf.ae_measurable.real_to_nnreal.coe_nnreal_real, _⟩
  rw [has_finite_integral_iff_norm]
  refine' lt_of_le_of_ltₓ _ ((has_finite_integral_iff_norm _).1 hf.has_finite_integral)
  apply lintegral_mono
  intro x
  simp [Real.norm_eq_abs, Ennreal.of_real_le_of_real, abs_le, abs_nonneg, le_abs_self]

theorem of_real_to_real_ae_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x < ∞) : (fun x => Ennreal.ofReal (f x).toReal) =ᵐ[μ] f :=
  by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, of_real_to_real, Ne.def, not_false_iff]

theorem coe_to_nnreal_ae_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x < ∞) : (fun x => ((f x).toNnreal : ℝ≥0∞)) =ᵐ[μ] f := by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, Ne.def, not_false_iff, coe_to_nnreal]

section

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem integrable_with_density_iff_integrable_coe_smul {f : α → ℝ≥0 } (hf : Measurable f) {g : α → E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => (f x : ℝ) • g x) μ := by
  by_cases' H : AeMeasurable (fun x : α => (f x : ℝ) • g x) μ
  · simp only [integrable, ae_measurable_with_density_iff hf, has_finite_integral, H, true_andₓ]
    rw [lintegral_with_density_eq_lintegral_mul₀' hf.coe_nnreal_ennreal.ae_measurable]
    · congr
      ext1 x
      simp only [nnnorm_smul, Nnreal.nnnorm_eq, coe_mul, Pi.mul_apply]
      
    · rw [ae_measurable_with_density_ennreal_iff hf]
      convert H.nnnorm.coe_nnreal_ennreal
      ext1 x
      simp only [nnnorm_smul, Nnreal.nnnorm_eq, coe_mul]
      
    
  · simp only [integrable, ae_measurable_with_density_iff hf, H, false_andₓ]
    

theorem integrable_with_density_iff_integrable_smul {f : α → ℝ≥0 } (hf : Measurable f) {g : α → E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => f x • g x) μ :=
  integrable_with_density_iff_integrable_coe_smul hf

theorem integrable_with_density_iff_integrable_smul' {f : α → ℝ≥0∞} (hf : Measurable f) (hflt : ∀ᵐ x ∂μ, f x < ∞)
    {g : α → E} : Integrable g (μ.withDensity f) ↔ Integrable (fun x => (f x).toReal • g x) μ := by
  rw [← with_density_congr_ae (coe_to_nnreal_ae_eq hflt), integrable_with_density_iff_integrable_smul]
  · rfl
    
  · exact hf.ennreal_to_nnreal
    

theorem integrable_with_density_iff_integrable_coe_smul₀ {f : α → ℝ≥0 } (hf : AeMeasurable f μ) {g : α → E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => (f x : ℝ) • g x) μ :=
  calc
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable g (μ.withDensity fun x => hf.mk f x) := by
      suffices (fun x => (f x : ℝ≥0∞)) =ᵐ[μ] fun x => hf.mk f x by
        rw [with_density_congr_ae this]
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]
    _ ↔ Integrable (fun x => (hf.mk f x : ℝ) • g x) μ :=
      integrable_with_density_iff_integrable_coe_smul hf.measurable_mk
    _ ↔ Integrable (fun x => (f x : ℝ) • g x) μ := by
      apply integrable_congr
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]
    

theorem integrable_with_density_iff_integrable_smul₀ {f : α → ℝ≥0 } (hf : AeMeasurable f μ) {g : α → E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => f x • g x) μ :=
  integrable_with_density_iff_integrable_coe_smul₀ hf

end

theorem integrable_with_density_iff {f : α → ℝ≥0∞} (hf : Measurable f) (hflt : ∀ᵐ x ∂μ, f x < ∞) {g : α → ℝ} :
    Integrable g (μ.withDensity f) ↔ Integrable (fun x => g x * (f x).toReal) μ := by
  have : (fun x => g x * (f x).toReal) = fun x => (f x).toReal • g x := by
    simp [mul_comm]
  rw [this]
  exact integrable_with_density_iff_integrable_smul' hf hflt

section

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem mem_ℒ1_smul_of_L1_with_density {f : α → ℝ≥0 } (f_meas : Measurable f)
    (u : lp E 1 (μ.withDensity fun x => f x)) : Memℒp (fun x => f x • u x) 1 μ :=
  mem_ℒp_one_iff_integrable.2 <|
    (integrable_with_density_iff_integrable_smul f_meas).1 <| mem_ℒp_one_iff_integrable.1 (lp.mem_ℒp u)

variable (μ)

/-- The map `u ↦ f • u` is an isometry between the `L^1` spaces for `μ.with_density f` and `μ`. -/
noncomputable def withDensitySmulLi {f : α → ℝ≥0 } (f_meas : Measurable f) :
    lp E 1 (μ.withDensity fun x => f x) →ₗᵢ[ℝ] lp E 1 μ where
  toFun := fun u => (mem_ℒ1_smul_of_L1_with_density f_meas u).toLp _
  map_add' := by
    intro u v
    ext1
    filter_upwards [(mem_ℒ1_smul_of_L1_with_density f_meas u).coe_fn_to_Lp,
      (mem_ℒ1_smul_of_L1_with_density f_meas v).coe_fn_to_Lp,
      (mem_ℒ1_smul_of_L1_with_density f_meas (u + v)).coe_fn_to_Lp,
      Lp.coe_fn_add ((mem_ℒ1_smul_of_L1_with_density f_meas u).toLp _)
        ((mem_ℒ1_smul_of_L1_with_density f_meas v).toLp _),
      (ae_with_density_iff f_meas.coe_nnreal_ennreal).1 (Lp.coe_fn_add u v)]
    intro x hu hv huv h' h''
    rw [huv, h', Pi.add_apply, hu, hv]
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, add_zeroₓ]
      
    · rw [h'' _, Pi.add_apply, smul_add]
      simpa only [Ne.def, Ennreal.coe_eq_zero] using hx
      
  map_smul' := by
    intro r u
    ext1
    filter_upwards [(ae_with_density_iff f_meas.coe_nnreal_ennreal).1 (Lp.coe_fn_smul r u),
      (mem_ℒ1_smul_of_L1_with_density f_meas (r • u)).coe_fn_to_Lp,
      Lp.coe_fn_smul r ((mem_ℒ1_smul_of_L1_with_density f_meas u).toLp _),
      (mem_ℒ1_smul_of_L1_with_density f_meas u).coe_fn_to_Lp]
    intro x h h' h'' h'''
    rw [RingHom.id_apply, h', h'', Pi.smul_apply, h''']
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, smul_zero]
      
    · rw [h _, smul_comm, Pi.smul_apply]
      simpa only [Ne.def, Ennreal.coe_eq_zero] using hx
      
  norm_map' := by
    intro u
    simp only [snorm, LinearMap.coe_mk, Lp.norm_to_Lp, one_ne_zero, Ennreal.one_ne_top, Ennreal.one_to_real, if_false,
      snorm', Ennreal.rpow_one, _root_.div_one, Lp.norm_def]
    rw
      [lintegral_with_density_eq_lintegral_mul_non_measurable _ f_meas.coe_nnreal_ennreal
        (Filter.eventually_of_forall fun x => Ennreal.coe_lt_top)]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [(mem_ℒ1_smul_of_L1_with_density f_meas u).coe_fn_to_Lp] with x hx
    rw [hx, Pi.mul_apply]
    change ↑∥(f x : ℝ) • u x∥₊ = ↑(f x) * ↑∥u x∥₊
    simp only [nnnorm_smul, Nnreal.nnnorm_eq, Ennreal.coe_mul]

@[simp]
theorem with_density_smul_li_apply {f : α → ℝ≥0 } (f_meas : Measurable f) (u : lp E 1 (μ.withDensity fun x => f x)) :
    withDensitySmulLi μ f_meas u = (mem_ℒ1_smul_of_L1_with_density f_meas u).toLp fun x => f x • u x :=
  rfl

end

theorem mem_ℒ1_to_real_of_lintegral_ne_top {f : α → ℝ≥0∞} (hfm : AeMeasurable f μ) (hfi : (∫⁻ x, f x ∂μ) ≠ ∞) :
    Memℒp (fun x => (f x).toReal) 1 μ := by
  rw [mem_ℒp, snorm_one_eq_lintegral_nnnorm]
  exact ⟨AeMeasurable.ennreal_to_real hfm, has_finite_integral_to_real_of_lintegral_ne_top hfi⟩

theorem integrable_to_real_of_lintegral_ne_top {f : α → ℝ≥0∞} (hfm : AeMeasurable f μ) (hfi : (∫⁻ x, f x ∂μ) ≠ ∞) :
    Integrable (fun x => (f x).toReal) μ :=
  mem_ℒp_one_iff_integrable.1 <| mem_ℒ1_to_real_of_lintegral_ne_top hfm hfi

section PosPart

/-! ### Lemmas used for defining the positive part of a `L¹` function -/


theorem Integrable.max_zero {f : α → ℝ} (hf : Integrable f μ) : Integrable (fun a => max (f a) 0) μ :=
  ⟨hf.AeMeasurable.max measurable_const.AeMeasurable, hf.HasFiniteIntegral.max_zero⟩

theorem Integrable.min_zero {f : α → ℝ} (hf : Integrable f μ) : Integrable (fun a => min (f a) 0) μ :=
  ⟨hf.AeMeasurable.min measurable_const.AeMeasurable, hf.HasFiniteIntegral.min_zero⟩

end PosPart

section NormedSpace

variable {𝕜 : Type _} [NormedField 𝕜] [NormedSpace 𝕜 β] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]

theorem Integrable.smul [BorelSpace β] (c : 𝕜) {f : α → β} (hf : Integrable f μ) : Integrable (c • f) μ :=
  ⟨hf.AeMeasurable.const_smul c, hf.HasFiniteIntegral.smul c⟩

theorem integrable_smul_iff [BorelSpace β] {c : 𝕜} (hc : c ≠ 0) (f : α → β) : Integrable (c • f) μ ↔ Integrable f μ :=
  and_congr (ae_measurable_const_smul_iff₀ hc) (has_finite_integral_smul_iff hc f)

theorem Integrable.const_mul {f : α → ℝ} (h : Integrable f μ) (c : ℝ) : Integrable (fun x => c * f x) μ :=
  Integrable.smul c h

theorem Integrable.mul_const {f : α → ℝ} (h : Integrable f μ) (c : ℝ) : Integrable (fun x => f x * c) μ := by
  simp_rw [mul_comm, h.const_mul _]

end NormedSpace

section NormedSpaceOverCompleteField

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] [CompleteSpace 𝕜] [MeasurableSpace 𝕜]

variable [BorelSpace 𝕜]

variable {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]

theorem integrable_smul_const {f : α → 𝕜} {c : E} (hc : c ≠ 0) : Integrable (fun x => f x • c) μ ↔ Integrable f μ := by
  simp_rw [integrable, ae_measurable_smul_const hc, And.congr_right_iff, has_finite_integral, nnnorm_smul,
    Ennreal.coe_mul]
  intro hf
  rw [lintegral_mul_const' _ _ Ennreal.coe_ne_top, Ennreal.mul_lt_top_iff]
  have : ∀ x : ℝ≥0∞, x = 0 → x < ∞ := by
    simp
  simp [hc, or_iff_left_of_imp (this _)]

end NormedSpaceOverCompleteField

section IsROrC

variable {𝕜 : Type _} [IsROrC 𝕜] {f : α → 𝕜}

theorem Integrable.of_real {f : α → ℝ} (hf : Integrable f μ) : Integrable (fun x => (f x : 𝕜)) μ := by
  rw [← mem_ℒp_one_iff_integrable] at hf⊢
  exact hf.of_real

theorem Integrable.re_im_iff :
    Integrable (fun x => IsROrC.re (f x)) μ ∧ Integrable (fun x => IsROrC.im (f x)) μ ↔ Integrable f μ := by
  simp_rw [← mem_ℒp_one_iff_integrable]
  exact mem_ℒp_re_im_iff

theorem Integrable.re (hf : Integrable f μ) : Integrable (fun x => IsROrC.re (f x)) μ := by
  rw [← mem_ℒp_one_iff_integrable] at hf⊢
  exact hf.re

theorem Integrable.im (hf : Integrable f μ) : Integrable (fun x => IsROrC.im (f x)) μ := by
  rw [← mem_ℒp_one_iff_integrable] at hf⊢
  exact hf.im

end IsROrC

section InnerProduct

variable {𝕜 E : Type _} [IsROrC 𝕜] [InnerProductSpace 𝕜 E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [SecondCountableTopology E] {f : α → E}

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

theorem Integrable.const_inner (c : E) (hf : Integrable f μ) : Integrable (fun x => ⟪c, f x⟫) μ := by
  rw [← mem_ℒp_one_iff_integrable] at hf⊢
  exact hf.const_inner c

theorem Integrable.inner_const (hf : Integrable f μ) (c : E) : Integrable (fun x => ⟪f x, c⟫) μ := by
  rw [← mem_ℒp_one_iff_integrable] at hf⊢
  exact hf.inner_const c

end InnerProduct

section Trim

variable {H : Type _} [NormedGroup H] [MeasurableSpace H] [OpensMeasurableSpace H] {m0 : MeasurableSpace α}
  {μ' : Measure α} {f : α → H}

theorem Integrable.trim (hm : m ≤ m0) (hf_int : Integrable f μ') (hf : @Measurable _ _ m _ f) :
    Integrable f (μ'.trim hm) := by
  refine' ⟨Measurable.ae_measurable hf, _⟩
  rw [has_finite_integral, lintegral_trim hm _]
  · exact hf_int.2
    
  · exact @Measurable.coe_nnreal_ennreal α m _ (@Measurable.nnnorm _ α _ _ _ m _ hf)
    

theorem integrable_of_integrable_trim (hm : m ≤ m0) (hf_int : Integrable f (μ'.trim hm)) : Integrable f μ' := by
  obtain ⟨hf_meas_ae, hf⟩ := hf_int
  refine' ⟨ae_measurable_of_ae_measurable_trim hm hf_meas_ae, _⟩
  rw [has_finite_integral] at hf⊢
  rwa [lintegral_trim_ae hm _] at hf
  exact @AeMeasurable.coe_nnreal_ennreal α m _ _ (@AeMeasurable.nnnorm H α _ _ _ m _ _ hf_meas_ae)

end Trim

section SigmaFinite

variable {E : Type _} {m0 : MeasurableSpace α} [NormedGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]

theorem integrable_of_forall_fin_meas_le' {μ : Measure α} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (C : ℝ≥0∞)
    (hC : C < ∞) {f : α → E} (hf_meas : AeMeasurable f μ)
    (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → (∫⁻ x in s, nnnorm (f x) ∂μ) ≤ C) : Integrable f μ :=
  ⟨hf_meas, (lintegral_le_of_forall_fin_meas_le' hm C hf_meas.nnnorm.coe_nnreal_ennreal hf).trans_lt hC⟩

theorem integrable_of_forall_fin_meas_le [SigmaFinite μ] (C : ℝ≥0∞) (hC : C < ∞) {f : α → E}
    (hf_meas : AeMeasurable f μ) (hf : ∀ s : Set α, MeasurableSet s → μ s ≠ ∞ → (∫⁻ x in s, nnnorm (f x) ∂μ) ≤ C) :
    Integrable f μ :=
  @integrable_of_forall_fin_meas_le' _ _ _ _ _ _ _ _ _
    (by
      rwa [trim_eq_self])
    C hC _ hf_meas hf

end SigmaFinite

/-! ### The predicate `integrable` on measurable functions modulo a.e.-equality -/


namespace AeEqFun

section

/-- A class of almost everywhere equal functions is `integrable` if its function representative
is integrable. -/
def Integrable (f : α →ₘ[μ] β) : Prop :=
  Integrable f μ

theorem integrable_mk {f : α → β} (hf : AeMeasurable f μ) :
    Integrable (mk f hf : α →ₘ[μ] β) ↔ MeasureTheory.Integrable f μ := by
  simp [integrable]
  apply integrable_congr
  exact coe_fn_mk f hf

theorem integrable_coe_fn {f : α →ₘ[μ] β} : MeasureTheory.Integrable f μ ↔ Integrable f := by
  rw [← integrable_mk, mk_coe_fn]

theorem integrable_zero : Integrable (0 : α →ₘ[μ] β) :=
  (integrable_zero α β μ).congr (coe_fn_mk _ _).symm

end

section

variable [BorelSpace β]

theorem Integrable.neg {f : α →ₘ[μ] β} : Integrable f → Integrable (-f) :=
  (induction_on f) fun f hfm hfi => (integrable_mk _).2 ((integrable_mk hfm).1 hfi).neg

section

variable [SecondCountableTopology β]

theorem integrable_iff_mem_L1 {f : α →ₘ[μ] β} : Integrable f ↔ f ∈ (α →₁[μ] β) := by
  rw [← integrable_coe_fn, ← mem_ℒp_one_iff_integrable, Lp.mem_Lp_iff_mem_ℒp]

theorem Integrable.add {f g : α →ₘ[μ] β} : Integrable f → Integrable g → Integrable (f + g) := by
  refine' induction_on₂ f g fun f hf g hg hfi hgi => _
  simp only [integrable_mk, mk_add_mk] at hfi hgi⊢
  exact hfi.add hgi

theorem Integrable.sub {f g : α →ₘ[μ] β} (hf : Integrable f) (hg : Integrable g) : Integrable (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

end

section NormedSpace

variable {𝕜 : Type _} [NormedField 𝕜] [NormedSpace 𝕜 β] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]

theorem Integrable.smul {c : 𝕜} {f : α →ₘ[μ] β} : Integrable f → Integrable (c • f) :=
  (induction_on f) fun f hfm hfi => (integrable_mk _).2 <| ((integrable_mk hfm).1 hfi).smul _

end NormedSpace

end

end AeEqFun

namespace L1

variable [SecondCountableTopology β] [BorelSpace β]

theorem integrable_coe_fn (f : α →₁[μ] β) : Integrable f μ := by
  rw [← mem_ℒp_one_iff_integrable]
  exact Lp.mem_ℒp f

theorem has_finite_integral_coe_fn (f : α →₁[μ] β) : HasFiniteIntegral f μ :=
  (integrable_coe_fn f).HasFiniteIntegral

theorem measurable_coe_fn (f : α →₁[μ] β) : Measurable f :=
  lp.measurable f

theorem ae_measurable_coe_fn (f : α →₁[μ] β) : AeMeasurable f μ :=
  lp.ae_measurable f

theorem edist_def (f g : α →₁[μ] β) : edist f g = ∫⁻ a, edist (f a) (g a) ∂μ := by
  simp [Lp.edist_def, snorm, snorm']
  simp [edist_eq_coe_nnnorm_sub]

theorem dist_def (f g : α →₁[μ] β) : dist f g = (∫⁻ a, edist (f a) (g a) ∂μ).toReal := by
  simp [Lp.dist_def, snorm, snorm']
  simp [edist_eq_coe_nnnorm_sub]

theorem norm_def (f : α →₁[μ] β) : ∥f∥ = (∫⁻ a, nnnorm (f a) ∂μ).toReal := by
  simp [Lp.norm_def, snorm, snorm']

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `norm_def` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
theorem norm_sub_eq_lintegral (f g : α →₁[μ] β) : ∥f - g∥ = (∫⁻ x, (nnnorm (f x - g x) : ℝ≥0∞) ∂μ).toReal := by
  rw [norm_def]
  congr 1
  rw [lintegral_congr_ae]
  filter_upwards [Lp.coe_fn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]

theorem of_real_norm_eq_lintegral (f : α →₁[μ] β) : Ennreal.ofReal ∥f∥ = ∫⁻ x, (nnnorm (f x) : ℝ≥0∞) ∂μ := by
  rw [norm_def, Ennreal.of_real_to_real]
  exact ne_of_ltₓ (has_finite_integral_coe_fn f)

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `of_real_norm_eq_lintegral` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
theorem of_real_norm_sub_eq_lintegral (f g : α →₁[μ] β) :
    Ennreal.ofReal ∥f - g∥ = ∫⁻ x, (nnnorm (f x - g x) : ℝ≥0∞) ∂μ := by
  simp_rw [of_real_norm_eq_lintegral, ← edist_eq_coe_nnnorm]
  apply lintegral_congr_ae
  filter_upwards [Lp.coe_fn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]

end L1

namespace Integrable

variable [SecondCountableTopology β] [BorelSpace β]

/-- Construct the equivalence class `[f]` of an integrable function `f`, as a member of the
space `L1 β 1 μ`. -/
def toL1 (f : α → β) (hf : Integrable f μ) : α →₁[μ] β :=
  (mem_ℒp_one_iff_integrable.2 hf).toLp f

@[simp]
theorem to_L1_coe_fn (f : α →₁[μ] β) (hf : Integrable f μ) : hf.toL1 f = f := by
  simp [integrable.to_L1]

theorem coe_fn_to_L1 {f : α → β} (hf : Integrable f μ) : hf.toL1 f =ᵐ[μ] f :=
  AeEqFun.coe_fn_mk _ _

@[simp]
theorem to_L1_zero (h : Integrable (0 : α → β) μ) : h.toL1 0 = 0 :=
  rfl

@[simp]
theorem to_L1_eq_mk (f : α → β) (hf : Integrable f μ) : (hf.toL1 f : α →ₘ[μ] β) = AeEqFun.mk f hf.AeMeasurable :=
  rfl

@[simp]
theorem to_L1_eq_to_L1_iff (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 f hf = toL1 g hg ↔ f =ᵐ[μ] g :=
  Memℒp.to_Lp_eq_to_Lp_iff _ _

theorem to_L1_add (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 (f + g) (hf.add hg) = toL1 f hf + toL1 g hg :=
  rfl

theorem to_L1_neg (f : α → β) (hf : Integrable f μ) : toL1 (-f) (Integrable.neg hf) = -toL1 f hf :=
  rfl

theorem to_L1_sub (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 (f - g) (hf.sub hg) = toL1 f hf - toL1 g hg :=
  rfl

theorem norm_to_L1 (f : α → β) (hf : Integrable f μ) : ∥hf.toL1 f∥ = Ennreal.toReal (∫⁻ a, edist (f a) 0 ∂μ) := by
  simp [to_L1, snorm, snorm']
  simp [edist_eq_coe_nnnorm]

theorem norm_to_L1_eq_lintegral_norm (f : α → β) (hf : Integrable f μ) :
    ∥hf.toL1 f∥ = Ennreal.toReal (∫⁻ a, Ennreal.ofReal ∥f a∥ ∂μ) := by
  rw [norm_to_L1, lintegral_norm_eq_lintegral_edist]

@[simp]
theorem edist_to_L1_to_L1 (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    edist (hf.toL1 f) (hg.toL1 g) = ∫⁻ a, edist (f a) (g a) ∂μ := by
  simp [integrable.to_L1, snorm, snorm']
  simp [edist_eq_coe_nnnorm_sub]

@[simp]
theorem edist_to_L1_zero (f : α → β) (hf : Integrable f μ) : edist (hf.toL1 f) 0 = ∫⁻ a, edist (f a) 0 ∂μ := by
  simp [integrable.to_L1, snorm, snorm']
  simp [edist_eq_coe_nnnorm]

variable {𝕜 : Type _} [NormedField 𝕜] [NormedSpace 𝕜 β] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]

theorem to_L1_smul (f : α → β) (hf : Integrable f μ) (k : 𝕜) : toL1 (fun a => k • f a) (hf.smul k) = k • toL1 f hf :=
  rfl

theorem to_L1_smul' (f : α → β) (hf : Integrable f μ) (k : 𝕜) : toL1 (k • f) (hf.smul k) = k • toL1 f hf :=
  rfl

end Integrable

end MeasureTheory

open MeasureTheory

variable {E : Type _} [NormedGroup E] [MeasurableSpace E] [BorelSpace E] {𝕜 : Type _} [NondiscreteNormedField 𝕜]
  [NormedSpace 𝕜 E] {H : Type _} [NormedGroup H] [NormedSpace 𝕜 H]

theorem MeasureTheory.Integrable.apply_continuous_linear_map {φ : α → H →L[𝕜] E} (φ_int : Integrable φ μ) (v : H) :
    Integrable (fun a => φ a v) μ :=
  (φ_int.norm.mul_const ∥v∥).mono' (φ_int.AeMeasurable.apply_continuous_linear_map v)
    (eventually_of_forall fun a => (φ a).le_op_norm v)

variable [MeasurableSpace H] [OpensMeasurableSpace H]

theorem ContinuousLinearMap.integrable_comp {φ : α → H} (L : H →L[𝕜] E) (φ_int : Integrable φ μ) :
    Integrable (fun a : α => L (φ a)) μ :=
  ((Integrable.norm φ_int).const_mul ∥L∥).mono' (L.Measurable.comp_ae_measurable φ_int.AeMeasurable)
    (eventually_of_forall fun a => L.le_op_norm (φ a))

