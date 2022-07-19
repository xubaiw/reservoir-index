/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathbin.Probability.Notation
import Mathbin.Probability.Independence

/-!

# Probabilistic properties of the conditional expectation

This file contains some properties about the conditional expectation which does not belong in
the main conditional expectation file.

## Main result

* `measure_theory.condexp_indep_eq`: If `m₁, m₂` are independent σ-algebras and `f` is a
  `m₁`-measurable function, then `𝔼[f | m₂] = 𝔼[f]` almost everywhere.

-/


open TopologicalSpace Filter

open Nnreal Ennreal MeasureTheory ProbabilityTheory BigOperators

namespace MeasureTheory

open ProbabilityTheory

variable {α E : Type _} [NormedGroup E] [NormedSpace ℝ E] [CompleteSpace E] {m₁ m₂ m : MeasurableSpace α}
  {μ : Measure α} {f : α → E}

/-- If `m₁, m₂` are independent σ-algebras and `f` is `m₁`-measurable, then `𝔼[f | m₂] = 𝔼[f]`
almost everywhere. -/
theorem condexp_indep_eq (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m) [SigmaFinite (μ.trim hle₂)] (hf : strongly_measurable[m₁] f)
    (hindp : Indepₓ m₁ m₂ μ) : μ[f|m₂] =ᵐ[μ] fun x => μ[f] := by
  by_cases' hfint : integrable f μ
  swap
  · exact (integral_undef hfint).symm ▸ condexp_undef hfint
    
  have hfint₁ := hfint.trim hle₁ hf
  refine'
    (ae_eq_condexp_of_forall_set_integral_eq hle₂ hfint (fun s _ hs => integrable_on_const.2 (Or.inr hs))
        (fun s hms hs => _) strongly_measurable_const.ae_strongly_measurable').symm
  rw [set_integral_const]
  rw [← mem_ℒp_one_iff_integrable] at hfint
  refine' hfint.induction_strongly_measurable hle₁ Ennreal.one_ne_top _ _ _ _ _ _
  · intro c t hmt ht
    rw [integral_indicator (hle₁ _ hmt), set_integral_const, smul_smul, ← Ennreal.to_real_mul, mul_comm, ←
      hindp _ _ hmt hms, set_integral_indicator (hle₁ _ hmt), set_integral_const, Set.inter_comm]
    
  · intro u v hdisj huint hvint hu hv hu_eq hv_eq
    rw [mem_ℒp_one_iff_integrable] at huint hvint
    rw [integral_add' huint hvint, smul_add, hu_eq, hv_eq, integral_add' huint.integrable_on hvint.integrable_on]
    
  · have heq₁ :
      (fun f : Lp_meas E ℝ m₁ 1 μ => ∫ x, f x ∂μ) = (fun f : Lp E 1 μ => ∫ x, f x ∂μ) ∘ Submodule.subtypeL _ := by
      refine' funext fun f => integral_congr_ae _
      simp_rw [Submodule.coe_subtypeL', Submodule.coe_subtype, ← coe_fn_coe_base]
    have heq₂ :
      (fun f : Lp_meas E ℝ m₁ 1 μ => ∫ x in s, f x ∂μ) =
        (fun f : Lp E 1 μ => ∫ x in s, f x ∂μ) ∘ Submodule.subtypeL _ :=
      by
      refine' funext fun f => integral_congr_ae (ae_restrict_of_ae _)
      simp_rw [Submodule.coe_subtypeL', Submodule.coe_subtype, ← coe_fn_coe_base]
      exact eventually_of_forall fun _ => rfl
    refine' is_closed_eq (Continuous.const_smul _ _) _
    · rw [heq₁]
      exact continuous_integral.comp (ContinuousLinearMap.continuous _)
      
    · rw [heq₂]
      exact (continuous_set_integral _).comp (ContinuousLinearMap.continuous _)
      
    
  · intro u v huv huint hueq
    rwa [← integral_congr_ae huv, ← (set_integral_congr_ae (hle₂ _ hms) _ : (∫ x in s, u x ∂μ) = ∫ x in s, v x ∂μ)]
    filter_upwards [huv] with x hx _ using hx
    
  · exact ⟨f, hf, eventually_eq.rfl⟩
    

end MeasureTheory

