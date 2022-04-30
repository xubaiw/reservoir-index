/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathbin.MeasureTheory.Decomposition.Lebesgue

/-!
# Radon-Nikodym theorem

This file proves the Radon-Nikodym theorem. The Radon-Nikodym theorem states that, given measures
`μ, ν`, if `have_lebesgue_decomposition μ ν`, then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that `μ = fν`.
In particular, we have `f = rn_deriv μ ν`.

The Radon-Nikodym theorem will allow us to define many important concepts in probability theory,
most notably probability cumulative functions. It could also be used to define the conditional
expectation of a real function, but we take a different approach (see the file
`measure_theory/function/conditional_expectation`).

## Main results

* `measure_theory.measure.absolutely_continuous_iff_with_density_rn_deriv_eq` :
  the Radon-Nikodym theorem
* `measure_theory.signed_measure.absolutely_continuous_iff_with_density_rn_deriv_eq` :
  the Radon-Nikodym theorem for signed measures

## Tags

Radon-Nikodym theorem
-/


noncomputable section

open Classical MeasureTheory Nnreal Ennreal

variable {α β : Type _} {m : MeasurableSpace α}

namespace MeasureTheory

namespace Measureₓ

include m

theorem with_density_rn_deriv_eq (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) :
    ν.withDensity (rnDeriv μ ν) = μ := by
  obtain ⟨hf₁, ⟨E, hE₁, hE₂, hE₃⟩, hadd⟩ := have_lebesgue_decomposition_spec μ ν
  have : singular_part μ ν = 0 := by
    refine' le_antisymmₓ (fun A hA => _) (measure.zero_le _)
    suffices singular_part μ ν Set.Univ = 0 by
      rw [measure.coe_zero, Pi.zero_apply, ← this]
      exact measure_mono (Set.subset_univ _)
    rw [← measure_add_measure_compl hE₁, hE₂, zero_addₓ]
    have : (singular_part μ ν + ν.with_density (rn_deriv μ ν)) (Eᶜ) = μ (Eᶜ) := by
      rw [← hadd]
    rw [measure.coe_add, Pi.add_apply, h hE₃] at this
    exact (add_eq_zero_iff.1 this).1
  rw [this, zero_addₓ] at hadd
  exact hadd.symm

/-- **The Radon-Nikodym theorem**: Given two measures `μ` and `ν`, if
`have_lebesgue_decomposition μ ν`, then `μ` is absolutely continuous to `ν` if and only if
`ν.with_density (rn_deriv μ ν) = μ`. -/
theorem absolutely_continuous_iff_with_density_rn_deriv_eq {μ ν : Measure α} [HaveLebesgueDecomposition μ ν] :
    μ ≪ ν ↔ ν.withDensity (rnDeriv μ ν) = μ :=
  ⟨with_density_rn_deriv_eq μ ν, fun h => h ▸ with_density_absolutely_continuous _ _⟩

theorem with_density_rn_deriv_to_real_eq {μ ν : Measure α} [IsFiniteMeasure μ] [HaveLebesgueDecomposition μ ν]
    (h : μ ≪ ν) {i : Set α} (hi : MeasurableSet i) : (∫ x in i, (μ.rnDeriv ν x).toReal ∂ν) = (μ i).toReal := by
  rw [integral_to_real, ← with_density_apply _ hi, with_density_rn_deriv_eq μ ν h]
  · measurability
    
  · refine' ae_lt_top (μ.measurable_rn_deriv ν) (lt_of_le_of_ltₓ (lintegral_mono_set i.subset_univ) _).Ne
    rw [← with_density_apply _ MeasurableSet.univ, with_density_rn_deriv_eq μ ν h]
    exact measure_lt_top _ _
    

end Measureₓ

namespace SignedMeasure

include m

open Measureₓ VectorMeasure

theorem with_densityᵥ_rn_deriv_eq (s : SignedMeasure α) (μ : Measure α) [SigmaFinite μ]
    (h : s ≪ᵥ μ.toEnnrealVectorMeasure) : μ.withDensityᵥ (s.rnDeriv μ) = s := by
  rw [absolutely_continuous_ennreal_iff, (_ : μ.to_ennreal_vector_measure.ennreal_to_measure = μ),
    total_variation_absolutely_continuous_iff] at h
  · ext1 i hi
    rw [with_densityᵥ_apply (integrable_rn_deriv _ _) hi, rn_deriv, integral_sub,
      with_density_rn_deriv_to_real_eq h.1 hi, with_density_rn_deriv_to_real_eq h.2 hi]
    · conv_rhs => rw [← s.to_signed_measure_to_jordan_decomposition]
      erw [vector_measure.sub_apply]
      rw [to_signed_measure_apply_measurable hi, to_signed_measure_apply_measurable hi]
      
    all_goals
      rw [← integrable_on_univ]
      refine' integrable_on.restrict _ MeasurableSet.univ
      refine' ⟨_, has_finite_integral_to_real_of_lintegral_ne_top _⟩
      · apply Measurable.ae_strongly_measurable
        measurability
        
      · rw [set_lintegral_univ]
        exact (lintegral_rn_deriv_lt_top _ _).Ne
        
    
  · exact equiv_measure.right_inv μ
    

/-- The Radon-Nikodym theorem for signed measures. -/
theorem absolutely_continuous_iff_with_densityᵥ_rn_deriv_eq (s : SignedMeasure α) (μ : Measure α) [SigmaFinite μ] :
    s ≪ᵥ μ.toEnnrealVectorMeasure ↔ μ.withDensityᵥ (s.rnDeriv μ) = s :=
  ⟨with_densityᵥ_rn_deriv_eq s μ, fun h => h ▸ with_densityᵥ_absolutely_continuous _ _⟩

end SignedMeasure

end MeasureTheory

