/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Yury Kudryashov
-/
import Mathbin.MeasureTheory.Measure.MeasureSpace

/-! # Mutually singular measures

Two measures `μ`, `ν` are said to be mutually singular (`measure_theory.measure.mutually_singular`,
localized notation `μ ⊥ₘ ν`) if there exists a measurable set `s` such that `μ s = 0` and
`ν sᶜ = 0`. The measurability of `s` is an unnecessary assumption (see
`measure_theory.measure.mutually_singular.mk`) but we keep it because this way `rcases (h : μ ⊥ₘ ν)`
gives us a measurable set and usually it is easy to prove measurability.

In this file we define the predicate `measure_theory.measure.mutually_singular` and prove basic
facts about it.

## Tags

measure, mutually singular
-/


open Set

open MeasureTheory Nnreal Ennreal

namespace MeasureTheory

namespace Measureₓ

variable {α : Type _} {m0 : MeasurableSpace α} {μ μ₁ μ₂ ν ν₁ ν₂ : Measure α}

/-- Two measures `μ`, `ν` are said to be mutually singular if there exists a measurable set `s`
such that `μ s = 0` and `ν sᶜ = 0`. -/
def MutuallySingular {m0 : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∃ s : Set α, MeasurableSet s ∧ μ s = 0 ∧ ν (sᶜ) = 0

-- mathport name: «expr ⊥ₘ »
localized [MeasureTheory] infixl:60 " ⊥ₘ " => MeasureTheory.Measure.MutuallySingular

namespace MutuallySingular

theorem mk {s t : Set α} (hs : μ s = 0) (ht : ν t = 0) (hst : univ ⊆ s ∪ t) : MutuallySingular μ ν := by
  use to_measurable μ s, measurable_set_to_measurable _ _, (measure_to_measurable _).trans hs
  refine' measure_mono_null (fun x hx => (hst trivialₓ).resolve_left fun hxs => hx _) ht
  exact subset_to_measurable _ _ hxs

@[simp]
theorem zero_right : μ ⊥ₘ 0 :=
  ⟨∅, MeasurableSet.empty, measure_empty, rfl⟩

@[symm]
theorem symm (h : ν ⊥ₘ μ) : μ ⊥ₘ ν :=
  let ⟨i, hi, his, hit⟩ := h
  ⟨iᶜ, hi.compl, hit, (compl_compl i).symm ▸ his⟩

theorem comm : μ ⊥ₘ ν ↔ ν ⊥ₘ μ :=
  ⟨fun h => h.symm, fun h => h.symm⟩

@[simp]
theorem zero_left : 0 ⊥ₘ μ :=
  zero_right.symm

theorem mono_ac (h : μ₁ ⊥ₘ ν₁) (hμ : μ₂ ≪ μ₁) (hν : ν₂ ≪ ν₁) : μ₂ ⊥ₘ ν₂ :=
  let ⟨s, hs, h₁, h₂⟩ := h
  ⟨s, hs, hμ h₁, hν h₂⟩

theorem mono (h : μ₁ ⊥ₘ ν₁) (hμ : μ₂ ≤ μ₁) (hν : ν₂ ≤ ν₁) : μ₂ ⊥ₘ ν₂ :=
  h.mono_ac hμ.AbsolutelyContinuous hν.AbsolutelyContinuous

@[simp]
theorem sum_left {ι : Type _} [Encodable ι] {μ : ι → Measure α} : sum μ ⊥ₘ ν ↔ ∀ i, μ i ⊥ₘ ν := by
  refine' ⟨fun h i => h.mono (le_sum _ _) le_rfl, fun H => _⟩
  choose s hsm hsμ hsν using H
  refine' ⟨⋂ i, s i, MeasurableSet.Inter hsm, _, _⟩
  · rw [sum_apply _ (MeasurableSet.Inter hsm), Ennreal.tsum_eq_zero]
    exact fun i => measure_mono_null (Inter_subset _ _) (hsμ i)
    
  · rwa [compl_Inter, measure_Union_null_iff]
    

@[simp]
theorem sum_right {ι : Type _} [Encodable ι] {ν : ι → Measure α} : μ ⊥ₘ sum ν ↔ ∀ i, μ ⊥ₘ ν i :=
  comm.trans <| sum_left.trans <| forall_congrₓ fun i => comm

@[simp]
theorem add_left_iff : μ₁ + μ₂ ⊥ₘ ν ↔ μ₁ ⊥ₘ ν ∧ μ₂ ⊥ₘ ν := by
  rw [← sum_cond, sum_left, Bool.forall_bool, cond, cond, And.comm]

@[simp]
theorem add_right_iff : μ ⊥ₘ ν₁ + ν₂ ↔ μ ⊥ₘ ν₁ ∧ μ ⊥ₘ ν₂ :=
  comm.trans <| add_left_iff.trans <| and_congr comm comm

theorem add_left (h₁ : ν₁ ⊥ₘ μ) (h₂ : ν₂ ⊥ₘ μ) : ν₁ + ν₂ ⊥ₘ μ :=
  add_left_iff.2 ⟨h₁, h₂⟩

theorem add_right (h₁ : μ ⊥ₘ ν₁) (h₂ : μ ⊥ₘ ν₂) : μ ⊥ₘ ν₁ + ν₂ :=
  add_right_iff.2 ⟨h₁, h₂⟩

theorem smul (r : ℝ≥0∞) (h : ν ⊥ₘ μ) : r • ν ⊥ₘ μ :=
  h.mono_ac (AbsolutelyContinuous.rfl.smul r) AbsolutelyContinuous.rfl

theorem smul_nnreal (r : ℝ≥0 ) (h : ν ⊥ₘ μ) : r • ν ⊥ₘ μ :=
  h.smul r

end MutuallySingular

end Measureₓ

end MeasureTheory

