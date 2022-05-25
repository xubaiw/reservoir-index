/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Analysis.Convex.StrictConvexSpace

/-!
# Uniformly convex spaces

This file defines uniformly convex spaces, which are real normed vector spaces in which for all
strictly positive `ε`, there exists some strictly positive `δ` such that `ε ≤ ∥x - y∥` implies
`∥x + y∥ ≤ 2 - δ` for all `x` and `y` of norm at most than `1`. This means that the triangle
inequality is strict with a uniform bound, as opposed to strictly convex spaces where the triangle
inequality is strict but not necessarily uniformly (`∥x + y∥ < ∥x∥ + ∥y∥` for all `x` and `y` not in
the same ray).

## Main declarations

`uniform_convex_space E` means that `E` is a uniformly convex space.

## TODO

* Milman-Pettis
* Hanner's inequalities

## Tags

convex, uniformly convex
-/


open Set Metric

open Convex Pointwise

/-- A *uniformly convex space* is a real normed space where .

See also `uniform_convex_space.of_uniform_convex_closed_unit_ball`. -/
class UniformConvexSpace (E : Type _) [SemiNormedGroup E] : Prop where
  uniform_convex : ∀ ⦃ε : ℝ⦄, 0 < ε → ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ∥x∥ = 1 → ∀ ⦃y⦄, ∥y∥ = 1 → ε ≤ ∥x - y∥ → ∥x + y∥ ≤ 2 - δ

variable {E : Type _}

section SemiNormedGroup

variable (E) [SemiNormedGroup E] [UniformConvexSpace E] {ε : ℝ}

theorem exists_forall_sphere_dist_add_le_two_sub (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ∥x∥ = 1 → ∀ ⦃y⦄, ∥y∥ = 1 → ε ≤ ∥x - y∥ → ∥x + y∥ ≤ 2 - δ :=
  UniformConvexSpace.uniform_convex hε

variable [NormedSpace ℝ E]

theorem exists_forall_closed_ball_dist_add_le_two_sub (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ∥x∥ ≤ 1 → ∀ ⦃y⦄, ∥y∥ ≤ 1 → ε ≤ ∥x - y∥ → ∥x + y∥ ≤ 2 - δ := by
  have hε' : 0 < ε / 3 := div_pos hε zero_lt_three
  obtain ⟨δ, hδ, h⟩ := exists_forall_sphere_dist_add_le_two_sub E hε'
  set δ' := min (1 / 2) (min (ε / 3) <| δ / 3)
  refine' ⟨δ', lt_minₓ one_half_pos <| lt_minₓ hε' (div_pos hδ zero_lt_three), fun x hx y hy hxy => _⟩
  obtain hx' | hx' := le_or_ltₓ ∥x∥ (1 - δ')
  · exact (norm_add_le_of_le hx' hy).trans (sub_add_eq_add_sub _ _ _).le
    
  obtain hy' | hy' := le_or_ltₓ ∥y∥ (1 - δ')
  · exact (norm_add_le_of_le hx hy').trans (add_sub_assoc _ _ _).Ge
    
  have hδ' : 0 < 1 - δ' := sub_pos_of_lt (min_lt_of_left_lt one_half_lt_one)
  have h₁ : ∀ z : E, 1 - δ' < ∥z∥ → ∥∥z∥⁻¹ • z∥ = 1 := by
    rintro z hz
    rw [norm_smul_of_nonneg (inv_nonneg.2 <| norm_nonneg _), inv_mul_cancel (hδ'.trans hz).ne']
  have h₂ : ∀ z : E, ∥z∥ ≤ 1 → 1 - δ' ≤ ∥z∥ → ∥∥z∥⁻¹ • z - z∥ ≤ δ' := by
    rintro z hz hδz
    nth_rw 2[← one_smul ℝ z]
    rwa [← sub_smul, norm_smul_of_nonneg (sub_nonneg_of_le <| one_le_inv (hδ'.trans_le hδz) hz), sub_mul,
      inv_mul_cancel (hδ'.trans_le hδz).ne', one_mulₓ, sub_le]
  set x' := ∥x∥⁻¹ • x
  set y' := ∥y∥⁻¹ • y
  have hxy' : ε / 3 ≤ ∥x' - y'∥ :=
    calc
      ε / 3 = ε - (ε / 3 + ε / 3) := by
        ring
      _ ≤ ∥x - y∥ - (∥x' - x∥ + ∥y' - y∥) :=
        sub_le_sub hxy
          (add_le_add ((h₂ _ hx hx'.le).trans <| min_le_of_right_le <| min_le_leftₓ _ _) <|
            (h₂ _ hy hy'.le).trans <| min_le_of_right_le <| min_le_leftₓ _ _)
      _ ≤ _ := by
        have : ∀ x' y', x - y = x' - y' + (x - x') + (y' - y) := fun _ _ => by
          abel
        rw [sub_le_iff_le_add, norm_sub_rev _ x, ← add_assocₓ, this]
        exact norm_add₃_le _ _ _
      
  calc ∥x + y∥ ≤ ∥x' + y'∥ + ∥x' - x∥ + ∥y' - y∥ := by
      have : ∀ x' y', x + y = x' + y' + (x - x') + (y - y') := fun _ _ => by
        abel
      rw [norm_sub_rev, norm_sub_rev y', this]
      exact norm_add₃_le _ _ _ _ ≤ 2 - δ + δ' + δ' :=
      add_le_add_three (h (h₁ _ hx') (h₁ _ hy') hxy') (h₂ _ hx hx'.le) (h₂ _ hy hy'.le)_ ≤ 2 - δ' := by
      rw [← le_sub_iff_add_le, ← le_sub_iff_add_le, sub_sub, sub_sub]
      refine' sub_le_sub_left _ _
      ring_nf
      rw [← mul_div_cancel' δ three_ne_zero]
      exact mul_le_mul_of_nonneg_left (min_le_of_right_le <| min_le_rightₓ _ _) three_pos.le

theorem exists_forall_closed_ball_dist_add_le_two_mul_sub (hε : 0 < ε) (r : ℝ) :
    ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ∥x∥ ≤ r → ∀ ⦃y⦄, ∥y∥ ≤ r → ε ≤ ∥x - y∥ → ∥x + y∥ ≤ 2 * r - δ := by
  obtain hr | hr := le_or_ltₓ r 0
  · exact
      ⟨1, one_pos, fun x hx y hy h =>
        (hε.not_le <| h.trans <| (norm_sub_le _ _).trans <| add_nonpos (hx.trans hr) (hy.trans hr)).elim⟩
    
  obtain ⟨δ, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (div_pos hε hr)
  refine' ⟨δ * r, mul_pos hδ hr, fun x hx y hy hxy => _⟩
  rw [← div_le_one hr, div_eq_inv_mul, ← norm_smul_of_nonneg (inv_nonneg.2 hr.le)] at hx hy <;>
    try
      infer_instance
  have := h hx hy
  simp_rw [← smul_add, ← smul_sub, norm_smul_of_nonneg (inv_nonneg.2 hr.le), ← div_eq_inv_mul, div_le_div_right hr,
    div_le_iff hr, sub_mul]  at this
  exact this hxy

end SemiNormedGroup

variable [NormedGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]

-- See note [lower instance priority]
instance (priority := 100) UniformConvexSpace.to_strict_convex_space : StrictConvexSpace ℝ E :=
  (StrictConvexSpace.of_norm_add_lt one_half_pos one_half_pos (add_halves _)) fun x y hx hy hxy => by
    obtain ⟨δ, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (norm_sub_pos_iff.2 hxy)
    rw [← smul_add, norm_smul_of_nonneg one_half_pos.le, ← lt_div_iff' one_half_pos, one_div_one_div]
    exact (h hx hy le_rfl).trans_lt (sub_lt_self _ hδ)

