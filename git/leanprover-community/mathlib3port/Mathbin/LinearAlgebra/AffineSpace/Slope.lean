/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Algebra.Order.Module
import Mathbin.LinearAlgebra.AffineSpace.AffineMap
import Mathbin.Tactic.FieldSimp

/-!
# Slope of a function

In this file we define the slope of a function `f : k → PE` taking values in an affine space over
`k` and prove some basic theorems about `slope`. The `slope` function naturally appears in the Mean
Value Theorem, and in the proof of the fact that a function with nonnegative second derivative on an
interval is convex on this interval.

## Tags

affine space, slope
-/


open AffineMap

variable {k E PE : Type _} [Field k] [AddCommGroupₓ E] [Module k E] [AddTorsor E PE]

include E

/-- `slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)` is the slope of a function `f` on the interval
`[a, b]`. Note that `slope f a a = 0`, not the derivative of `f` at `a`. -/
def slope (f : k → PE) (a b : k) : E :=
  (b - a)⁻¹ • (f b -ᵥ f a)

theorem slope_fun_def (f : k → PE) : slope f = fun a b => (b - a)⁻¹ • (f b -ᵥ f a) :=
  rfl

omit E

theorem slope_def_field (f : k → k) (a b : k) : slope f a b = (f b - f a) / (b - a) :=
  div_eq_inv_mul.symm

@[simp]
theorem slope_same (f : k → PE) (a : k) : (slope f a a : E) = 0 := by
  rw [slope, sub_self, inv_zero, zero_smul]

include E

theorem slope_def_module (f : k → E) (a b : k) : slope f a b = (b - a)⁻¹ • (f b - f a) :=
  rfl

@[simp]
theorem sub_smul_slope (f : k → PE) (a b : k) : (b - a) • slope f a b = f b -ᵥ f a := by
  rcases eq_or_ne a b with (rfl | hne)
  · rw [sub_self, zero_smul, vsub_self]
    
  · rw [slope, smul_inv_smul₀ (sub_ne_zero.2 hne.symm)]
    

theorem sub_smul_slope_vadd (f : k → PE) (a b : k) : (b - a) • slope f a b +ᵥ f a = f b := by
  rw [sub_smul_slope, vsub_vadd]

@[simp]
theorem slope_vadd_const (f : k → E) (c : PE) : (slope fun x => f x +ᵥ c) = slope f := by
  ext a b
  simp only [slope, vadd_vsub_vadd_cancel_right, vsub_eq_sub]

@[simp]
theorem slope_sub_smul (f : k → E) {a b : k} (h : a ≠ b) : slope (fun x => (x - a) • f x) a b = f b := by
  simp [slope, inv_smul_smul₀ (sub_ne_zero.2 h.symm)]

theorem eq_of_slope_eq_zero {f : k → PE} {a b : k} (h : slope f a b = (0 : E)) : f a = f b := by
  rw [← sub_smul_slope_vadd f a b, h, smul_zero, zero_vadd]

theorem slope_comm (f : k → PE) (a b : k) : slope f a b = slope f b a := by
  rw [slope, slope, ← neg_vsub_eq_vsub_rev, smul_neg, ← neg_smul, neg_inv, neg_sub]

/-- `slope f a c` is a linear combination of `slope f a b` and `slope f b c`. This version
explicitly provides coefficients. If `a ≠ c`, then the sum of the coefficients is `1`, so it is
actually an affine combination, see `line_map_slope_slope_sub_div_sub`. -/
theorem sub_div_sub_smul_slope_add_sub_div_sub_smul_slope (f : k → PE) (a b c : k) :
    ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c = slope f a c := by
  by_cases' hab : a = b
  · subst hab
    rw [sub_self, zero_div, zero_smul, zero_addₓ]
    by_cases' hac : a = c
    · simp [hac]
      
    · rw [div_self (sub_ne_zero.2 <| Ne.symm hac), one_smul]
      
    
  by_cases' hbc : b = c
  · subst hbc
    simp [sub_ne_zero.2 (Ne.symm hab)]
    
  rw [add_commₓ]
  simp_rw [slope, div_eq_inv_mul, mul_smul, ← smul_add, smul_inv_smul₀ (sub_ne_zero.2 <| Ne.symm hab),
    smul_inv_smul₀ (sub_ne_zero.2 <| Ne.symm hbc), vsub_add_vsub_cancel]

/-- `slope f a c` is an affine combination of `slope f a b` and `slope f b c`. This version uses
`line_map` to express this property. -/
theorem line_map_slope_slope_sub_div_sub (f : k → PE) (a b c : k) (h : a ≠ c) :
    lineMap (slope f a b) (slope f b c) ((c - b) / (c - a)) = slope f a c := by
  field_simp [sub_ne_zero.2 h.symm, ← sub_div_sub_smul_slope_add_sub_div_sub_smul_slope f a b c, line_map_apply_module]

/-- `slope f a b` is an affine combination of `slope f a (line_map a b r)` and
`slope f (line_map a b r) b`. We use `line_map` to express this property. -/
theorem line_map_slope_line_map_slope_line_map (f : k → PE) (a b r : k) :
    lineMap (slope f (lineMap a b r) b) (slope f a (lineMap a b r)) r = slope f a b := by
  obtain rfl | hab : a = b ∨ a ≠ b := Classical.em _
  · simp
    
  rw [slope_comm _ a, slope_comm _ a, slope_comm _ _ b]
  convert line_map_slope_slope_sub_div_sub f b (line_map a b r) a hab.symm using 2
  rw [line_map_apply_ring, eq_div_iff (sub_ne_zero.2 hab), sub_mul, one_mulₓ, mul_sub, ← sub_sub, sub_sub_cancel]

