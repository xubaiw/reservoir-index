/-
Copyright (c) 2021 Yury Kudriashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudriashov, Malo Jaffré
-/
import Mathbin.Analysis.Convex.Function

/-!
# Slopes of convex functions

This file relates convexity/concavity of functions in a linearly ordered field and the monotonicity
of their slopes.

The main use is to show convexity/concavity from monotonicity of the derivative.
-/


variable {𝕜 : Type _} [LinearOrderedField 𝕜] {s : Set 𝕜} {f : 𝕜 → 𝕜}

/-- If `f : 𝕜 → 𝕜` is convex, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is less than the slope of the secant line of `f` on `[x, z]`. -/
theorem ConvexOn.slope_mono_adjacent (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y)
    (hyz : y < z) : (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) := by
  have hxz := hxy.trans hyz
  rw [← sub_pos] at hxy hxz hyz
  suffices f y / (y - x) + f y / (z - y) ≤ f x / (y - x) + f z / (z - y) by
    ring_nf  at this⊢
    linarith
  set a := (z - y) / (z - x)
  set b := (y - x) / (z - x)
  have hy : a • x + b • z = y := by
    field_simp
    rw [div_eq_iff] <;> [ring, linarith]
  have key :=
    hf.2 hx hz
      (show 0 ≤ a by
        apply div_nonneg <;> linarith)
      (show 0 ≤ b by
        apply div_nonneg <;> linarith)
      (show a + b = 1 by
        field_simp
        rw [div_eq_iff] <;> [ring, linarith])
  rw [hy] at key
  replace key := mul_le_mul_of_nonneg_left key hxz.le
  field_simp [hxy.ne', hyz.ne', hxz.ne', mul_comm (z - x) _]  at key⊢
  rw [div_le_div_right]
  · linarith
    
  · nlinarith
    

/-- If `f : 𝕜 → 𝕜` is concave, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is greater than the slope of the secant line of `f` on `[x, z]`. -/
theorem ConcaveOn.slope_anti_adjacent (hf : ConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y)
    (hyz : y < z) : (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) := by
  rw [← neg_le_neg_iff, ← neg_sub_neg (f x), ← neg_sub_neg (f y)]
  simp_rw [← Pi.neg_apply, ← neg_div, neg_sub]
  exact ConvexOn.slope_mono_adjacent hf.neg hx hz hxy hyz

/-- If `f : 𝕜 → 𝕜` is strictly convex, then for any three points `x < y < z` the slope of the
secant line of `f` on `[x, y]` is strictly less than the slope of the secant line of `f` on
`[x, z]`. -/
theorem StrictConvexOn.slope_strict_mono_adjacent (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) : (f y - f x) / (y - x) < (f z - f y) / (z - y) := by
  have hxz := hxy.trans hyz
  have hxz' := hxz.ne
  rw [← sub_pos] at hxy hxz hyz
  suffices f y / (y - x) + f y / (z - y) < f x / (y - x) + f z / (z - y) by
    ring_nf  at this⊢
    linarith
  set a := (z - y) / (z - x)
  set b := (y - x) / (z - x)
  have hy : a • x + b • z = y := by
    field_simp
    rw [div_eq_iff] <;> [ring, linarith]
  have key :=
    hf.2 hx hz hxz' (div_pos hyz hxz) (div_pos hxy hxz)
      (show a + b = 1 by
        field_simp
        rw [div_eq_iff] <;> [ring, linarith])
  rw [hy] at key
  replace key := mul_lt_mul_of_pos_left key hxz
  field_simp [hxy.ne', hyz.ne', hxz.ne', mul_comm (z - x) _]  at key⊢
  rw [div_lt_div_right]
  · linarith
    
  · nlinarith
    

/-- If `f : 𝕜 → 𝕜` is strictly concave, then for any three points `x < y < z` the slope of the
secant line of `f` on `[x, y]` is strictly greater than the slope of the secant line of `f` on
`[x, z]`. -/
theorem StrictConcaveOn.slope_anti_adjacent (hf : StrictConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) : (f z - f y) / (z - y) < (f y - f x) / (y - x) := by
  rw [← neg_lt_neg_iff, ← neg_sub_neg (f x), ← neg_sub_neg (f y)]
  simp_rw [← Pi.neg_apply, ← neg_div, neg_sub]
  exact StrictConvexOn.slope_strict_mono_adjacent hf.neg hx hz hxy hyz

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
less than the slope of the secant line of `f` on `[x, z]`, then `f` is convex. -/
theorem convex_on_of_slope_mono_adjacent (hs : Convex 𝕜 s)
    (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z → (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :
    ConvexOn 𝕜 s f :=
  (LinearOrderₓ.convex_on_of_lt hs) fun x hx z hz hxz a b ha hb hab => by
    let y := a * x + b * z
    have hxy : x < y := by
      rw [← one_mulₓ x, ← hab, add_mulₓ]
      exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _
    have hyz : y < z := by
      rw [← one_mulₓ z, ← hab, add_mulₓ]
      exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _
    have : (f y - f x) * (z - y) ≤ (f z - f y) * (y - x) :=
      (div_le_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz)
    have hxz : 0 < z - x := sub_pos.2 (hxy.trans hyz)
    have ha : (z - y) / (z - x) = a := by
      rw [eq_comm, ← sub_eq_iff_eq_add'] at hab
      simp_rw [div_eq_iff hxz.ne', y, ← hab]
      ring
    have hb : (y - x) / (z - x) = b := by
      rw [eq_comm, ← sub_eq_iff_eq_add] at hab
      simp_rw [div_eq_iff hxz.ne', y, ← hab]
      ring
    rwa [sub_mul, sub_mul, sub_le_iff_le_add', ← add_sub_assoc, le_sub_iff_add_le, ← mul_addₓ, sub_add_sub_cancel, ←
      le_div_iff hxz, add_div, mul_div_assoc, mul_div_assoc, mul_comm (f x), mul_comm (f z), ha, hb] at this

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
greater than the slope of the secant line of `f` on `[x, z]`, then `f` is concave. -/
theorem concave_on_of_slope_anti_adjacent (hs : Convex 𝕜 s)
    (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) :
    ConcaveOn 𝕜 s f := by
  rw [← neg_convex_on_iff]
  refine' convex_on_of_slope_mono_adjacent hs fun x y z hx hz hxy hyz => _
  rw [← neg_le_neg_iff]
  simp_rw [← neg_div, neg_sub, Pi.neg_apply, neg_sub_neg]
  exact hf hx hz hxy hyz

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
strictly less than the slope of the secant line of `f` on `[x, z]`, then `f` is strictly convex. -/
theorem strict_convex_on_of_slope_strict_mono_adjacent (hs : Convex 𝕜 s)
    (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z → (f y - f x) / (y - x) < (f z - f y) / (z - y)) :
    StrictConvexOn 𝕜 s f :=
  (LinearOrderₓ.strict_convex_on_of_lt hs) fun x hx z hz hxz a b ha hb hab => by
    let y := a * x + b * z
    have hxy : x < y := by
      rw [← one_mulₓ x, ← hab, add_mulₓ]
      exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _
    have hyz : y < z := by
      rw [← one_mulₓ z, ← hab, add_mulₓ]
      exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _
    have : (f y - f x) * (z - y) < (f z - f y) * (y - x) :=
      (div_lt_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz)
    have hxz : 0 < z - x := sub_pos.2 (hxy.trans hyz)
    have ha : (z - y) / (z - x) = a := by
      rw [eq_comm, ← sub_eq_iff_eq_add'] at hab
      simp_rw [div_eq_iff hxz.ne', y, ← hab]
      ring
    have hb : (y - x) / (z - x) = b := by
      rw [eq_comm, ← sub_eq_iff_eq_add] at hab
      simp_rw [div_eq_iff hxz.ne', y, ← hab]
      ring
    rwa [sub_mul, sub_mul, sub_lt_iff_lt_add', ← add_sub_assoc, lt_sub_iff_add_lt, ← mul_addₓ, sub_add_sub_cancel, ←
      lt_div_iff hxz, add_div, mul_div_assoc, mul_div_assoc, mul_comm (f x), mul_comm (f z), ha, hb] at this

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
strictly greater than the slope of the secant line of `f` on `[x, z]`, then `f` is strictly concave.
-/
theorem strict_concave_on_of_slope_strict_anti_adjacent (hs : Convex 𝕜 s)
    (hf : ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) < (f y - f x) / (y - x)) :
    StrictConcaveOn 𝕜 s f := by
  rw [← neg_strict_convex_on_iff]
  refine' strict_convex_on_of_slope_strict_mono_adjacent hs fun x y z hx hz hxy hyz => _
  rw [← neg_lt_neg_iff]
  simp_rw [← neg_div, neg_sub, Pi.neg_apply, neg_sub_neg]
  exact hf hx hz hxy hyz

/-- A function `f : 𝕜 → 𝕜` is convex iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is less than the slope of the secant line of `f` on `[x, z]`. -/
theorem convex_on_iff_slope_mono_adjacent :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z → (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
  ⟨fun h => ⟨h.1, fun x y z => h.slope_mono_adjacent⟩, fun h => convex_on_of_slope_mono_adjacent h.1 h.2⟩

/-- A function `f : 𝕜 → 𝕜` is concave iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is greater than the slope of the secant line of `f` on `[x, z]`. -/
theorem concave_on_iff_slope_anti_adjacent :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
  ⟨fun h => ⟨h.1, fun x y z => h.slope_anti_adjacent⟩, fun h => concave_on_of_slope_anti_adjacent h.1 h.2⟩

/-- A function `f : 𝕜 → 𝕜` is strictly convex iff for any three points `x < y < z` the slope of
the secant line of `f` on `[x, y]` is strictly less than the slope of the secant line of `f` on
`[x, z]`. -/
theorem strict_convex_on_iff_slope_strict_mono_adjacent :
    StrictConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z → (f y - f x) / (y - x) < (f z - f y) / (z - y) :=
  ⟨fun h => ⟨h.1, fun x y z => h.slope_strict_mono_adjacent⟩, fun h =>
    strict_convex_on_of_slope_strict_mono_adjacent h.1 h.2⟩

/-- A function `f : 𝕜 → 𝕜` is strictly concave iff for any three points `x < y < z` the slope of
the secant line of `f` on `[x, y]` is strictly greater than the slope of the secant line of `f` on
`[x, z]`. -/
theorem strict_concave_on_iff_slope_strict_anti_adjacent :
    StrictConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) < (f y - f x) / (y - x) :=
  ⟨fun h => ⟨h.1, fun x y z => h.slope_anti_adjacent⟩, fun h => strict_concave_on_of_slope_strict_anti_adjacent h.1 h.2⟩

