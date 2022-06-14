/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.Convex.Integral
import Mathbin.MeasureTheory.Integral.IntervalIntegral

/-!
# Integral average over an interval

In this file we introduce notation `⨍ x in a..b, f x` for the average `⨍ x in Ι a b, f x` of `f`
over the interval `Ι a b = set.Ioc (min a b) (max a b)` w.r.t. the Lebesgue measure, then prove
formulas for this average:

* `interval_average_eq`: `⨍ x in a..b, f x = (b - a)⁻¹ • ∫ x in a..b, f x`;
* `interval_average_eq_div`: `⨍ x in a..b, f x = (∫ x in a..b, f x) / (b - a)`.

We also prove that `⨍ x in a..b, f x = ⨍ x in b..a, f x`, see `interval_average_symm`.

## Notation

`⨍ x in a..b, f x`: average of `f` over the interval `Ι a b` w.r.t. the Lebesgue measure.

-/


open MeasureTheory Set TopologicalSpace

open Interval

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [CompleteSpace E]

-- mathport name: «expr⨍ in .. , »
notation3 "⨍ " (...) " in " a ".." b ", " r:(scoped f => average Measure.restrict volume Ι a b f) => r

theorem interval_average_symm (f : ℝ → E) (a b : ℝ) : (⨍ x in a..b, f x) = ⨍ x in b..a, f x := by
  rw [set_average_eq, set_average_eq, interval_oc_swap]

theorem interval_average_eq (f : ℝ → E) (a b : ℝ) : (⨍ x in a..b, f x) = (b - a)⁻¹ • ∫ x in a..b, f x := by
  cases' le_or_ltₓ a b with h h
  · rw [set_average_eq, interval_oc_of_le h, Real.volume_Ioc, intervalIntegral.integral_of_le h,
      Ennreal.to_real_of_real (sub_nonneg.2 h)]
    
  · rw [set_average_eq, interval_oc_of_lt h, Real.volume_Ioc, intervalIntegral.integral_of_ge h.le,
      Ennreal.to_real_of_real (sub_nonneg.2 h.le), smul_neg, ← neg_smul, ← inv_neg, neg_sub]
    

theorem interval_average_eq_div (f : ℝ → ℝ) (a b : ℝ) : (⨍ x in a..b, f x) = (∫ x in a..b, f x) / (b - a) := by
  rw [interval_average_eq, smul_eq_mul, div_eq_inv_mul]

