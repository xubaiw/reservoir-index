/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import Mathbin.Analysis.SpecialFunctions.Log.Basic
import Mathbin.Analysis.SpecialFunctions.Pow
import Mathbin.Data.Int.Log

/-!
# Real logarithm base `b`

In this file we define `real.logb` to be the logarithm of a real number in a given base `b`. We
define this as the division of the natural logarithms of the argument and the base, so that we have
a globally defined function with `logb b 0 = 0`, `logb b (-x) = logb b x` `logb 0 x = 0` and
`logb (-b) x = logb b x`.

We prove some basic properties of this function and its relation to `rpow`.

## Tags

logarithm, continuity
-/


open Set Filter Function

open TopologicalSpace

noncomputable section

namespace Real

variable {b x y : ℝ}

/-- The real logarithm in a given base. As with the natural logarithm, we define `logb b x` to
be `logb b |x|` for `x < 0`, and `0` for `x = 0`.-/
@[pp_nodot]
noncomputable def logb (b x : ℝ) : ℝ :=
  log x / log b

theorem log_div_log : log x / log b = logb b x :=
  rfl

@[simp]
theorem logb_zero : logb b 0 = 0 := by
  simp [logb]

@[simp]
theorem logb_one : logb b 1 = 0 := by
  simp [logb]

@[simp]
theorem logb_abs (x : ℝ) : logb b (abs x) = logb b x := by
  rw [logb, logb, log_abs]

@[simp]
theorem logb_neg_eq_logb (x : ℝ) : logb b (-x) = logb b x := by
  rw [← logb_abs x, ← logb_abs (-x), abs_neg]

theorem logb_mul (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x * y) = logb b x + logb b y := by
  simp_rw [logb, log_mul hx hy, add_div]

theorem logb_div (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x / y) = logb b x - logb b y := by
  simp_rw [logb, log_div hx hy, sub_div]

@[simp]
theorem logb_inv (x : ℝ) : logb b x⁻¹ = -logb b x := by
  simp [logb, neg_div]

section BPosAndNeOne

variable (b_pos : 0 < b)

variable (b_ne_one : b ≠ 1)

include b_pos b_ne_one

private theorem log_b_ne_zero : log b ≠ 0 := by
  have b_ne_zero : b ≠ 0
  linarith
  have b_ne_minus_one : b ≠ -1
  linarith
  simp [b_ne_one, b_ne_zero, b_ne_minus_one]

@[simp]
theorem logb_rpow : logb b (b ^ x) = x := by
  rw [logb, div_eq_iff, log_rpow b_pos]
  exact log_b_ne_zero b_pos b_ne_one

theorem rpow_logb_eq_abs (hx : x ≠ 0) : b ^ logb b x = abs x := by
  apply log_inj_on_pos
  simp only [Set.mem_Ioi]
  apply rpow_pos_of_pos b_pos
  simp only [abs_pos, mem_Ioi, Ne.def, hx, not_false_iff]
  rw [log_rpow b_pos, logb, log_abs]
  field_simp [log_b_ne_zero b_pos b_ne_one]

@[simp]
theorem rpow_logb (hx : 0 < x) : b ^ logb b x = x := by
  rw [rpow_logb_eq_abs b_pos b_ne_one hx.ne']
  exact abs_of_pos hx

theorem rpow_logb_of_neg (hx : x < 0) : b ^ logb b x = -x := by
  rw [rpow_logb_eq_abs b_pos b_ne_one (ne_of_ltₓ hx)]
  exact abs_of_neg hx

theorem surj_on_logb : SurjOn (logb b) (Ioi 0) Univ := fun x _ =>
  ⟨rpow b x, rpow_pos_of_pos b_pos x, logb_rpow b_pos b_ne_one⟩

theorem logb_surjective : Surjective (logb b) := fun x => ⟨b ^ x, logb_rpow b_pos b_ne_one⟩

@[simp]
theorem range_logb : Range (logb b) = univ :=
  (logb_surjective b_pos b_ne_one).range_eq

theorem surj_on_logb' : SurjOn (logb b) (Iio 0) Univ := by
  intro x x_in_univ
  use -(b ^ x)
  constructor
  · simp only [Right.neg_neg_iff, Set.mem_Iio]
    apply rpow_pos_of_pos b_pos
    
  · rw [logb_neg_eq_logb, logb_rpow b_pos b_ne_one]
    

end BPosAndNeOne

section OneLtB

variable (hb : 1 < b)

include hb

private theorem b_pos : 0 < b := by
  linarith

private theorem b_ne_one : b ≠ 1 := by
  linarith

@[simp]
theorem logb_le_logb (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ x ≤ y := by
  rw [logb, logb, div_le_div_right (log_pos hb), log_le_log h h₁]

theorem logb_lt_logb (hx : 0 < x) (hxy : x < y) : logb b x < logb b y := by
  rw [logb, logb, div_lt_div_right (log_pos hb)]
  exact log_lt_log hx hxy

@[simp]
theorem logb_lt_logb_iff (hx : 0 < x) (hy : 0 < y) : logb b x < logb b y ↔ x < y := by
  rw [logb, logb, div_lt_div_right (log_pos hb)]
  exact log_lt_log_iff hx hy

theorem logb_le_iff_le_rpow (hx : 0 < x) : logb b x ≤ y ↔ x ≤ b ^ y := by
  rw [← rpow_le_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one hb) hx]

theorem logb_lt_iff_lt_rpow (hx : 0 < x) : logb b x < y ↔ x < b ^ y := by
  rw [← rpow_lt_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one hb) hx]

theorem le_logb_iff_rpow_le (hy : 0 < y) : x ≤ logb b y ↔ b ^ x ≤ y := by
  rw [← rpow_le_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one hb) hy]

theorem lt_logb_iff_rpow_lt (hy : 0 < y) : x < logb b y ↔ b ^ x < y := by
  rw [← rpow_lt_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one hb) hy]

theorem logb_pos_iff (hx : 0 < x) : 0 < logb b x ↔ 1 < x := by
  rw [← @logb_one b]
  rw [logb_lt_logb_iff hb zero_lt_one hx]

theorem logb_pos (hx : 1 < x) : 0 < logb b x := by
  rw [logb_pos_iff hb (lt_transₓ zero_lt_one hx)]
  exact hx

theorem logb_neg_iff (h : 0 < x) : logb b x < 0 ↔ x < 1 := by
  rw [← logb_one]
  exact logb_lt_logb_iff hb h zero_lt_one

theorem logb_neg (h0 : 0 < x) (h1 : x < 1) : logb b x < 0 :=
  (logb_neg_iff hb h0).2 h1

theorem logb_nonneg_iff (hx : 0 < x) : 0 ≤ logb b x ↔ 1 ≤ x := by
  rw [← not_ltₓ, logb_neg_iff hb hx, not_ltₓ]

theorem logb_nonneg (hx : 1 ≤ x) : 0 ≤ logb b x :=
  (logb_nonneg_iff hb (zero_lt_one.trans_le hx)).2 hx

theorem logb_nonpos_iff (hx : 0 < x) : logb b x ≤ 0 ↔ x ≤ 1 := by
  rw [← not_ltₓ, logb_pos_iff hb hx, not_ltₓ]

theorem logb_nonpos_iff' (hx : 0 ≤ x) : logb b x ≤ 0 ↔ x ≤ 1 := by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [le_reflₓ, zero_le_one]
    
  exact logb_nonpos_iff hb hx

theorem logb_nonpos (hx : 0 ≤ x) (h'x : x ≤ 1) : logb b x ≤ 0 :=
  (logb_nonpos_iff' hb hx).2 h'x

theorem strict_mono_on_logb : StrictMonoOn (logb b) (Set.Ioi 0) := fun x hx y hy hxy => logb_lt_logb hb hx hxy

theorem strict_anti_on_logb : StrictAntiOn (logb b) (Set.Iio 0) := by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs y, ← logb_abs x]
  refine' logb_lt_logb hb (abs_pos.2 hy.ne) _
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

theorem logb_inj_on_pos : Set.InjOn (logb b) (Set.Ioi 0) :=
  (strict_mono_on_logb hb).InjOn

theorem eq_one_of_pos_of_logb_eq_zero (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 :=
  logb_inj_on_pos hb (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.logb_one.symm)

theorem logb_ne_zero_of_pos_of_ne_one (hx_pos : 0 < x) (hx : x ≠ 1) : logb b x ≠ 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero hb hx_pos) hx

theorem tendsto_logb_at_top : Tendsto (logb b) atTop atTop :=
  Tendsto.at_top_div_const (log_pos hb) tendsto_log_at_top

end OneLtB

section BPosAndBLtOne

variable (b_pos : 0 < b)

variable (b_lt_one : b < 1)

include b_lt_one

private theorem b_ne_one : b ≠ 1 := by
  linarith

include b_pos

@[simp]
theorem logb_le_logb_of_base_lt_one (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ y ≤ x := by
  rw [logb, logb, div_le_div_right_of_neg (log_neg b_pos b_lt_one), log_le_log h₁ h]

theorem logb_lt_logb_of_base_lt_one (hx : 0 < x) (hxy : x < y) : logb b y < logb b x := by
  rw [logb, logb, div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log hx hxy

@[simp]
theorem logb_lt_logb_iff_of_base_lt_one (hx : 0 < x) (hy : 0 < y) : logb b x < logb b y ↔ y < x := by
  rw [logb, logb, div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log_iff hy hx

theorem logb_le_iff_le_rpow_of_base_lt_one (hx : 0 < x) : logb b x ≤ y ↔ b ^ y ≤ x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hx]

theorem logb_lt_iff_lt_rpow_of_base_lt_one (hx : 0 < x) : logb b x < y ↔ b ^ y < x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hx]

theorem le_logb_iff_rpow_le_of_base_lt_one (hy : 0 < y) : x ≤ logb b y ↔ y ≤ b ^ x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hy]

theorem lt_logb_iff_rpow_lt_of_base_lt_one (hy : 0 < y) : x < logb b y ↔ y < b ^ x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hy]

theorem logb_pos_iff_of_base_lt_one (hx : 0 < x) : 0 < logb b x ↔ x < 1 := by
  rw [← @logb_one b, logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one zero_lt_one hx]

theorem logb_pos_of_base_lt_one (hx : 0 < x) (hx' : x < 1) : 0 < logb b x := by
  rw [logb_pos_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'

theorem logb_neg_iff_of_base_lt_one (h : 0 < x) : logb b x < 0 ↔ 1 < x := by
  rw [← @logb_one b, logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one h zero_lt_one]

theorem logb_neg_of_base_lt_one (h1 : 1 < x) : logb b x < 0 :=
  (logb_neg_iff_of_base_lt_one b_pos b_lt_one (lt_transₓ zero_lt_one h1)).2 h1

theorem logb_nonneg_iff_of_base_lt_one (hx : 0 < x) : 0 ≤ logb b x ↔ x ≤ 1 := by
  rw [← not_ltₓ, logb_neg_iff_of_base_lt_one b_pos b_lt_one hx, not_ltₓ]

theorem logb_nonneg_of_base_lt_one (hx : 0 < x) (hx' : x ≤ 1) : 0 ≤ logb b x := by
  rw [logb_nonneg_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'

theorem logb_nonpos_iff_of_base_lt_one (hx : 0 < x) : logb b x ≤ 0 ↔ 1 ≤ x := by
  rw [← not_ltₓ, logb_pos_iff_of_base_lt_one b_pos b_lt_one hx, not_ltₓ]

theorem strict_anti_on_logb_of_base_lt_one : StrictAntiOn (logb b) (Set.Ioi 0) := fun x hx y hy hxy =>
  logb_lt_logb_of_base_lt_one b_pos b_lt_one hx hxy

theorem strict_mono_on_logb_of_base_lt_one : StrictMonoOn (logb b) (Set.Iio 0) := by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← logb_abs y, ← logb_abs x]
  refine' logb_lt_logb_of_base_lt_one b_pos b_lt_one (abs_pos.2 hy.ne) _
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

theorem logb_inj_on_pos_of_base_lt_one : Set.InjOn (logb b) (Set.Ioi 0) :=
  (strict_anti_on_logb_of_base_lt_one b_pos b_lt_one).InjOn

theorem eq_one_of_pos_of_logb_eq_zero_of_base_lt_one (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 :=
  logb_inj_on_pos_of_base_lt_one b_pos b_lt_one (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one)
    (h₂.trans Real.logb_one.symm)

theorem logb_ne_zero_of_pos_of_ne_one_of_base_lt_one (hx_pos : 0 < x) (hx : x ≠ 1) : logb b x ≠ 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero_of_base_lt_one b_pos b_lt_one hx_pos) hx

theorem tendsto_logb_at_top_of_base_lt_one : Tendsto (logb b) atTop atBot := by
  rw [tendsto_at_top_at_bot]
  intro e
  use 1⊔b ^ e
  intro a
  simp only [and_imp, sup_le_iff]
  intro ha
  rw [logb_le_iff_le_rpow_of_base_lt_one b_pos b_lt_one]
  tauto
  exact lt_of_lt_of_leₓ zero_lt_one ha

end BPosAndBLtOne

theorem floor_logb_nat_cast {b : ℕ} {r : ℝ} (hb : 1 < b) (hr : 0 ≤ r) : ⌊logb b r⌋ = Int.log b r := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.log_zero_right, Int.floor_zero]
    
  have hb1' : 1 < (b : ℝ) := nat.one_lt_cast.mpr hb
  apply le_antisymmₓ
  · rw [← Int.zpow_le_iff_le_log hb hr, ← rpow_int_cast b]
    refine' le_of_le_of_eq _ (rpow_logb (zero_lt_one.trans hb1') hb1'.ne' hr)
    exact rpow_le_rpow_of_exponent_le hb1'.le (Int.floor_le _)
    
  · rw [Int.le_floor, le_logb_iff_rpow_le hb1' hr, rpow_int_cast]
    exact Int.zpow_log_le_self hb hr
    

theorem ceil_logb_nat_cast {b : ℕ} {r : ℝ} (hb : 1 < b) (hr : 0 ≤ r) : ⌈logb b r⌉ = Int.clog b r := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [logb_zero, Int.clog_zero_right, Int.ceil_zero]
    
  have hb1' : 1 < (b : ℝ) := nat.one_lt_cast.mpr hb
  apply le_antisymmₓ
  · rw [Int.ceil_le, logb_le_iff_le_rpow hb1' hr, rpow_int_cast]
    refine' Int.self_le_zpow_clog hb r
    
  · rw [← Int.le_zpow_iff_clog_le hb hr, ← rpow_int_cast b]
    refine' (rpow_logb (zero_lt_one.trans hb1') hb1'.ne' hr).symm.trans_le _
    exact rpow_le_rpow_of_exponent_le hb1'.le (Int.le_ceil _)
    

@[simp]
theorem logb_eq_zero : logb b x = 0 ↔ b = 0 ∨ b = 1 ∨ b = -1 ∨ x = 0 ∨ x = 1 ∨ x = -1 := by
  simp_rw [logb, div_eq_zero_iff, log_eq_zero]
  tauto

-- TODO add other limits and continuous API lemmas analogous to those in log.lean
open BigOperators

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem logb_prod {α : Type _} (s : Finset α) (f : α → ℝ) (hf : ∀, ∀ x ∈ s, ∀, f x ≠ 0) :
    logb b (∏ i in s, f i) = ∑ i in s, logb b (f i) := by
  classical
  induction' s using Finset.induction_on with a s ha ih
  · simp
    
  simp only [Finset.mem_insert, forall_eq_or_imp] at hf
  simp [ha, ih hf.2, logb_mul hf.1 (Finset.prod_ne_zero_iff.2 hf.2)]

end Real

