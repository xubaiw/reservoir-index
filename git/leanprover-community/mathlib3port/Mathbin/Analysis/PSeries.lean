/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Analysis.SpecialFunctions.Pow

/-!
# Convergence of `p`-series

In this file we prove that the series `∑' k in ℕ, 1 / k ^ p` converges if and only if `p > 1`.
The proof is based on the
[Cauchy condensation test](https://en.wikipedia.org/wiki/Cauchy_condensation_test): `∑ k, f k`
converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. We prove this test in
`nnreal.summable_condensed_iff` and `summable_condensed_iff_of_nonneg`, then use it to prove
`summable_one_div_rpow`. After this transformation, a `p`-series turns into a geometric series.

## TODO

It should be easy to generalize arguments to Schlömilch's generalization of the Cauchy condensation
test once we need it.

## Tags

p-series, Cauchy condensation test
-/


open Filter

open BigOperators Ennreal Nnreal TopologicalSpace

/-!
### Cauchy condensation test

In this section we prove the Cauchy condensation test: for `f : ℕ → ℝ≥0` or `f : ℕ → ℝ`,
`∑ k, f k` converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. Instead of giving a monolithic
proof, we split it into a series of lemmas with explicit estimates of partial sums of each series in
terms of the partial sums of the other series.
-/


namespace Finset

variable {M : Type _} [OrderedAddCommMonoid M] {f : ℕ → M}

theorem le_sum_condensed' (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k in ico 1 (2 ^ n), f k) ≤ ∑ k in range n, 2 ^ k • f (2 ^ k) := by
  induction' n with n ihn
  · simp
    
  suffices (∑ k in Ico (2 ^ n) (2 ^ (n + 1)), f k) ≤ 2 ^ n • f (2 ^ n) by
    rw [sum_range_succ, ← sum_Ico_consecutive]
    exact add_le_add ihn this
    exacts[n.one_le_two_pow, Nat.pow_le_pow_of_le_rightₓ zero_lt_two n.le_succ]
  have : ∀ k ∈ Ico (2 ^ n) (2 ^ (n + 1)), f k ≤ f (2 ^ n) := fun k hk => hf (pow_pos zero_lt_two _) (mem_Ico.mp hk).1
  convert sum_le_sum this
  simp [pow_succₓ, two_mul]

theorem le_sum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k in range (2 ^ n), f k) ≤ f 0 + ∑ k in range n, 2 ^ k • f (2 ^ k) := by
  convert add_le_add_left (le_sum_condensed' hf n) (f 0)
  rw [← sum_range_add_sum_Ico _ n.one_le_two_pow, sum_range_succ, sum_range_zero, zero_addₓ]

theorem sum_condensed_le' (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k in range n, 2 ^ k • f (2 ^ (k + 1))) ≤ ∑ k in ico 2 (2 ^ n + 1), f k := by
  induction' n with n ihn
  · simp
    
  suffices 2 ^ n • f (2 ^ (n + 1)) ≤ ∑ k in Ico (2 ^ n + 1) (2 ^ (n + 1) + 1), f k by
    rw [sum_range_succ, ← sum_Ico_consecutive]
    exact add_le_add ihn this
    exacts[add_le_add_right n.one_le_two_pow _, add_le_add_right (Nat.pow_le_pow_of_le_rightₓ zero_lt_two n.le_succ) _]
  have : ∀ k ∈ Ico (2 ^ n + 1) (2 ^ (n + 1) + 1), f (2 ^ (n + 1)) ≤ f k := fun k hk =>
    hf (n.one_le_two_pow.trans_lt <| (Nat.lt_succ_of_leₓ le_rflₓ).trans_le (mem_Ico.mp hk).1)
      (Nat.le_of_lt_succₓ <| (mem_Ico.mp hk).2)
  convert sum_le_sum this
  simp [pow_succₓ, two_mul]

theorem sum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k in range (n + 1), 2 ^ k • f (2 ^ k)) ≤ f 1 + 2 • ∑ k in ico 2 (2 ^ n + 1), f k := by
  convert add_le_add_left (nsmul_le_nsmul_of_le_right (sum_condensed_le' hf n) 2) (f 1)
  simp [sum_range_succ', add_commₓ, pow_succₓ, mul_nsmul, sum_nsmul]

end Finset

namespace Ennreal

variable {f : ℕ → ℝ≥0∞}

theorem le_tsum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) : (∑' k, f k) ≤ f 0 + ∑' k : ℕ, 2 ^ k * f (2 ^ k) :=
  by
  rw [Ennreal.tsum_eq_supr_nat' (Nat.tendsto_pow_at_top_at_top_of_one_lt _root_.one_lt_two)]
  refine' supr_le fun n => (Finset.le_sum_condensed hf n).trans (add_le_add_left _ _)
  simp only [nsmul_eq_mul, Nat.cast_powₓ, Nat.cast_two]
  apply Ennreal.sum_le_tsum

theorem tsum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) :
    (∑' k : ℕ, 2 ^ k * f (2 ^ k)) ≤ f 1 + 2 * ∑' k, f k := by
  rw [Ennreal.tsum_eq_supr_nat' (tendsto_at_top_mono Nat.le_succₓ tendsto_id), two_mul, ← two_nsmul]
  refine'
    supr_le fun n =>
      le_transₓ _ (add_le_add_left (nsmul_le_nsmul_of_le_right (Ennreal.sum_le_tsum <| Finset.ico 2 (2 ^ n + 1)) _) _)
  simpa using Finset.sum_condensed_le hf n

end Ennreal

namespace Nnreal

/-- Cauchy condensation test for a series of `nnreal` version. -/
theorem summable_condensed_iff {f : ℕ → ℝ≥0 } (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => 2 ^ k * f (2 ^ k)) ↔ Summable f := by
  simp only [← Ennreal.tsum_coe_ne_top_iff_summable, Ne.def, not_iff_not, Ennreal.coe_mul, Ennreal.coe_pow,
    Ennreal.coe_two]
  constructor <;> intro h
  · replace hf : ∀ m n, 1 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m := fun m n hm hmn =>
      Ennreal.coe_le_coe.2 (hf (zero_lt_one.trans hm) hmn)
    simpa [h, Ennreal.add_eq_top] using Ennreal.tsum_condensed_le hf
    
  · replace hf : ∀ m n, 0 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m := fun m n hm hmn => Ennreal.coe_le_coe.2 (hf hm hmn)
    simpa [h, Ennreal.add_eq_top] using Ennreal.le_tsum_condensed hf
    

end Nnreal

/-- Cauchy condensation test for series of nonnegative real numbers. -/
theorem summable_condensed_iff_of_nonneg {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
    (h_mono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) : (Summable fun k : ℕ => 2 ^ k * f (2 ^ k)) ↔ Summable f := by
  lift f to ℕ → ℝ≥0 using h_nonneg
  simp only [Nnreal.coe_le_coe] at *
  exact_mod_cast Nnreal.summable_condensed_iff h_mono

open Real

/-!
### Convergence of the `p`-series

In this section we prove that for a real number `p`, the series `∑' n : ℕ, 1 / (n ^ p)` converges if
and only if `1 < p`. There are many different proofs of this fact. The proof in this file uses the
Cauchy condensation test we formalized above. This test implies that `∑ n, 1 / (n ^ p)` converges if
and only if `∑ n, 2 ^ n / ((2 ^ n) ^ p)` converges, and the latter series is a geometric series with
common ratio `2 ^ {1 - p}`. -/


/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp]
theorem Real.summable_nat_rpow_inv {p : ℝ} : Summable (fun n => (n ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p := by
  cases' le_or_ltₓ 0 p with hp hp
  /- Cauchy condensation test applies only to antitone sequences, so we consider the
    cases `0 ≤ p` and `p < 0` separately. -/
  · rw [← summable_condensed_iff_of_nonneg]
    · simp_rw [Nat.cast_powₓ, Nat.cast_two, ← rpow_nat_cast, ← rpow_mul zero_lt_two.le, mul_comm _ p,
        rpow_mul zero_lt_two.le, rpow_nat_cast, ← inv_pow, ← mul_powₓ, summable_geometric_iff_norm_lt_1]
      nth_rw 0[← rpow_one 2]
      rw [← division_def, ← rpow_sub zero_lt_two, norm_eq_abs, abs_of_pos (rpow_pos_of_pos zero_lt_two _),
        rpow_lt_one_iff zero_lt_two.le]
      norm_num
      
    · intro n
      exact inv_nonneg.2 (rpow_nonneg_of_nonneg n.cast_nonneg _)
      
    · intro m n hm hmn
      exact inv_le_inv_of_le (rpow_pos_of_pos (Nat.cast_pos.2 hm) _) (rpow_le_rpow m.cast_nonneg (Nat.cast_le.2 hmn) hp)
      
    
  -- If `p < 0`, then `1 / n ^ p` tends to infinity, thus the series diverges.
  · suffices ¬Summable (fun n => (n ^ p)⁻¹ : ℕ → ℝ) by
      have : ¬1 < p := fun hp₁ => hp.not_le (zero_le_one.trans hp₁.le)
      simpa [this, -one_div]
    · intro h
      obtain ⟨k : ℕ, hk₁ : ((k ^ p)⁻¹ : ℝ) < 1, hk₀ : k ≠ 0⟩ :=
        ((h.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)).And (eventually_cofinite_ne 0)).exists
      apply hk₀
      rw [← pos_iff_ne_zero, ← @Nat.cast_pos ℝ] at hk₀
      simpa [inv_lt_one_iff_of_pos (rpow_pos_of_pos hk₀ _), one_lt_rpow_iff_of_pos hk₀, hp, hp.not_lt, hk₀] using hk₁
      
    

@[simp]
theorem Real.summable_nat_rpow {p : ℝ} : Summable (fun n => n ^ p : ℕ → ℝ) ↔ p < -1 := by
  rcases neg_surjective p with ⟨p, rfl⟩
  simp [rpow_neg]

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
theorem Real.summable_one_div_nat_rpow {p : ℝ} : Summable (fun n => 1 / n ^ p : ℕ → ℝ) ↔ 1 < p := by
  simp

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp]
theorem Real.summable_nat_pow_inv {p : ℕ} : Summable (fun n => (n ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p := by
  simp only [← rpow_nat_cast, Real.summable_nat_rpow_inv, Nat.one_lt_cast]

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
theorem Real.summable_one_div_nat_pow {p : ℕ} : Summable (fun n => 1 / n ^ p : ℕ → ℝ) ↔ 1 < p := by
  simp

/-- Harmonic series is not unconditionally summable. -/
theorem Real.not_summable_nat_cast_inv : ¬Summable (fun n => n⁻¹ : ℕ → ℝ) := by
  have : ¬Summable (fun n => (n ^ 1)⁻¹ : ℕ → ℝ) := mt Real.summable_nat_pow_inv.1 (lt_irreflₓ 1)
  simpa

/-- Harmonic series is not unconditionally summable. -/
theorem Real.not_summable_one_div_nat_cast : ¬Summable (fun n => 1 / n : ℕ → ℝ) := by
  simpa only [inv_eq_one_div] using Real.not_summable_nat_cast_inv

/-- **Divergence of the Harmonic Series** -/
theorem Real.tendsto_sum_range_one_div_nat_succ_at_top :
    Tendsto (fun n => ∑ i in Finset.range n, (1 / (i + 1) : ℝ)) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_at_top_of_nonneg]
  · exact_mod_cast mt (summable_nat_add_iff 1).1 Real.not_summable_one_div_nat_cast
    
  · exact fun i => div_nonneg zero_le_one i.cast_add_one_pos.le
    

@[simp]
theorem Nnreal.summable_rpow_inv {p : ℝ} : Summable (fun n => (n ^ p)⁻¹ : ℕ → ℝ≥0 ) ↔ 1 < p := by
  simp [← Nnreal.summable_coe]

@[simp]
theorem Nnreal.summable_rpow {p : ℝ} : Summable (fun n => n ^ p : ℕ → ℝ≥0 ) ↔ p < -1 := by
  simp [← Nnreal.summable_coe]

theorem Nnreal.summable_one_div_rpow {p : ℝ} : Summable (fun n => 1 / n ^ p : ℕ → ℝ≥0 ) ↔ 1 < p := by
  simp

section

open Finset

variable {α : Type _} [LinearOrderedField α]

theorem sum_Ioc_inv_sq_le_sub {k n : ℕ} (hk : k ≠ 0) (h : k ≤ n) : (∑ i in ioc k n, ((i ^ 2)⁻¹ : α)) ≤ k⁻¹ - n⁻¹ := by
  refine' Nat.le_induction _ _ n h
  · simp only [Ioc_self, sum_empty, sub_self]
    
  intro n hn IH
  rw [sum_Ioc_succ_top hn]
  apply (add_le_add IH le_rflₓ).trans
  simp only [sub_eq_add_neg, add_assocₓ, Nat.cast_addₓ, Nat.cast_oneₓ, le_add_neg_iff_add_le, add_le_iff_nonpos_right,
    neg_add_le_iff_le_add, add_zeroₓ]
  have A : 0 < (n : α) := by
    simpa using hk.bot_lt.trans_le hn
  have B : 0 < (n : α) + 1 := by
    linarith
  field_simp [B.ne']
  rw [div_le_div_iff _ A, ← sub_nonneg]
  · ring_nf
    exact B.le
    
  · nlinarith
    

theorem sum_Ioo_inv_sq_le (k n : ℕ) : (∑ i in ioo k n, ((i ^ 2)⁻¹ : α)) ≤ 2 / (k + 1) :=
  calc
    (∑ i in ioo k n, ((i ^ 2)⁻¹ : α)) ≤ ∑ i in ioc k (max (k + 1) n), (i ^ 2)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [mem_Ioo] at hx
        simp only [hx, hx.2.le, mem_Ioc, le_max_iff, or_trueₓ, and_selfₓ]
        
      · intro i hi hident
        exact inv_nonneg.2 (sq_nonneg _)
        
    _ ≤ ((k + 1) ^ 2)⁻¹ + ∑ i in ioc k.succ (max (k + 1) n), (i ^ 2)⁻¹ := by
      rw [← Nat.Icc_succ_left, ← Nat.Ico_succ_right, sum_eq_sum_Ico_succ_bot]
      swap
      · exact Nat.succ_lt_succₓ ((Nat.lt_succ_selfₓ k).trans_le (le_max_leftₓ _ _))
        
      rw [Nat.Ico_succ_right, Nat.Icc_succ_left, Nat.cast_succₓ]
    _ ≤ ((k + 1) ^ 2)⁻¹ + (k + 1)⁻¹ := by
      refine' add_le_add le_rflₓ ((sum_Ioc_inv_sq_le_sub _ (le_max_leftₓ _ _)).trans _)
      · simp only [Ne.def, Nat.succ_ne_zero, not_false_iff]
        
      · simp only [Nat.cast_succₓ, one_div, sub_le_self_iff, inv_nonneg, Nat.cast_nonneg]
        
    _ ≤ 1 / (k + 1) + 1 / (k + 1) := by
      have A : (1 : α) ≤ k + 1 := by
        simp only [le_add_iff_nonneg_left, Nat.cast_nonneg]
      simp_rw [← one_div]
      apply add_le_add_right
      refine' div_le_div zero_le_one le_rflₓ (zero_lt_one.trans_le A) _
      simpa using pow_le_pow A one_le_two
    _ = 2 / (k + 1) := by
      ring
    

end

