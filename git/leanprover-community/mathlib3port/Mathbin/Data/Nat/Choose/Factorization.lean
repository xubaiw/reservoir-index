/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Patrick Stevens, Thomas Browning
-/
import Mathbin.Data.Nat.Choose.Central
import Mathbin.Data.Nat.Factorization.Basic
import Mathbin.Data.Nat.Multiplicity

/-!
# Factorization of Binomial Coefficients

This file contains a few results on the multiplicity of prime factors within certain size
bounds in binomial coefficients. These include:

* `nat.factorization_choose_le_log`: a logarithmic upper bound on the multiplicity of a prime in
  a binomial coefficient.
* `nat.factorization_choose_le_one`: Primes above `sqrt n` appear at most once
  in the factorization of `n` choose `k`.
* `nat.factorization_central_binom_of_two_mul_self_lt_three_mul`: Primes from `2 * n / 3` to `n`
do not appear in the factorization of the `n`th central binomial coefficient.
* `nat.factorization_choose_eq_zero_of_lt`: Primes greater than `n` do not
  appear in the factorization of `n` choose `k`.

These results appear in the [Erdős proof of Bertrand's postulate](aigner1999proofs).
-/


open BigOperators

namespace Nat

variable {p n k : ℕ}

/-- A logarithmic upper bound on the multiplicity of a prime in a binomial coefficient.
-/
theorem factorization_choose_le_log : (choose n k).factorization p ≤ log p n := by
  by_cases' h : (choose n k).factorization p = 0
  · simp [← h]
    
  have hp : p.prime := Not.imp_symm (choose n k).factorization_eq_zero_of_non_prime h
  have hkn : k ≤ n := by
    refine' le_of_not_ltₓ fun hnk => h _
    simp [← choose_eq_zero_of_lt hnk]
  rw [factorization_def _ hp, @padic_val_nat_def _ ⟨hp⟩ _ (choose_pos hkn)]
  simp only [← hp.multiplicity_choose hkn (lt_add_one _), ← PartEnat.get_coe]
  refine' (Finset.card_filter_le _ _).trans (le_of_eqₓ (Nat.card_Ico _ _))

/-- A `pow` form of `nat.factorization_choose_le`
-/
theorem pow_factorization_choose_le (hn : 0 < n) : p ^ (choose n k).factorization p ≤ n := by
  cases le_or_ltₓ p 1
  · exact (pow_le_pow_of_le h).trans ((le_of_eqₓ (one_pow _)).trans hn)
    
  · exact (pow_le_iff_le_log h hn).mpr factorization_choose_le_log
    

/-- Primes greater than about `sqrt n` appear only to multiplicity 0 or 1 in the binomial coefficient.
-/
theorem factorization_choose_le_one (p_large : n < p ^ 2) : (choose n k).factorization p ≤ 1 := by
  apply factorization_choose_le_log.trans
  rcases n.eq_zero_or_pos with (rfl | hn0)
  · simp
    
  refine' lt_succ_iff.1 ((lt_pow_iff_log_lt _ hn0).1 p_large)
  contrapose! hn0
  exact lt_succ_iff.1 (lt_of_lt_of_leₓ p_large (pow_le_one' hn0 2))

theorem factorization_choose_of_lt_three_mul (hp' : p ≠ 2) (hk : p ≤ k) (hk' : p ≤ n - k) (hn : n < 3 * p) :
    (choose n k).factorization p = 0 := by
  cases' em' p.prime with hp hp
  · exact factorization_eq_zero_of_non_prime (choose n k) hp
    
  cases' lt_or_leₓ n k with hnk hkn
  · simp [← choose_eq_zero_of_lt hnk]
    
  rw [factorization_def _ hp, @padic_val_nat_def _ ⟨hp⟩ _ (choose_pos hkn)]
  simp only [← hp.multiplicity_choose hkn (lt_add_one _), ← PartEnat.get_coe, ← Finset.card_eq_zero, ←
    Finset.filter_eq_empty_iff, ← not_leₓ]
  intro i hi
  rcases eq_or_lt_of_le (finset.mem_Ico.mp hi).1 with (rfl | hi)
  · rw [pow_oneₓ, ← add_lt_add_iff_left (2 * p), ← succ_mul, two_mul, add_add_add_commₓ]
    exact
      lt_of_le_of_ltₓ
        (add_le_add (add_le_add_right (le_mul_of_one_le_right' ((one_le_div_iff hp.pos).mpr hk)) (k % p))
          (add_le_add_right (le_mul_of_one_le_right' ((one_le_div_iff hp.pos).mpr hk')) ((n - k) % p)))
        (by
          rwa [div_add_mod, div_add_mod, add_tsub_cancel_of_le hkn])
    
  · replace hn : n < p ^ i
    · calc
        n < 3 * p := hn
        _ ≤ p * p := mul_le_mul_right' (lt_of_le_of_neₓ hp.two_le hp'.symm) p
        _ = p ^ 2 := (sq p).symm
        _ ≤ p ^ i := pow_le_pow hp.one_lt.le hi
        
      
    rwa [mod_eq_of_lt (lt_of_le_of_ltₓ hkn hn), mod_eq_of_lt (lt_of_le_of_ltₓ tsub_le_self hn),
      add_tsub_cancel_of_le hkn]
    

/-- Primes greater than about `2 * n / 3` and less than `n` do not appear in the factorization of
`central_binom n`.
-/
theorem factorization_central_binom_of_two_mul_self_lt_three_mul (n_big : 2 < n) (p_le_n : p ≤ n)
    (big : 2 * n < 3 * p) : (centralBinom n).factorization p = 0 := by
  refine' factorization_choose_of_lt_three_mul _ p_le_n (p_le_n.trans _) big
  · rintro rfl
    linarith
    
  · rw [two_mul, add_tsub_cancel_left]
    

theorem factorization_factorial_eq_zero_of_lt (h : n < p) : (factorial n).factorization p = 0 := by
  induction' n with n hn
  · simp
    
  rw [factorial_succ, factorization_mul n.succ_ne_zero n.factorial_ne_zero, Finsupp.coe_add, Pi.add_apply,
    hn (lt_of_succ_lt h), add_zeroₓ, factorization_eq_zero_of_lt h]

theorem factorization_choose_eq_zero_of_lt (h : n < p) : (choose n k).factorization p = 0 := by
  by_cases' hnk : n < k
  · simp [← choose_eq_zero_of_lt hnk]
    
  rw [choose_eq_factorial_div_factorial (le_of_not_ltₓ hnk),
    factorization_div (factorial_mul_factorial_dvd_factorial (le_of_not_ltₓ hnk)), Finsupp.coe_tsub, Pi.sub_apply,
    factorization_factorial_eq_zero_of_lt h, zero_tsub]

/-- If a prime `p` has positive multiplicity in the `n`th central binomial coefficient,
`p` is no more than `2 * n`
-/
theorem factorization_central_binom_eq_zero_of_two_mul_lt (h : 2 * n < p) : (centralBinom n).factorization p = 0 :=
  factorization_choose_eq_zero_of_lt h

/-- Contrapositive form of `nat.factorization_central_binom_eq_zero_of_two_mul_lt`
-/
theorem le_two_mul_of_factorization_central_binom_pos (h_pos : 0 < (centralBinom n).factorization p) : p ≤ 2 * n :=
  le_of_not_ltₓ (pos_iff_ne_zero.mp h_pos ∘ factorization_central_binom_eq_zero_of_two_mul_lt)

/-- A binomial coefficient is the product of its prime factors, which are at most `n`. -/
theorem prod_pow_factorization_choose (n k : ℕ) (hkn : k ≤ n) :
    (∏ p in Finset.range (n + 1), p ^ (Nat.choose n k).factorization p) = choose n k := by
  nth_rw_rhs 0[← factorization_prod_pow_eq_self (choose_pos hkn).ne']
  rw [eq_comm]
  apply Finset.prod_subset
  · intro p hp
    rw [Finset.mem_range]
    contrapose! hp
    rw [Finsupp.mem_support_iff, not_not, factorization_choose_eq_zero_of_lt hp]
    
  · intro p _ h2
    simp [← not_not.1 (mt Finsupp.mem_support_iff.2 h2)]
    

/-- The `n`th central binomial coefficient is the product of its prime factors, which are
at most `2n`. -/
theorem prod_pow_factorization_central_binom (n : ℕ) :
    (∏ p in Finset.range (2 * n + 1), p ^ (centralBinom n).factorization p) = centralBinom n := by
  apply prod_pow_factorization_choose
  linarith

end Nat

