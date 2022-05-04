/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Nat.Prime
import Mathbin.Data.Zmod.Basic
import Mathbin.RingTheory.Multiplicity
import Mathbin.Data.Nat.Periodic
import Mathbin.Algebra.CharP.Two

/-!
# Euler's totient function

This file defines [Euler's totient function](https://en.wikipedia.org/wiki/Euler's_totient_function)
`nat.totient n` which counts the number of naturals less than `n` that are coprime with `n`.
We prove the divisor sum formula, namely that `n` equals `φ` summed over the divisors of `n`. See
`sum_totient`. We also prove two lemmas to help compute totients, namely `totient_mul` and
`totient_prime_pow`.
-/


open Finset

open BigOperators

namespace Nat

/-- Euler's totient function. This counts the number of naturals strictly less than `n` which are
coprime with `n`. -/
def totient (n : ℕ) : ℕ :=
  ((range n).filter n.Coprime).card

-- mathport name: «exprφ»
localized [Nat] notation "φ" => Nat.totient

@[simp]
theorem totient_zero : φ 0 = 0 :=
  rfl

@[simp]
theorem totient_one : φ 1 = 1 := by
  simp [totient]

theorem totient_eq_card_coprime (n : ℕ) : φ n = ((range n).filter n.Coprime).card :=
  rfl

theorem totient_le (n : ℕ) : φ n ≤ n :=
  ((range n).card_filter_le _).trans_eq (card_range n)

theorem totient_lt (n : ℕ) (hn : 1 < n) : φ n < n :=
  (card_lt_card
        (filter_ssubset.2
          ⟨0, by
            simp [hn.ne', pos_of_gt hn]⟩)).trans_eq
    (card_range n)

theorem totient_pos : ∀ {n : ℕ}, 0 < n → 0 < φ n
  | 0 => by
    decide
  | 1 => by
    simp [totient]
  | n + 2 => fun h =>
    card_pos.2
      ⟨1,
        mem_filter.2
          ⟨mem_range.2
              (by
                decide),
            coprime_one_rightₓ _⟩⟩

theorem filter_coprime_Ico_eq_totient (a n : ℕ) : ((ico n (n + a)).filter (Coprime a)).card = totient a := by
  rw [totient, filter_Ico_card_eq_of_periodic, count_eq_card_filter_range]
  exact periodic_coprime a

theorem Ico_filter_coprime_le {a : ℕ} (k n : ℕ) (a_pos : 0 < a) :
    ((ico k (k + n)).filter (Coprime a)).card ≤ totient a * (n / a + 1) := by
  conv_lhs => rw [← Nat.mod_add_divₓ n a]
  induction' n / a with i ih
  · rw [← filter_coprime_Ico_eq_totient a k]
    simp only [add_zeroₓ, mul_oneₓ, mul_zero, le_of_ltₓ (mod_lt n a_pos)]
    mono
    refine' monotone_filter_left a.coprime _
    simp only [Finset.le_eq_subset]
    exact Ico_subset_Ico rfl.le (add_le_add_left (le_of_ltₓ (mod_lt n a_pos)) k)
    
  simp only [mul_succ]
  simp_rw [← add_assocₓ]  at ih⊢
  calc
    (filter a.coprime (Ico k (k + n % a + a * i + a))).card =
        (filter a.coprime (Ico k (k + n % a + a * i) ∪ Ico (k + n % a + a * i) (k + n % a + a * i + a))).card :=
      by
      congr
      rw [Ico_union_Ico_eq_Ico]
      rw [add_assocₓ]
      exact le_self_add
      exact le_self_add _ ≤ (filter a.coprime (Ico k (k + n % a + a * i))).card + a.totient := by
      rw [filter_union, ← filter_coprime_Ico_eq_totient a (k + n % a + a * i)]
      apply card_union_le _ ≤ a.totient * i + a.totient + a.totient := add_le_add_right ih (totient a)

open Zmod

/-- Note this takes an explicit `fintype ((zmod n)ˣ)` argument to avoid trouble with instance
diamonds. -/
@[simp]
theorem _root_.zmod.card_units_eq_totient (n : ℕ) [Fact (0 < n)] [Fintype (Zmod n)ˣ] : Fintype.card (Zmod n)ˣ = φ n :=
  calc
    Fintype.card (Zmod n)ˣ = Fintype.card { x : Zmod n // x.val.Coprime n } := Fintype.card_congr Zmod.unitsEquivCoprime
    _ = φ n := by
      apply Finset.card_congr fun _ => a.1.val
      · intro a
        simp (config := { contextual := true })[(a : Zmod n).val_lt, a.prop.symm]
        
      · intro _ _ _ _ h
        rw [Subtype.ext_iff_val]
        apply val_injective
        exact h
        
      · intro b hb
        rw [Finset.mem_filter, Finset.mem_range] at hb
        refine' ⟨⟨b, _⟩, Finset.mem_univ _, _⟩
        · let u := unit_of_coprime b hb.2.symm
          exact val_coe_unit_coprime u
          
        · show Zmod.val (b : Zmod n) = b
          rw [val_nat_cast, Nat.mod_eq_of_ltₓ hb.1]
          
        
    

theorem totient_even {n : ℕ} (hn : 2 < n) : Even n.totient := by
  have : Fact (1 < n) := ⟨one_lt_two.trans hn⟩
  suffices 2 = orderOf (-1 : (Zmod n)ˣ) by
    rw [← Zmod.card_units_eq_totient, even_iff_two_dvd, this]
    exact order_of_dvd_card_univ
  rw [← order_of_units, Units.coe_neg_one, order_of_neg_one, ringChar.eq (Zmod n) n, if_neg hn.ne']

theorem totient_mul {m n : ℕ} (h : m.Coprime n) : φ (m * n) = φ m * φ n :=
  if hmn0 : m * n = 0 then by
    cases' Nat.mul_eq_zero.1 hmn0 with h h <;> simp only [totient_zero, mul_zero, zero_mul, h]
  else by
    have : Fact (0 < m * n) := ⟨Nat.pos_of_ne_zeroₓ hmn0⟩
    have : Fact (0 < m) := ⟨Nat.pos_of_ne_zeroₓ <| left_ne_zero_of_mul hmn0⟩
    have : Fact (0 < n) := ⟨Nat.pos_of_ne_zeroₓ <| right_ne_zero_of_mul hmn0⟩
    simp only [← Zmod.card_units_eq_totient]
    rw [Fintype.card_congr (Units.mapEquiv (Zmod.chineseRemainder h).toMulEquiv).toEquiv,
      Fintype.card_congr (@MulEquiv.prodUnits (Zmod m) (Zmod n) _ _).toEquiv, Fintype.card_prod]

theorem sum_totient (n : ℕ) : (∑ m in (range n.succ).filter (· ∣ n), φ m) = n :=
  if hn0 : n = 0 then by
    simp [hn0]
  else
    calc
      (∑ m in (range n.succ).filter (· ∣ n), φ m) =
          ∑ d in (range n.succ).filter (· ∣ n), ((range (n / d)).filter fun m => gcdₓ (n / d) m = 1).card :=
        Eq.symm <|
          sum_bij (fun d _ => n / d)
            (fun d hd =>
              mem_filter.2
                ⟨mem_range.2 <| lt_succ_of_le <| Nat.div_le_selfₓ _ _, by
                  conv => rhs rw [← Nat.mul_div_cancel'ₓ (mem_filter.1 hd).2] <;> simp ⟩)
            (fun _ _ => rfl)
            (fun a b ha hb h => by
              have ha : a * (n / a) = n := Nat.mul_div_cancel'ₓ (mem_filter.1 ha).2
              have : 0 < n / a :=
                Nat.pos_of_ne_zeroₓ fun h => by
                  simp_all [lt_irreflₓ]
              rw [← Nat.mul_left_inj this, ha, h, Nat.mul_div_cancel'ₓ (mem_filter.1 hb).2])
            fun b hb =>
            have hb : b < n.succ ∧ b ∣ n := by
              simpa [-range_succ] using hb
            have hbn : n / b ∣ n :=
              ⟨b, by
                rw [Nat.div_mul_cancelₓ hb.2]⟩
            have hnb0 : n / b ≠ 0 := fun h => by
              simpa [h, Ne.symm hn0] using Nat.div_mul_cancelₓ hbn
            ⟨n / b, mem_filter.2 ⟨mem_range.2 <| lt_succ_of_le <| Nat.div_le_selfₓ _ _, hbn⟩, by
              rw [← Nat.mul_left_inj (Nat.pos_of_ne_zeroₓ hnb0), Nat.mul_div_cancel'ₓ hb.2, Nat.div_mul_cancelₓ hbn]⟩
      _ = ∑ d in (range n.succ).filter (· ∣ n), ((range n).filter fun m => gcdₓ n m = d).card :=
        sum_congr rfl fun d hd =>
          have hd : d ∣ n := (mem_filter.1 hd).2
          have hd0 : 0 < d := Nat.pos_of_ne_zeroₓ fun h => hn0 (eq_zero_of_zero_dvd <| h ▸ hd)
          card_congr (fun m hm => d * m)
            (fun m hm =>
              have hm : m < n / d ∧ gcdₓ (n / d) m = 1 := by
                simpa using hm
              mem_filter.2
                ⟨mem_range.2 <| Nat.mul_div_cancel'ₓ hd ▸ (mul_lt_mul_left hd0).2 hm.1, by
                  rw [← Nat.mul_div_cancel'ₓ hd, gcd_mul_left, hm.2, mul_oneₓ]⟩)
            (fun a b ha hb h => (Nat.mul_right_inj hd0).1 h) fun b hb =>
            have hb : b < n ∧ gcdₓ n b = d := by
              simpa using hb
            ⟨b / d,
              mem_filter.2
                ⟨mem_range.2
                    ((mul_lt_mul_left (show 0 < d from hb.2 ▸ hb.2.symm ▸ hd0)).1
                      (by
                        rw [← hb.2, Nat.mul_div_cancel'ₓ (gcd_dvd_left _ _),
                            Nat.mul_div_cancel'ₓ (gcd_dvd_right _ _)] <;>
                          exact hb.1)),
                  hb.2 ▸ coprime_div_gcd_div_gcdₓ (hb.2.symm ▸ hd0)⟩,
              hb.2 ▸ Nat.mul_div_cancel'ₓ (gcd_dvd_rightₓ _ _)⟩
      _ = ((filter (· ∣ n) (range n.succ)).bUnion fun d => (range n).filter fun m => gcdₓ n m = d).card :=
        (card_bUnion
            (by
              intros <;> apply disjoint_filter.2 <;> cc)).symm
      _ = (range n).card :=
        congr_argₓ card
          (Finset.ext fun m =>
            ⟨by
              simp , fun hm =>
              have h : m < n := mem_range.1 hm
              mem_bUnion.2
                ⟨gcdₓ n m,
                  mem_filter.2
                    ⟨mem_range.2 (lt_succ_of_leₓ (le_of_dvdₓ (lt_of_le_of_ltₓ (zero_le _) h) (gcd_dvd_leftₓ _ _))),
                      gcd_dvd_leftₓ _ _⟩,
                  mem_filter.2 ⟨hm, rfl⟩⟩⟩)
      _ = n := card_range _
      

/-- When `p` is prime, then the totient of `p ^ (n + 1)` is `p ^ n * (p - 1)` -/
theorem totient_prime_pow_succ {p : ℕ} (hp : p.Prime) (n : ℕ) : φ (p ^ (n + 1)) = p ^ n * (p - 1) :=
  calc
    φ (p ^ (n + 1)) = ((range (p ^ (n + 1))).filter (Coprime (p ^ (n + 1)))).card := totient_eq_card_coprime _
    _ = (range (p ^ (n + 1)) \ (range (p ^ n)).Image (· * p)).card :=
      congr_argₓ card
        (by
          rw [sdiff_eq_filter]
          apply filter_congr
          simp only [mem_range, mem_filter, coprime_pow_left_iff n.succ_pos, mem_image, not_exists,
            hp.coprime_iff_not_dvd]
          intro a ha
          constructor
          · rintro hap b _ rfl
            exact hap (dvd_mul_left _ _)
            
          · rintro h ⟨b, rfl⟩
            rw [pow_succₓ] at ha
            exact h b (lt_of_mul_lt_mul_left ha (zero_le _)) (mul_comm _ _)
            )
    _ = _ := by
      have h1 : Set.InjOn (· * p) (range (p ^ n)) := fun x _ y _ => (Nat.mul_left_inj hp.Pos).1
      have h2 : (range (p ^ n)).Image (· * p) ⊆ range (p ^ (n + 1)) := fun a => by
        simp only [mem_image, mem_range, exists_imp_distrib]
        rintro b h rfl
        rw [pow_succ'ₓ]
        exact (mul_lt_mul_right hp.pos).2 h
      rw [card_sdiff h2, card_image_of_inj_on h1, card_range, card_range, ← one_mulₓ (p ^ n), pow_succₓ, ← tsub_mul,
        one_mulₓ, mul_comm]
    

/-- When `p` is prime, then the totient of `p ^ n` is `p ^ (n - 1) * (p - 1)` -/
theorem totient_prime_pow {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) : φ (p ^ n) = p ^ (n - 1) * (p - 1) := by
  rcases exists_eq_succ_of_ne_zero (pos_iff_ne_zero.1 hn) with ⟨m, rfl⟩ <;> exact totient_prime_pow_succ hp _

theorem totient_prime {p : ℕ} (hp : p.Prime) : φ p = p - 1 := by
  rw [← pow_oneₓ p, totient_prime_pow hp] <;> simp

theorem totient_mul_of_prime_of_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) : (p * n).totient = p * n.totient := by
  by_cases' hzero : n = 0
  · simp [hzero]
    
  · have hfin := multiplicity.finite_nat_iff.2 ⟨hp.ne_one, zero_lt_iff.2 hzero⟩
    have h0 : 0 < (multiplicity p n).get hfin := multiplicity.pos_of_dvd hfin h
    obtain ⟨m, hm, hndiv⟩ := multiplicity.exists_eq_pow_mul_and_not_dvd hfin
    rw [hm, ← mul_assoc, ← pow_succₓ, Nat.totient_mul (coprime_comm.mp (hp.coprime_pow_of_not_dvd hndiv)),
      Nat.totient_mul (coprime_comm.mp (hp.coprime_pow_of_not_dvd hndiv)), ← mul_assoc]
    congr
    rw [← succ_pred_eq_of_pos h0, totient_prime_pow_succ hp, totient_prime_pow_succ hp, succ_pred_eq_of_pos h0, ←
      mul_assoc p, ← pow_succₓ, ← succ_pred_eq_of_pos h0, Nat.pred_succ]
    

theorem totient_eq_iff_prime {p : ℕ} (hp : 0 < p) : p.totient = p - 1 ↔ p.Prime := by
  refine' ⟨fun h => _, totient_prime⟩
  replace hp : 1 < p
  · apply lt_of_le_of_neₓ
    · rwa [succ_le_iff]
      
    · rintro rfl
      rw [totient_one, tsub_self] at h
      exact one_ne_zero h
      
    
  rw [totient_eq_card_coprime, range_eq_Ico, ← Ico_insert_succ_left hp.le, Finset.filter_insert,
    if_neg (not_coprime_of_dvd_of_dvd hp (dvd_refl p) (dvd_zero p)), ← Nat.card_Ico 1 p] at h
  refine' p.prime_of_coprime hp fun n hn hnz => Finset.filter_card_eq h n <| finset.mem_Ico.mpr ⟨_, hn⟩
  rwa [succ_le_iff, pos_iff_ne_zero]

theorem card_units_zmod_lt_sub_one {p : ℕ} (hp : 1 < p) [Fintype (Zmod p)ˣ] : Fintype.card (Zmod p)ˣ ≤ p - 1 := by
  have : Fact (0 < p) := ⟨zero_lt_one.trans hp⟩
  rw [Zmod.card_units_eq_totient p]
  exact Nat.le_pred_of_ltₓ (Nat.totient_lt p hp)

theorem prime_iff_card_units (p : ℕ) [Fintype (Zmod p)ˣ] : p.Prime ↔ Fintype.card (Zmod p)ˣ = p - 1 := by
  by_cases' hp : p = 0
  · subst hp
    simp only [Zmod, not_prime_zero, false_iffₓ, zero_tsub]
    -- the substI created an non-defeq but subsingleton instance diamond; resolve it
    suffices Fintype.card ℤˣ ≠ 0 by
      convert this
    simp
    
  have : Fact (0 < p) := ⟨Nat.pos_of_ne_zeroₓ hp⟩
  rw [Zmod.card_units_eq_totient, Nat.totient_eq_iff_prime (Fact.out (0 < p))]

@[simp]
theorem totient_two : φ 2 = 1 :=
  (totient_prime prime_two).trans rfl

theorem totient_eq_one_iff : ∀ {n : ℕ}, n.totient = 1 ↔ n = 1 ∨ n = 2
  | 0 => by
    simp
  | 1 => by
    simp
  | 2 => by
    simp
  | n + 3 => by
    have : 3 ≤ n + 3 := le_add_self
    simp only [succ_succ_ne_one, false_orₓ]
    exact
      ⟨fun h => not_even_one.elim <| h ▸ totient_even this, by
        rintro ⟨⟩⟩

/-! ### Euler's product formula for the totient function

We prove several different statements of this formula. -/


/-- Euler's product formula for the totient function. -/
theorem totient_eq_prod_factorization {n : ℕ} (hn : n ≠ 0) :
    φ n = n.factorization.Prod fun p k => p ^ (k - 1) * (p - 1) := by
  rw [multiplicative_factorization φ (@totient_mul) totient_one hn]
  apply Finsupp.prod_congr fun p hp => _
  have h := zero_lt_iff.mpr (finsupp.mem_support_iff.mp hp)
  rw [totient_prime_pow (prime_of_mem_factorization hp) h]

/-- Euler's product formula for the totient function. -/
theorem totient_mul_prod_factors (n : ℕ) :
    (φ n * ∏ p in n.factors.toFinset, p) = n * ∏ p in n.factors.toFinset, p - 1 := by
  by_cases' hn : n = 0
  · simp [hn]
    
  rw [totient_eq_prod_factorization hn]
  nth_rw 2[← factorization_prod_pow_eq_self hn]
  simp only [← prod_factorization_eq_prod_factors, ← Finsupp.prod_mul]
  refine' Finsupp.prod_congr fun p hp => _
  rw [Finsupp.mem_support_iff, ← zero_lt_iff] at hp
  rw [mul_comm, ← mul_assoc, ← pow_succₓ, Nat.sub_add_cancelₓ hp]

/-- Euler's product formula for the totient function. -/
theorem totient_eq_div_factors_mul (n : ℕ) :
    φ n = (n / ∏ p in n.factors.toFinset, p) * ∏ p in n.factors.toFinset, p - 1 := by
  rw [← mul_div_left n.totient, totient_mul_prod_factors, mul_comm, Nat.mul_div_assocₓ _ (prod_prime_factors_dvd n),
    mul_comm]
  simpa [prod_factorization_eq_prod_factors] using prod_pos fun p => pos_of_mem_factorization

/-- Euler's product formula for the totient function. -/
theorem totient_eq_mul_prod_factors (n : ℕ) : (φ n : ℚ) = n * ∏ p in n.factors.toFinset, 1 - p⁻¹ := by
  by_cases' hn : n = 0
  · simp [hn]
    
  have hn' : (n : ℚ) ≠ 0 := by
    simp [hn]
  have hpQ : (∏ p in n.factors.to_finset, (p : ℚ)) ≠ 0 := by
    rw [← cast_prod, cast_ne_zero, ← zero_lt_iff, ← prod_factorization_eq_prod_factors]
    exact prod_pos fun p hp => pos_of_mem_factorization hp
  simp only [totient_eq_div_factors_mul n, prod_prime_factors_dvd n, cast_mul, cast_prod, cast_dvd_char_zero,
    mul_comm_div', mul_right_inj' hn', div_eq_iff hpQ, ← prod_mul_distrib]
  refine' prod_congr rfl fun p hp => _
  have hp := pos_of_mem_factors (list.mem_to_finset.mp hp)
  have hp' : (p : ℚ) ≠ 0 := cast_ne_zero.mpr hp.ne.symm
  rw [sub_mul, one_mulₓ, mul_comm, mul_inv_cancel hp', cast_pred hp]

end Nat

