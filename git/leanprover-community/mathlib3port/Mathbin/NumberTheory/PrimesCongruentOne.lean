/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathbin.RingTheory.Polynomial.Cyclotomic.Basic
import Mathbin.Topology.Algebra.Polynomial
import Mathbin.FieldTheory.Finite.Basic

/-!
# Primes congruent to one

We prove that, for any positive `k : ℕ`, there are infinitely many primes `p` such that
`p ≡ 1 [MOD k]`.
-/


namespace Nat

open Polynomial Nat Filter

/-- For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. -/
theorem exists_prime_ge_modeq_one (k n : ℕ) (hpos : 0 < k) : ∃ p : ℕ, Nat.Prime p ∧ n ≤ p ∧ p ≡ 1 [MOD k] := by
  have hli : tendsto (abs ∘ fun a : ℕ => abs (a : ℚ)) at_top at_top := by
    simp only [(· ∘ ·), abs_cast]
    exact nat.strict_mono_cast.monotone.tendsto_at_top_at_top exists_nat_ge
  have hcff : Int.castRingHom ℚ (cyclotomic k ℤ).leadingCoeff ≠ 0 := by
    simp only [cyclotomic.monic, RingHom.eq_int_cast, monic.leading_coeff, Int.cast_oneₓ, Ne.def, not_false_iff,
      one_ne_zero]
  obtain ⟨a, ha⟩ :=
    tendsto_at_top_at_top.1
      (tendsto_abv_eval₂_at_top (Int.castRingHom ℚ) abs (cyclotomic k ℤ) (degree_cyclotomic_pos k ℤ hpos) hcff hli) 2
  let b := a * (k * n.factorial)
  have hgt : 1 < (eval (↑(a * (k * n.factorial))) (cyclotomic k ℤ)).natAbs := by
    suffices hgtabs : 1 < abs (eval (↑b) (cyclotomic k ℤ))
    · rw [Int.abs_eq_nat_abs] at hgtabs
      exact_mod_cast hgtabs
      
    suffices hgtrat : 1 < abs (eval (↑b) (cyclotomic k ℚ))
    · rw [← map_cyclotomic_int k ℚ, ← Int.cast_coe_nat, ← Int.coe_cast_ring_hom, eval_map, eval₂_hom,
        Int.coe_cast_ring_hom] at hgtrat
      assumption_mod_cast
      
    suffices hleab : a ≤ b
    · replace ha := lt_of_lt_of_leₓ one_lt_two (ha b hleab)
      rwa [← eval_map, map_cyclotomic_int k ℚ, abs_cast] at ha
      
    exact le_mul_of_pos_right (mul_pos hpos (factorial_pos n))
  let p := min_fac (eval (↑b) (cyclotomic k ℤ)).natAbs
  have hprime : Fact p.prime := ⟨min_fac_prime (ne_of_ltₓ hgt).symm⟩
  have hroot : is_root (cyclotomic k (Zmod p)) (cast_ring_hom (Zmod p) b) := by
    rw [is_root.def, ← map_cyclotomic_int k (Zmod p), eval_map, coe_cast_ring_hom, ← Int.cast_coe_nat, ←
      Int.coe_cast_ring_hom, eval₂_hom, Int.coe_cast_ring_hom, Zmod.int_coe_zmod_eq_zero_iff_dvd _ _]
    apply Int.dvd_nat_abs.1
    exact_mod_cast min_fac_dvd (eval (↑b) (cyclotomic k ℤ)).natAbs
  refine' ⟨p, hprime.1, _, _⟩
  · by_contra habs
    exact
      (prime.dvd_iff_not_coprime hprime.1).1 (dvd_factorial (min_fac_pos _) (le_of_not_geₓ habs))
        (coprime_of_root_cyclotomic hpos hroot).symm.coprime_mul_left_right.coprime_mul_left_right
    
  · have hdiv :=
      order_of_dvd_of_pow_eq_one
        (Zmod.units_pow_card_sub_one_eq_one p (Zmod.unitOfCoprime b (coprime_of_root_cyclotomic hpos hroot)))
    have : ¬p ∣ k :=
      hprime.1.coprime_iff_not_dvd.1
        (coprime_of_root_cyclotomic hpos hroot).symm.coprime_mul_left_right.coprime_mul_right_right
    have := NeZero.of_not_dvd (Zmod p) this
    have : k = orderOf (b : Zmod p) := (is_root_cyclotomic_iff.mp hroot).eq_order_of
    rw [← order_of_units, Zmod.coe_unit_of_coprime, ← this] at hdiv
    exact ((modeq_iff_dvd' hprime.1.Pos).2 hdiv).symm
    

theorem frequently_at_top_modeq_one (k : ℕ) (hpos : 0 < k) : ∃ᶠ p in at_top, Nat.Prime p ∧ p ≡ 1 [MOD k] := by
  refine' frequently_at_top.2 fun n => _
  obtain ⟨p, hp⟩ := exists_prime_ge_modeq_one k n hpos
  exact ⟨p, ⟨hp.2.1, hp.1, hp.2.2⟩⟩

theorem infinite_set_of_prime_modeq_one (k : ℕ) (hpos : 0 < k) : Set.Infinite { p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k] } :=
  frequently_at_top_iff_infinite.1 (frequently_at_top_modeq_one k hpos)

end Nat

