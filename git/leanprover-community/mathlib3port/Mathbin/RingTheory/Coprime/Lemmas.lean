/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Int.Gcd
import Mathbin.RingTheory.Coprime.Basic

/-!
# Additional lemmas about elements of a ring satisfying `is_coprime`

These lemmas are in a separate file to the definition of `is_coprime` as they require more imports.

Notably, this includes lemmas about `finset.prod` as this requires importing big_operators, and
lemmas about `has_pow` since these are easiest to prove via `finset.prod`.

-/


universe u v

variable {R : Type u} {I : Type v} [CommSemiringₓ R] {x y z : R} {s : I → R} {t : Finset I}

open_locale BigOperators Classical

theorem Nat.is_coprime_iff_coprime {m n : ℕ} : IsCoprime (m : ℤ) n ↔ Nat.Coprime m n :=
  ⟨fun ⟨a, b, H⟩ =>
    Nat.eq_one_of_dvd_one <|
      Int.coe_nat_dvd.1 <| by
        rw [Int.coe_nat_one, ← H]
        exact
          dvd_add (dvd_mul_of_dvd_right (Int.coe_nat_dvd.2 <| Nat.gcd_dvd_leftₓ m n) _)
            (dvd_mul_of_dvd_right (Int.coe_nat_dvd.2 <| Nat.gcd_dvd_rightₓ m n) _),
    fun H =>
    ⟨Nat.gcdA m n, Nat.gcdB m n, by
      rw [mul_comm _ (m : ℤ), mul_comm _ (n : ℤ), ← Nat.gcd_eq_gcd_ab, show _ = _ from H, Int.coe_nat_one]⟩⟩

theorem IsCoprime.prod_left : (∀, ∀ i ∈ t, ∀, IsCoprime (s i) x) → IsCoprime (∏ i in t, s i) x :=
  (Finset.induction_on t fun _ => is_coprime_one_left) fun b t hbt ih H => by
    rw [Finset.prod_insert hbt]
    rw [Finset.forall_mem_insert] at H
    exact H.1.mul_left (ih H.2)

theorem IsCoprime.prod_right : (∀, ∀ i ∈ t, ∀, IsCoprime x (s i)) → IsCoprime x (∏ i in t, s i) := by
  simpa only [is_coprime_comm] using IsCoprime.prod_left

theorem IsCoprime.prod_left_iff : IsCoprime (∏ i in t, s i) x ↔ ∀, ∀ i ∈ t, ∀, IsCoprime (s i) x :=
  (Finset.induction_on t ((iff_of_true is_coprime_one_left) fun _ => False.elim)) fun b t hbt ih => by
    rw [Finset.prod_insert hbt, IsCoprime.mul_left_iff, ih, Finset.forall_mem_insert]

theorem IsCoprime.prod_right_iff : IsCoprime x (∏ i in t, s i) ↔ ∀, ∀ i ∈ t, ∀, IsCoprime x (s i) := by
  simpa only [is_coprime_comm] using IsCoprime.prod_left_iff

theorem IsCoprime.of_prod_left (H1 : IsCoprime (∏ i in t, s i) x) (i : I) (hit : i ∈ t) : IsCoprime (s i) x :=
  IsCoprime.prod_left_iff.1 H1 i hit

theorem IsCoprime.of_prod_right (H1 : IsCoprime x (∏ i in t, s i)) (i : I) (hit : i ∈ t) : IsCoprime x (s i) :=
  IsCoprime.prod_right_iff.1 H1 i hit

theorem Finset.prod_dvd_of_coprime :
    ∀ Hs : (t : Set I).Pairwise (IsCoprime on s) Hs1 : ∀, ∀ i ∈ t, ∀, s i ∣ z, (∏ x in t, s x) ∣ z :=
  Finset.induction_on t (fun _ _ => one_dvd z)
    (by
      intro a r har ih Hs Hs1
      rw [Finset.prod_insert har]
      have aux1 : a ∈ (↑(insert a r) : Set I) := Finset.mem_insert_self a r
      refine'
        (IsCoprime.prod_right fun i hir =>
              Hs aux1 (Finset.mem_insert_of_mem hir) <| by
                rintro rfl
                exact har hir).mul_dvd
          (Hs1 a aux1) ((ih (Hs.mono _)) fun i hi => Hs1 i <| Finset.mem_insert_of_mem hi)
      simp only [Finset.coe_insert, Set.subset_insert])

theorem Fintype.prod_dvd_of_coprime [Fintype I] (Hs : Pairwise (IsCoprime on s)) (Hs1 : ∀ i, s i ∣ z) :
    (∏ x, s x) ∣ z :=
  Finset.prod_dvd_of_coprime (Hs.set_pairwise _) fun i _ => Hs1 i

variable {m n : ℕ}

theorem IsCoprime.pow_left (H : IsCoprime x y) : IsCoprime (x ^ m) y := by
  rw [← Finset.card_range m, ← Finset.prod_const]
  exact IsCoprime.prod_left fun _ _ => H

theorem IsCoprime.pow_right (H : IsCoprime x y) : IsCoprime x (y ^ n) := by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact IsCoprime.prod_right fun _ _ => H

theorem IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y ^ n) :=
  H.pow_left.pow_right

theorem IsCoprime.pow_left_iff (hm : 0 < m) : IsCoprime (x ^ m) y ↔ IsCoprime x y := by
  refine' ⟨fun h => _, IsCoprime.pow_left⟩
  rw [← Finset.card_range m, ← Finset.prod_const] at h
  exact h.of_prod_left 0 (finset.mem_range.mpr hm)

theorem IsCoprime.pow_right_iff (hm : 0 < m) : IsCoprime x (y ^ m) ↔ IsCoprime x y :=
  is_coprime_comm.trans <| (IsCoprime.pow_left_iff hm).trans <| is_coprime_comm

theorem IsCoprime.pow_iff (hm : 0 < m) (hn : 0 < n) : IsCoprime (x ^ m) (y ^ n) ↔ IsCoprime x y :=
  (IsCoprime.pow_left_iff hm).trans <| IsCoprime.pow_right_iff hn

