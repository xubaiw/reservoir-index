/-
Copyright (c) 2021 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/
import Mathbin.Algebra.IsPrimePow
import Mathbin.Algebra.Squarefree
import Mathbin.Order.Hom.Bounded
import Mathbin.Algebra.GcdMonoid.Basic

/-!

# Chains of divisors

The results in this file show that in the monoid `associates M` of a `unique_factorization_monoid`
`M`, an element `a` is an n-th prime power iff its set of divisors is a strictly increasing chain
of length `n + 1`, meaning that we can find a strictly increasing bijection between `fin (n + 1)`
and the set of factors of `a`.

## Main results
- `divisor_chain.exists_chain_of_prime_pow` : existence of a chain for prime powers.
- `divisor_chain.is_prime_pow_of_has_chain` : elements that have a chain are prime powers.
- `multiplicity_prime_eq_multiplicity_image_by_factor_order_iso` : if there is a
  monotone bijection `d` between the set of factors of `a : associates M` and the set of factors of
  `b : associates N` then for any prime `p ∣ a`, `multiplicity p a = multiplicity (d p) b`.
- `multiplicity_eq_multiplicity_factor_dvd_iso_of_mem_normalized_factor` : if there is a bijection
  between the set of factors of `a : M` and `b : N` then for any prime `p ∣ a`,
  `multiplicity p a = multiplicity (d p) b`


## Todo
- Create a structure for chains of divisors.
- Simplify proof of `mem_normalized_factors_factor_dvd_iso_of_mem_normalized_factors` using
  `mem_normalized_factors_factor_order_iso_of_mem_normalized_factors` or vice versa.

-/


variable {M : Type _} [CancelCommMonoidWithZero M]

open UniqueFactorizationMonoid multiplicity Irreducible Associates

namespace DivisorChain

theorem exists_chain_of_prime_pow {p : Associates M} {n : ℕ} (hn : n ≠ 0) (hp : Prime p) :
    ∃ c : Finₓ (n + 1) → Associates M, c 1 = p ∧ StrictMono c ∧ ∀ {r : Associates M}, r ≤ p ^ n ↔ ∃ i, r = c i := by
  refine' ⟨fun i => p ^ (i : ℕ), _, fun n m h => _, fun y => ⟨fun h => _, _⟩⟩
  · rw [Finₓ.coe_one', Nat.mod_eq_of_ltₓ, pow_oneₓ]
    exact Nat.lt_succ_of_leₓ (nat.one_le_iff_ne_zero.mpr hn)
    
  · exact
      associates.dvd_not_unit_iff_lt.mp
        ⟨pow_ne_zero n hp.ne_zero, p ^ (m - n : ℕ),
          not_is_unit_of_not_is_unit_dvd hp.not_unit (dvd_pow dvd_rfl (Nat.sub_pos_of_ltₓ h).ne'),
          (pow_mul_pow_sub p h.le).symm⟩
    
  · obtain ⟨i, i_le, hi⟩ := (dvd_prime_pow hp n).1 h
    rw [associated_iff_eq] at hi
    exact ⟨⟨i, Nat.lt_succ_of_leₓ i_le⟩, hi⟩
    
  · rintro ⟨i, rfl⟩
    exact ⟨p ^ (n - i : ℕ), (pow_mul_pow_sub p (nat.succ_le_succ_iff.mp i.2)).symm⟩
    

theorem element_of_chain_not_is_unit_of_index_ne_zero {n : ℕ} {i : Finₓ (n + 1)} (i_pos : i ≠ 0)
    {c : Finₓ (n + 1) → Associates M} (h₁ : StrictMono c) : ¬IsUnit (c i) :=
  DvdNotUnit.not_unit
    (Associates.dvd_not_unit_iff_lt.2 (h₁ <| show (0 : Finₓ (n + 1)) < i from i.pos_iff_ne_zero.mpr i_pos))

theorem first_of_chain_is_unit {q : Associates M} {n : ℕ} {c : Finₓ (n + 1) → Associates M} (h₁ : StrictMono c)
    (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) : IsUnit (c 0) := by
  obtain ⟨i, hr⟩ := h₂.mp Associates.one_le
  rw [Associates.is_unit_iff_eq_one, ← Associates.le_one_iff, hr]
  exact h₁.monotone (Finₓ.zero_le i)

/-- The second element of a chain is irreducible. -/
theorem second_of_chain_is_irreducible {q : Associates M} {n : ℕ} (hn : n ≠ 0) {c : Finₓ (n + 1) → Associates M}
    (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) (hq : q ≠ 0) : Irreducible (c 1) := by
  cases n
  · contradiction
    
  refine' (Associates.is_atom_iff (ne_zero_of_dvd_ne_zero hq (h₂.2 ⟨1, rfl⟩))).mp ⟨_, fun b hb => _⟩
  · exact ne_bot_of_gt (h₁ (show (0 : Finₓ (n + 2)) < 1 from Finₓ.one_pos))
    
  obtain ⟨⟨i, hi⟩, rfl⟩ := h₂.1 (hb.le.trans (h₂.2 ⟨1, rfl⟩))
  cases i
  · exact (Associates.is_unit_iff_eq_one _).mp (first_of_chain_is_unit h₁ @h₂)
    
  · simpa [← Finₓ.lt_iff_coe_lt_coe] using h₁.lt_iff_lt.mp hb
    

theorem eq_second_of_chain_of_prime_dvd {p q r : Associates M} {n : ℕ} (hn : n ≠ 0) {c : Finₓ (n + 1) → Associates M}
    (h₁ : StrictMono c) (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hp : Prime p) (hr : r ∣ q) (hp' : p ∣ r) :
    p = c 1 := by
  cases n
  · contradiction
    
  obtain ⟨i, rfl⟩ := h₂.1 (dvd_trans hp' hr)
  refine' congr_arg c ((eq_of_ge_of_not_gt _) fun hi => _)
  · rw [Finₓ.le_iff_coe_le_coe, Finₓ.coe_one, Nat.succ_le_iff, ← Finₓ.coe_zero, ← Finₓ.lt_iff_coe_lt_coe,
      Finₓ.pos_iff_ne_zero]
    rintro rfl
    exact hp.not_unit (first_of_chain_is_unit h₁ @h₂)
    
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  · cases hi
    
  refine'
    not_irreducible_of_not_unit_dvd_not_unit
      (DvdNotUnit.not_unit (Associates.dvd_not_unit_iff_lt.2 (h₁ (show (0 : Finₓ (n + 2)) < j from _)))) _
      hp.irreducible
  · simpa [Finₓ.succ_zero_eq_one, ← Finₓ.succ_lt_succ_iff] using hi
    
  · refine' Associates.dvd_not_unit_iff_lt.2 (h₁ _)
    simpa only [← Finₓ.coe_eq_cast_succ] using Finₓ.lt_succ
    

theorem card_subset_divisors_le_length_of_chain {q : Associates M} {n : ℕ} {c : Finₓ (n + 1) → Associates M}
    (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) {m : Finset (Associates M)} (hm : ∀ r, r ∈ m → r ≤ q) : m.card ≤ n + 1 := by
  classical
  have mem_image : ∀ r : Associates M, r ≤ q → r ∈ finset.univ.image c := by
    intro r hr
    obtain ⟨i, hi⟩ := h₂.1 hr
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩
  rw [← Finset.card_fin (n + 1)]
  exact (Finset.card_le_of_subset fun x hx => mem_image x <| hm x hx).trans Finset.card_image_le

variable [UniqueFactorizationMonoid M]

theorem element_of_chain_eq_pow_second_of_chain {q r : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Finₓ (n + 1) → Associates M} (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) (hr : r ∣ q) (hq : q ≠ 0) :
    ∃ i : Finₓ (n + 1), r = c 1 ^ (i : ℕ) := by
  classical
  let i := (normalized_factors r).card
  have hi : normalized_factors r = Multiset.repeat (c 1) i := by
    apply Multiset.eq_repeat_of_mem
    intro b hb
    refine'
      eq_second_of_chain_of_prime_dvd hn h₁ (fun r' => h₂) (prime_of_normalized_factor b hb) hr
        (dvd_of_mem_normalized_factors hb)
  have H : r = c 1 ^ i := by
    have := UniqueFactorizationMonoid.normalized_factors_prod (ne_zero_of_dvd_ne_zero hq hr)
    rw [associated_iff_eq, hi, Multiset.prod_repeat] at this
    rw [this]
  refine' ⟨⟨i, _⟩, H⟩
  have : (finset.univ.image fun m : Finₓ (i + 1) => c 1 ^ (m : ℕ)).card = i + 1 := by
    conv_rhs => rw [← Finset.card_fin (i + 1)]
    cases n
    · contradiction
      
    rw [Finset.card_image_iff]
    refine' Set.inj_on_of_injective (fun m m' h => Finₓ.ext _) _
    refine'
      pow_injective_of_not_unit
        (element_of_chain_not_is_unit_of_index_ne_zero
          (by
            simp )
          h₁)
        _ h
    exact Irreducible.ne_zero (second_of_chain_is_irreducible hn h₁ (@h₂) hq)
  suffices H' : ∀, ∀ r ∈ finset.univ.image fun m : Finₓ (i + 1) => c 1 ^ (m : ℕ), ∀, r ≤ q
  · simp only [Nat.succ_le_iff, ← Nat.succ_eq_add_one, this]
    apply card_subset_divisors_le_length_of_chain (@h₂) H'
    
  simp only [← Finset.mem_image]
  rintro r ⟨a, ha, rfl⟩
  refine' dvd_trans _ hr
  use c 1 ^ (i - a)
  rw [pow_mul_pow_sub (c 1)]
  · exact H
    
  · exact nat.succ_le_succ_iff.mp a.2
    

theorem eq_pow_second_of_chain_of_has_chain {q : Associates M} {n : ℕ} (hn : n ≠ 0) {c : Finₓ (n + 1) → Associates M}
    (h₁ : StrictMono c) (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hq : q ≠ 0) : q = c 1 ^ n := by
  classical
  obtain ⟨i, hi'⟩ := element_of_chain_eq_pow_second_of_chain hn h₁ (fun r => h₂) (dvd_refl q) hq
  convert hi'
  refine' (Nat.lt_succ_iffₓ.1 i.prop).antisymm' (Nat.le_of_succ_le_succₓ _)
  calc
    n + 1 = (Finset.univ : Finset (Finₓ (n + 1))).card := (Finset.card_fin _).symm
    _ = (finset.univ.image c).card := (finset.card_image_iff.mpr (h₁.injective.inj_on _)).symm
    _ ≤ (finset.univ.image fun m : Finₓ (i + 1) => c 1 ^ (m : ℕ)).card := Finset.card_le_of_subset _
    _ ≤ (Finset.univ : Finset (Finₓ (i + 1))).card := Finset.card_image_le
    _ = i + 1 := Finset.card_fin _
    
  intro r hr
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hr
  have := h₂.2 ⟨j, rfl⟩
  rw [hi'] at this
  obtain ⟨u, hu, hu'⟩ := (dvd_prime_pow (show Prime (c 1) from _) i).1 this
  refine' finset.mem_image.mpr ⟨u, Finset.mem_univ _, _⟩
  · rw [associated_iff_eq] at hu'
    rw [Finₓ.coe_coe_of_lt (Nat.lt_succ_of_leₓ hu), hu']
    
  · rw [← irreducible_iff_prime]
    exact second_of_chain_is_irreducible hn h₁ (@h₂) hq
    

theorem is_prime_pow_of_has_chain {q : Associates M} {n : ℕ} (hn : n ≠ 0) {c : Finₓ (n + 1) → Associates M}
    (h₁ : StrictMono c) (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hq : q ≠ 0) : IsPrimePow q :=
  ⟨c 1, n, irreducible_iff_prime.mp (second_of_chain_is_irreducible hn h₁ (@h₂) hq), zero_lt_iff.mpr hn,
    (eq_pow_second_of_chain_of_has_chain hn h₁ (@h₂) hq).symm⟩

end DivisorChain

variable {N : Type _} [CancelCommMonoidWithZero N]

theorem factor_order_iso_map_one_eq_bot {m : Associates M} {n : Associates N}
    (d : { l : Associates M // l ≤ m } ≃o { l : Associates N // l ≤ n }) : (d ⟨1, one_dvd m⟩ : Associates N) = 1 := by
  letI : OrderBot { l : Associates M // l ≤ m } := Subtype.orderBot bot_le
  letI : OrderBot { l : Associates N // l ≤ n } := Subtype.orderBot bot_le
  simp [Associates.bot_eq_one]

theorem coe_factor_order_iso_map_eq_one_iff {m u : Associates M} {n : Associates N} (hu' : u ≤ m)
    (d : Set.Iic m ≃o Set.Iic n) : (d ⟨u, hu'⟩ : Associates N) = 1 ↔ u = 1 :=
  ⟨fun hu => by
    rw
      [show u = ↑(d.symm ⟨↑(d ⟨u, hu'⟩), (d ⟨u, hu'⟩).Prop⟩) by
        simp only [← Subtype.coe_eta, ← OrderIso.symm_apply_apply, ← Subtype.coe_mk]]
    convert factor_order_iso_map_one_eq_bot d.symm, fun hu => by
    simp_rw [hu]
    convert factor_order_iso_map_one_eq_bot d⟩

section

variable [UniqueFactorizationMonoid N] [UniqueFactorizationMonoid M]

open DivisorChain

theorem pow_image_of_prime_by_factor_order_iso_dvd [DecidableEq (Associates M)] {m p : Associates M} {n : Associates N}
    (hn : n ≠ 0) (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) {s : ℕ} (hs' : p ^ s ≤ m) :
    (d ⟨p, dvd_of_mem_normalized_factors hp⟩ : Associates N) ^ s ≤ n := by
  by_cases' hs : s = 0
  · simp [← hs]
    
  suffices (d ⟨p, dvd_of_mem_normalized_factors hp⟩ : Associates N) ^ s = ↑(d ⟨p ^ s, hs'⟩) by
    rw [this]
    apply Subtype.prop (d ⟨p ^ s, hs'⟩)
  obtain ⟨c₁, rfl, hc₁', hc₁''⟩ := exists_chain_of_prime_pow hs (prime_of_normalized_factor p hp)
  set c₂ : Finₓ (s + 1) → Associates N := fun t =>
    d
      ⟨c₁ t,
        le_transₓ
          (hc₁''.2
            ⟨t, by
              simp ⟩)
          hs'⟩
  have c₂.def : ∀ t, c₂ t = d ⟨c₁ t, _⟩ := fun t => rfl
  refine' (congr_arg (· ^ s) (c₂.def 1).symm).trans _
  refine' (eq_pow_second_of_chain_of_has_chain hs (fun t u h => _) (fun r => ⟨fun hr => _, _⟩) _).symm
  · rw [c₂.def, c₂.def, Subtype.coe_lt_coe, d.lt_iff_lt, Subtype.mk_lt_mk, hc₁'.lt_iff_lt]
    exact h
    
  · have : r ≤ n := hr.trans (d ⟨c₁ 1 ^ s, _⟩).2
    suffices d.symm ⟨r, this⟩ ≤ ⟨c₁ 1 ^ s, hs'⟩ by
      obtain ⟨i, hi⟩ := hc₁''.1 this
      use i
      simp only [← c₂.def, hi, ← d.apply_symm_apply, ← Subtype.coe_eta, ← Subtype.coe_mk]
    conv_rhs => rw [← d.symm_apply_apply ⟨c₁ 1 ^ s, hs'⟩]
    rw [d.symm.le_iff_le]
    simpa only [Subtype.coe_le_coe, ← Subtype.coe_mk] using hr
    
  · rintro ⟨i, hr⟩
    rw [hr, c₂.def, Subtype.coe_le_coe, d.le_iff_le]
    simpa [← Subtype.mk_le_mk] using hc₁''.2 ⟨i, rfl⟩
    
  exact ne_zero_of_dvd_ne_zero hn (Subtype.prop (d ⟨c₁ 1 ^ s, _⟩))

theorem map_prime_of_factor_order_iso [DecidableEq (Associates M)] {m p : Associates M} {n : Associates N} (hn : n ≠ 0)
    (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    Prime (d ⟨p, dvd_of_mem_normalized_factors hp⟩ : Associates N) := by
  rw [← irreducible_iff_prime]
  refine' (Associates.is_atom_iff <| ne_zero_of_dvd_ne_zero hn (d ⟨p, _⟩).Prop).mp ⟨_, fun b hb => _⟩
  · rw [Ne.def, ← Associates.is_unit_iff_eq_bot, Associates.is_unit_iff_eq_one, coe_factor_order_iso_map_eq_one_iff _ d]
    rintro rfl
    exact (prime_of_normalized_factor 1 hp).not_unit is_unit_one
    
  · obtain ⟨x, hx⟩ := d.surjective ⟨b, le_transₓ (le_of_ltₓ hb) (d ⟨p, dvd_of_mem_normalized_factors hp⟩).Prop⟩
    rw [← Subtype.coe_mk b _, Subtype.coe_lt_coe, ← hx] at hb
    letI : OrderBot { l : Associates M // l ≤ m } := Subtype.orderBot bot_le
    letI : OrderBot { l : Associates N // l ≤ n } := Subtype.orderBot bot_le
    suffices x = ⊥ by
      rw [this, OrderIso.map_bot d] at hx
      refine' (Subtype.mk_eq_bot_iff _ _).mp hx.symm
      exact bot_le
    obtain ⟨a, ha⟩ := x
    rw [Subtype.mk_eq_bot_iff]
    · exact
        ((Associates.is_atom_iff <| Prime.ne_zero <| prime_of_normalized_factor p hp).mpr <|
              irreducible_of_normalized_factor p hp).right
          a (subtype.mk_lt_mk.mp <| d.lt_iff_lt.mp hb)
      
    exact bot_le
    

theorem mem_normalized_factors_factor_order_iso_of_mem_normalized_factors [DecidableEq (Associates M)]
    [DecidableEq (Associates N)] {m p : Associates M} {n : Associates N} (hn : n ≠ 0) (hp : p ∈ normalizedFactors m)
    (d : Set.Iic m ≃o Set.Iic n) : ↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩) ∈ normalizedFactors n := by
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalized_factors_of_dvd hn (map_prime_of_factor_order_iso hn hp d).Irreducible
      (d ⟨p, dvd_of_mem_normalized_factors hp⟩).Prop
  rw [associated_iff_eq] at hq'
  rwa [hq']

variable [DecidableRel ((· ∣ ·) : M → M → Prop)] [DecidableRel ((· ∣ ·) : N → N → Prop)]

theorem multiplicity_prime_le_multiplicity_image_by_factor_order_iso [DecidableEq (Associates M)] {m p : Associates M}
    {n : Associates N} (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    multiplicity p m ≤ multiplicity (↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩)) n := by
  by_cases' hn : n = 0
  · simp [← hn]
    
  by_cases' hm : m = 0
  · simpa [← hm] using hp
    
  rw [← PartEnat.coe_get (finite_iff_dom.1 <| finite_prime_left (prime_of_normalized_factor p hp) hm), ←
    pow_dvd_iff_le_multiplicity]
  exact pow_image_of_prime_by_factor_order_iso_dvd hn hp d (pow_multiplicity_dvd _)

theorem multiplicity_prime_eq_multiplicity_image_by_factor_order_iso [DecidableEq (Associates M)] {m p : Associates M}
    {n : Associates N} (hn : n ≠ 0) (hp : p ∈ normalizedFactors m) (d : Set.Iic m ≃o Set.Iic n) :
    multiplicity p m = multiplicity (↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩)) n := by
  refine' le_antisymmₓ (multiplicity_prime_le_multiplicity_image_by_factor_order_iso hp d) _
  suffices
    multiplicity (↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩)) n ≤
      multiplicity (↑(d.symm (d ⟨p, dvd_of_mem_normalized_factors hp⟩))) m
    by
    rw [d.symm_apply_apply ⟨p, dvd_of_mem_normalized_factors hp⟩, Subtype.coe_mk] at this
    exact this
  letI := Classical.decEq (Associates N)
  simpa only [← Subtype.coe_eta] using
    multiplicity_prime_le_multiplicity_image_by_factor_order_iso
      (mem_normalized_factors_factor_order_iso_of_mem_normalized_factors hn hp d) d.symm

end

variable [Unique Mˣ] [Unique Nˣ]

/-- The order isomorphism between the factors of `mk m` and the factors of `mk n` induced by a
  bijection between the factors of `m` and the factors of `n` that preserves `∣`. -/
@[simps]
def mkFactorOrderIsoOfFactorDvdEquiv {m : M} {n : N} (d : { l : M // l ∣ m } ≃ { l : N // l ∣ n })
    (hd : ∀ l l', (d l : N) ∣ d l' ↔ (l : M) ∣ (l' : M)) : Set.Iic (Associates.mk m) ≃o Set.Iic (Associates.mk n) where
  toFun := fun l =>
    ⟨Associates.mk
        (d
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l
            rw [Subtype.coe_mk, associates_equiv_of_unique_units_apply, out_dvd_iff]
            exact hx⟩),
      mk_le_mk_iff_dvd_iff.mpr (Subtype.prop (d ⟨associatesEquivOfUniqueUnits ↑l, _⟩))⟩
  invFun := fun l =>
    ⟨Associates.mk
        (d.symm
          ⟨associatesEquivOfUniqueUnits ↑l, by
            obtain ⟨x, hx⟩ := l <;>
              rw [Subtype.coe_mk, associates_equiv_of_unique_units_apply, out_dvd_iff] <;> exact hx⟩),
      mk_le_mk_iff_dvd_iff.mpr (Subtype.prop (d.symm ⟨associatesEquivOfUniqueUnits ↑l, _⟩))⟩
  left_inv := fun ⟨l, hl⟩ => by
    simp only [← Subtype.coe_eta, ← Equivₓ.symm_apply_apply, ← Subtype.coe_mk, ← associates_equiv_of_unique_units_apply,
      ← mk_out, ← out_mk, ← normalize_eq]
  right_inv := fun ⟨l, hl⟩ => by
    simp only [← Subtype.coe_eta, ← Equivₓ.apply_symm_apply, ← Subtype.coe_mk, ← associates_equiv_of_unique_units_apply,
      ← out_mk, ← normalize_eq, ← mk_out]
  map_rel_iff' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ <;>
      simp only [← Equivₓ.coe_fn_mk, ← Subtype.mk_le_mk, ← Associates.mk_le_mk_iff_dvd_iff, ← hd, ← Subtype.coe_mk, ←
        associates_equiv_of_unique_units_apply, ← out_dvd_iff, ← mk_out]

variable [UniqueFactorizationMonoid M] [UniqueFactorizationMonoid N] [DecidableEq M]

theorem mem_normalized_factors_factor_dvd_iso_of_mem_normalized_factors [DecidableEq N] {m p : M} {n : N} (hm : m ≠ 0)
    (hn : n ≠ 0) (hp : p ∈ normalizedFactors m) (d : { l : M // l ∣ m } ≃ { l : N // l ∣ n })
    (hd : ∀ l l', (d l : N) ∣ d l' ↔ (l : M) ∣ (l' : M)) :
    ↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩) ∈ normalizedFactors n := by
  suffices
    Prime
      ↑(d
          ⟨associatesEquivOfUniqueUnits (associates_equiv_of_unique_units.symm p), by
            simp [← dvd_of_mem_normalized_factors hp]⟩)
    by
    simp only [← associates_equiv_of_unique_units_apply, ← out_mk, ← normalize_eq, ←
      associates_equiv_of_unique_units_symm_apply] at this
    obtain ⟨q, hq, hq'⟩ :=
      exists_mem_normalized_factors_of_dvd hn this.irreducible
        (d
            ⟨p, by
              apply dvd_of_mem_normalized_factors <;> convert hp⟩).Prop
    rwa [associated_iff_eq.mp hq']
  have :
    Associates.mk
        ↑(d
            ⟨associatesEquivOfUniqueUnits (associates_equiv_of_unique_units.symm p), by
              simp only [← dvd_of_mem_normalized_factors hp, ← associates_equiv_of_unique_units_apply, ← out_mk, ←
                normalize_eq, ← associates_equiv_of_unique_units_symm_apply]⟩) =
      ↑(mkFactorOrderIsoOfFactorDvdEquiv d hd
          ⟨associates_equiv_of_unique_units.symm p, by
            simp only [← associates_equiv_of_unique_units_symm_apply] <;>
              exact mk_dvd_mk.mpr (dvd_of_mem_normalized_factors hp)⟩) :=
    by
    rw [mk_factor_order_iso_of_factor_dvd_equiv_apply_coe]
    simp only [← Subtype.coe_mk]
  rw [← Associates.prime_mk, this]
  letI := Classical.decEq (Associates M)
  refine' map_prime_of_factor_order_iso (mk_ne_zero.mpr hn) _ _
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalized_factors_of_dvd (mk_ne_zero.mpr hm)
      ((prime_mk p).mpr
          (prime_of_normalized_factor p
            (by
              convert hp))).Irreducible
      (mk_le_mk_of_dvd (dvd_of_mem_normalized_factors hp))
  simpa only [← associated_iff_eq.mp hq', ← associates_equiv_of_unique_units_symm_apply] using hq

variable [DecidableRel ((· ∣ ·) : M → M → Prop)] [DecidableRel ((· ∣ ·) : N → N → Prop)]

theorem multiplicity_eq_multiplicity_factor_dvd_iso_of_mem_normalized_factor {m p : M} {n : N} (hm : m ≠ 0) (hn : n ≠ 0)
    (hp : p ∈ normalizedFactors m) (d : { l : M // l ∣ m } ≃ { l : N // l ∣ n })
    (hd : ∀ l l', (d l : N) ∣ d l' ↔ (l : M) ∣ l') :
    multiplicity p m = multiplicity (d ⟨p, dvd_of_mem_normalized_factors hp⟩ : N) n := by
  suffices
    multiplicity (Associates.mk p) (Associates.mk m) =
      multiplicity
        (Associates.mk
          ↑(d
              ⟨associatesEquivOfUniqueUnits (associates_equiv_of_unique_units.symm p), by
                simp [← dvd_of_mem_normalized_factors hp]⟩))
        (Associates.mk n)
    by
    simpa only [← multiplicity_mk_eq_multiplicity, ← associates_equiv_of_unique_units_symm_apply, ←
      associates_equiv_of_unique_units_apply, ← out_mk, ← normalize_eq] using this
  have :
    Associates.mk
        ↑(d
            ⟨associatesEquivOfUniqueUnits (associates_equiv_of_unique_units.symm p), by
              simp only [← dvd_of_mem_normalized_factors hp, ← associates_equiv_of_unique_units_symm_apply, ←
                associates_equiv_of_unique_units_apply, ← out_mk, ← normalize_eq]⟩) =
      ↑(mkFactorOrderIsoOfFactorDvdEquiv d hd
          ⟨associates_equiv_of_unique_units.symm p, by
            rw [associates_equiv_of_unique_units_symm_apply] <;>
              exact mk_le_mk_of_dvd (dvd_of_mem_normalized_factors hp)⟩) :=
    by
    rw [mk_factor_order_iso_of_factor_dvd_equiv_apply_coe]
    rfl
  rw [this]
  letI := Classical.decEq (Associates M)
  refine'
    multiplicity_prime_eq_multiplicity_image_by_factor_order_iso (mk_ne_zero.mpr hn) _
      (mkFactorOrderIsoOfFactorDvdEquiv d hd)
  obtain ⟨q, hq, hq'⟩ :=
    exists_mem_normalized_factors_of_dvd (mk_ne_zero.mpr hm)
      ((prime_mk p).mpr (prime_of_normalized_factor p hp)).Irreducible
      (mk_le_mk_of_dvd (dvd_of_mem_normalized_factors hp))
  rwa [associated_iff_eq.mp hq']

