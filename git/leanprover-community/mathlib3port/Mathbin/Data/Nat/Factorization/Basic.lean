/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import Mathbin.Data.Nat.Prime
import Mathbin.Data.Finsupp.Multiset
import Mathbin.Algebra.BigOperators.Finsupp
import Mathbin.Tactic.Linarith.Default
import Mathbin.Tactic.IntervalCases

/-!
# Prime factorizations

 `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`.  For example, since 2000 = 2^4 * 5^3,
  * `factorization 2000 2` is 4
  * `factorization 2000 5` is 3
  * `factorization 2000 k` is 0 for all other `k : ℕ`.

## TODO

* As discussed in this Zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/217875/topic/Multiplicity.20in.20the.20naturals
We have lots of disparate ways of talking about the multiplicity of a prime
in a natural number, including `factors.count`, `padic_val_nat`, `multiplicity`,
and the material in `data/pnat/factors`.  Move some of this material to this file,
prove results about the relationships between these definitions,
and (where appropriate) choose a uniform canonical way of expressing these ideas.

* Moreover, the results here should be generalised to an arbitrary unique factorization monoid
with a normalization function, and then deduplicated.  The basics of this have been started in
`ring_theory/unique_factorization_domain`.

* Extend the inductions to any `normalization_monoid` with unique factorization.

-/


open Nat Finset List Finsupp

open BigOperators

namespace Nat

/-- `n.factorization` is the finitely supported function `ℕ →₀ ℕ`
 mapping each prime factor of `n` to its multiplicity in `n`. -/
noncomputable def factorization (n : ℕ) : ℕ →₀ ℕ :=
  (n.factors : Multiset ℕ).toFinsupp

/-! ### Basic facts about factorization -/


@[simp]
theorem factorization_prod_pow_eq_self {n : ℕ} (hn : n ≠ 0) : n.factorization.Prod pow = n := by
  simp only [← prod_to_multiset, factorization, Multiset.coe_prod, Multiset.to_finsupp_to_multiset]
  exact prod_factors hn

/-- We can write both `n.factorization p` and `n.factors.count p` to represent the power
of `p` in the factorization of `n`: we declare the former to be the simp-normal form.
However, since `factorization` is a finsupp it's noncomputable.  This theorem can also
be used in reverse to compute values of `factorization n p` when required. -/
@[simp]
theorem factors_count_eq {n p : ℕ} : n.factors.count p = n.factorization p := by
  simp [factorization]

theorem eq_of_factorization_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : ℕ, a.factorization p = b.factorization p) : a = b :=
  eq_of_perm_factors ha hb
    (by
      simpa only [List.perm_iff_count, factors_count_eq] using h)

/-- Every nonzero natural number has a unique prime factorization -/
theorem factorization_inj : Set.InjOn factorization { x : ℕ | x ≠ 0 } := fun a ha b hb h =>
  eq_of_factorization_eq ha hb fun p => by
    simp [h]

@[simp]
theorem factorization_zero : factorization 0 = 0 := by
  simp [factorization]

@[simp]
theorem factorization_one : factorization 1 = 0 := by
  simp [factorization]

/-- The support of `n.factorization` is exactly `n.factors.to_finset` -/
@[simp]
theorem support_factorization {n : ℕ} : n.factorization.support = n.factors.toFinset := by
  simpa [factorization, Multiset.to_finsupp_support]

theorem factor_iff_mem_factorization {n p : ℕ} : p ∈ n.factorization.support ↔ p ∈ n.factors := by
  simp only [support_factorization, List.mem_to_finset]

theorem prime_of_mem_factorization {n p : ℕ} (hp : p ∈ n.factorization.support) : p.Prime :=
  prime_of_mem_factors (factor_iff_mem_factorization.mp hp)

theorem pos_of_mem_factorization {n p : ℕ} (hp : p ∈ n.factorization.support) : 0 < p :=
  Prime.pos (prime_of_mem_factorization hp)

theorem le_of_mem_factorization {n p : ℕ} (h : p ∈ n.factorization.support) : p ≤ n :=
  le_of_mem_factors (factor_iff_mem_factorization.mp h)

@[simp]
theorem factorization_eq_zero_of_non_prime (n : ℕ) {p : ℕ} (hp : ¬p.Prime) : n.factorization p = 0 :=
  not_mem_support_iff.1 (mt prime_of_mem_factorization hp)

theorem factorization_eq_zero_of_lt {n p : ℕ} (h : n < p) : n.factorization p = 0 :=
  Finsupp.not_mem_support_iff.mp (mt le_of_mem_factorization (not_le_of_lt h))

@[simp]
theorem factorization_zero_right (n : ℕ) : n.factorization 0 = 0 :=
  factorization_eq_zero_of_non_prime _ not_prime_zero

@[simp]
theorem factorization_one_right (n : ℕ) : n.factorization 1 = 0 :=
  factorization_eq_zero_of_non_prime _ not_prime_one

theorem dvd_of_factorization_pos {n p : ℕ} (hn : n.factorization p ≠ 0) : p ∣ n :=
  dvd_of_mem_factors (factor_iff_mem_factorization.1 (mem_support_iff.2 hn))

theorem Prime.factorization_pos_of_dvd {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h : p ∣ n) : 0 < n.factorization p := by
  rwa [← factors_count_eq, count_pos, mem_factors_iff_dvd hn hp]

/-- The only numbers with empty prime factorization are `0` and `1` -/
theorem factorization_eq_zero_iff (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 := by
  simp [factorization, AddEquiv.map_eq_zero_iff, Multiset.coe_eq_zero]

theorem factorization_eq_zero_iff' (n p : ℕ) : n.factorization p = 0 ↔ ¬p.Prime ∨ ¬p ∣ n ∨ n = 0 := by
  rw [← not_mem_support_iff, support_factorization, mem_to_finset]
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    
  · simp [hn, Nat.mem_factors, not_and_distrib]
    

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp]
theorem factorization_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization = a.factorization + b.factorization := by
  ext p
  simp only [add_apply, ← factors_count_eq, perm_iff_count.mp (perm_factors_mul ha hb) p, count_append]

theorem factorization_mul_support {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization.support = a.factorization.support ∪ b.factorization.support := by
  ext q
  simp only [Finset.mem_union, factor_iff_mem_factorization]
  exact mem_factors_mul ha hb

/-- For any `p`, the power of `p` in `n^k` is `k` times the power in `n` -/
@[simp]
theorem factorization_pow (n k : ℕ) : factorization (n ^ k) = k • n.factorization := by
  induction' k with k ih
  · simp
    
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    
  rw [pow_succₓ, factorization_mul hn (pow_ne_zero _ hn), ih, succ_eq_one_add, add_smul, one_smul]

/-- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
@[simp]
theorem Prime.factorization {p : ℕ} (hp : Prime p) : p.factorization = single p 1 := by
  ext q
  rw [← factors_count_eq, factors_prime hp, single_apply, count_singleton', if_congr eq_comm] <;> rfl

/-- For prime `p` the only prime factor of `p^k` is `p` with multiplicity `k` -/
theorem Prime.factorization_pow {p k : ℕ} (hp : Prime p) : factorization (p ^ k) = single p k := by
  simp [hp]

/-- If the factorization of `n` contains just one number `p` then `n` is a power of `p` -/
theorem eq_pow_of_factorization_eq_single {n p k : ℕ} (hn : n ≠ 0) (h : n.factorization = Finsupp.single p k) :
    n = p ^ k := by
  rw [← Nat.factorization_prod_pow_eq_self hn, h]
  simp

/-- If a product over `n.factorization` doesn't use the multiplicities of the prime factors
then it's equal to the corresponding product over `n.factors.to_finset` -/
theorem prod_factorization_eq_prod_factors {n : ℕ} {β : Type _} [CommMonoidₓ β] (f : ℕ → β) :
    (n.factorization.Prod fun p k => f p) = ∏ p in n.factors.toFinset, f p := by
  apply prod_congr support_factorization
  simp

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
/-- For any `p : ℕ` and any function `g : α → ℕ` that's non-zero on `S : finset α`,
the power of `p` in `S.prod g` equals the sum over `x ∈ S` of the powers of `p` in `g x`.
Generalises `factorization_mul`, which is the special case where `S.card = 2` and `g = id`. -/
theorem factorization_prod {α : Type _} {S : Finset α} {g : α → ℕ} (hS : ∀, ∀ x ∈ S, ∀, g x ≠ 0) :
    (S.Prod g).factorization = S.Sum fun x => (g x).factorization := by
  classical
  ext p
  apply Finset.induction_on' S
  · simp
    
  · intro x T hxS hTS hxT IH
    have hT : T.prod g ≠ 0 := prod_ne_zero_iff.mpr fun x hx => hS x (hTS hx)
    simp [prod_insert hxT, sum_insert hxT, ← IH, factorization_mul (hS x hxS) hT]
    

/-! ### Equivalence between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/


/-- Any finsupp `f : ℕ →₀ ℕ` whose support is in the primes is equal to the factorization of
the product `∏ (a : ℕ) in f.support, a ^ f a`. -/
theorem prod_pow_factorization_eq_self {f : ℕ →₀ ℕ} (hf : ∀ p : ℕ, p ∈ f.support → Prime p) :
    (f.Prod pow).factorization = f := by
  have h : ∀ x : ℕ, x ∈ f.support → x ^ f x ≠ 0 := fun p hp => pow_ne_zero _ (Prime.ne_zero (hf p hp))
  simp only [Finsupp.prod, factorization_prod h]
  nth_rw_rhs 0[(sum_single f).symm]
  exact sum_congr rfl fun p hp => prime.factorization_pow (hf p hp)

theorem eq_factorization_iff {n : ℕ} {f : ℕ →₀ ℕ} (hn : n ≠ 0) (hf : ∀, ∀ p ∈ f.support, ∀, Prime p) :
    f = n.factorization ↔ f.Prod pow = n :=
  ⟨fun h => by
    rw [h, factorization_prod_pow_eq_self hn], fun h => by
    rw [← h, prod_pow_factorization_eq_self hf]⟩

/-- The equiv between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/
noncomputable def factorizationEquiv : ℕ+ ≃ { f : ℕ →₀ ℕ | ∀, ∀ p ∈ f.support, ∀, Prime p } where
  toFun := fun ⟨n, hn⟩ => ⟨n.factorization, fun _ => prime_of_mem_factorization⟩
  invFun := fun ⟨f, hf⟩ => ⟨f.Prod pow, prod_pow_pos_of_zero_not_mem_support fun H => not_prime_zero (hf 0 H)⟩
  left_inv := fun ⟨x, hx⟩ => Subtype.ext <| factorization_prod_pow_eq_self hx.Ne.symm
  right_inv := fun ⟨f, hf⟩ => Subtype.ext <| prod_pow_factorization_eq_self hf

theorem factorization_equiv_apply (n : ℕ+) : (factorizationEquiv n).1 = n.1.factorization := by
  cases n
  rfl

theorem factorization_equiv_inv_apply {f : ℕ →₀ ℕ} (hf : ∀, ∀ p ∈ f.support, ∀, Prime p) :
    (factorizationEquiv.symm ⟨f, hf⟩).1 = f.Prod pow :=
  rfl

/-! ### Factorization and divisibility -/


theorem dvd_of_mem_factorization {n p : ℕ} (h : p ∈ n.factorization.support) : p ∣ n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    
  simp [← mem_factors_iff_dvd hn (prime_of_mem_factorization h), factor_iff_mem_factorization.mp h]

theorem pow_factorization_dvd (n p : ℕ) : p ^ n.factorization p ∣ n := by
  by_cases' hp : p.prime
  swap
  · simp [factorization_eq_zero_of_non_prime n hp]
    
  rw [← factors_count_eq]
  apply dvd_of_factors_subperm (pow_ne_zero _ hp.ne_zero)
  rw [hp.factors_pow, List.subperm_ext_iff]
  intro q hq
  simp [List.eq_of_mem_repeat hq]

theorem pow_factorization_le {n : ℕ} (p : ℕ) (hn : n ≠ 0) : p ^ n.factorization p ≤ n :=
  le_of_dvdₓ hn.bot_lt (Nat.pow_factorization_dvd n p)

theorem div_pow_factorization_ne_zero {n : ℕ} (p : ℕ) (hn : n ≠ 0) : n / p ^ n.factorization p ≠ 0 := by
  by_cases' pp : Nat.Prime p
  · apply mt (Nat.div_eq_zero_iff (pow_pos (prime.pos pp) _)).1
    simp [le_of_dvd hn.bot_lt (Nat.pow_factorization_dvd n p)]
    
  · simp [Nat.factorization_eq_zero_of_non_prime n pp, hn]
    

theorem pow_succ_factorization_not_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) : ¬p ^ (n.factorization p + 1) ∣ n := by
  intro h
  have := factors_sublist_of_dvd h hn
  rw [hp.factors_pow, ← le_count_iff_repeat_sublist, factors_count_eq] at this
  linarith

theorem factorization_le_iff_dvd {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) : d.factorization ≤ n.factorization ↔ d ∣ n := by
  constructor
  · intro hdn
    set K := n.factorization - d.factorization with hK
    use K.prod pow
    rw [← factorization_prod_pow_eq_self hn, ← factorization_prod_pow_eq_self hd, ←
      Finsupp.prod_add_index' pow_zeroₓ pow_addₓ, hK, add_tsub_cancel_of_le hdn]
    
  · rintro ⟨c, rfl⟩
    rw [factorization_mul hd (right_ne_zero_of_mul hn)]
    simp
    

theorem factorization_le_factorization_mul_left {a b : ℕ} (hb : b ≠ 0) : a.factorization ≤ (a * b).factorization := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
    
  rw [factorization_le_iff_dvd ha <| mul_ne_zero ha hb]
  exact Dvd.intro b rfl

theorem factorization_le_factorization_mul_right {a b : ℕ} (ha : a ≠ 0) : b.factorization ≤ (a * b).factorization := by
  rw [mul_comm]
  apply factorization_le_factorization_mul_left ha

theorem Prime.pow_dvd_iff_le_factorization {p k n : ℕ} (pp : Prime p) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ n.factorization p := by
  rw [← factorization_le_iff_dvd (pow_pos pp.pos k).ne' hn, pp.factorization_pow, single_le_iff]

theorem Prime.pow_dvd_iff_dvd_pow_factorization {p k n : ℕ} (pp : Prime p) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ p ^ k ∣ p ^ n.factorization p := by
  rw [pow_dvd_pow_iff_le_right pp.one_lt, pp.pow_dvd_iff_le_factorization hn]

theorem Prime.dvd_iff_one_le_factorization {p n : ℕ} (pp : Prime p) (hn : n ≠ 0) : p ∣ n ↔ 1 ≤ n.factorization p :=
  Iff.trans
    (by
      simp )
    (pp.pow_dvd_iff_le_factorization hn)

theorem exists_factorization_lt_of_lt {a b : ℕ} (ha : a ≠ 0) (hab : a < b) :
    ∃ p : ℕ, a.factorization p < b.factorization p := by
  have hb : b ≠ 0 := (ha.bot_lt.trans hab).ne'
  contrapose! hab
  rw [← Finsupp.le_def, factorization_le_iff_dvd hb ha] at hab
  exact le_of_dvd ha.bot_lt hab

@[simp]
theorem factorization_div {d n : ℕ} (h : d ∣ n) : (n / d).factorization = n.factorization - d.factorization := by
  rcases eq_or_ne d 0 with (rfl | hd)
  · simp [zero_dvd_iff.mp h]
    
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    
  apply add_left_injective d.factorization
  simp only
  rw [tsub_add_cancel_of_le <| (Nat.factorization_le_iff_dvd hd hn).mpr h, ←
    Nat.factorization_mul (Nat.div_pos (Nat.le_of_dvdₓ hn.bot_lt h) hd.bot_lt).ne' hd, Nat.div_mul_cancelₓ h]

theorem not_dvd_div_pow_factorization {n p : ℕ} (hp : Prime p) (hn : n ≠ 0) : ¬p ∣ n / p ^ n.factorization p := by
  rw [Nat.Prime.dvd_iff_one_le_factorization hp (div_pow_factorization_ne_zero p hn),
    Nat.factorization_div (Nat.pow_factorization_dvd n p)]
  simp [hp.factorization]

theorem dvd_iff_div_factorization_eq_tsub {d n : ℕ} (hd : d ≠ 0) (hdn : d ≤ n) :
    d ∣ n ↔ (n / d).factorization = n.factorization - d.factorization := by
  refine' ⟨factorization_div, _⟩
  rcases eq_or_lt_of_le hdn with (rfl | hd_lt_n)
  · simp
    
  have h1 : n / d ≠ 0 := fun H => Nat.lt_asymmₓ hd_lt_n ((Nat.div_eq_zero_iff hd.bot_lt).mp H)
  intro h
  rw [dvd_iff_le_div_mul n d]
  by_contra h2
  cases' exists_factorization_lt_of_lt (mul_ne_zero h1 hd) (not_le.mp h2) with p hp
  rwa [factorization_mul h1 hd, add_apply, ← lt_tsub_iff_right, h, tsub_apply, lt_self_iff_false] at hp

theorem dvd_iff_prime_pow_dvd_dvd (n d : ℕ) : d ∣ n ↔ ∀ p k : ℕ, Prime p → p ^ k ∣ d → p ^ k ∣ n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    
  rcases eq_or_ne d 0 with (rfl | hd)
  · simp only [zero_dvd_iff, hn, false_iffₓ, not_forall]
    refine' ⟨2, n, prime_two, ⟨dvd_zero _, _⟩⟩
    apply mt (le_of_dvd hn.bot_lt) (not_le.mpr (lt_two_pow n))
    
  refine' ⟨fun h p k _ hpkd => dvd_trans hpkd h, _⟩
  rw [← factorization_le_iff_dvd hd hn, Finsupp.le_def]
  intro h p
  by_cases' pp : Prime p
  swap
  · simp [factorization_eq_zero_of_non_prime d pp]
    
  rw [← pp.pow_dvd_iff_le_factorization hn]
  exact h p _ pp (pow_factorization_dvd _ _)

theorem prod_prime_factors_dvd (n : ℕ) : (∏ p : ℕ in n.factors.toFinset, p) ∣ n := by
  by_cases' hn : n = 0
  · subst hn
    simp
    
  simpa [prod_factors hn] using Multiset.to_finset_prod_dvd_prod (n.factors : Multiset ℕ)

theorem factorization_gcd {a b : ℕ} (ha_pos : a ≠ 0) (hb_pos : b ≠ 0) :
    (gcdₓ a b).factorization = a.factorization⊓b.factorization := by
  let dfac := a.factorization⊓b.factorization
  let d := dfac.prod pow
  have dfac_prime : ∀ p : ℕ, p ∈ dfac.support → Prime p := by
    intro p hp
    have : p ∈ a.factors ∧ p ∈ b.factors := by
      simpa using hp
    exact prime_of_mem_factors this.1
  have h1 : d.factorization = dfac := prod_pow_factorization_eq_self dfac_prime
  have hd_pos : d ≠ 0 := (factorization_equiv.inv_fun ⟨dfac, dfac_prime⟩).2.Ne.symm
  suffices d = gcd a b by
    rwa [← this]
  apply gcd_greatest
  · rw [← factorization_le_iff_dvd hd_pos ha_pos, h1]
    exact inf_le_left
    
  · rw [← factorization_le_iff_dvd hd_pos hb_pos, h1]
    exact inf_le_right
    
  · intro e hea heb
    rcases Decidable.eq_or_ne e 0 with (rfl | he_pos)
    · simp only [zero_dvd_iff] at hea
      contradiction
      
    have hea' := (factorization_le_iff_dvd he_pos ha_pos).mpr hea
    have heb' := (factorization_le_iff_dvd he_pos hb_pos).mpr heb
    simp [← factorization_le_iff_dvd he_pos hd_pos, h1, hea', heb']
    

theorem div_factorization_pos {q r : ℕ} (hr : Nat.Prime r) (hq : q ≠ 0) : q / r ^ q.factorization r ≠ 0 := by
  set n := q.factorization r
  set a := q / r ^ n
  apply mt (Nat.div_eq_zero_iff (pow_pos (Nat.Prime.pos hr) _)).1
  exact not_lt.mpr (Nat.le_of_dvdₓ (pos_iff_ne_zero.mpr hq) (Nat.pow_factorization_dvd q r))

theorem ne_dvd_factorization_div {q r : ℕ} (hr : Nat.Prime r) (hq : q ≠ 0) : ¬r ∣ q / r ^ q.factorization r := by
  set n := q.factorization r
  set a := q / r ^ n
  by_contra r_dvd_a
  have a_fact_r_pos : a.factorization r ≠ 0 :=
    ne_of_gtₓ (Nat.Prime.factorization_pos_of_dvd hr (div_factorization_pos hr hq) r_dvd_a)
  have a_fact_r_zero : a.factorization r = 0 :=
    calc
      a.factorization r = (q.factorization - (r ^ n).factorization) r := by
        rw [← Nat.factorization_div (Nat.pow_factorization_dvd q r)]
      _ = q.factorization r - (r ^ n).factorization r := (Nat.factorization q).tsub_apply (r ^ n).factorization r
      _ = n - (Finsupp.single r n) r := by
        rw [Nat.Prime.factorization_pow hr]
      _ = n - n := by
        rw [Finsupp.single_eq_same, tsub_self]
      _ = 0 := tsub_self n
      
  exact absurd a_fact_r_zero a_fact_r_pos

/-! ### Factorization and coprimes -/


/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
theorem factorization_mul_apply_of_coprime {p a b : ℕ} (hab : Coprime a b) :
    (a * b).factorization p = a.factorization p + b.factorization p := by
  simp only [← factors_count_eq, perm_iff_count.mp (perm_factors_mul_of_coprime hab), count_append]

/-- For coprime `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
theorem factorization_mul_of_coprime {a b : ℕ} (hab : Coprime a b) :
    (a * b).factorization = a.factorization + b.factorization := by
  ext q
  simp only [Finsupp.coe_add, add_apply, ← factors_count_eq, factorization_mul_apply_of_coprime hab]

/-- If `p` is a prime factor of `a` then the power of `p` in `a` is the same that in `a * b`,
for any `b` coprime to `a`. -/
theorem factorization_eq_of_coprime_left {p a b : ℕ} (hab : Coprime a b) (hpa : p ∈ a.factors) :
    (a * b).factorization p = a.factorization p := by
  rw [factorization_mul_apply_of_coprime hab, ← factors_count_eq, ← factors_count_eq]
  simpa only [count_eq_zero_of_not_mem (coprime_factors_disjoint hab hpa)]

/-- If `p` is a prime factor of `b` then the power of `p` in `b` is the same that in `a * b`,
for any `a` coprime to `b`. -/
theorem factorization_eq_of_coprime_right {p a b : ℕ} (hab : Coprime a b) (hpb : p ∈ b.factors) :
    (a * b).factorization p = b.factorization p := by
  rw [mul_comm]
  exact factorization_eq_of_coprime_left (coprime_comm.mp hab) hpb

/-- The prime factorizations of coprime `a` and `b` are disjoint -/
theorem factorization_disjoint_of_coprime {a b : ℕ} (hab : Coprime a b) :
    Disjoint a.factorization.support b.factorization.support := by
  simpa only [support_factorization] using disjoint_to_finset_iff_disjoint.mpr (coprime_factors_disjoint hab)

/-- For coprime `a` and `b` the prime factorization `a * b` is the union of those of `a` and `b` -/
theorem factorization_mul_support_of_coprime {a b : ℕ} (hab : Coprime a b) :
    (a * b).factorization.support = a.factorization.support ∪ b.factorization.support := by
  rw [factorization_mul_of_coprime hab]
  exact support_add_eq (factorization_disjoint_of_coprime hab)

/-! ### Induction principles involving factorizations -/


/-- Given `P 0, P 1` and a way to extend `P a` to `P (p ^ n * a)` for prime `p` not dividing `a`,
we can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def recOnPrimePow {P : ℕ → Sort _} (h0 : P 0) (h1 : P 1)
    (h : ∀ a p n : ℕ, p.Prime → ¬p ∣ a → 0 < n → P a → P (p ^ n * a)) : ∀ a : ℕ, P a := fun a =>
  (Nat.strongRecOn a) fun n =>
    match n with
    | 0 => fun _ => h0
    | 1 => fun _ => h1
    | k + 2 => fun hk => by
      let p := (k + 2).minFac
      have hp : Prime p := min_fac_prime (succ_succ_ne_one k)
      -- the awkward `let` stuff here is because `factorization` is noncomputable (finsupp);
      -- we get around this by using the computable `factors.count`, and rewriting when we want
      -- to use the `factorization` API
      let t := (k + 2).factors.count p
      have ht : t = (k + 2).factorization p := factors_count_eq
      have hpt : p ^ t ∣ k + 2 := by
        rw [ht]
        exact pow_factorization_dvd _ _
      have htp : 0 < t := by
        rw [ht]
        exact hp.factorization_pos_of_dvd (Nat.succ_ne_zero _) (min_fac_dvd _)
      convert h ((k + 2) / p ^ t) p t hp _ _ _
      · rw [Nat.mul_div_cancel'ₓ hpt]
        
      · rw [Nat.dvd_div_iff hpt, ← pow_succ'ₓ, ht]
        exact pow_succ_factorization_not_dvd (k + 1).succ_ne_zero hp
        
      · exact htp
        
      · apply hk _ (Nat.div_lt_of_lt_mul _)
        simp [lt_mul_iff_one_lt_left Nat.succ_pos', one_lt_pow_iff htp.ne, hp.one_lt]
        

/-- Given `P 0`, `P 1`, and `P (p ^ n)` for positive prime powers, and a way to extend `P a` and
`P b` to `P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def recOnPosPrimePosCoprime {P : ℕ → Sort _} (hp : ∀ p n : ℕ, Prime p → 0 < n → P (p ^ n)) (h0 : P 0) (h1 : P 1)
    (h : ∀ a b, 1 < a → 1 < b → Coprime a b → P a → P b → P (a * b)) : ∀ a, P a :=
  recOnPrimePow h0 h1 <| by
    intro a p n hp' hpa hn hPa
    by_cases' ha1 : a = 1
    · rw [ha1, mul_oneₓ]
      exact hp p n hp' hn
      
    refine'
      h (p ^ n) a (hp'.one_lt.trans_le (le_self_pow (prime.one_lt hp').le (succ_le_iff.mpr hn))) _ _ (hp _ _ hp' hn) hPa
    · refine' lt_of_not_geₓ fun h : a ≤ 1 => _
      interval_cases a
      · simpa only [dvd_zero, not_true] using hpa
        
      · contradiction
        
      
    simpa [hn, prime.coprime_iff_not_dvd hp']

/-- Given `P 0`, `P (p ^ n)` for all prime powers, and a way to extend `P a` and `P b` to
`P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def recOnPrimeCoprime {P : ℕ → Sort _} (h0 : P 0) (hp : ∀ p n : ℕ, Prime p → P (p ^ n))
    (h : ∀ a b, 1 < a → 1 < b → Coprime a b → P a → P b → P (a * b)) : ∀ a, P a :=
  recOnPosPrimePosCoprime (fun p n h _ => hp p n h) h0 (hp 2 0 prime_two) h

/-- Given `P 0`, `P 1`, `P p` for all primes, and a way to extend `P a` and `P b` to
`P (a * b)`, we can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def recOnMul {P : ℕ → Sort _} (h0 : P 0) (h1 : P 1) (hp : ∀ p, Prime p → P p) (h : ∀ a b, P a → P b → P (a * b)) :
    ∀ a, P a :=
  let hp : ∀ p n : ℕ, Prime p → P (p ^ n) := fun p n hp' =>
    match n with
    | 0 => h1
    | n + 1 => h _ _ (hp p hp') (_match _)
  (recOnPrimeCoprime h0 hp) fun a b _ _ _ => h a b

/-- For any multiplicative function `f` with `f 1 = 1` and any `n ≠ 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
theorem multiplicative_factorization {β : Type _} [CommMonoidₓ β] (f : ℕ → β)
    (h_mult : ∀ x y : ℕ, Coprime x y → f (x * y) = f x * f y) (hf : f 1 = 1) :
    ∀ {n : ℕ}, n ≠ 0 → f n = n.factorization.Prod fun p k => f (p ^ k) := by
  apply' Nat.recOnPosPrimePosCoprime
  · intro p k hp hk hpk
    simp [prime.factorization_pow hp, Finsupp.prod_single_index _, hf]
    
  · simp
    
  · rintro -
    rw [factorization_one, hf]
    simp
    
  · intro a b _ _ hab ha hb hab_pos
    rw [h_mult a b hab, ha (left_ne_zero_of_mul hab_pos), hb (right_ne_zero_of_mul hab_pos),
      factorization_mul_of_coprime hab, ← prod_add_index_of_disjoint]
    convert factorization_disjoint_of_coprime hab
    

/-- For any multiplicative function `f` with `f 1 = 1` and `f 0 = 1`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
theorem multiplicative_factorization' {β : Type _} [CommMonoidₓ β] (f : ℕ → β)
    (h_mult : ∀ x y : ℕ, Coprime x y → f (x * y) = f x * f y) (hf0 : f 0 = 1) (hf1 : f 1 = 1) :
    ∀ {n : ℕ}, f n = n.factorization.Prod fun p k => f (p ^ k) := by
  apply' Nat.recOnPosPrimePosCoprime
  · intro p k hp hk
    simp only [hp.factorization_pow]
    rw [prod_single_index _]
    simp [hf1]
    
  · simp [hf0]
    
  · rw [factorization_one, hf1]
    simp
    
  · intro a b _ _ hab ha hb
    rw [h_mult a b hab, ha, hb, factorization_mul_of_coprime hab, ← prod_add_index_of_disjoint]
    convert factorization_disjoint_of_coprime hab
    

end Nat

