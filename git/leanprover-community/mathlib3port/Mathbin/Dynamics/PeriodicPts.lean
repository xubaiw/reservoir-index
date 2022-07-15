/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Algebra.Hom.Iterate
import Mathbin.Data.List.Cycle
import Mathbin.Data.Nat.Prime
import Mathbin.Dynamics.FixedPoints.Basic

/-!
# Periodic points

A point `x : α` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.

## Main definitions

* `is_periodic_pt f n x` : `x` is a periodic point of `f` of period `n`, i.e. `f^[n] x = x`.
  We do not require `n > 0` in the definition.
* `pts_of_period f n` : the set `{x | is_periodic_pt f n x}`. Note that `n` is not required to
  be the minimal period of `x`.
* `periodic_pts f` : the set of all periodic points of `f`.
* `minimal_period f x` : the minimal period of a point `x` under an endomorphism `f` or zero
  if `x` is not a periodic point of `f`.
* `orbit f x`: the cycle `[x, f x, f (f x), ...]` for a periodic point.

## Main statements

We provide “dot syntax”-style operations on terms of the form `h : is_periodic_pt f n x` including
arithmetic operations on `n` and `h.map (hg : semiconj_by g f f')`. We also prove that `f`
is bijective on each set `pts_of_period f n` and on `periodic_pts f`. Finally, we prove that `x`
is a periodic point of `f` of period `n` if and only if `minimal_period f x | n`.

## References

* https://en.wikipedia.org/wiki/Periodic_point

-/


open Set

namespace Function

variable {α : Type _} {β : Type _} {f fa : α → α} {fb : β → β} {x y : α} {m n : ℕ}

/-- A point `x` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.
Note that we do not require `0 < n` in this definition. Many theorems about periodic points
need this assumption. -/
def IsPeriodicPt (f : α → α) (n : ℕ) (x : α) :=
  IsFixedPt (f^[n]) x

/-- A fixed point of `f` is a periodic point of `f` of any prescribed period. -/
theorem IsFixedPt.is_periodic_pt (hf : IsFixedPt f x) (n : ℕ) : IsPeriodicPt f n x :=
  hf.iterate n

/-- For the identity map, all points are periodic. -/
theorem is_periodic_id (n : ℕ) (x : α) : IsPeriodicPt id n x :=
  (is_fixed_pt_id x).IsPeriodicPt n

/-- Any point is a periodic point of period `0`. -/
theorem is_periodic_pt_zero (f : α → α) (x : α) : IsPeriodicPt f 0 x :=
  is_fixed_pt_id x

namespace IsPeriodicPt

instance [DecidableEq α] {f : α → α} {n : ℕ} {x : α} : Decidable (IsPeriodicPt f n x) :=
  is_fixed_pt.decidable

protected theorem is_fixed_pt (hf : IsPeriodicPt f n x) : IsFixedPt (f^[n]) x :=
  hf

protected theorem map (hx : IsPeriodicPt fa n x) {g : α → β} (hg : Semiconj g fa fb) : IsPeriodicPt fb n (g x) :=
  hx.map (hg.iterate_right n)

theorem apply_iterate (hx : IsPeriodicPt f n x) (m : ℕ) : IsPeriodicPt f n ((f^[m]) x) :=
  hx.map <| Commute.iterate_self f m

protected theorem apply (hx : IsPeriodicPt f n x) : IsPeriodicPt f n (f x) :=
  hx.apply_iterate 1

protected theorem add (hn : IsPeriodicPt f n x) (hm : IsPeriodicPt f m x) : IsPeriodicPt f (n + m) x := by
  rw [is_periodic_pt, iterate_add]
  exact hn.comp hm

theorem left_of_add (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f m x) : IsPeriodicPt f n x := by
  rw [is_periodic_pt, iterate_add] at hn
  exact hn.left_of_comp hm

theorem right_of_add (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f n x) : IsPeriodicPt f m x := by
  rw [add_commₓ] at hn
  exact hn.left_of_add hm

protected theorem sub (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) : IsPeriodicPt f (m - n) x := by
  cases' le_totalₓ n m with h h
  · refine' left_of_add _ hn
    rwa [tsub_add_cancel_of_le h]
    
  · rw [tsub_eq_zero_iff_le.mpr h]
    apply is_periodic_pt_zero
    

protected theorem mul_const (hm : IsPeriodicPt f m x) (n : ℕ) : IsPeriodicPt f (m * n) x := by
  simp only [← is_periodic_pt, ← iterate_mul, ← hm.is_fixed_pt.iterate n]

protected theorem const_mul (hm : IsPeriodicPt f m x) (n : ℕ) : IsPeriodicPt f (n * m) x := by
  simp only [← mul_comm n, ← hm.mul_const n]

theorem trans_dvd (hm : IsPeriodicPt f m x) {n : ℕ} (hn : m ∣ n) : IsPeriodicPt f n x :=
  let ⟨k, hk⟩ := hn
  hk.symm ▸ hm.mul_const k

protected theorem iterate (hf : IsPeriodicPt f n x) (m : ℕ) : IsPeriodicPt (f^[m]) n x := by
  rw [is_periodic_pt, ← iterate_mul, mul_comm, iterate_mul]
  exact hf.is_fixed_pt.iterate m

theorem comp {g : α → α} (hco : Commute f g) (hf : IsPeriodicPt f n x) (hg : IsPeriodicPt g n x) :
    IsPeriodicPt (f ∘ g) n x := by
  rw [is_periodic_pt, hco.comp_iterate]
  exact hf.comp hg

theorem comp_lcm {g : α → α} (hco : Commute f g) (hf : IsPeriodicPt f m x) (hg : IsPeriodicPt g n x) :
    IsPeriodicPt (f ∘ g) (Nat.lcmₓ m n) x :=
  (hf.trans_dvd <| Nat.dvd_lcm_leftₓ _ _).comp hco (hg.trans_dvd <| Nat.dvd_lcm_rightₓ _ _)

theorem left_of_comp {g : α → α} (hco : Commute f g) (hfg : IsPeriodicPt (f ∘ g) n x) (hg : IsPeriodicPt g n x) :
    IsPeriodicPt f n x := by
  rw [is_periodic_pt, hco.comp_iterate] at hfg
  exact hfg.left_of_comp hg

theorem iterate_mod_apply (h : IsPeriodicPt f n x) (m : ℕ) : (f^[m % n]) x = (f^[m]) x := by
  conv_rhs => rw [← Nat.mod_add_divₓ m n, iterate_add_apply, (h.mul_const _).Eq]

protected theorem mod (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) : IsPeriodicPt f (m % n) x :=
  (hn.iterate_mod_apply m).trans hm

protected theorem gcd (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) : IsPeriodicPt f (m.gcd n) x := by
  revert hm hn
  refine' Nat.gcdₓ.induction m n (fun n h0 hn => _) fun m n hm ih hm hn => _
  · rwa [Nat.gcd_zero_leftₓ]
    
  · rw [Nat.gcd_recₓ]
    exact ih (hn.mod hm) hm
    

/-- If `f` sends two periodic points `x` and `y` of the same positive period to the same point,
then `x = y`. For a similar statement about points of different periods see `eq_of_apply_eq`. -/
theorem eq_of_apply_eq_same (hx : IsPeriodicPt f n x) (hy : IsPeriodicPt f n y) (hn : 0 < n) (h : f x = f y) : x = y :=
  by
  rw [← hx.eq, ← hy.eq, ← iterate_pred_comp_of_pos f hn, comp_app, h]

/-- If `f` sends two periodic points `x` and `y` of positive periods to the same point,
then `x = y`. -/
theorem eq_of_apply_eq (hx : IsPeriodicPt f m x) (hy : IsPeriodicPt f n y) (hm : 0 < m) (hn : 0 < n) (h : f x = f y) :
    x = y :=
  (hx.mul_const n).eq_of_apply_eq_same (hy.const_mul m) (mul_pos hm hn) h

end IsPeriodicPt

/-- The set of periodic points of a given (possibly non-minimal) period. -/
def PtsOfPeriod (f : α → α) (n : ℕ) : Set α :=
  { x : α | IsPeriodicPt f n x }

@[simp]
theorem mem_pts_of_period : x ∈ PtsOfPeriod f n ↔ IsPeriodicPt f n x :=
  Iff.rfl

theorem Semiconj.maps_to_pts_of_period {g : α → β} (h : Semiconj g fa fb) (n : ℕ) :
    MapsTo g (PtsOfPeriod fa n) (PtsOfPeriod fb n) :=
  (h.iterate_right n).maps_to_fixed_pts

theorem bij_on_pts_of_period (f : α → α) {n : ℕ} (hn : 0 < n) : BijOn f (PtsOfPeriod f n) (PtsOfPeriod f n) :=
  ⟨(Commute.refl f).maps_to_pts_of_period n, fun x hx y hy hxy => hx.eq_of_apply_eq_same hy hn hxy, fun x hx =>
    ⟨(f^[n.pred]) x, hx.apply_iterate _, by
      rw [← comp_app f, comp_iterate_pred_of_pos f hn, hx.eq]⟩⟩

theorem directed_pts_of_period_pnat (f : α → α) : Directed (· ⊆ ·) fun n : ℕ+ => PtsOfPeriod f n := fun m n =>
  ⟨m * n, fun x hx => hx.mul_const n, fun x hx => hx.const_mul m⟩

/-- The set of periodic points of a map `f : α → α`. -/
def PeriodicPts (f : α → α) : Set α :=
  { x : α | ∃ n > 0, IsPeriodicPt f n x }

theorem mk_mem_periodic_pts (hn : 0 < n) (hx : IsPeriodicPt f n x) : x ∈ PeriodicPts f :=
  ⟨n, hn, hx⟩

theorem mem_periodic_pts : x ∈ PeriodicPts f ↔ ∃ n > 0, IsPeriodicPt f n x :=
  Iff.rfl

theorem is_periodic_pt_of_mem_periodic_pts_of_is_periodic_pt_iterate (hx : x ∈ PeriodicPts f)
    (hm : IsPeriodicPt f m ((f^[n]) x)) : IsPeriodicPt f m x := by
  rcases hx with ⟨r, hr, hr'⟩
  convert (hm.apply_iterate ((n / r + 1) * r - n)).Eq
  suffices n ≤ (n / r + 1) * r by
    rw [← iterate_add_apply, Nat.sub_add_cancelₓ this, iterate_mul, (hr'.iterate _).Eq]
  rw [add_mulₓ, one_mulₓ]
  exact (Nat.lt_div_mul_add hr).le

variable (f)

theorem bUnion_pts_of_period : (⋃ n > 0, PtsOfPeriod f n) = PeriodicPts f :=
  Set.ext fun x => by
    simp [← mem_periodic_pts]

theorem Union_pnat_pts_of_period : (⋃ n : ℕ+, PtsOfPeriod f n) = PeriodicPts f :=
  supr_subtype.trans <| bUnion_pts_of_period f

theorem bij_on_periodic_pts : BijOn f (PeriodicPts f) (PeriodicPts f) :=
  Union_pnat_pts_of_period f ▸
    bij_on_Union_of_directed (directed_pts_of_period_pnat f) fun i => bij_on_pts_of_period f i.Pos

variable {f}

theorem Semiconj.maps_to_periodic_pts {g : α → β} (h : Semiconj g fa fb) : MapsTo g (PeriodicPts fa) (PeriodicPts fb) :=
  fun x ⟨n, hn, hx⟩ => ⟨n, hn, hx.map h⟩

open Classical

noncomputable section

/-- Minimal period of a point `x` under an endomorphism `f`. If `x` is not a periodic point of `f`,
then `minimal_period f x = 0`. -/
def minimalPeriod (f : α → α) (x : α) :=
  if h : x ∈ PeriodicPts f then Nat.findₓ h else 0

theorem is_periodic_pt_minimal_period (f : α → α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x := by
  delta' minimal_period
  split_ifs with hx
  · exact (Nat.find_specₓ hx).snd
    
  · exact is_periodic_pt_zero f x
    

@[simp]
theorem iterate_minimal_period : (f^[minimalPeriod f x]) x = x :=
  is_periodic_pt_minimal_period f x

@[simp]
theorem iterate_add_minimal_period_eq : (f^[n + minimalPeriod f x]) x = (f^[n]) x := by
  rw [iterate_add_apply]
  congr
  exact is_periodic_pt_minimal_period f x

@[simp]
theorem iterate_mod_minimal_period_eq : (f^[n % minimalPeriod f x]) x = (f^[n]) x :=
  (is_periodic_pt_minimal_period f x).iterate_mod_apply n

theorem minimal_period_pos_of_mem_periodic_pts (hx : x ∈ PeriodicPts f) : 0 < minimalPeriod f x := by
  simp only [← minimal_period, ← dif_pos hx, ← (Nat.find_specₓ hx).fst.lt]

theorem minimal_period_eq_zero_of_nmem_periodic_pts (hx : x ∉ PeriodicPts f) : minimalPeriod f x = 0 := by
  simp only [← minimal_period, ← dif_neg hx]

theorem IsPeriodicPt.minimal_period_pos (hn : 0 < n) (hx : IsPeriodicPt f n x) : 0 < minimalPeriod f x :=
  minimal_period_pos_of_mem_periodic_pts <| mk_mem_periodic_pts hn hx

theorem minimal_period_pos_iff_mem_periodic_pts : 0 < minimalPeriod f x ↔ x ∈ PeriodicPts f :=
  ⟨not_imp_not.1 fun h => by
      simp only [← minimal_period, ← dif_neg h, ← lt_irreflₓ 0, ← not_false_iff],
    minimal_period_pos_of_mem_periodic_pts⟩

theorem minimal_period_eq_zero_iff_nmem_periodic_pts : minimalPeriod f x = 0 ↔ x ∉ PeriodicPts f := by
  rw [← minimal_period_pos_iff_mem_periodic_pts, not_ltₓ, nonpos_iff_eq_zero]

theorem IsPeriodicPt.minimal_period_le (hn : 0 < n) (hx : IsPeriodicPt f n x) : minimalPeriod f x ≤ n := by
  rw [minimal_period, dif_pos (mk_mem_periodic_pts hn hx)]
  exact Nat.find_min'ₓ (mk_mem_periodic_pts hn hx) ⟨hn, hx⟩

theorem minimal_period_apply_iterate (hx : x ∈ PeriodicPts f) (n : ℕ) :
    minimalPeriod f ((f^[n]) x) = minimalPeriod f x := by
  apply
    (is_periodic_pt.minimal_period_le (minimal_period_pos_of_mem_periodic_pts hx) _).antisymm
      ((is_periodic_pt_of_mem_periodic_pts_of_is_periodic_pt_iterate hx
            (is_periodic_pt_minimal_period f _)).minimal_period_le
        (minimal_period_pos_of_mem_periodic_pts _))
  · exact (is_periodic_pt_minimal_period f x).apply_iterate n
    
  · rcases hx with ⟨m, hm, hx⟩
    exact ⟨m, hm, hx.apply_iterate n⟩
    

theorem minimal_period_apply (hx : x ∈ PeriodicPts f) : minimalPeriod f (f x) = minimalPeriod f x :=
  minimal_period_apply_iterate hx 1

theorem le_of_lt_minimal_period_of_iterate_eq {m n : ℕ} (hm : m < minimalPeriod f x) (hmn : (f^[m]) x = (f^[n]) x) :
    m ≤ n := by
  by_contra' hmn'
  rw [← Nat.add_sub_of_leₓ hmn'.le, add_commₓ, iterate_add_apply] at hmn
  exact
    ((is_periodic_pt.minimal_period_le (tsub_pos_of_lt hmn')
              (is_periodic_pt_of_mem_periodic_pts_of_is_periodic_pt_iterate
                (minimal_period_pos_iff_mem_periodic_pts.1 ((zero_le m).trans_lt hm)) hmn)).trans
          (Nat.sub_leₓ m n)).not_lt
      hm

theorem eq_of_lt_minimal_period_of_iterate_eq {m n : ℕ} (hm : m < minimalPeriod f x) (hn : n < minimalPeriod f x)
    (hmn : (f^[m]) x = (f^[n]) x) : m = n :=
  (le_of_lt_minimal_period_of_iterate_eq hm hmn).antisymm (le_of_lt_minimal_period_of_iterate_eq hn hmn.symm)

theorem eq_iff_lt_minimal_period_of_iterate_eq {m n : ℕ} (hm : m < minimalPeriod f x) (hn : n < minimalPeriod f x) :
    (f^[m]) x = (f^[n]) x ↔ m = n :=
  ⟨eq_of_lt_minimal_period_of_iterate_eq hm hn, congr_arg _⟩

theorem minimal_period_id : minimalPeriod id x = 1 :=
  ((is_periodic_id _ _).minimal_period_le Nat.one_posₓ).antisymm
    (Nat.succ_le_of_ltₓ ((is_periodic_id _ _).minimal_period_pos Nat.one_posₓ))

theorem is_fixed_point_iff_minimal_period_eq_one : minimalPeriod f x = 1 ↔ IsFixedPt f x := by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [← iterate_one f]
    refine' Function.IsPeriodicPt.is_fixed_pt _
    rw [← h]
    exact is_periodic_pt_minimal_period f x
    
  · exact
      ((h.is_periodic_pt 1).minimal_period_le Nat.one_posₓ).antisymm
        (Nat.succ_le_of_ltₓ ((h.is_periodic_pt 1).minimal_period_pos Nat.one_posₓ))
    

theorem IsPeriodicPt.eq_zero_of_lt_minimal_period (hx : IsPeriodicPt f n x) (hn : n < minimalPeriod f x) : n = 0 :=
  Eq.symm <| (eq_or_lt_of_le <| n.zero_le).resolve_right fun hn0 => not_ltₓ.2 (hx.minimal_period_le hn0) hn

theorem not_is_periodic_pt_of_pos_of_lt_minimal_period :
    ∀ {n : ℕ} n0 : n ≠ 0 hn : n < minimalPeriod f x, ¬IsPeriodicPt f n x
  | 0, n0, _ => (n0 rfl).elim
  | n + 1, _, hn => fun hp => Nat.succ_ne_zero _ (hp.eq_zero_of_lt_minimal_period hn)

theorem IsPeriodicPt.minimal_period_dvd (hx : IsPeriodicPt f n x) : minimalPeriod f x ∣ n :=
  ((eq_or_lt_of_le <| n.zero_le).elim fun hn0 => hn0 ▸ dvd_zero _) fun hn0 =>
    Nat.dvd_iff_mod_eq_zeroₓ.2 <|
      (hx.mod <| is_periodic_pt_minimal_period f x).eq_zero_of_lt_minimal_period <|
        Nat.mod_ltₓ _ <| hx.minimal_period_pos hn0

theorem is_periodic_pt_iff_minimal_period_dvd : IsPeriodicPt f n x ↔ minimalPeriod f x ∣ n :=
  ⟨IsPeriodicPt.minimal_period_dvd, fun h => (is_periodic_pt_minimal_period f x).trans_dvd h⟩

open Nat

theorem minimal_period_eq_minimal_period_iff {g : β → β} {y : β} :
    minimalPeriod f x = minimalPeriod g y ↔ ∀ n, IsPeriodicPt f n x ↔ IsPeriodicPt g n y := by
  simp_rw [is_periodic_pt_iff_minimal_period_dvd, dvd_right_iff_eq]

theorem minimal_period_eq_prime {p : ℕ} [hp : Fact p.Prime] (hper : IsPeriodicPt f p x) (hfix : ¬IsFixedPt f x) :
    minimalPeriod f x = p :=
  (hp.out.eq_one_or_self_of_dvd _ hper.minimal_period_dvd).resolve_left
    (mt is_fixed_point_iff_minimal_period_eq_one.1 hfix)

theorem minimal_period_eq_prime_pow {p k : ℕ} [hp : Fact p.Prime] (hk : ¬IsPeriodicPt f (p ^ k) x)
    (hk1 : IsPeriodicPt f (p ^ (k + 1)) x) : minimalPeriod f x = p ^ (k + 1) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow hp.out <;> rwa [← is_periodic_pt_iff_minimal_period_dvd]

theorem Commute.minimal_period_of_comp_dvd_lcm {g : α → α} (h : Function.Commute f g) :
    minimalPeriod (f ∘ g) x ∣ Nat.lcmₓ (minimalPeriod f x) (minimalPeriod g x) := by
  rw [← is_periodic_pt_iff_minimal_period_dvd]
  exact (is_periodic_pt_minimal_period f x).comp_lcm h (is_periodic_pt_minimal_period g x)

theorem Commute.minimal_period_of_comp_dvd_mul {g : α → α} (h : Function.Commute f g) :
    minimalPeriod (f ∘ g) x ∣ minimalPeriod f x * minimalPeriod g x :=
  dvd_trans h.minimal_period_of_comp_dvd_lcm (lcm_dvd_mul _ _)

theorem Commute.minimal_period_of_comp_eq_mul_of_coprime {g : α → α} (h : Function.Commute f g)
    (hco : Coprime (minimalPeriod f x) (minimalPeriod g x)) :
    minimalPeriod (f ∘ g) x = minimalPeriod f x * minimalPeriod g x := by
  apply dvd_antisymm h.minimal_period_of_comp_dvd_mul
  suffices :
    ∀ {f g : α → α},
      Commute f g → coprime (minimal_period f x) (minimal_period g x) → minimal_period f x ∣ minimal_period (f ∘ g) x
  exact hco.mul_dvd_of_dvd_of_dvd (this h hco) (h.comp_eq.symm ▸ this h.symm hco.symm)
  clear hco h f g
  intro f g h hco
  refine' hco.dvd_of_dvd_mul_left (is_periodic_pt.left_of_comp h _ _).minimal_period_dvd
  · exact (is_periodic_pt_minimal_period _ _).const_mul _
    
  · exact (is_periodic_pt_minimal_period _ _).mul_const _
    

private theorem minimal_period_iterate_eq_div_gcd_aux (h : 0 < gcdₓ (minimalPeriod f x) n) :
    minimalPeriod (f^[n]) x = minimalPeriod f x / Nat.gcdₓ (minimalPeriod f x) n := by
  apply Nat.dvd_antisymm
  · apply is_periodic_pt.minimal_period_dvd
    rw [is_periodic_pt, is_fixed_pt, ← iterate_mul, ← Nat.mul_div_assocₓ _ (gcd_dvd_left _ _), mul_comm,
      Nat.mul_div_assocₓ _ (gcd_dvd_right _ _), mul_comm, iterate_mul]
    exact (is_periodic_pt_minimal_period f x).iterate _
    
  · apply coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd h)
    apply dvd_of_mul_dvd_mul_right h
    rw [Nat.div_mul_cancelₓ (gcd_dvd_left _ _), mul_assoc, Nat.div_mul_cancelₓ (gcd_dvd_right _ _), mul_comm]
    apply is_periodic_pt.minimal_period_dvd
    rw [is_periodic_pt, is_fixed_pt, iterate_mul]
    exact is_periodic_pt_minimal_period _ _
    

theorem minimal_period_iterate_eq_div_gcd (h : n ≠ 0) :
    minimalPeriod (f^[n]) x = minimalPeriod f x / Nat.gcdₓ (minimalPeriod f x) n :=
  minimal_period_iterate_eq_div_gcd_aux <| gcd_pos_of_pos_rightₓ _ (Nat.pos_of_ne_zeroₓ h)

theorem minimal_period_iterate_eq_div_gcd' (h : x ∈ PeriodicPts f) :
    minimalPeriod (f^[n]) x = minimalPeriod f x / Nat.gcdₓ (minimalPeriod f x) n :=
  minimal_period_iterate_eq_div_gcd_aux <| gcd_pos_of_pos_leftₓ n (minimal_period_pos_iff_mem_periodic_pts.mpr h)

/-- The orbit of a periodic point `x` of `f` is the cycle `[x, f x, f (f x), ...]`. Its length is
the minimal period of `x`.

If `x` is not a periodic point, then this is the empty (aka nil) cycle. -/
def periodicOrbit (f : α → α) (x : α) : Cycle α :=
  (List.range (minimalPeriod f x)).map fun n => (f^[n]) x

/-- The definition of a periodic orbit, in terms of `list.map`. -/
theorem periodic_orbit_def (f : α → α) (x : α) :
    periodicOrbit f x = (List.range (minimalPeriod f x)).map fun n => (f^[n]) x :=
  rfl

/-- The definition of a periodic orbit, in terms of `cycle.map`. -/
theorem periodic_orbit_eq_cycle_map (f : α → α) (x : α) :
    periodicOrbit f x = (List.range (minimalPeriod f x) : Cycle ℕ).map fun n => (f^[n]) x :=
  rfl

@[simp]
theorem periodic_orbit_length : (periodicOrbit f x).length = minimalPeriod f x := by
  rw [periodic_orbit, Cycle.length_coe, List.length_mapₓ, List.length_range]

@[simp]
theorem periodic_orbit_eq_nil_iff_not_periodic_pt : periodicOrbit f x = Cycle.nil ↔ x ∉ PeriodicPts f := by
  simp [← periodic_orbit]
  exact minimal_period_eq_zero_iff_nmem_periodic_pts

theorem periodic_orbit_eq_nil_of_not_periodic_pt (h : x ∉ PeriodicPts f) : periodicOrbit f x = Cycle.nil :=
  periodic_orbit_eq_nil_iff_not_periodic_pt.2 h

@[simp]
theorem mem_periodic_orbit_iff (hx : x ∈ PeriodicPts f) : y ∈ periodicOrbit f x ↔ ∃ n, (f^[n]) x = y := by
  simp only [← periodic_orbit, ← Cycle.mem_coe_iff, ← List.mem_mapₓ, ← List.mem_range]
  use fun ⟨a, ha, ha'⟩ => ⟨a, ha'⟩
  rintro ⟨n, rfl⟩
  use n % minimal_period f x, mod_lt _ (minimal_period_pos_of_mem_periodic_pts hx)
  rw [iterate_mod_minimal_period_eq]

@[simp]
theorem iterate_mem_periodic_orbit (hx : x ∈ PeriodicPts f) (n : ℕ) : (f^[n]) x ∈ periodicOrbit f x :=
  (mem_periodic_orbit_iff hx).2 ⟨n, rfl⟩

@[simp]
theorem self_mem_periodic_orbit (hx : x ∈ PeriodicPts f) : x ∈ periodicOrbit f x :=
  iterate_mem_periodic_orbit hx 0

theorem nodup_periodic_orbit : (periodicOrbit f x).Nodup := by
  rw [periodic_orbit, Cycle.nodup_coe_iff, List.nodup_map_iff_inj_on (List.nodup_range _)]
  intro m hm n hn hmn
  rw [List.mem_range] at hm hn
  rwa [eq_iff_lt_minimal_period_of_iterate_eq hm hn] at hmn

theorem periodic_orbit_apply_iterate_eq (hx : x ∈ PeriodicPts f) (n : ℕ) :
    periodicOrbit f ((f^[n]) x) = periodicOrbit f x :=
  Eq.symm <|
    Cycle.coe_eq_coe.2 <|
      ⟨n, by
        apply List.ext_le _ fun m _ _ => _
        · simp [← minimal_period_apply_iterate hx]
          
        · rw [List.nth_le_rotate _ n m]
          simp [← iterate_add_apply]
          ⟩

theorem periodic_orbit_apply_eq (hx : x ∈ PeriodicPts f) : periodicOrbit f (f x) = periodicOrbit f x :=
  periodic_orbit_apply_iterate_eq hx 1

theorem periodic_orbit_chain (r : α → α → Prop) {f : α → α} {x : α} :
    (periodicOrbit f x).Chain r ↔ ∀, ∀ n < minimalPeriod f x, ∀, r ((f^[n]) x) ((f^[n + 1]) x) := by
  by_cases' hx : x ∈ periodic_pts f
  · have hx' := minimal_period_pos_of_mem_periodic_pts hx
    have hM := Nat.sub_add_cancelₓ (succ_le_iff.2 hx')
    rw [periodic_orbit, ← Cycle.map_coe, Cycle.chain_map, ← hM, Cycle.chain_range_succ]
    refine' ⟨_, fun H => ⟨_, fun m hm => H _ (hm.trans (Nat.lt_succ_selfₓ _))⟩⟩
    · rintro ⟨hr, H⟩ n hn
      cases' eq_or_lt_of_le (lt_succ_iff.1 hn) with hM' hM'
      · rwa [hM', hM, iterate_minimal_period]
        
      · exact H _ hM'
        
      
    · rw [iterate_zero_apply]
      nth_rw 2[← @iterate_minimal_period α f x]
      nth_rw 1[← hM]
      exact H _ (Nat.lt_succ_selfₓ _)
      
    
  · rw [periodic_orbit_eq_nil_of_not_periodic_pt hx, minimal_period_eq_zero_of_nmem_periodic_pts hx]
    simp
    

theorem periodic_orbit_chain' (r : α → α → Prop) {f : α → α} {x : α} (hx : x ∈ PeriodicPts f) :
    (periodicOrbit f x).Chain r ↔ ∀ n, r ((f^[n]) x) ((f^[n + 1]) x) := by
  rw [periodic_orbit_chain r]
  refine' ⟨fun H n => _, fun H n _ => H n⟩
  rw [iterate_succ_apply, ← iterate_mod_minimal_period_eq]
  nth_rw 1[← iterate_mod_minimal_period_eq]
  rw [← iterate_succ_apply, minimal_period_apply hx]
  exact H _ (mod_lt _ (minimal_period_pos_of_mem_periodic_pts hx))

end Function

namespace MulAction

open Function

variable {α β : Type _} [Groupₓ α] [MulAction α β] {a : α} {b : β}

@[to_additive]
theorem pow_smul_eq_iff_minimal_period_dvd {n : ℕ} : a ^ n • b = b ↔ Function.minimalPeriod ((· • ·) a) b ∣ n := by
  rw [← is_periodic_pt_iff_minimal_period_dvd, is_periodic_pt, is_fixed_pt, smul_iterate]

@[to_additive]
theorem zpow_smul_eq_iff_minimal_period_dvd {n : ℤ} : a ^ n • b = b ↔ (Function.minimalPeriod ((· • ·) a) b : ℤ) ∣ n :=
  by
  cases n
  · rw [Int.of_nat_eq_coe, zpow_coe_nat, Int.coe_nat_dvd, pow_smul_eq_iff_minimal_period_dvd]
    
  · rw [Int.neg_succ_of_nat_coe, zpow_neg, zpow_coe_nat, inv_smul_eq_iff, eq_comm, dvd_neg, Int.coe_nat_dvd,
      pow_smul_eq_iff_minimal_period_dvd]
    

variable (a b)

@[simp, to_additive]
theorem pow_smul_mod_minimal_period (n : ℕ) : a ^ (n % Function.minimalPeriod ((· • ·) a) b) • b = a ^ n • b := by
  conv_rhs =>
    rw [← Nat.mod_add_divₓ n (minimal_period ((· • ·) a) b), pow_addₓ, mul_smul,
      pow_smul_eq_iff_minimal_period_dvd.mpr (dvd_mul_right _ _)]

@[simp, to_additive]
theorem zpow_smul_mod_minimal_period (n : ℤ) : a ^ (n % (Function.minimalPeriod ((· • ·) a) b : ℤ)) • b = a ^ n • b :=
  by
  conv_rhs =>
    rw [← Int.mod_add_div n (minimal_period ((· • ·) a) b), zpow_add, mul_smul,
      zpow_smul_eq_iff_minimal_period_dvd.mpr (dvd_mul_right _ _)]

end MulAction

