/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Huỳnh Trần Khanh, Stuart Presnell
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Finset.Sym

/-!
# Stars and bars

In this file, we prove (in `sym.card_sym_eq_multichoose`) that the function `multichoose n k`
defined in `data/nat/choose/basic` counts the number of multisets of cardinality `k` over an
alphabet of cardinality `n`. In conjunction with `nat.multichoose_eq` proved in
`data/nat/choose/basic`, which shows that `multichoose n k = choose (n + k - 1) k`,
this is central to the "stars and bars" technique in combinatorics, where we switch between
counting multisets of size `k` over an alphabet of size `n` to counting strings of `k` elements
("stars") separated by `n-1` dividers ("bars").

## Informal statement

Many problems in mathematics are of the form of (or can be reduced to) putting `k` indistinguishable
objects into `n` distinguishable boxes; for example, the problem of finding natural numbers
`x1, ..., xn` whose sum is `k`. This is equivalent to forming a multiset of cardinality `k` from
an alphabet of cardinality `n` -- for each box `i ∈ [1, n]` the multiset contains as many copies
of `i` as there are items in the `i`th box.

The "stars and bars" technique arises from another way of presenting the same problem. Instead of
putting `k` items into `n` boxes, we take a row of `k` items (the "stars") and separate them by
inserting `n-1` dividers (the "bars").  For example, the pattern `*|||**|*|` exhibits 4 items
distributed into 6 boxes -- note that any box, including the first and last, may be empty.
Such arrangements of `k` stars and `n-1` bars are in 1-1 correspondence with multisets of size `k`
over an alphabet of size `n`, and are counted by `choose (n + k - 1) k`.

Note that this problem is one component of Gian-Carlo Rota's "Twelvefold Way"
https://en.wikipedia.org/wiki/Twelvefold_way

## Formal statement

Here we generalise the alphabet to an arbitrary fintype `α`, and we use `sym α k` as the type of
multisets of size `k` over `α`. Thus the statement that these are counted by `multichoose` is:
`sym.card_sym_eq_multichoose : card (sym α k) = multichoose (card α) k`
while the "stars and bars" technique gives
`sym.card_sym_eq_choose : card (sym α k) = choose (card α + k - 1) k`


## Tags

stars and bars, multichoose
-/


open Finset Fintype Function Sum Nat

variable {α β : Type _}

namespace Sym

section Sym

variable (α) (n : ℕ)

/-- Over `fin n+1`, the multisets of size `k+1` containing `0` are equivalent to those of size `k`,
as demonstrated by respectively erasing or appending `0`.
-/
protected def e1 {n k : ℕ} : { s : Sym (Finₓ n.succ) k.succ // ↑0 ∈ s } ≃ Sym (Finₓ n.succ) k where
  toFun := fun s => s.1.erase 0 s.2
  invFun := fun s => ⟨cons 0 s, mem_cons_self 0 s⟩
  left_inv := fun s => by
    simp
  right_inv := fun s => by
    simp

/-- The multisets of size `k` over `fin n+2` not containing `0`
are equivalent to those of size `k` over `fin n+1`,
as demonstrated by respectively decrementing or incrementing every element of the multiset.
-/
protected def e2 {n k : ℕ} : { s : Sym (Finₓ n.succ.succ) k // ↑0 ∉ s } ≃ Sym (Finₓ n.succ) k where
  toFun := fun s => map (Finₓ.predAbove 0) s.1
  invFun := fun s =>
    ⟨map (Finₓ.succAbove 0) s, (mt mem_map.1) (not_exists.2 fun t => not_and.2 fun _ => Finₓ.succ_above_ne _ t)⟩
  left_inv := fun s => by
    obtain ⟨s, hs⟩ := s
    simp only [← Finₓ.zero_succ_above, ← map_map, ← comp_app]
    nth_rw_rhs 0[← map_id' s]
    refine' Sym.map_congr fun v hv => _
    simp [← Finₓ.pred_above_zero (ne_of_mem_of_not_mem hv hs)]
  right_inv := fun s => by
    simp only [← Finₓ.zero_succ_above, ← map_map, ← comp_app]
    nth_rw_rhs 0[← map_id' s]
    refine' Sym.map_congr fun v hv => _
    rw [← Finₓ.zero_succ_above v, ← Finₓ.cast_succ_zero, Finₓ.pred_above_succ_above 0 v]

theorem card_sym_fin_eq_multichoose (n k : ℕ) : card (Sym (Finₓ n) k) = multichoose n k := by
  apply @pincer_recursion fun n k => card (Sym (Finₓ n) k) = multichoose n k
  · simp
    
  · intro b
    induction' b with b IHb
    · simp
      
    rw [multichoose_zero_succ, card_eq_zero_iff]
    infer_instance
    
  · intro x y h1 h2
    rw [multichoose_succ_succ, ← h1, ← h2, add_commₓ]
    cases x
    · simp only [← card_eq_zero_iff, ← Nat.nat_zero_eq_zero, ← card_unique, ← self_eq_add_rightₓ]
      infer_instance
      
    rw [← card_sum]
    refine' Fintype.card_congr (Equivₓ.symm _)
    apply (Equivₓ.sumCongr sym.E1.symm sym.E2.symm).trans
    apply Equivₓ.sumCompl
    

/-- For any fintype `α` of cardinality `n`, `card (sym α k) = multichoose (card α) k` -/
theorem card_sym_eq_multichoose (α : Type _) (k : ℕ) [Fintype α] [Fintype (Sym α k)] :
    card (Sym α k) = multichoose (card α) k := by
  rw [← card_sym_fin_eq_multichoose]
  exact card_congr (equiv_congr (equiv_fin α))

/-- The *stars and bars* lemma: the cardinality of `sym α k` is equal to
`nat.choose (card α + k - 1) k`. -/
theorem card_sym_eq_choose {α : Type _} [Fintype α] (k : ℕ) [Fintype (Sym α k)] :
    card (Sym α k) = (card α + k - 1).choose k := by
  rw [card_sym_eq_multichoose, Nat.multichoose_eq]

end Sym

end Sym

namespace Sym2

variable [DecidableEq α]

/-- The `diag` of `s : finset α` is sent on a finset of `sym2 α` of card `s.card`. -/
theorem card_image_diag (s : Finset α) : (s.diag.Image Quotientₓ.mk).card = s.card := by
  rw [card_image_of_inj_on, diag_card]
  rintro ⟨x₀, x₁⟩ hx _ _ h
  cases Quotientₓ.eq.1 h
  · rfl
    
  · simp only [← mem_coe, ← mem_diag] at hx
    rw [hx.2]
    

theorem two_mul_card_image_off_diag (s : Finset α) : 2 * (s.offDiag.Image Quotientₓ.mk).card = s.offDiag.card := by
  rw
    [card_eq_sum_card_fiberwise
      (fun x => mem_image_of_mem _ : ∀, ∀ x ∈ s.off_diag, ∀, Quotientₓ.mk x ∈ s.off_diag.image Quotientₓ.mk),
    sum_const_nat (Quotientₓ.ind _), mul_comm]
  rintro ⟨x, y⟩ hxy
  simp_rw [mem_image, exists_prop, mem_off_diag, Quotientₓ.eq] at hxy
  obtain ⟨a, ⟨ha₁, ha₂, ha⟩, h⟩ := hxy
  obtain ⟨hx, hy, hxy⟩ : x ∈ s ∧ y ∈ s ∧ x ≠ y := by
    cases h <;> have := ha.symm <;> exact ⟨‹_›, ‹_›, ‹_›⟩
  have hxy' : y ≠ x := hxy.symm
  have : (s.off_diag.filter fun z => ⟦z⟧ = ⟦(x, y)⟧) = ({(x, y), (y, x)} : Finset _) := by
    ext ⟨x₁, y₁⟩
    rw [mem_filter, mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.inj_iff, Prod.mk.inj_iff, and_iff_right_iff_imp]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rw [mem_off_diag] <;> exact ⟨‹_›, ‹_›, ‹_›⟩
  -- hxy' is used here
  rw [this, card_insert_of_not_mem, card_singleton]
  simp only [← not_and, ← Prod.mk.inj_iff, ← mem_singleton]
  exact fun _ => hxy'

/-- The `off_diag` of `s : finset α` is sent on a finset of `sym2 α` of card `s.off_diag.card / 2`.
This is because every element `⟦(x, y)⟧` of `sym2 α` not on the diagonal comes from exactly two
pairs: `(x, y)` and `(y, x)`. -/
theorem card_image_off_diag (s : Finset α) : (s.offDiag.Image Quotientₓ.mk).card = s.card.choose 2 := by
  rw [Nat.choose_two_right, mul_tsub, mul_oneₓ, ← off_diag_card,
    Nat.div_eq_of_eq_mul_rightₓ zero_lt_two (two_mul_card_image_off_diag s).symm]

theorem card_subtype_diag [Fintype α] : card { a : Sym2 α // a.IsDiag } = card α := by
  convert card_image_diag (univ : Finset α)
  rw [Fintype.card_of_subtype, ← filter_image_quotient_mk_is_diag]
  rintro x
  rw [mem_filter, univ_product_univ, mem_image]
  obtain ⟨a, ha⟩ := Quotientₓ.exists_rep x
  exact and_iff_right ⟨a, mem_univ _, ha⟩

theorem card_subtype_not_diag [Fintype α] : card { a : Sym2 α // ¬a.IsDiag } = (card α).choose 2 := by
  convert card_image_off_diag (univ : Finset α)
  rw [Fintype.card_of_subtype, ← filter_image_quotient_mk_not_is_diag]
  rintro x
  rw [mem_filter, univ_product_univ, mem_image]
  obtain ⟨a, ha⟩ := Quotientₓ.exists_rep x
  exact and_iff_right ⟨a, mem_univ _, ha⟩

/-- Finset **stars and bars** for the case `n = 2`. -/
theorem _root_.finset.card_sym2 (s : Finset α) : s.Sym2.card = s.card * (s.card + 1) / 2 := by
  rw [← image_diag_union_image_off_diag, card_union_eq, Sym2.card_image_diag, Sym2.card_image_off_diag,
    Nat.choose_two_right, add_commₓ, ← Nat.triangle_succ, Nat.succ_sub_one, mul_comm]
  rintro m he
  rw [inf_eq_inter, mem_inter, mem_image, mem_image] at he
  obtain ⟨⟨a, ha, rfl⟩, b, hb, hab⟩ := he
  refine' not_is_diag_mk_of_mem_off_diag hb _
  rw [hab]
  exact is_diag_mk_of_mem_diag ha

/-- Type **stars and bars** for the case `n = 2`. -/
protected theorem card [Fintype α] : card (Sym2 α) = card α * (card α + 1) / 2 :=
  Finset.card_sym2 _

end Sym2

