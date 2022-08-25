/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Hom.Equiv
import Mathbin.Algebra.Ring.Opposite
import Mathbin.Data.Finset.Fold
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Set.Pairwise

/-!
# Big operators

In this file we define products and sums indexed by finite sets (specifically, `finset`).

## Notation

We introduce the following notation, localized in `big_operators`.
To enable the notation, use `open_locale big_operators`.

Let `s` be a `finset α`, and `f : α → β` a function.

* `∏ x in s, f x` is notation for `finset.prod s f` (assuming `β` is a `comm_monoid`)
* `∑ x in s, f x` is notation for `finset.sum s f` (assuming `β` is an `add_comm_monoid`)
* `∏ x, f x` is notation for `finset.prod finset.univ f`
  (assuming `α` is a `fintype` and `β` is a `comm_monoid`)
* `∑ x, f x` is notation for `finset.sum finset.univ f`
  (assuming `α` is a `fintype` and `β` is an `add_comm_monoid`)

## Implementation Notes

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

-/


universe u v w

variable {ι : Type _} {β : Type u} {α : Type v} {γ : Type w}

open Finₓ

namespace Finset

/-- `∏ x in s, f x` is the product of `f x`
as `x` ranges over the elements of the finite set `s`.
-/
@[to_additive "`∑ x in s, f x` is the sum of `f x` as `x` ranges over the elements\nof the finite set `s`."]
protected def prod [CommMonoidₓ β] (s : Finset α) (f : α → β) : β :=
  (s.1.map f).Prod

@[simp, to_additive]
theorem prod_mk [CommMonoidₓ β] (s : Multiset α) (hs : s.Nodup) (f : α → β) :
    (⟨s, hs⟩ : Finset α).Prod f = (s.map f).Prod :=
  rfl

@[simp, to_additive]
theorem prod_val [CommMonoidₓ α] (s : Finset α) : s.1.Prod = s.Prod id := by
  rw [Finset.prod, Multiset.map_id]

end Finset

library_note "operator precedence of big operators"/-- There is no established mathematical convention
for the operator precedence of big operators like `∏` and `∑`.
We will have to make a choice.

Online discussions, such as https://math.stackexchange.com/q/185538/30839
seem to suggest that `∏` and `∑` should have the same precedence,
and that this should be somewhere between `*` and `+`.
The latter have precedence levels `70` and `65` respectively,
and we therefore choose the level `67`.

In practice, this means that parentheses should be placed as follows:
```lean
∑ k in K, (a k + b k) = ∑ k in K, a k + ∑ k in K, b k →
  ∏ k in K, a k * b k = (∏ k in K, a k) * (∏ k in K, b k)
```
(Example taken from page 490 of Knuth's *Concrete Mathematics*.)
-/


-- mathport name: «expr∑ , »
localized [BigOperators] notation3"∑ "(...)", "r:(scoped f => Finset.sum Finset.univ f) => r

-- mathport name: «expr∏ , »
localized [BigOperators] notation3"∏ "(...)", "r:(scoped f => Finset.prod Finset.univ f) => r

-- mathport name: «expr∑ in , »
localized [BigOperators] notation3"∑ "(...)" in "s", "r:(scoped f => Finset.sum s f) => r

-- mathport name: «expr∏ in , »
localized [BigOperators] notation3"∏ "(...)" in "s", "r:(scoped f => Finset.prod s f) => r

open BigOperators

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

@[to_additive]
theorem prod_eq_multiset_prod [CommMonoidₓ β] (s : Finset α) (f : α → β) : (∏ x in s, f x) = (s.1.map f).Prod :=
  rfl

@[to_additive]
theorem prod_eq_fold [CommMonoidₓ β] (s : Finset α) (f : α → β) : (∏ x in s, f x) = s.fold (· * ·) 1 f :=
  rfl

@[simp]
theorem sum_multiset_singleton (s : Finset α) : (s.Sum fun x => {x}) = s.val := by
  simp only [sum_eq_multiset_sum, Multiset.sum_map_singleton]

end Finset

@[to_additive]
theorem map_prod [CommMonoidₓ β] [CommMonoidₓ γ] {G : Type _} [MonoidHomClass G β γ] (g : G) (f : α → β)
    (s : Finset α) : g (∏ x in s, f x) = ∏ x in s, g (f x) := by
  simp only [Finset.prod_eq_multiset_prod, map_multiset_prod, Multiset.map_map]

section Deprecated

/-- Deprecated: use `_root_.map_prod` instead. -/
@[to_additive "Deprecated: use `_root_.map_sum` instead."]
protected theorem MonoidHom.map_prod [CommMonoidₓ β] [CommMonoidₓ γ] (g : β →* γ) (f : α → β) (s : Finset α) :
    g (∏ x in s, f x) = ∏ x in s, g (f x) :=
  map_prod g f s

/-- Deprecated: use `_root_.map_prod` instead. -/
@[to_additive "Deprecated: use `_root_.map_sum` instead."]
protected theorem MulEquiv.map_prod [CommMonoidₓ β] [CommMonoidₓ γ] (g : β ≃* γ) (f : α → β) (s : Finset α) :
    g (∏ x in s, f x) = ∏ x in s, g (f x) :=
  map_prod g f s

/-- Deprecated: use `_root_.map_list_prod` instead. -/
protected theorem RingHom.map_list_prod [Semiringₓ β] [Semiringₓ γ] (f : β →+* γ) (l : List β) :
    f l.Prod = (l.map f).Prod :=
  map_list_prod f l

/-- Deprecated: use `_root_.map_list_sum` instead. -/
protected theorem RingHom.map_list_sum [NonAssocSemiringₓ β] [NonAssocSemiringₓ γ] (f : β →+* γ) (l : List β) :
    f l.Sum = (l.map f).Sum :=
  map_list_sum f l

/-- A morphism into the opposite ring acts on the product by acting on the reversed elements.

Deprecated: use `_root_.unop_map_list_prod` instead.
-/
protected theorem RingHom.unop_map_list_prod [Semiringₓ β] [Semiringₓ γ] (f : β →+* γᵐᵒᵖ) (l : List β) :
    MulOpposite.unop (f l.Prod) = (l.map (MulOpposite.unop ∘ f)).reverse.Prod :=
  unop_map_list_prod f l

/-- Deprecated: use `_root_.map_multiset_prod` instead. -/
protected theorem RingHom.map_multiset_prod [CommSemiringₓ β] [CommSemiringₓ γ] (f : β →+* γ) (s : Multiset β) :
    f s.Prod = (s.map f).Prod :=
  map_multiset_prod f s

/-- Deprecated: use `_root_.map_multiset_sum` instead. -/
protected theorem RingHom.map_multiset_sum [NonAssocSemiringₓ β] [NonAssocSemiringₓ γ] (f : β →+* γ) (s : Multiset β) :
    f s.Sum = (s.map f).Sum :=
  map_multiset_sum f s

/-- Deprecated: use `_root_.map_prod` instead. -/
protected theorem RingHom.map_prod [CommSemiringₓ β] [CommSemiringₓ γ] (g : β →+* γ) (f : α → β) (s : Finset α) :
    g (∏ x in s, f x) = ∏ x in s, g (f x) :=
  map_prod g f s

/-- Deprecated: use `_root_.map_sum` instead. -/
protected theorem RingHom.map_sum [NonAssocSemiringₓ β] [NonAssocSemiringₓ γ] (g : β →+* γ) (f : α → β) (s : Finset α) :
    g (∑ x in s, f x) = ∑ x in s, g (f x) :=
  map_sum g f s

end Deprecated

@[to_additive]
theorem MonoidHom.coe_finset_prod [MulOneClassₓ β] [CommMonoidₓ γ] (f : α → β →* γ) (s : Finset α) :
    ⇑(∏ x in s, f x) = ∏ x in s, f x :=
  (MonoidHom.coeFn β γ).map_prod _ _

-- See also `finset.prod_apply`, with the same conclusion
-- but with the weaker hypothesis `f : α → β → γ`.
@[simp, to_additive]
theorem MonoidHom.finset_prod_apply [MulOneClassₓ β] [CommMonoidₓ γ] (f : α → β →* γ) (s : Finset α) (b : β) :
    (∏ x in s, f x) b = ∏ x in s, f x b :=
  (MonoidHom.eval b).map_prod _ _

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

namespace Finset

section CommMonoidₓ

variable [CommMonoidₓ β]

@[simp, to_additive]
theorem prod_empty : (∏ x in ∅, f x) = 1 :=
  rfl

@[to_additive]
theorem prod_of_empty [IsEmpty α] : (∏ i, f i) = 1 := by
  rw [univ_eq_empty, prod_empty]

@[simp, to_additive]
theorem prod_cons (h : a ∉ s) : (∏ x in cons a s h, f x) = f a * ∏ x in s, f x :=
  fold_cons h

@[simp, to_additive]
theorem prod_insert [DecidableEq α] : a ∉ s → (∏ x in insert a s, f x) = f a * ∏ x in s, f x :=
  fold_insert

/-- The product of `f` over `insert a s` is the same as
the product over `s`, as long as `a` is in `s` or `f a = 1`.
-/
@[simp,
  to_additive
      "The sum of `f` over `insert a s` is the same as\nthe sum over `s`, as long as `a` is in `s` or `f a = 0`."]
theorem prod_insert_of_eq_one_if_not_mem [DecidableEq α] (h : a ∉ s → f a = 1) :
    (∏ x in insert a s, f x) = ∏ x in s, f x := by
  by_cases' hm : a ∈ s
  · simp_rw [insert_eq_of_mem hm]
    
  · rw [prod_insert hm, h hm, one_mulₓ]
    

/-- The product of `f` over `insert a s` is the same as the product over `s`, as long as `f a = 1`.
-/
@[simp, to_additive "The sum of `f` over `insert a s` is the same as\nthe sum over `s`, as long as `f a = 0`."]
theorem prod_insert_one [DecidableEq α] (h : f a = 1) : (∏ x in insert a s, f x) = ∏ x in s, f x :=
  prod_insert_of_eq_one_if_not_mem fun _ => h

@[simp, to_additive]
theorem prod_singleton : (∏ x in singleton a, f x) = f a :=
  Eq.trans fold_singleton <| mul_oneₓ _

@[to_additive]
theorem prod_pair [DecidableEq α] {a b : α} (h : a ≠ b) : (∏ x in ({a, b} : Finset α), f x) = f a * f b := by
  rw [prod_insert (not_mem_singleton.2 h), prod_singleton]

@[simp, to_additive]
theorem prod_const_one : (∏ x in s, (1 : β)) = 1 := by
  simp only [Finset.prod, Multiset.map_const, Multiset.prod_repeat, one_pow]

@[simp, to_additive]
theorem prod_image [DecidableEq α] {s : Finset γ} {g : γ → α} :
    (∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) → (∏ x in s.Image g, f x) = ∏ x in s, f (g x) :=
  fold_image

@[simp, to_additive]
theorem prod_map (s : Finset α) (e : α ↪ γ) (f : γ → β) : (∏ x in s.map e, f x) = ∏ x in s, f (e x) := by
  rw [Finset.prod, Finset.map_val, Multiset.map_map] <;> rfl

@[congr, to_additive]
theorem prod_congr (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → s₁.Prod f = s₂.Prod g := by
  rw [h] <;> exact fold_congr

attribute [congr] Finset.sum_congr

@[to_additive]
theorem prod_disj_union (h) : (∏ x in s₁.disjUnion s₂ h, f x) = (∏ x in s₁, f x) * ∏ x in s₂, f x := by
  refine' Eq.trans _ (fold_disj_union h)
  rw [one_mulₓ]
  rfl

@[to_additive]
theorem prod_union_inter [DecidableEq α] :
    ((∏ x in s₁ ∪ s₂, f x) * ∏ x in s₁ ∩ s₂, f x) = (∏ x in s₁, f x) * ∏ x in s₂, f x :=
  fold_union_inter

@[to_additive]
theorem prod_union [DecidableEq α] (h : Disjoint s₁ s₂) : (∏ x in s₁ ∪ s₂, f x) = (∏ x in s₁, f x) * ∏ x in s₂, f x :=
  by
  rw [← prod_union_inter, disjoint_iff_inter_eq_empty.mp h] <;> exact (mul_oneₓ _).symm

@[to_additive]
theorem prod_filter_mul_prod_filter_not (s : Finset α) (p : α → Prop) [DecidablePred p] [DecidablePred fun x => ¬p x]
    (f : α → β) : ((∏ x in s.filter p, f x) * ∏ x in s.filter fun x => ¬p x, f x) = ∏ x in s, f x := by
  haveI := Classical.decEq α
  rw [← prod_union (filter_inter_filter_neg_eq p s).le, filter_union_filter_neg_eq]

section ToList

@[simp, to_additive]
theorem prod_to_list (s : Finset α) (f : α → β) : (s.toList.map f).Prod = s.Prod f := by
  rw [Finset.prod, ← Multiset.coe_prod, ← Multiset.coe_map, Finset.coe_to_list]

end ToList

@[to_additive]
theorem _root_.equiv.perm.prod_comp (σ : Equivₓ.Perm α) (s : Finset α) (f : α → β) (hs : { a | σ a ≠ a } ⊆ s) :
    (∏ x in s, f (σ x)) = ∏ x in s, f x := by
  convert (prod_map _ σ.to_embedding _).symm
  exact (map_perm hs).symm

@[to_additive]
theorem _root_.equiv.perm.prod_comp' (σ : Equivₓ.Perm α) (s : Finset α) (f : α → α → β) (hs : { a | σ a ≠ a } ⊆ s) :
    (∏ x in s, f (σ x) x) = ∏ x in s, f x (σ.symm x) := by
  convert σ.prod_comp s (fun x => f x (σ.symm x)) hs
  ext
  rw [Equivₓ.symm_apply_apply]

end CommMonoidₓ

end Finset

section

open Finset

variable [Fintype α] [DecidableEq α] [CommMonoidₓ β]

@[to_additive]
theorem IsCompl.prod_mul_prod {s t : Finset α} (h : IsCompl s t) (f : α → β) :
    ((∏ i in s, f i) * ∏ i in t, f i) = ∏ i, f i :=
  (Finset.prod_union h.Disjoint).symm.trans <| by
    rw [← Finset.sup_eq_union, h.sup_eq_top] <;> rfl

end

namespace Finset

section CommMonoidₓ

variable [CommMonoidₓ β]

/-- Multiplying the products of a function over `s` and over `sᶜ` gives the whole product.
For a version expressed with subtypes, see `fintype.prod_subtype_mul_prod_subtype`. -/
@[to_additive
      "Adding the sums of a function over `s` and over `sᶜ` gives the whole sum.\nFor a version expressed with subtypes, see `fintype.sum_subtype_add_sum_subtype`. "]
theorem prod_mul_prod_compl [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
    ((∏ i in s, f i) * ∏ i in sᶜ, f i) = ∏ i, f i :=
  IsCompl.prod_mul_prod is_compl_compl f

@[to_additive]
theorem prod_compl_mul_prod [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
    ((∏ i in sᶜ, f i) * ∏ i in s, f i) = ∏ i, f i :=
  (@is_compl_compl _ s _).symm.prod_mul_prod f

@[to_additive]
theorem prod_sdiff [DecidableEq α] (h : s₁ ⊆ s₂) : ((∏ x in s₂ \ s₁, f x) * ∏ x in s₁, f x) = ∏ x in s₂, f x := by
  rw [← prod_union sdiff_disjoint, sdiff_union_of_subset h]

@[simp, to_additive]
theorem prod_sum_elim [DecidableEq (Sum α γ)] (s : Finset α) (t : Finset γ) (f : α → β) (g : γ → β) :
    (∏ x in s.map Function.Embedding.inl ∪ t.map Function.Embedding.inr, Sum.elim f g x) =
      (∏ x in s, f x) * ∏ x in t, g x :=
  by
  rw [prod_union, prod_map, prod_map]
  · simp only [Sum.elim_inl, Function.Embedding.inl_apply, Function.Embedding.inr_apply, Sum.elim_inr]
    
  · simp only [disjoint_left, Finset.mem_map, Finset.mem_map]
    rintro _ ⟨i, hi, rfl⟩ ⟨j, hj, H⟩
    cases H
    

@[simp, to_additive]
theorem prod_on_sum [Fintype α] [Fintype γ] (f : Sum α γ → β) :
    (∏ x : Sum α γ, f x) = (∏ x : α, f (Sum.inl x)) * ∏ x : γ, f (Sum.inr x) := by
  haveI := Classical.decEq (Sum α γ)
  convert prod_sum_elim univ univ (fun x => f (Sum.inl x)) fun x => f (Sum.inr x)
  · ext a
    constructor
    · intro x
      cases a
      · simp only [mem_union, mem_map, mem_univ, Function.Embedding.inl_apply, or_falseₓ, exists_true_left,
          exists_apply_eq_applyₓ, Function.Embedding.inr_apply, exists_false]
        
      · simp only [mem_union, mem_map, mem_univ, Function.Embedding.inl_apply, false_orₓ, exists_true_left,
          exists_false, Function.Embedding.inr_apply, exists_apply_eq_applyₓ]
        
      
    · simp only [mem_univ, implies_true_iff]
      
    
  · simp only [Sum.elim_comp_inl_inr]
    

@[to_additive]
theorem prod_bUnion [DecidableEq α] {s : Finset γ} {t : γ → Finset α} (hs : Set.PairwiseDisjoint (↑s) t) :
    (∏ x in s.bUnion t, f x) = ∏ x in s, ∏ i in t x, f i := by
  haveI := Classical.decEq γ
  induction' s using Finset.induction_on with x s hxs ih hd
  · simp_rw [bUnion_empty, prod_empty]
    
  · simp_rw [coe_insert, Set.pairwise_disjoint_insert, mem_coe] at hs
    have : Disjoint (t x) (Finset.bUnion s t) :=
      (disjoint_bUnion_right _ _ _).mpr fun y hy => (hs.2 y hy) fun H => hxs <| H.substr hy
    rw [bUnion_insert, prod_insert hxs, prod_union this, ih hs.1]
    

/-- Product over a sigma type equals the product of fiberwise products. For rewriting
in the reverse direction, use `finset.prod_sigma'`.  -/
@[to_additive
      "Sum over a sigma type equals the sum of fiberwise sums. For rewriting\nin the reverse direction, use `finset.sum_sigma'`"]
theorem prod_sigma {σ : α → Type _} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : Sigma σ → β) :
    (∏ x in s.Sigma t, f x) = ∏ a in s, ∏ s in t a, f ⟨a, s⟩ := by
  classical <;>
    calc
      (∏ x in s.sigma t, f x) = ∏ x in s.bUnion fun a => (t a).map (Function.Embedding.sigmaMk a), f x := by
        rw [sigma_eq_bUnion]
      _ = ∏ a in s, ∏ x in (t a).map (Function.Embedding.sigmaMk a), f x :=
        prod_bUnion fun a₁ ha a₂ ha₂ h x hx => by
          simp only [inf_eq_inter, mem_inter, mem_map, Function.Embedding.sigma_mk_apply] at hx
          rcases hx with ⟨⟨y, hy, rfl⟩, ⟨z, hz, hz'⟩⟩
          cc
      _ = ∏ a in s, ∏ s in t a, f ⟨a, s⟩ := (prod_congr rfl) fun _ _ => prod_map _ _ _
      

@[to_additive]
theorem prod_sigma' {σ : α → Type _} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : ∀ a, σ a → β) :
    (∏ a in s, ∏ s in t a, f a s) = ∏ x in s.Sigma t, f x.1 x.2 :=
  Eq.symm <| prod_sigma s t fun x => f x.1 x.2

/-- Reorder a product.

  The difference with `prod_bij'` is that the bijection is specified as a surjective injection,
  rather than by an inverse function.
-/
@[to_additive
      "\n  Reorder a sum.\n\n  The difference with `sum_bij'` is that the bijection is specified as a surjective injection,\n  rather than by an inverse function.\n"]
theorem prod_bij {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β} (i : ∀ a ∈ s, γ) (hi : ∀ a ha, i a ha ∈ t)
    (h : ∀ a ha, f a = g (i a ha)) (i_inj : ∀ a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) : (∏ x in s, f x) = ∏ x in t, g x :=
  congr_arg Multiset.prod (Multiset.map_eq_map_of_bij_of_nodup f g s.2 t.2 i hi h i_inj i_surj)

/-- Reorder a product.

  The difference with `prod_bij` is that the bijection is specified with an inverse, rather than
  as a surjective injection.
-/
@[to_additive
      "\n  Reorder a sum.\n\n  The difference with `sum_bij` is that the bijection is specified with an inverse, rather than\n  as a surjective injection.\n"]
theorem prod_bij' {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β} (i : ∀ a ∈ s, γ) (hi : ∀ a ha, i a ha ∈ t)
    (h : ∀ a ha, f a = g (i a ha)) (j : ∀ a ∈ t, α) (hj : ∀ a ha, j a ha ∈ s)
    (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a) (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) :
    (∏ x in s, f x) = ∏ x in t, g x := by
  refine' prod_bij i hi h _ _
  · intro a1 a2 h1 h2 eq
    rw [← left_inv a1 h1, ← left_inv a2 h2]
    cc
    
  · intro b hb
    use j b hb
    use hj b hb
    exact (right_inv b hb).symm
    

@[to_additive]
theorem prod_finset_product (r : Finset (γ × α)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : γ × α, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f : γ × α → β} :
    (∏ p in r, f p) = ∏ c in s, ∏ a in t c, f (c, a) := by
  refine' Eq.trans _ (prod_sigma s t fun p => f (p.1, p.2))
  exact
    prod_bij' (fun p hp => ⟨p.1, p.2⟩) (fun p => mem_sigma.mpr ∘ (h p).mp) (fun p hp => congr_arg f prod.mk.eta.symm)
      (fun p hp => (p.1, p.2)) (fun p => (h (p.1, p.2)).mpr ∘ mem_sigma.mp) (fun p hp => Prod.mk.eta) fun p hp => p.eta

@[to_additive]
theorem prod_finset_product' (r : Finset (γ × α)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : γ × α, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f : γ → α → β} :
    (∏ p in r, f p.1 p.2) = ∏ c in s, ∏ a in t c, f c a :=
  prod_finset_product r s t h

@[to_additive]
theorem prod_finset_product_right (r : Finset (α × γ)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α × γ → β} :
    (∏ p in r, f p) = ∏ c in s, ∏ a in t c, f (a, c) := by
  refine' Eq.trans _ (prod_sigma s t fun p => f (p.2, p.1))
  exact
    prod_bij' (fun p hp => ⟨p.2, p.1⟩) (fun p => mem_sigma.mpr ∘ (h p).mp) (fun p hp => congr_arg f prod.mk.eta.symm)
      (fun p hp => (p.2, p.1)) (fun p => (h (p.2, p.1)).mpr ∘ mem_sigma.mp) (fun p hp => Prod.mk.eta) fun p hp => p.eta

@[to_additive]
theorem prod_finset_product_right' (r : Finset (α × γ)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α → γ → β} :
    (∏ p in r, f p.1 p.2) = ∏ c in s, ∏ a in t c, f a c :=
  prod_finset_product_right r s t h

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:124:4: warning: unsupported: rw with cfg: { occs := occurrences.pos «expr[ ,]»([2]) }
@[to_additive]
theorem prod_fiberwise_of_maps_to [DecidableEq γ] {s : Finset α} {t : Finset γ} {g : α → γ} (h : ∀ x ∈ s, g x ∈ t)
    (f : α → β) : (∏ y in t, ∏ x in s.filter fun x => g x = y, f x) = ∏ x in s, f x := by
  letI := Classical.decEq α
  rw [← bUnion_filter_eq_of_maps_to h]
  refine' (prod_bUnion fun x' hx y' hy hne => _).symm
  rw [Function.onFun, disjoint_filter]
  rintro x hx rfl
  exact hne

@[to_additive]
theorem prod_image' [DecidableEq α] {s : Finset γ} {g : γ → α} (h : γ → β)
    (eq : ∀ c ∈ s, f (g c) = ∏ x in s.filter fun c' => g c' = g c, h x) : (∏ x in s.Image g, f x) = ∏ x in s, h x :=
  calc
    (∏ x in s.Image g, f x) = ∏ x in s.Image g, ∏ x in s.filter fun c' => g c' = x, h x :=
      (prod_congr rfl) fun x hx =>
        let ⟨c, hcs, hc⟩ := mem_image.1 hx
        hc ▸ Eq c hcs
    _ = ∏ x in s, h x := prod_fiberwise_of_maps_to (fun x => mem_image_of_mem g) _
    

@[to_additive]
theorem prod_mul_distrib : (∏ x in s, f x * g x) = (∏ x in s, f x) * ∏ x in s, g x :=
  Eq.trans
    (by
      rw [one_mulₓ] <;> rfl)
    fold_op_distrib

@[to_additive]
theorem prod_product {s : Finset γ} {t : Finset α} {f : γ × α → β} :
    (∏ x in s ×ˢ t, f x) = ∏ x in s, ∏ y in t, f (x, y) :=
  prod_finset_product (s ×ˢ t) s (fun a => t) fun p => mem_product

/-- An uncurried version of `finset.prod_product`. -/
@[to_additive "An uncurried version of `finset.sum_product`"]
theorem prod_product' {s : Finset γ} {t : Finset α} {f : γ → α → β} :
    (∏ x in s ×ˢ t, f x.1 x.2) = ∏ x in s, ∏ y in t, f x y :=
  prod_product

@[to_additive]
theorem prod_product_right {s : Finset γ} {t : Finset α} {f : γ × α → β} :
    (∏ x in s ×ˢ t, f x) = ∏ y in t, ∏ x in s, f (x, y) :=
  prod_finset_product_right (s ×ˢ t) t (fun a => s) fun p => mem_product.trans And.comm

/-- An uncurried version of `finset.prod_product_right`. -/
@[to_additive "An uncurried version of `finset.prod_product_right`"]
theorem prod_product_right' {s : Finset γ} {t : Finset α} {f : γ → α → β} :
    (∏ x in s ×ˢ t, f x.1 x.2) = ∏ y in t, ∏ x in s, f x y :=
  prod_product_right

/-- Generalization of `finset.prod_comm` to the case when the inner `finset`s depend on the outer
variable. -/
@[to_additive "Generalization of `finset.sum_comm` to the case when the inner `finset`s depend on\nthe outer variable."]
theorem prod_comm' {s : Finset γ} {t : γ → Finset α} {t' : Finset α} {s' : α → Finset γ}
    (h : ∀ x y, x ∈ s ∧ y ∈ t x ↔ x ∈ s' y ∧ y ∈ t') {f : γ → α → β} :
    (∏ x in s, ∏ y in t x, f x y) = ∏ y in t', ∏ x in s' y, f x y := by
  classical
  have : ∀ z : γ × α, (z ∈ s.bUnion fun x => (t x).map <| Function.Embedding.sectr x _) ↔ z.1 ∈ s ∧ z.2 ∈ t z.1 := by
    rintro ⟨x, y⟩
    simp
  exact
    (prod_finset_product' _ _ _ this).symm.trans
      ((prod_finset_product_right' _ _ _) fun ⟨x, y⟩ => (this _).trans ((h x y).trans And.comm))

@[to_additive]
theorem prod_comm {s : Finset γ} {t : Finset α} {f : γ → α → β} :
    (∏ x in s, ∏ y in t, f x y) = ∏ y in t, ∏ x in s, f x y :=
  prod_comm' fun _ _ => Iff.rfl

@[to_additive]
theorem prod_hom_rel [CommMonoidₓ γ] {r : β → γ → Prop} {f : α → β} {g : α → γ} {s : Finset α} (h₁ : r 1 1)
    (h₂ : ∀ a b c, r b c → r (f a * b) (g a * c)) : r (∏ x in s, f x) (∏ x in s, g x) := by
  delta' Finset.prod
  apply Multiset.prod_hom_rel <;> assumption

@[to_additive]
theorem prod_eq_one {f : α → β} {s : Finset α} (h : ∀ x ∈ s, f x = 1) : (∏ x in s, f x) = 1 :=
  calc
    (∏ x in s, f x) = ∏ x in s, 1 := Finset.prod_congr rfl h
    _ = 1 := Finset.prod_const_one
    

@[to_additive]
theorem prod_subset_one_on_sdiff [DecidableEq α] (h : s₁ ⊆ s₂) (hg : ∀ x ∈ s₂ \ s₁, g x = 1)
    (hfg : ∀ x ∈ s₁, f x = g x) : (∏ i in s₁, f i) = ∏ i in s₂, g i := by
  rw [← prod_sdiff h, prod_eq_one hg, one_mulₓ]
  exact prod_congr rfl hfg

@[to_additive]
theorem prod_subset (h : s₁ ⊆ s₂) (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 1) : (∏ x in s₁, f x) = ∏ x in s₂, f x :=
  haveI := Classical.decEq α
  prod_subset_one_on_sdiff h
    (by
      simpa)
    fun _ _ => rfl

@[to_additive]
theorem prod_filter_of_ne {p : α → Prop} [DecidablePred p] (hp : ∀ x ∈ s, f x ≠ 1 → p x) :
    (∏ x in s.filter p, f x) = ∏ x in s, f x :=
  (prod_subset (filter_subset _ _)) fun x => by
    classical
    rw [not_imp_comm, mem_filter]
    exact fun h₁ h₂ => ⟨h₁, hp _ h₁ h₂⟩

-- If we use `[decidable_eq β]` here, some rewrites fail because they find a wrong `decidable`
-- instance first; `{∀ x, decidable (f x ≠ 1)}` doesn't work with `rw ← prod_filter_ne_one`
@[to_additive]
theorem prod_filter_ne_one [∀ x, Decidable (f x ≠ 1)] : (∏ x in s.filter fun x => f x ≠ 1, f x) = ∏ x in s, f x :=
  prod_filter_of_ne fun _ _ => id

@[to_additive]
theorem prod_filter (p : α → Prop) [DecidablePred p] (f : α → β) :
    (∏ a in s.filter p, f a) = ∏ a in s, if p a then f a else 1 :=
  calc
    (∏ a in s.filter p, f a) = ∏ a in s.filter p, if p a then f a else 1 :=
      prod_congr rfl fun a h => by
        rw [if_pos (mem_filter.1 h).2]
    _ = ∏ a in s, if p a then f a else 1 := by
      refine' prod_subset (filter_subset _ s) fun x hs h => _
      rw [mem_filter, not_and] at h
      exact if_neg (h hs)
    

@[to_additive]
theorem prod_eq_single_of_mem {s : Finset α} {f : α → β} (a : α) (h : a ∈ s) (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) :
    (∏ x in s, f x) = f a := by
  haveI := Classical.decEq α
  calc
    (∏ x in s, f x) = ∏ x in {a}, f x := by
      refine' (prod_subset _ _).symm
      · intro _ H
        rwa [mem_singleton.1 H]
        
      · simpa only [mem_singleton]
        
    _ = f a := prod_singleton
    

@[to_additive]
theorem prod_eq_single {s : Finset α} {f : α → β} (a : α) (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) (h₁ : a ∉ s → f a = 1) :
    (∏ x in s, f x) = f a :=
  haveI := Classical.decEq α
  Classical.by_cases (fun this : a ∈ s => prod_eq_single_of_mem a this h₀) fun this : a ∉ s =>
    ((prod_congr rfl) fun b hb =>
          h₀ b hb <| by
            rintro rfl <;> cc).trans <|
      prod_const_one.trans (h₁ this).symm

@[to_additive]
theorem prod_eq_mul_of_mem {s : Finset α} {f : α → β} (a b : α) (ha : a ∈ s) (hb : b ∈ s) (hn : a ≠ b)
    (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) : (∏ x in s, f x) = f a * f b := by
  haveI := Classical.decEq α <;> let s' := ({a, b} : Finset α)
  have hu : s' ⊆ s := by
    refine' insert_subset.mpr _
    apply And.intro ha
    apply singleton_subset_iff.mpr hb
  have hf : ∀ c ∈ s, c ∉ s' → f c = 1 := by
    intro c hc hcs
    apply h₀ c hc
    apply not_or_distrib.mp
    intro hab
    apply hcs
    apply mem_insert.mpr
    rw [mem_singleton]
    exact hab
  rw [← prod_subset hu hf]
  exact Finset.prod_pair hn

@[to_additive]
theorem prod_eq_mul {s : Finset α} {f : α → β} (a b : α) (hn : a ≠ b) (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1)
    (ha : a ∉ s → f a = 1) (hb : b ∉ s → f b = 1) : (∏ x in s, f x) = f a * f b := by
  haveI := Classical.decEq α <;> by_cases' h₁ : a ∈ s <;> by_cases' h₂ : b ∈ s
  · exact prod_eq_mul_of_mem a b h₁ h₂ hn h₀
    
  · rw [hb h₂, mul_oneₓ]
    apply prod_eq_single_of_mem a h₁
    exact fun c hc hca => h₀ c hc ⟨hca, ne_of_mem_of_not_mem hc h₂⟩
    
  · rw [ha h₁, one_mulₓ]
    apply prod_eq_single_of_mem b h₂
    exact fun c hc hcb => h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, hcb⟩
    
  · rw [ha h₁, hb h₂, mul_oneₓ]
    exact
      trans (prod_congr rfl fun c hc => h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, ne_of_mem_of_not_mem hc h₂⟩) prod_const_one
    

@[to_additive]
theorem prod_attach {f : α → β} : (∏ x in s.attach, f x) = ∏ x in s, f x :=
  haveI := Classical.decEq α
  calc
    (∏ x in s.attach, f x.val) = ∏ x in s.attach.Image Subtype.val, f x := by
      rw [prod_image] <;> exact fun x _ y _ => Subtype.eq
    _ = _ := by
      rw [attach_image_val]
    

/-- A product over `s.subtype p` equals one over `s.filter p`. -/
@[simp, to_additive "A sum over `s.subtype p` equals one over `s.filter p`."]
theorem prod_subtype_eq_prod_filter (f : α → β) {p : α → Prop} [DecidablePred p] :
    (∏ x in s.Subtype p, f x) = ∏ x in s.filter p, f x := by
  conv_lhs => erw [← prod_map (s.subtype p) (Function.Embedding.subtype _) f]
  exact prod_congr (subtype_map _) fun x hx => rfl

/-- If all elements of a `finset` satisfy the predicate `p`, a product
over `s.subtype p` equals that product over `s`. -/
@[to_additive
      "If all elements of a `finset` satisfy the predicate `p`, a sum\nover `s.subtype p` equals that sum over `s`."]
theorem prod_subtype_of_mem (f : α → β) {p : α → Prop} [DecidablePred p] (h : ∀ x ∈ s, p x) :
    (∏ x in s.Subtype p, f x) = ∏ x in s, f x := by
  simp_rw [prod_subtype_eq_prod_filter, filter_true_of_mem h]

/-- A product of a function over a `finset` in a subtype equals a
product in the main type of a function that agrees with the first
function on that `finset`. -/
@[to_additive
      "A sum of a function over a `finset` in a subtype equals a\nsum in the main type of a function that agrees with the first\nfunction on that `finset`."]
theorem prod_subtype_map_embedding {p : α → Prop} {s : Finset { x // p x }} {f : { x // p x } → β} {g : α → β}
    (h : ∀ x : { x // p x }, x ∈ s → g x = f x) : (∏ x in s.map (Function.Embedding.subtype _), g x) = ∏ x in s, f x :=
  by
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl h

variable (f s)

@[to_additive]
theorem prod_coe_sort_eq_attach (f : s → β) : (∏ i : s, f i) = ∏ i in s.attach, f i :=
  rfl

@[to_additive]
theorem prod_coe_sort : (∏ i : s, f i) = ∏ i in s, f i :=
  prod_attach

@[to_additive]
theorem prod_finset_coe (f : α → β) (s : Finset α) : (∏ i : (s : Set α), f i) = ∏ i in s, f i :=
  prod_coe_sort s f

variable {f s}

@[to_additive]
theorem prod_subtype {p : α → Prop} {F : Fintype (Subtype p)} (s : Finset α) (h : ∀ x, x ∈ s ↔ p x) (f : α → β) :
    (∏ a in s, f a) = ∏ a : Subtype p, f a := by
  have : (· ∈ s) = p := Set.ext h
  subst p
  rw [← prod_coe_sort]
  congr

/-- The product of a function `g` defined only on a set `s` is equal to
the product of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 1` off `s`. -/
@[to_additive
      "The sum of a function `g` defined only on a set `s` is equal to\nthe sum of a function `f` defined everywhere,\nas long as `f` and `g` agree on `s`, and `f = 0` off `s`."]
theorem prod_congr_set {α : Type _} [CommMonoidₓ α] {β : Type _} [Fintype β] (s : Set β) [DecidablePred (· ∈ s)]
    (f : β → α) (g : s → α) (w : ∀ (x : β) (h : x ∈ s), f x = g ⟨x, h⟩) (w' : ∀ x : β, x ∉ s → f x = 1) :
    Finset.univ.Prod f = Finset.univ.Prod g := by
  rw [←
    @Finset.prod_subset _ _ s.to_finset Finset.univ f _
      (by
        simp )]
  · rw [Finset.prod_subtype]
    · apply Finset.prod_congr rfl
      exact fun ⟨x, h⟩ _ => w x h
      
    · simp
      
    
  · rintro x _ h
    exact
      w' x
        (by
          simpa using h)
    

@[to_additive]
theorem prod_apply_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} [DecidablePred fun x => ¬p x]
    (f : ∀ x : α, p x → γ) (g : ∀ x : α, ¬p x → γ) (h : γ → β) :
    (∏ x in s, h (if hx : p x then f x hx else g x hx)) =
      (∏ x in (s.filter p).attach, h (f x.1 (mem_filter.mp x.2).2)) *
        ∏ x in (s.filter fun x => ¬p x).attach, h (g x.1 (mem_filter.mp x.2).2) :=
  calc
    (∏ x in s, h (if hx : p x then f x hx else g x hx)) =
        (∏ x in s.filter p, h (if hx : p x then f x hx else g x hx)) *
          ∏ x in s.filter fun x => ¬p x, h (if hx : p x then f x hx else g x hx) :=
      (prod_filter_mul_prod_filter_not s p _).symm
    _ =
        (∏ x in (s.filter p).attach, h (if hx : p x.1 then f x.1 hx else g x.1 hx)) *
          ∏ x in (s.filter fun x => ¬p x).attach, h (if hx : p x.1 then f x.1 hx else g x.1 hx) :=
      congr_arg2ₓ _ prod_attach.symm prod_attach.symm
    _ =
        (∏ x in (s.filter p).attach, h (f x.1 (mem_filter.mp x.2).2)) *
          ∏ x in (s.filter fun x => ¬p x).attach, h (g x.1 (mem_filter.mp x.2).2) :=
      congr_arg2ₓ _ (prod_congr rfl fun x hx => congr_arg h (dif_pos (mem_filter.mp x.2).2))
        (prod_congr rfl fun x hx => congr_arg h (dif_neg (mem_filter.mp x.2).2))
    

@[to_additive]
theorem prod_apply_ite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (h : γ → β) :
    (∏ x in s, h (if p x then f x else g x)) = (∏ x in s.filter p, h (f x)) * ∏ x in s.filter fun x => ¬p x, h (g x) :=
  trans (prod_apply_dite _ _ _) (congr_arg2ₓ _ (@prod_attach _ _ _ _ (h ∘ f)) (@prod_attach _ _ _ _ (h ∘ g)))

@[to_additive]
theorem prod_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f : ∀ x : α, p x → β) (g : ∀ x : α, ¬p x → β) :
    (∏ x in s, if hx : p x then f x hx else g x hx) =
      (∏ x in (s.filter p).attach, f x.1 (mem_filter.mp x.2).2) *
        ∏ x in (s.filter fun x => ¬p x).attach, g x.1 (mem_filter.mp x.2).2 :=
  by
  simp [prod_apply_dite _ _ fun x => x]

@[to_additive]
theorem prod_ite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f g : α → β) :
    (∏ x in s, if p x then f x else g x) = (∏ x in s.filter p, f x) * ∏ x in s.filter fun x => ¬p x, g x := by
  simp [prod_apply_ite _ _ fun x => x]

@[to_additive]
theorem prod_ite_of_false {p : α → Prop} {hp : DecidablePred p} (f g : α → β) (h : ∀ x ∈ s, ¬p x) :
    (∏ x in s, if p x then f x else g x) = ∏ x in s, g x := by
  rw [prod_ite]
  simp [filter_false_of_mem h, filter_true_of_mem h]

@[to_additive]
theorem prod_ite_of_true {p : α → Prop} {hp : DecidablePred p} (f g : α → β) (h : ∀ x ∈ s, p x) :
    (∏ x in s, if p x then f x else g x) = ∏ x in s, f x := by
  simp_rw [← ite_not (p _)]
  apply prod_ite_of_false
  simpa

@[to_additive]
theorem prod_apply_ite_of_false {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β) (h : ∀ x ∈ s, ¬p x) :
    (∏ x in s, k (if p x then f x else g x)) = ∏ x in s, k (g x) := by
  simp_rw [apply_ite k]
  exact prod_ite_of_false _ _ h

@[to_additive]
theorem prod_apply_ite_of_true {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β) (h : ∀ x ∈ s, p x) :
    (∏ x in s, k (if p x then f x else g x)) = ∏ x in s, k (f x) := by
  simp_rw [apply_ite k]
  exact prod_ite_of_true _ _ h

@[to_additive]
theorem prod_extend_by_one [DecidableEq α] (s : Finset α) (f : α → β) :
    (∏ i in s, if i ∈ s then f i else 1) = ∏ i in s, f i :=
  (prod_congr rfl) fun i hi => if_pos hi

@[simp, to_additive]
theorem prod_dite_eq [DecidableEq α] (s : Finset α) (a : α) (b : ∀ x : α, a = x → β) :
    (∏ x in s, if h : a = x then b x h else 1) = ite (a ∈ s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intros
      rw [dif_neg]
      cc
      
    · cc
      
    
  · rw [Finset.prod_eq_one]
    intros
    rw [dif_neg]
    intro
    cc
    

@[simp, to_additive]
theorem prod_dite_eq' [DecidableEq α] (s : Finset α) (a : α) (b : ∀ x : α, x = a → β) :
    (∏ x in s, if h : x = a then b x h else 1) = ite (a ∈ s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intros
      rw [dif_neg]
      cc
      
    · cc
      
    
  · rw [Finset.prod_eq_one]
    intros
    rw [dif_neg]
    intro
    cc
    

@[simp, to_additive]
theorem prod_ite_eq [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
    (∏ x in s, ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq s a fun x _ => b x

/-- A product taken over a conditional whose condition is an equality test on the index and whose
alternative is `1` has value either the term at that index or `1`.

The difference with `finset.prod_ite_eq` is that the arguments to `eq` are swapped. -/
@[simp,
  to_additive
      "A sum taken over a conditional whose condition is an equality test on the index\nand whose alternative is `0` has value either the term at that index or `0`.\n\nThe difference with `finset.sum_ite_eq` is that the arguments to `eq` are swapped."]
theorem prod_ite_eq' [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
    (∏ x in s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x

@[to_additive]
theorem prod_ite_index (p : Prop) [Decidable p] (s t : Finset α) (f : α → β) :
    (∏ x in if p then s else t, f x) = if p then ∏ x in s, f x else ∏ x in t, f x :=
  apply_ite (fun s => ∏ x in s, f x) _ _ _

@[simp, to_additive]
theorem prod_ite_irrel (p : Prop) [Decidable p] (s : Finset α) (f g : α → β) :
    (∏ x in s, if p then f x else g x) = if p then ∏ x in s, f x else ∏ x in s, g x := by
  split_ifs with h <;> rfl

@[simp, to_additive]
theorem prod_dite_irrel (p : Prop) [Decidable p] (s : Finset α) (f : p → α → β) (g : ¬p → α → β) :
    (∏ x in s, if h : p then f h x else g h x) = if h : p then ∏ x in s, f h x else ∏ x in s, g h x := by
  split_ifs with h <;> rfl

@[simp]
theorem sum_pi_single' {ι M : Type _} [DecidableEq ι] [AddCommMonoidₓ M] (i : ι) (x : M) (s : Finset ι) :
    (∑ j in s, Pi.single i x j) = if i ∈ s then x else 0 :=
  sum_dite_eq' _ _ _

@[simp]
theorem sum_pi_single {ι : Type _} {M : ι → Type _} [DecidableEq ι] [∀ i, AddCommMonoidₓ (M i)] (i : ι) (f : ∀ i, M i)
    (s : Finset ι) : (∑ j in s, Pi.single j (f j) i) = if i ∈ s then f i else 0 :=
  sum_dite_eq _ _ _

@[to_additive]
theorem prod_bij_ne_one {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β} (i : ∀ a ∈ s, f a ≠ 1 → γ)
    (hi : ∀ a h₁ h₂, i a h₁ h₂ ∈ t) (i_inj : ∀ a₁ a₂ h₁₁ h₁₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, g b ≠ 1 → ∃ a h₁ h₂, b = i a h₁ h₂) (h : ∀ a h₁ h₂, f a = g (i a h₁ h₂)) :
    (∏ x in s, f x) = ∏ x in t, g x := by
  classical <;>
    exact
      calc
        (∏ x in s, f x) = ∏ x in s.filter fun x => f x ≠ 1, f x := prod_filter_ne_one.symm
        _ = ∏ x in t.filter fun x => g x ≠ 1, g x :=
          prod_bij (fun a ha => i a (mem_filter.mp ha).1 (mem_filter.mp ha).2)
            (fun a ha =>
              (mem_filter.mp ha).elim fun h₁ h₂ => mem_filter.mpr ⟨hi a h₁ h₂, fun hg => h₂ (hg ▸ h a h₁ h₂)⟩)
            (fun a ha => (mem_filter.mp ha).elim <| h a)
            (fun a₁ a₂ ha₁ ha₂ =>
              (mem_filter.mp ha₁).elim fun ha₁₁ ha₁₂ => (mem_filter.mp ha₂).elim fun ha₂₁ ha₂₂ => i_inj a₁ a₂ _ _ _ _)
            fun b hb =>
            (mem_filter.mp hb).elim fun h₁ h₂ =>
              let ⟨a, ha₁, ha₂, Eq⟩ := i_surj b h₁ h₂
              ⟨a, mem_filter.mpr ⟨ha₁, ha₂⟩, Eq⟩
        _ = ∏ x in t, g x := prod_filter_ne_one
        

@[to_additive]
theorem prod_dite_of_false {p : α → Prop} {hp : DecidablePred p} (h : ∀ x ∈ s, ¬p x) (f : ∀ x : α, p x → β)
    (g : ∀ x : α, ¬p x → β) : (∏ x in s, if hx : p x then f x hx else g x hx) = ∏ x : s, g x.val (h x.val x.property) :=
  prod_bij (fun x hx => ⟨x, hx⟩)
    (fun x hx => by
      simp )
    (fun a ha => by
      dsimp'
      rw [dif_neg])
    (fun a₁ a₂ h₁ h₂ hh => congr_arg coe hh) fun b hb =>
    ⟨b.1, b.2, by
      simp ⟩

@[to_additive]
theorem prod_dite_of_true {p : α → Prop} {hp : DecidablePred p} (h : ∀ x ∈ s, p x) (f : ∀ x : α, p x → β)
    (g : ∀ x : α, ¬p x → β) : (∏ x in s, if hx : p x then f x hx else g x hx) = ∏ x : s, f x.val (h x.val x.property) :=
  prod_bij (fun x hx => ⟨x, hx⟩)
    (fun x hx => by
      simp )
    (fun a ha => by
      dsimp'
      rw [dif_pos])
    (fun a₁ a₂ h₁ h₂ hh => congr_arg coe hh) fun b hb =>
    ⟨b.1, b.2, by
      simp ⟩

@[to_additive]
theorem nonempty_of_prod_ne_one (h : (∏ x in s, f x) ≠ 1) : s.Nonempty :=
  s.eq_empty_or_nonempty.elim (fun H => False.elim <| h <| H.symm ▸ prod_empty) id

@[to_additive]
theorem exists_ne_one_of_prod_ne_one (h : (∏ x in s, f x) ≠ 1) : ∃ a ∈ s, f a ≠ 1 := by
  classical
  rw [← prod_filter_ne_one] at h
  rcases nonempty_of_prod_ne_one h with ⟨x, hx⟩
  exact ⟨x, (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩

@[to_additive]
theorem prod_range_succ_comm (f : ℕ → β) (n : ℕ) : (∏ x in range (n + 1), f x) = f n * ∏ x in range n, f x := by
  rw [range_succ, prod_insert not_mem_range_self]

@[to_additive]
theorem prod_range_succ (f : ℕ → β) (n : ℕ) : (∏ x in range (n + 1), f x) = (∏ x in range n, f x) * f n := by
  simp only [mul_comm, prod_range_succ_comm]

@[to_additive]
theorem prod_range_succ' (f : ℕ → β) : ∀ n : ℕ, (∏ k in range (n + 1), f k) = (∏ k in range n, f (k + 1)) * f 0
  | 0 => prod_range_succ _ _
  | n + 1 => by
    rw [prod_range_succ _ n, mul_right_commₓ, ← prod_range_succ', prod_range_succ]

@[to_additive]
theorem eventually_constant_prod {u : ℕ → β} {N : ℕ} (hu : ∀ n ≥ N, u n = 1) {n : ℕ} (hn : N ≤ n) :
    (∏ k in range (n + 1), u k) = ∏ k in range (N + 1), u k := by
  obtain ⟨m, rfl : n = N + m⟩ := le_iff_exists_add.mp hn
  clear hn
  induction' m with m hm
  · simp
    
  erw [prod_range_succ, hm]
  simp [hu]

@[to_additive]
theorem prod_range_add (f : ℕ → β) (n m : ℕ) :
    (∏ x in range (n + m), f x) = (∏ x in range n, f x) * ∏ x in range m, f (n + x) := by
  induction' m with m hm
  · simp
    
  · rw [Nat.add_succ, prod_range_succ, hm, prod_range_succ, mul_assoc]
    

@[to_additive]
theorem prod_range_add_div_prod_range {α : Type _} [CommGroupₓ α] (f : ℕ → α) (n m : ℕ) :
    ((∏ k in range (n + m), f k) / ∏ k in range n, f k) = ∏ k in Finset.range m, f (n + k) :=
  div_eq_of_eq_mul' (prod_range_add f n m)

@[to_additive]
theorem prod_range_zero (f : ℕ → β) : (∏ k in range 0, f k) = 1 := by
  rw [range_zero, prod_empty]

@[to_additive sum_range_one]
theorem prod_range_one (f : ℕ → β) : (∏ k in range 1, f k) = f 0 := by
  rw [range_one]
  apply @prod_singleton β ℕ 0 f

open List

@[to_additive]
theorem prod_list_map_count [DecidableEq α] (l : List α) {M : Type _} [CommMonoidₓ M] (f : α → M) :
    (l.map f).Prod = ∏ m in l.toFinset, f m ^ l.count m := by
  induction' l with a s IH
  · simp only [map_nil, prod_nil, count_nil, pow_zeroₓ, prod_const_one]
    
  simp only [List.map, List.prod_cons, to_finset_cons, IH]
  by_cases' has : a ∈ s.to_finset
  · rw [insert_eq_of_mem has, ← insert_erase has, prod_insert (not_mem_erase _ _), prod_insert (not_mem_erase _ _), ←
      mul_assoc, count_cons_self, pow_succₓ]
    congr 1
    refine' prod_congr rfl fun x hx => _
    rw [count_cons_of_ne (ne_of_mem_erase hx)]
    
  rw [prod_insert has, count_cons_self, count_eq_zero_of_not_mem (mt mem_to_finset.2 has), pow_oneₓ]
  congr 1
  refine' prod_congr rfl fun x hx => _
  rw [count_cons_of_ne]
  rintro rfl
  exact has hx

@[to_additive]
theorem prod_list_count [DecidableEq α] [CommMonoidₓ α] (s : List α) : s.Prod = ∏ m in s.toFinset, m ^ s.count m := by
  simpa using prod_list_map_count s id

@[to_additive]
theorem prod_list_count_of_subset [DecidableEq α] [CommMonoidₓ α] (m : List α) (s : Finset α) (hs : m.toFinset ⊆ s) :
    m.Prod = ∏ i in s, i ^ m.count i := by
  rw [prod_list_count]
  refine' prod_subset hs fun x _ hx => _
  rw [mem_to_finset] at hx
  rw [count_eq_zero_of_not_mem hx, pow_zeroₓ]

theorem sum_filter_count_eq_countp [DecidableEq α] (p : α → Prop) [DecidablePred p] (l : List α) :
    (∑ x in l.toFinset.filter p, l.count x) = l.countp p := by
  simp [Finset.sum, sum_map_count_dedup_filter_eq_countp p l]

open Multiset

@[to_additive]
theorem prod_multiset_map_count [DecidableEq α] (s : Multiset α) {M : Type _} [CommMonoidₓ M] (f : α → M) :
    (s.map f).Prod = ∏ m in s.toFinset, f m ^ s.count m := by
  refine' Quot.induction_on s fun l => _
  simp [prod_list_map_count l f]

@[to_additive]
theorem prod_multiset_count [DecidableEq α] [CommMonoidₓ α] (s : Multiset α) :
    s.Prod = ∏ m in s.toFinset, m ^ s.count m := by
  convert prod_multiset_map_count s id
  rw [Multiset.map_id]

@[to_additive]
theorem prod_multiset_count_of_subset [DecidableEq α] [CommMonoidₓ α] (m : Multiset α) (s : Finset α)
    (hs : m.toFinset ⊆ s) : m.Prod = ∏ i in s, i ^ m.count i := by
  revert hs
  refine' Quot.induction_on m fun l => _
  simp only [quot_mk_to_coe'', coe_prod, coe_count]
  apply prod_list_count_of_subset l s

@[to_additive]
theorem prod_mem_multiset [DecidableEq α] (m : Multiset α) (f : { x // x ∈ m } → β) (g : α → β) (hfg : ∀ x, f x = g x) :
    (∏ x : { x // x ∈ m }, f x) = ∏ x in m.toFinset, g x :=
  prod_bij (fun x _ => x.1) (fun x _ => Multiset.mem_to_finset.mpr x.2) (fun _ _ => hfg _)
    (fun _ _ _ _ h => by
      ext
      assumption)
    fun y hy => ⟨⟨y, Multiset.mem_to_finset.mp hy⟩, Finset.mem_univ _, rfl⟩

/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors.
-/
@[to_additive
      "To prove a property of a sum, it suffices to prove that\nthe property is additive and holds on summands."]
theorem prod_induction {M : Type _} [CommMonoidₓ M] (f : α → M) (p : M → Prop) (p_mul : ∀ a b, p a → p b → p (a * b))
    (p_one : p 1) (p_s : ∀ x ∈ s, p <| f x) : p <| ∏ x in s, f x :=
  Multiset.prod_induction _ _ p_mul p_one (Multiset.forall_mem_map_iff.mpr p_s)

/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors.
-/
@[to_additive
      "To prove a property of a sum, it suffices to prove that\nthe property is additive and holds on summands."]
theorem prod_induction_nonempty {M : Type _} [CommMonoidₓ M] (f : α → M) (p : M → Prop)
    (p_mul : ∀ a b, p a → p b → p (a * b)) (hs_nonempty : s.Nonempty) (p_s : ∀ x ∈ s, p <| f x) : p <| ∏ x in s, f x :=
  Multiset.prod_induction_nonempty p p_mul
    (by
      simp [nonempty_iff_ne_empty.mp hs_nonempty])
    (Multiset.forall_mem_map_iff.mpr p_s)

/-- For any product along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can verify
that it's equal to a different function just by checking ratios of adjacent terms.

This is a multiplicative discrete analogue of the fundamental theorem of calculus. -/
@[to_additive
      "For any sum along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can\nverify that it's equal to a different function just by checking differences of adjacent terms.\n\nThis is a discrete analogue of the fundamental theorem of calculus."]
theorem prod_range_induction (f s : ℕ → β) (h0 : s 0 = 1) (h : ∀ n, s (n + 1) = s n * f n) (n : ℕ) :
    (∏ k in Finset.range n, f k) = s n := by
  induction' n with k hk
  · simp only [h0, Finset.prod_range_zero]
    
  · simp only [hk, Finset.prod_range_succ, h, mul_comm]
    

/-- A telescoping product along `{0, ..., n - 1}` of a commutative group valued function reduces to
the ratio of the last and first factors. -/
@[to_additive
      "A telescoping sum along `{0, ..., n - 1}` of an additive commutative group valued\nfunction reduces to the difference of the last and first terms."]
theorem prod_range_div {M : Type _} [CommGroupₓ M] (f : ℕ → M) (n : ℕ) :
    (∏ i in range n, f (i + 1) / f i) = f n / f 0 := by
  apply prod_range_induction <;> simp

@[to_additive]
theorem prod_range_div' {M : Type _} [CommGroupₓ M] (f : ℕ → M) (n : ℕ) :
    (∏ i in range n, f i / f (i + 1)) = f 0 / f n := by
  apply prod_range_induction <;> simp

@[to_additive]
theorem eq_prod_range_div {M : Type _} [CommGroupₓ M] (f : ℕ → M) (n : ℕ) :
    f n = f 0 * ∏ i in range n, f (i + 1) / f i := by
  rw [prod_range_div, mul_div_cancel'_right]

@[to_additive]
theorem eq_prod_range_div' {M : Type _} [CommGroupₓ M] (f : ℕ → M) (n : ℕ) :
    f n = ∏ i in range (n + 1), if i = 0 then f 0 else f i / f (i - 1) := by
  conv_lhs => rw [Finset.eq_prod_range_div f]
  simp [Finset.prod_range_succ', mul_comm]

/-- A telescoping sum along `{0, ..., n-1}` of an `ℕ`-valued function
reduces to the difference of the last and first terms
when the function we are summing is monotone.
-/
theorem sum_range_tsub [CanonicallyOrderedAddMonoid α] [Sub α] [HasOrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] {f : ℕ → α} (h : Monotone f) (n : ℕ) :
    (∑ i in range n, f (i + 1) - f i) = f n - f 0 := by
  refine' sum_range_induction _ _ (tsub_self _) (fun n => _) _
  have h₁ : f n ≤ f (n + 1) := h (Nat.le_succₓ _)
  have h₂ : f 0 ≤ f n := h (Nat.zero_leₓ _)
  rw [tsub_add_eq_add_tsub h₂, add_tsub_cancel_of_le h₁]

@[simp, to_additive]
theorem prod_const (b : β) : (∏ x in s, b) = b ^ s.card :=
  haveI := Classical.decEq α
  Finset.induction_on s
    (by
      simp )
    fun a s has ih => by
    rw [prod_insert has, card_insert_of_not_mem has, pow_succₓ, ih]

@[to_additive]
theorem pow_eq_prod_const (b : β) : ∀ n, b ^ n = ∏ k in range n, b := by
  simp

@[to_additive]
theorem prod_pow (s : Finset α) (n : ℕ) (f : α → β) : (∏ x in s, f x ^ n) = (∏ x in s, f x) ^ n :=
  haveI := Classical.decEq α
  Finset.induction_on s
    (by
      simp )
    (by
      simp (config := { contextual := true })[mul_powₓ])

@[to_additive]
theorem prod_flip {n : ℕ} (f : ℕ → β) : (∏ r in range (n + 1), f (n - r)) = ∏ k in range (n + 1), f k := by
  induction' n with n ih
  · rw [prod_range_one, prod_range_one]
    
  · rw [prod_range_succ', prod_range_succ _ (Nat.succ n)]
    simp [← ih]
    

@[to_additive]
theorem prod_involution {s : Finset α} {f : α → β} :
    ∀ (g : ∀ a ∈ s, α) (h : ∀ a ha, f a * f (g a ha) = 1) (g_ne : ∀ a ha, f a ≠ 1 → g a ha ≠ a)
      (g_mem : ∀ a ha, g a ha ∈ s) (g_inv : ∀ a ha, g (g a ha) (g_mem a ha) = a), (∏ x in s, f x) = 1 :=
  by
  haveI := Classical.decEq α <;>
    haveI := Classical.decEq β <;>
      exact
        Finset.strongInductionOn s fun s ih g h g_ne g_mem g_inv =>
          s.eq_empty_or_nonempty.elim (fun hs => hs.symm ▸ rfl) fun ⟨x, hx⟩ =>
            have hmem : ∀ y ∈ (s.erase x).erase (g x hx), y ∈ s := fun y hy => mem_of_mem_erase (mem_of_mem_erase hy)
            have g_inj : ∀ {x hx y hy}, g x hx = g y hy → x = y := fun x hx y hy h => by
              rw [← g_inv x hx, ← g_inv y hy] <;> simp [h]
            have ih' : (∏ y in erase (erase s x) (g x hx), f y) = (1 : β) :=
              ih ((s.erase x).erase (g x hx))
                ⟨subset.trans (erase_subset _ _) (erase_subset _ _), fun h =>
                  not_mem_erase (g x hx) (s.erase x) (h (g_mem x hx))⟩
                (fun y hy => g y (hmem y hy)) (fun y hy => h y (hmem y hy)) (fun y hy => g_ne y (hmem y hy))
                (fun y hy =>
                  mem_erase.2
                    ⟨fun h : g y _ = g x hx => by
                      simpa [g_inj h] using hy,
                      mem_erase.2
                        ⟨fun h : g y _ = x => by
                          have : y = g x hx :=
                            g_inv y (hmem y hy) ▸ by
                              simp [h]
                          simpa [this] using hy, g_mem y (hmem y hy)⟩⟩)
                fun y hy => g_inv y (hmem y hy)
            if hx1 : f x = 1 then
              ih' ▸
                Eq.symm
                  (prod_subset hmem fun y hy hy₁ =>
                    have : y = x ∨ y = g x hx := by
                      simpa [hy, not_and_distrib, or_comm] using hy₁
                    this.elim (fun hy => hy.symm ▸ hx1) fun hy => h x hx ▸ hy ▸ hx1.symm ▸ (one_mulₓ _).symm)
            else by
              rw [← insert_erase hx, prod_insert (not_mem_erase _ _), ←
                insert_erase (mem_erase.2 ⟨g_ne x hx hx1, g_mem x hx⟩), prod_insert (not_mem_erase _ _), ih', mul_oneₓ,
                h x hx]

/-- The product of the composition of functions `f` and `g`, is the product over `b ∈ s.image g` of
`f b` to the power of the cardinality of the fibre of `b`. See also `finset.prod_image`. -/
@[to_additive
      "The sum of the composition of functions `f` and `g`, is the sum over `b ∈ s.image g`\nof `f b` times of the cardinality of the fibre of `b`. See also `finset.sum_image`."]
theorem prod_comp [DecidableEq γ] (f : γ → β) (g : α → γ) :
    (∏ a in s, f (g a)) = ∏ b in s.Image g, f b ^ (s.filter fun a => g a = b).card :=
  calc
    (∏ a in s, f (g a)) = ∏ x in (s.Image g).Sigma fun b : γ => s.filter fun a => g a = b, f (g x.2) :=
      prod_bij (fun a ha => ⟨g a, a⟩)
        (by
          simp <;> tauto)
        (fun _ _ => rfl)
        (by
          simp )
        (-- `(by finish)` closes this
        by
          rintro ⟨b_fst, b_snd⟩ H
          simp only [mem_image, exists_prop, mem_filter, mem_sigma] at H
          tauto)
    _ = ∏ b in s.Image g, ∏ a in s.filter fun a => g a = b, f (g a) := prod_sigma _ _ _
    _ = ∏ b in s.Image g, ∏ a in s.filter fun a => g a = b, f b :=
      prod_congr rfl fun b hb =>
        prod_congr rfl
          (by
            simp (config := { contextual := true }))
    _ = ∏ b in s.Image g, f b ^ (s.filter fun a => g a = b).card := prod_congr rfl fun _ _ => prod_const _
    

@[to_additive]
theorem prod_piecewise [DecidableEq α] (s t : Finset α) (f g : α → β) :
    (∏ x in s, (t.piecewise f g) x) = (∏ x in s ∩ t, f x) * ∏ x in s \ t, g x := by
  rw [piecewise, prod_ite, filter_mem_eq_inter, ← sdiff_eq_filter]

@[to_additive]
theorem prod_inter_mul_prod_diff [DecidableEq α] (s t : Finset α) (f : α → β) :
    ((∏ x in s ∩ t, f x) * ∏ x in s \ t, f x) = ∏ x in s, f x := by
  convert (s.prod_piecewise t f f).symm
  simp [Finset.piecewise]

@[to_additive]
theorem prod_eq_mul_prod_diff_singleton [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s) (f : α → β) :
    (∏ x in s, f x) = f i * ∏ x in s \ {i}, f x := by
  convert (s.prod_inter_mul_prod_diff {i} f).symm
  simp [h]

@[to_additive]
theorem prod_eq_prod_diff_singleton_mul [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s) (f : α → β) :
    (∏ x in s, f x) = (∏ x in s \ {i}, f x) * f i := by
  rw [prod_eq_mul_prod_diff_singleton h, mul_comm]

@[to_additive]
theorem _root_.fintype.prod_eq_mul_prod_compl [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    (∏ i, f i) = f a * ∏ i in {a}ᶜ, f i :=
  prod_eq_mul_prod_diff_singleton (mem_univ a) f

@[to_additive]
theorem _root_.fintype.prod_eq_prod_compl_mul [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    (∏ i, f i) = (∏ i in {a}ᶜ, f i) * f a :=
  prod_eq_prod_diff_singleton_mul (mem_univ a) f

theorem dvd_prod_of_mem (f : α → β) {a : α} {s : Finset α} (ha : a ∈ s) : f a ∣ ∏ i in s, f i := by
  classical
  rw [Finset.prod_eq_mul_prod_diff_singleton ha]
  exact dvd_mul_right _ _

/-- A product can be partitioned into a product of products, each equivalent under a setoid. -/
@[to_additive "A sum can be partitioned into a sum of sums, each equivalent under a setoid."]
theorem prod_partition (R : Setoidₓ α) [DecidableRel R.R] :
    (∏ x in s, f x) = ∏ xbar in s.Image Quotientₓ.mk, ∏ y in s.filter fun y => ⟦y⟧ = xbar, f y := by
  refine' (Finset.prod_image' f fun x hx => _).symm
  rfl

/-- If we can partition a product into subsets that cancel out, then the whole product cancels. -/
@[to_additive "If we can partition a sum into subsets that cancel out, then the whole sum cancels."]
theorem prod_cancels_of_partition_cancels (R : Setoidₓ α) [DecidableRel R.R]
    (h : ∀ x ∈ s, (∏ a in s.filter fun y => y ≈ x, f a) = 1) : (∏ x in s, f x) = 1 := by
  rw [prod_partition R, ← Finset.prod_eq_one]
  intro xbar xbar_in_s
  obtain ⟨x, x_in_s, xbar_eq_x⟩ := mem_image.mp xbar_in_s
  rw [← xbar_eq_x, filter_congr fun y _ => @Quotientₓ.eq _ R y x]
  apply h x x_in_s

@[to_additive]
theorem prod_update_of_not_mem [DecidableEq α] {s : Finset α} {i : α} (h : i ∉ s) (f : α → β) (b : β) :
    (∏ x in s, Function.update f i b x) = ∏ x in s, f x := by
  apply prod_congr rfl fun j hj => _
  have : j ≠ i := by
    intro eq
    rw [Eq] at hj
    exact h hj
  simp [this]

@[to_additive]
theorem prod_update_of_mem [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s) (f : α → β) (b : β) :
    (∏ x in s, Function.update f i b x) = b * ∏ x in s \ singleton i, f x := by
  rw [update_eq_piecewise, prod_piecewise]
  simp [h]

/-- If a product of a `finset` of size at most 1 has a given value, so
do the terms in that product. -/
@[to_additive eq_of_card_le_one_of_sum_eq
      "If a sum of a `finset` of size at most 1 has a given\nvalue, so do the terms in that sum."]
theorem eq_of_card_le_one_of_prod_eq {s : Finset α} (hc : s.card ≤ 1) {f : α → β} {b : β} (h : (∏ x in s, f x) = b) :
    ∀ x ∈ s, f x = b := by
  intro x hx
  by_cases' hc0 : s.card = 0
  · exact False.elim (card_ne_zero_of_mem hx hc0)
    
  · have h1 : s.card = 1 := le_antisymmₓ hc (Nat.one_le_of_lt (Nat.pos_of_ne_zeroₓ hc0))
    rw [card_eq_one] at h1
    cases' h1 with x2 hx2
    rw [hx2, mem_singleton] at hx
    simp_rw [hx2] at h
    rw [hx]
    rw [prod_singleton] at h
    exact h
    

/-- Taking a product over `s : finset α` is the same as multiplying the value on a single element
`f a` by the product of `s.erase a`.

See `multiset.prod_map_erase` for the `multiset` version. -/
@[to_additive
      "Taking a sum over `s : finset α` is the same as adding the value on a single element\n`f a` to the sum over `s.erase a`.\n\nSee `multiset.sum_map_erase` for the `multiset` version."]
theorem mul_prod_erase [DecidableEq α] (s : Finset α) (f : α → β) {a : α} (h : a ∈ s) :
    (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x := by
  rw [← prod_insert (not_mem_erase a s), insert_erase h]

/-- A variant of `finset.mul_prod_erase` with the multiplication swapped. -/
@[to_additive "A variant of `finset.add_sum_erase` with the addition swapped."]
theorem prod_erase_mul [DecidableEq α] (s : Finset α) (f : α → β) {a : α} (h : a ∈ s) :
    (∏ x in s.erase a, f x) * f a = ∏ x in s, f x := by
  rw [mul_comm, mul_prod_erase s f h]

/-- If a function applied at a point is 1, a product is unchanged by
removing that point, if present, from a `finset`. -/
@[to_additive
      "If a function applied at a point is 0, a sum is unchanged by\nremoving that point, if present, from a `finset`."]
theorem prod_erase [DecidableEq α] (s : Finset α) {f : α → β} {a : α} (h : f a = 1) :
    (∏ x in s.erase a, f x) = ∏ x in s, f x := by
  rw [← sdiff_singleton_eq_erase]
  refine' prod_subset (sdiff_subset _ _) fun x hx hnx => _
  rw [sdiff_singleton_eq_erase] at hnx
  rwa [eq_of_mem_of_not_mem_erase hx hnx]

theorem sum_erase_lt_of_pos {γ : Type _} [DecidableEq α] [OrderedAddCommMonoid γ] [CovariantClass γ γ (· + ·) (· < ·)]
    {s : Finset α} {d : α} (hd : d ∈ s) {f : α → γ} (hdf : 0 < f d) : (∑ m : α in s.erase d, f m) < ∑ m : α in s, f m :=
  by
  nth_rw_rhs 0[← Finset.insert_erase hd]
  rw [Finset.sum_insert (Finset.not_mem_erase d s)]
  exact lt_add_of_pos_left _ hdf

/-- If a product is 1 and the function is 1 except possibly at one
point, it is 1 everywhere on the `finset`. -/
@[to_additive "If a sum is 0 and the function is 0 except possibly at one\npoint, it is 0 everywhere on the `finset`."]
theorem eq_one_of_prod_eq_one {s : Finset α} {f : α → β} {a : α} (hp : (∏ x in s, f x) = 1)
    (h1 : ∀ x ∈ s, x ≠ a → f x = 1) : ∀ x ∈ s, f x = 1 := by
  intro x hx
  classical
  by_cases' h : x = a
  · rw [h]
    rw [h] at hx
    rw [← prod_subset (singleton_subset_iff.2 hx) fun t ht ha => h1 t ht (not_mem_singleton.1 ha), prod_singleton] at hp
    exact hp
    
  · exact h1 x hx h
    

theorem prod_pow_boole [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
    (∏ x in s, f x ^ ite (a = x) 1 0) = ite (a ∈ s) (f a) 1 := by
  simp

theorem prod_dvd_prod_of_dvd {S : Finset α} (g1 g2 : α → β) (h : ∀ a ∈ S, g1 a ∣ g2 a) : S.Prod g1 ∣ S.Prod g2 := by
  classical
  apply Finset.induction_on' S
  · simp
    
  intro a T haS _ haT IH
  repeat'
    rw [Finset.prod_insert haT]
  exact mul_dvd_mul (h a haS) IH

theorem prod_dvd_prod_of_subset {ι M : Type _} [CommMonoidₓ M] (s t : Finset ι) (f : ι → M) (h : s ⊆ t) :
    (∏ i in s, f i) ∣ ∏ i in t, f i :=
  Multiset.prod_dvd_prod_of_le <|
    Multiset.map_le_map <| by
      simpa

end CommMonoidₓ

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` over `s`
  is the sum of the products of `g` and `h`. -/
theorem prod_add_prod_eq [CommSemiringₓ β] {s : Finset α} {i : α} {f g h : α → β} (hi : i ∈ s) (h1 : g i + h i = f i)
    (h2 : ∀ j ∈ s, j ≠ i → g j = f j) (h3 : ∀ j ∈ s, j ≠ i → h j = f j) :
    ((∏ i in s, g i) + ∏ i in s, h i) = ∏ i in s, f i := by
  classical
  simp_rw [prod_eq_mul_prod_diff_singleton hi, ← h1, right_distrib]
  congr 2 <;> apply prod_congr rfl <;> simpa

theorem card_eq_sum_ones (s : Finset α) : s.card = ∑ _ in s, 1 := by
  simp

theorem sum_const_nat {m : ℕ} {f : α → ℕ} (h₁ : ∀ x ∈ s, f x = m) : (∑ x in s, f x) = card s * m := by
  rw [← Nat.nsmul_eq_mul, ← sum_const]
  apply sum_congr rfl h₁

@[simp]
theorem sum_boole {s : Finset α} {p : α → Prop} [NonAssocSemiringₓ β] {hp : DecidablePred p} :
    (∑ x in s, if p x then (1 : β) else (0 : β)) = (s.filter p).card := by
  simp [sum_ite]

theorem _root_.commute.sum_right [NonUnitalNonAssocSemiringₓ β] (s : Finset α) (f : α → β) (b : β)
    (h : ∀ i ∈ s, Commute b (f i)) : Commute b (∑ i in s, f i) :=
  (Commute.multiset_sum_right _ _) fun b hb => by
    obtain ⟨i, hi, rfl⟩ := multiset.mem_map.mp hb
    exact h _ hi

theorem _root_.commute.sum_left [NonUnitalNonAssocSemiringₓ β] (s : Finset α) (f : α → β) (b : β)
    (h : ∀ i ∈ s, Commute (f i) b) : Commute (∑ i in s, f i) b :=
  ((Commute.sum_right _ _ _) fun i hi => (h _ hi).symm).symm

section Opposite

open MulOpposite

/-- Moving to the opposite additive commutative monoid commutes with summing. -/
@[simp]
theorem op_sum [AddCommMonoidₓ β] {s : Finset α} (f : α → β) : op (∑ x in s, f x) = ∑ x in s, op (f x) :=
  (opAddEquiv : β ≃+ βᵐᵒᵖ).map_sum _ _

@[simp]
theorem unop_sum [AddCommMonoidₓ β] {s : Finset α} (f : α → βᵐᵒᵖ) : unop (∑ x in s, f x) = ∑ x in s, unop (f x) :=
  (opAddEquiv : β ≃+ βᵐᵒᵖ).symm.map_sum _ _

end Opposite

section DivisionCommMonoid

variable [DivisionCommMonoid β]

@[simp, to_additive]
theorem prod_inv_distrib : (∏ x in s, (f x)⁻¹) = (∏ x in s, f x)⁻¹ :=
  Multiset.prod_map_inv

@[simp, to_additive]
theorem prod_div_distrib : (∏ x in s, f x / g x) = (∏ x in s, f x) / ∏ x in s, g x :=
  Multiset.prod_map_div

@[to_additive]
theorem prod_zpow (f : α → β) (s : Finset α) (n : ℤ) : (∏ a in s, f a ^ n) = (∏ a in s, f a) ^ n :=
  Multiset.prod_map_zpow

end DivisionCommMonoid

section CommGroupₓ

variable [CommGroupₓ β] [DecidableEq α]

@[simp, to_additive]
theorem prod_sdiff_eq_div (h : s₁ ⊆ s₂) : (∏ x in s₂ \ s₁, f x) = (∏ x in s₂, f x) / ∏ x in s₁, f x := by
  rw [eq_div_iff_mul_eq', prod_sdiff h]

@[to_additive]
theorem prod_sdiff_div_prod_sdiff : ((∏ x in s₂ \ s₁, f x) / ∏ x in s₁ \ s₂, f x) = (∏ x in s₂, f x) / ∏ x in s₁, f x :=
  by
  simp [← Finset.prod_sdiff (@inf_le_left _ _ s₁ s₂), ← Finset.prod_sdiff (@inf_le_right _ _ s₁ s₂)]

@[simp, to_additive]
theorem prod_erase_eq_div {a : α} (h : a ∈ s) : (∏ x in s.erase a, f x) = (∏ x in s, f x) / f a := by
  rw [eq_div_iff_mul_eq', prod_erase_mul _ _ h]

end CommGroupₓ

@[simp]
theorem card_sigma {σ : α → Type _} (s : Finset α) (t : ∀ a, Finset (σ a)) : card (s.Sigma t) = ∑ a in s, card (t a) :=
  Multiset.card_sigma _ _

theorem card_bUnion [DecidableEq β] {s : Finset α} {t : α → Finset β}
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (t x) (t y)) : (s.bUnion t).card = ∑ u in s, card (t u) :=
  calc
    (s.bUnion t).card = ∑ i in s.bUnion t, 1 := by
      simp
    _ = ∑ a in s, ∑ i in t a, 1 := Finset.sum_bUnion h
    _ = ∑ u in s, card (t u) := by
      simp
    

theorem card_bUnion_le [DecidableEq β] {s : Finset α} {t : α → Finset β} : (s.bUnion t).card ≤ ∑ a in s, (t a).card :=
  haveI := Classical.decEq α
  Finset.induction_on s
    (by
      simp )
    fun a s has ih =>
    calc
      ((insert a s).bUnion t).card ≤ (t a).card + (s.bUnion t).card := by
        rw [bUnion_insert] <;> exact Finset.card_union_le _ _
      _ ≤ ∑ a in insert a s, card (t a) := by
        rw [sum_insert has] <;> exact add_le_add_left ih _
      

theorem card_eq_sum_card_fiberwise [DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β} (H : ∀ x ∈ s, f x ∈ t) :
    s.card = ∑ a in t, (s.filter fun x => f x = a).card := by
  simp only [card_eq_sum_ones, sum_fiberwise_of_maps_to H]

theorem card_eq_sum_card_image [DecidableEq β] (f : α → β) (s : Finset α) :
    s.card = ∑ a in s.Image f, (s.filter fun x => f x = a).card :=
  card_eq_sum_card_fiberwise fun _ => mem_image_of_mem _

theorem mem_sum {f : α → Multiset β} (s : Finset α) (b : β) : (b ∈ ∑ x in s, f x) ↔ ∃ a ∈ s, b ∈ f a := by
  classical
  refine'
    s.induction_on
      (by
        simp )
      _
  · intro a t hi ih
    simp [sum_insert hi, ih, or_and_distrib_right, exists_or_distrib]
    

section ProdEqZero

variable [CommMonoidWithZero β]

theorem prod_eq_zero (ha : a ∈ s) (h : f a = 0) : (∏ x in s, f x) = 0 := by
  haveI := Classical.decEq α
  rw [← prod_erase_mul _ _ ha, h, mul_zero]

theorem prod_boole {s : Finset α} {p : α → Prop} [DecidablePred p] :
    (∏ i in s, ite (p i) (1 : β) (0 : β)) = ite (∀ i ∈ s, p i) 1 0 := by
  split_ifs
  · apply prod_eq_one
    intro i hi
    rw [if_pos (h i hi)]
    
  · push_neg  at h
    rcases h with ⟨i, hi, hq⟩
    apply prod_eq_zero hi
    rw [if_neg hq]
    

variable [Nontrivial β] [NoZeroDivisors β]

theorem prod_eq_zero_iff : (∏ x in s, f x) = 0 ↔ ∃ a ∈ s, f a = 0 := by
  classical
  apply Finset.induction_on s
  exact ⟨Not.elim one_ne_zero, fun ⟨_, H, _⟩ => H.elim⟩
  intro a s ha ih
  rw [prod_insert ha, mul_eq_zero, bex_def, exists_mem_insert, ih, ← bex_def]

theorem prod_ne_zero_iff : (∏ x in s, f x) ≠ 0 ↔ ∀ a ∈ s, f a ≠ 0 := by
  rw [Ne, prod_eq_zero_iff]
  push_neg

end ProdEqZero

@[to_additive]
theorem prod_unique_nonempty {α β : Type _} [CommMonoidₓ β] [Unique α] (s : Finset α) (f : α → β) (h : s.Nonempty) :
    (∏ x in s, f x) = f default := by
  rw [h.eq_singleton_default, Finset.prod_singleton]

end Finset

namespace Fintype

open Finset

/-- `fintype.prod_bijective` is a variant of `finset.prod_bij` that accepts `function.bijective`.

See `function.bijective.prod_comp` for a version without `h`. -/
@[to_additive
      "`fintype.sum_equiv` is a variant of `finset.sum_bij` that accepts\n`function.bijective`.\n\nSee `function.bijective.sum_comp` for a version without `h`. "]
theorem prod_bijective {α β M : Type _} [Fintype α] [Fintype β] [CommMonoidₓ M] (e : α → β) (he : Function.Bijective e)
    (f : α → M) (g : β → M) (h : ∀ x, f x = g (e x)) : (∏ x : α, f x) = ∏ x : β, g x :=
  prod_bij (fun x _ => e x) (fun x _ => mem_univ (e x)) (fun x _ => h x) (fun x x' _ _ h => he.Injective h) fun y _ =>
    (he.Surjective y).imp fun a h => ⟨mem_univ _, h.symm⟩

/-- `fintype.prod_equiv` is a specialization of `finset.prod_bij` that
automatically fills in most arguments.

See `equiv.prod_comp` for a version without `h`.
-/
@[to_additive
      "`fintype.sum_equiv` is a specialization of `finset.sum_bij` that\nautomatically fills in most arguments.\n\nSee `equiv.sum_comp` for a version without `h`.\n"]
theorem prod_equiv {α β M : Type _} [Fintype α] [Fintype β] [CommMonoidₓ M] (e : α ≃ β) (f : α → M) (g : β → M)
    (h : ∀ x, f x = g (e x)) : (∏ x : α, f x) = ∏ x : β, g x :=
  prod_bijective e e.Bijective f g h

variable {f s}

@[to_additive]
theorem prod_unique {α β : Type _} [CommMonoidₓ β] [Unique α] (f : α → β) : (∏ x : α, f x) = f default := by
  rw [univ_unique, prod_singleton]

@[to_additive]
theorem prod_empty {α β : Type _} [CommMonoidₓ β] [IsEmpty α] (f : α → β) : (∏ x : α, f x) = 1 := by
  rw [eq_empty_of_is_empty (univ : Finset α), Finset.prod_empty]

@[to_additive]
theorem prod_subsingleton {α β : Type _} [CommMonoidₓ β] [Subsingleton α] [Fintype α] (f : α → β) (a : α) :
    (∏ x : α, f x) = f a := by
  haveI : Unique α := uniqueOfSubsingleton a
  convert prod_unique f

@[to_additive]
theorem prod_subtype_mul_prod_subtype {α β : Type _} [Fintype α] [CommMonoidₓ β] (p : α → Prop) (f : α → β)
    [DecidablePred p] : ((∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i) = ∏ i, f i := by
  classical
  let s := { x | p x }.toFinset
  rw [← Finset.prod_subtype s, ← Finset.prod_subtype (sᶜ)]
  · exact Finset.prod_mul_prod_compl _ _
    
  · simp
    
  · simp
    

end Fintype

namespace List

@[to_additive]
theorem prod_to_finset {M : Type _} [DecidableEq α] [CommMonoidₓ M] (f : α → M) :
    ∀ {l : List α} (hl : l.Nodup), l.toFinset.Prod f = (l.map f).Prod
  | [], _ => by
    simp
  | a :: l, hl => by
    let ⟨not_mem, hl⟩ := List.nodup_cons.mp hl
    simp [Finset.prod_insert (mt list.mem_to_finset.mp not_mem), prod_to_finset hl]

end List

namespace Multiset

theorem disjoint_list_sum_left {a : Multiset α} {l : List (Multiset α)} :
    Multiset.Disjoint l.Sum a ↔ ∀ b ∈ l, Multiset.Disjoint b a := by
  induction' l with b bs ih
  · simp only [zero_disjoint, List.not_mem_nilₓ, IsEmpty.forall_iff, forall_const, List.sum_nil]
    
  · simp_rw [List.sum_cons, disjoint_add_left, List.mem_cons_iffₓ, forall_eq_or_imp]
    simp [And.congr_left_iff, iff_selfₓ, ih]
    

theorem disjoint_list_sum_right {a : Multiset α} {l : List (Multiset α)} :
    Multiset.Disjoint a l.Sum ↔ ∀ b ∈ l, Multiset.Disjoint a b := by
  simpa only [disjoint_comm] using disjoint_list_sum_left

theorem disjoint_sum_left {a : Multiset α} {i : Multiset (Multiset α)} :
    Multiset.Disjoint i.Sum a ↔ ∀ b ∈ i, Multiset.Disjoint b a :=
  (Quotientₓ.induction_on i) fun l => by
    rw [quot_mk_to_coe, Multiset.coe_sum]
    exact disjoint_list_sum_left

theorem disjoint_sum_right {a : Multiset α} {i : Multiset (Multiset α)} :
    Multiset.Disjoint a i.Sum ↔ ∀ b ∈ i, Multiset.Disjoint a b := by
  simpa only [disjoint_comm] using disjoint_sum_left

theorem disjoint_finset_sum_left {β : Type _} {i : Finset β} {f : β → Multiset α} {a : Multiset α} :
    Multiset.Disjoint (i.Sum f) a ↔ ∀ b ∈ i, Multiset.Disjoint (f b) a := by
  convert (@disjoint_sum_left _ a) (map f i.val)
  simp [Finset.mem_def, And.congr_left_iff, iff_selfₓ]

theorem disjoint_finset_sum_right {β : Type _} {i : Finset β} {f : β → Multiset α} {a : Multiset α} :
    Multiset.Disjoint a (i.Sum f) ↔ ∀ b ∈ i, Multiset.Disjoint a (f b) := by
  simpa only [disjoint_comm] using disjoint_finset_sum_left

variable [DecidableEq α]

theorem add_eq_union_left_of_le {x y z : Multiset α} (h : y ≤ x) : z + x = z ∪ y ↔ z.Disjoint x ∧ x = y := by
  rw [← add_eq_union_iff_disjoint]
  constructor
  · intro h0
    rw [and_iff_right_of_imp]
    · exact (le_of_add_le_add_left <| h0.trans_le <| union_le_add z y).antisymm h
      
    · rintro rfl
      exact h0
      
    
  · rintro ⟨h0, rfl⟩
    exact h0
    

theorem add_eq_union_right_of_le {x y z : Multiset α} (h : z ≤ y) : x + y = x ∪ z ↔ y = z ∧ x.Disjoint y := by
  simpa only [and_comm] using add_eq_union_left_of_le h

-- ./././Mathport/Syntax/Translate/Basic.lean:556:2: warning: expanding binder collection (x «expr ∈ » i)
-- ./././Mathport/Syntax/Translate/Basic.lean:556:2: warning: expanding binder collection (x y «expr ∈ » i)
theorem finset_sum_eq_sup_iff_disjoint {β : Type _} {i : Finset β} {f : β → Multiset α} :
    i.Sum f = i.sup f ↔ ∀ (x y) (_ : x ∈ i) (_ : y ∈ i), x ≠ y → Multiset.Disjoint (f x) (f y) := by
  induction' i using Finset.cons_induction_on with z i hz hr
  · simp only [Finset.not_mem_empty, IsEmpty.forall_iff, implies_true_iff, Finset.sum_empty, Finset.sup_empty,
      bot_eq_zero, eq_self_iff_true]
    
  · simp_rw [Finset.sum_cons hz, Finset.sup_cons, Finset.mem_cons, Multiset.sup_eq_union, forall_eq_or_imp, Ne.def,
      eq_self_iff_true, not_true, IsEmpty.forall_iff, true_andₓ, imp_and_distrib, forall_and_distrib, ← hr,
      @eq_comm _ z]
    have := fun x (_ : x ∈ i) => ne_of_mem_of_not_mem H hz
    simp (config := { contextual := true })only [this, not_false_iff, true_implies_iff]
    simp_rw [← disjoint_finset_sum_left, ← disjoint_finset_sum_right, disjoint_comm, ← and_assoc, and_selfₓ]
    exact add_eq_union_left_of_le (Finset.sup_le fun x hx => le_sum_of_mem (mem_map_of_mem f hx))
    

theorem sup_powerset_len {α : Type _} [DecidableEq α] (x : Multiset α) :
    (Finset.sup (Finset.range (x.card + 1)) fun k => x.powersetLen k) = x.Powerset := by
  convert bind_powerset_len x
  rw [Multiset.bind, Multiset.join, ← Finset.range_coe, ← Finset.sum_eq_multiset_sum]
  exact Eq.symm (finset_sum_eq_sup_iff_disjoint.mpr fun _ _ _ _ h => disjoint_powerset_len x h)

@[simp]
theorem to_finset_sum_count_eq (s : Multiset α) : (∑ a in s.toFinset, s.count a) = s.card :=
  Multiset.induction_on s rfl fun a s ih =>
    calc
      (∑ x in toFinset (a ::ₘ s), count x (a ::ₘ s)) =
          ∑ x in toFinset (a ::ₘ s), (if x = a then 1 else 0) + count x s :=
        (Finset.sum_congr rfl) fun _ _ => by
          split_ifs <;> [simp only [h, count_cons_self, Nat.one_add], simp only [count_cons_of_ne h, zero_addₓ]]
      _ = card (a ::ₘ s) := by
        by_cases' a ∈ s.to_finset
        · have : (∑ x in s.to_finset, ite (x = a) 1 0) = ∑ x in {a}, ite (x = a) 1 0 := by
            rw [Finset.sum_ite_eq', if_pos h, Finset.sum_singleton, if_pos rfl]
          rw [to_finset_cons, Finset.insert_eq_of_mem h, Finset.sum_add_distrib, ih, this, Finset.sum_singleton,
            if_pos rfl, add_commₓ, card_cons]
          
        · have ha : a ∉ s := by
            rwa [mem_to_finset] at h
          have : (∑ x in to_finset s, ite (x = a) 1 0) = ∑ x in to_finset s, 0 :=
            Finset.sum_congr rfl fun x hx =>
              if_neg <| by
                rintro rfl <;> cc
          rw [to_finset_cons, Finset.sum_insert h, if_pos rfl, Finset.sum_add_distrib, this, Finset.sum_const_zero, ih,
            count_eq_zero_of_not_mem ha, zero_addₓ, add_commₓ, card_cons]
          
      

theorem count_sum' {s : Finset β} {a : α} {f : β → Multiset α} : count a (∑ x in s, f x) = ∑ x in s, count a (f x) := by
  dunfold Finset.sum
  rw [count_sum]

@[simp]
theorem to_finset_sum_count_nsmul_eq (s : Multiset α) : (∑ a in s.toFinset, s.count a • {a}) = s := by
  apply ext'
  intro b
  rw [count_sum']
  have h : count b s = count b (count b s • {b}) := by
    rw [count_nsmul, count_singleton_self, mul_oneₓ]
  rw [h]
  clear h
  apply Finset.sum_eq_single b
  · intro c h hcb
    rw [count_nsmul]
    convert mul_zero (count c s)
    apply count_eq_zero.mpr
    exact finset.not_mem_singleton.mpr (Ne.symm hcb)
    
  · intro hb
    rw [count_eq_zero_of_not_mem (mt mem_to_finset.2 hb), count_nsmul, zero_mul]
    

theorem exists_smul_of_dvd_count (s : Multiset α) {k : ℕ} (h : ∀ a : α, a ∈ s → k ∣ Multiset.count a s) :
    ∃ u : Multiset α, s = k • u := by
  use ∑ a in s.to_finset, (s.count a / k) • {a}
  have h₂ :
    (∑ x : α in s.to_finset, k • (count x s / k) • ({x} : Multiset α)) = ∑ x : α in s.to_finset, count x s • {x} := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← mul_nsmul, Nat.mul_div_cancel'ₓ (h x (mem_to_finset.mp hx))]
  rw [← Finset.sum_nsmul, h₂, to_finset_sum_count_nsmul_eq]

theorem to_finset_prod_dvd_prod [CommMonoidₓ α] (S : Multiset α) : S.toFinset.Prod id ∣ S.Prod := by
  rw [Finset.prod_eq_multiset_prod]
  refine' Multiset.prod_dvd_prod_of_le _
  simp [Multiset.dedup_le S]

@[to_additive]
theorem prod_sum {α : Type _} {ι : Type _} [CommMonoidₓ α] (f : ι → Multiset α) (s : Finset ι) :
    (∑ x in s, f x).Prod = ∏ x in s, (f x).Prod := by
  classical
  induction' s using Finset.induction_on with a t hat ih
  · rw [Finset.sum_empty, Finset.prod_empty, Multiset.prod_zero]
    
  · rw [Finset.sum_insert hat, Finset.prod_insert hat, Multiset.prod_add, ih]
    

end Multiset

namespace Nat

@[simp, norm_cast]
theorem cast_list_sum [AddMonoidWithOneₓ β] (s : List ℕ) : (↑s.Sum : β) = (s.map coe).Sum :=
  map_list_sum (castAddMonoidHom β) _

@[simp, norm_cast]
theorem cast_list_prod [Semiringₓ β] (s : List ℕ) : (↑s.Prod : β) = (s.map coe).Prod :=
  map_list_prod (castRingHom β) _

@[simp, norm_cast]
theorem cast_multiset_sum [AddCommMonoidWithOne β] (s : Multiset ℕ) : (↑s.Sum : β) = (s.map coe).Sum :=
  map_multiset_sum (castAddMonoidHom β) _

@[simp, norm_cast]
theorem cast_multiset_prod [CommSemiringₓ β] (s : Multiset ℕ) : (↑s.Prod : β) = (s.map coe).Prod :=
  map_multiset_prod (castRingHom β) _

@[simp, norm_cast]
theorem cast_sum [AddCommMonoidWithOne β] (s : Finset α) (f : α → ℕ) : ↑(∑ x in s, f x : ℕ) = ∑ x in s, (f x : β) :=
  map_sum (castAddMonoidHom β) _ _

@[simp, norm_cast]
theorem cast_prod [CommSemiringₓ β] (f : α → ℕ) (s : Finset α) : (↑(∏ i in s, f i) : β) = ∏ i in s, f i :=
  map_prod (castRingHom β) _ _

end Nat

namespace Int

@[simp, norm_cast]
theorem cast_list_sum [AddGroupWithOneₓ β] (s : List ℤ) : (↑s.Sum : β) = (s.map coe).Sum :=
  map_list_sum (castAddHom β) _

@[simp, norm_cast]
theorem cast_list_prod [Ringₓ β] (s : List ℤ) : (↑s.Prod : β) = (s.map coe).Prod :=
  map_list_prod (castRingHom β) _

@[simp, norm_cast]
theorem cast_multiset_sum [AddCommGroupWithOne β] (s : Multiset ℤ) : (↑s.Sum : β) = (s.map coe).Sum :=
  map_multiset_sum (castAddHom β) _

@[simp, norm_cast]
theorem cast_multiset_prod {R : Type _} [CommRingₓ R] (s : Multiset ℤ) : (↑s.Prod : R) = (s.map coe).Prod :=
  map_multiset_prod (castRingHom R) _

@[simp, norm_cast]
theorem cast_sum [AddCommGroupWithOne β] (s : Finset α) (f : α → ℤ) : ↑(∑ x in s, f x : ℤ) = ∑ x in s, (f x : β) :=
  map_sum (castAddHom β) _ _

@[simp, norm_cast]
theorem cast_prod {R : Type _} [CommRingₓ R] (f : α → ℤ) (s : Finset α) : (↑(∏ i in s, f i) : R) = ∏ i in s, f i :=
  (Int.castRingHom R).map_prod _ _

end Int

@[simp, norm_cast]
theorem Units.coe_prod {M : Type _} [CommMonoidₓ M] (f : α → Mˣ) (s : Finset α) :
    (↑(∏ i in s, f i) : M) = ∏ i in s, f i :=
  (Units.coeHom M).map_prod _ _

theorem Units.mk0_prod [CommGroupWithZero β] (s : Finset α) (f : α → β) (h) :
    Units.mk0 (∏ b in s, f b) h = ∏ b in s.attach, Units.mk0 (f b) fun hh => h (Finset.prod_eq_zero b.2 hh) := by
  classical
  induction s using Finset.induction_on <;> simp [*]

theorem nat_abs_sum_le {ι : Type _} (s : Finset ι) (f : ι → ℤ) : (∑ i in s, f i).natAbs ≤ ∑ i in s, (f i).natAbs := by
  classical
  apply Finset.induction_on s
  · simp only [Finset.sum_empty, Int.nat_abs_zero]
    
  · intro i s his IH
    simp only [his, Finset.sum_insert, not_false_iff]
    exact (Int.nat_abs_add_le _ _).trans (add_le_add le_rflₓ IH)
    

/-! ### `additive`, `multiplicative` -/


open Additive Multiplicative

section Monoidₓ

variable [Monoidₓ α]

@[simp]
theorem of_mul_list_prod (s : List α) : ofMul s.Prod = (s.map ofMul).Sum := by
  simpa [of_mul]

@[simp]
theorem to_mul_list_sum (s : List (Additive α)) : toMul s.Sum = (s.map toMul).Prod := by
  simpa [to_mul, of_mul]

end Monoidₓ

section AddMonoidₓ

variable [AddMonoidₓ α]

@[simp]
theorem of_add_list_prod (s : List α) : ofAdd s.Sum = (s.map ofAdd).Prod := by
  simpa [of_add]

@[simp]
theorem to_add_list_sum (s : List (Multiplicative α)) : toAdd s.Prod = (s.map toAdd).Sum := by
  simpa [to_add, of_add]

end AddMonoidₓ

section CommMonoidₓ

variable [CommMonoidₓ α]

@[simp]
theorem of_mul_multiset_prod (s : Multiset α) : ofMul s.Prod = (s.map ofMul).Sum := by
  simpa [of_mul]

@[simp]
theorem to_mul_multiset_sum (s : Multiset (Additive α)) : toMul s.Sum = (s.map toMul).Prod := by
  simpa [to_mul, of_mul]

@[simp]
theorem of_mul_prod (s : Finset ι) (f : ι → α) : ofMul (∏ i in s, f i) = ∑ i in s, ofMul (f i) :=
  rfl

@[simp]
theorem to_mul_sum (s : Finset ι) (f : ι → Additive α) : toMul (∑ i in s, f i) = ∏ i in s, toMul (f i) :=
  rfl

end CommMonoidₓ

section AddCommMonoidₓ

variable [AddCommMonoidₓ α]

@[simp]
theorem of_add_multiset_prod (s : Multiset α) : ofAdd s.Sum = (s.map ofAdd).Prod := by
  simpa [of_add]

@[simp]
theorem to_add_multiset_sum (s : Multiset (Multiplicative α)) : toAdd s.Prod = (s.map toAdd).Sum := by
  simpa [to_add, of_add]

@[simp]
theorem of_add_sum (s : Finset ι) (f : ι → α) : ofAdd (∑ i in s, f i) = ∏ i in s, ofAdd (f i) :=
  rfl

@[simp]
theorem to_add_prod (s : Finset ι) (f : ι → Multiplicative α) : toAdd (∏ i in s, f i) = ∑ i in s, toAdd (f i) :=
  rfl

end AddCommMonoidₓ

