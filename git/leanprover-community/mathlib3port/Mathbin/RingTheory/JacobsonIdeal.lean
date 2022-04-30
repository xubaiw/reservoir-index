/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma
-/
import Mathbin.RingTheory.Ideal.Quotient
import Mathbin.RingTheory.Polynomial.Basic

/-!
# Jacobson radical

The Jacobson radical of a ring `R` is defined to be the intersection of all maximal ideals of `R`.
This is similar to how the nilradical is equal to the intersection of all prime ideals of `R`.

We can extend the idea of the nilradical to ideals of `R`,
by letting the radical of an ideal `I` be the intersection of prime ideals containing `I`.
Under this extension, the original nilradical is the radical of the zero ideal `⊥`.
Here we define the Jacobson radical of an ideal `I` in a similar way,
as the intersection of maximal ideals containing `I`.

## Main definitions

Let `R` be a commutative ring, and `I` be an ideal of `R`

* `jacobson I` is the jacobson radical, i.e. the infimum of all maximal ideals containing I.

* `is_local I` is the proposition that the jacobson radical of `I` is itself a maximal ideal

## Main statements

* `mem_jacobson_iff` gives a characterization of members of the jacobson of I

* `is_local_of_is_maximal_radical`: if the radical of I is maximal then so is the jacobson radical

## Tags

Jacobson, Jacobson radical, Local Ideal

-/


universe u v

namespace Ideal

variable {R : Type u} [CommRingₓ R] {I : Ideal R}

variable {S : Type v} [CommRingₓ S]

open Polynomial

section Jacobson

/-- The Jacobson radical of `I` is the infimum of all maximal ideals containing `I`. -/
def jacobson (I : Ideal R) : Ideal R :=
  inf { J : Ideal R | I ≤ J ∧ IsMaximal J }

theorem le_jacobson : I ≤ jacobson I := fun x hx => mem_Inf.mpr fun J hJ => hJ.left hx

@[simp]
theorem jacobson_idem : jacobson (jacobson I) = jacobson I :=
  le_antisymmₓ (Inf_le_Inf fun J hJ => ⟨Inf_le hJ, hJ.2⟩) le_jacobson

theorem radical_le_jacobson : radical I ≤ jacobson I :=
  le_Inf fun J hJ => (radical_eq_Inf I).symm ▸ Inf_le ⟨hJ.left, IsMaximal.is_prime hJ.right⟩

theorem eq_radical_of_eq_jacobson : jacobson I = I → radical I = I := fun h =>
  le_antisymmₓ (le_transₓ radical_le_jacobson (le_of_eqₓ h)) le_radical

@[simp]
theorem jacobson_top : jacobson (⊤ : Ideal R) = ⊤ :=
  eq_top_iff.2 le_jacobson

@[simp]
theorem jacobson_eq_top_iff : jacobson I = ⊤ ↔ I = ⊤ :=
  ⟨fun H =>
    Classical.by_contradiction fun hi =>
      let ⟨M, hm, him⟩ := exists_le_maximal I hi
      lt_top_iff_ne_top.1 (lt_of_le_of_ltₓ (show jacobson I ≤ M from Inf_le ⟨him, hm⟩) <| lt_top_iff_ne_top.2 hm.ne_top)
        H,
    fun H => eq_top_iff.2 <| le_Inf fun J ⟨hij, hj⟩ => H ▸ hij⟩

theorem jacobson_eq_bot : jacobson I = ⊥ → I = ⊥ := fun h => eq_bot_iff.mpr (h ▸ le_jacobson)

theorem jacobson_eq_self_of_is_maximal [H : IsMaximal I] : I.jacobson = I :=
  le_antisymmₓ (Inf_le ⟨le_of_eqₓ rfl, H⟩) le_jacobson

instance (priority := 100) jacobson.is_maximal [H : IsMaximal I] : IsMaximal (jacobson I) :=
  ⟨⟨fun htop => H.1.1 (jacobson_eq_top_iff.1 htop), fun J hJ => H.1.2 _ (lt_of_le_of_ltₓ le_jacobson hJ)⟩⟩

theorem mem_jacobson_iff {x : R} : x ∈ jacobson I ↔ ∀ y, ∃ z, x * y * z + z - 1 ∈ I :=
  ⟨fun hx y =>
    Classical.by_cases
      (fun hxy : I⊔span {x * y + 1} = ⊤ =>
        let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 hxy)
        let ⟨r, hr⟩ := mem_span_singleton.1 hq
        ⟨r, by
          rw [← one_mulₓ r, ← mul_assoc, ← add_mulₓ, mul_oneₓ, ← hr, ← hpq, ← neg_sub, add_sub_cancel] <;>
            exact I.neg_mem hpi⟩)
      fun hxy : I⊔span {x * y + 1} ≠ ⊤ =>
      let ⟨M, hm1, hm2⟩ := exists_le_maximal _ hxy
      suffices x ∉ M from (this <| mem_Inf.1 hx ⟨le_transₓ le_sup_left hm2, hm1⟩).elim
      fun hxm =>
      hm1.1.1 <|
        (eq_top_iff_one _).2 <|
          add_sub_cancel' (x * y) 1 ▸
            M.sub_mem (le_sup_right.trans hm2 <| mem_span_singleton.2 dvd_rfl) (M.mul_mem_right _ hxm),
    fun hx =>
    mem_Inf.2 fun M ⟨him, hm⟩ =>
      Classical.by_contradiction fun hxm =>
        let ⟨y, hy⟩ := hm.exists_inv hxm
        let ⟨z, hz⟩ := hx (-y)
        hm.1.1 <|
          (eq_top_iff_one _).2 <|
            sub_sub_cancel (x * -y * z + z) 1 ▸
              M.sub_mem
                (by
                  rw [← one_mulₓ z, ← mul_assoc, ← add_mulₓ, mul_oneₓ, mul_neg, neg_add_eq_sub, ← neg_sub, neg_mul,
                    neg_mul_eq_mul_neg, mul_comm x y, mul_comm _ (-z)]
                  rcases hy with ⟨i, hi, df⟩
                  rw [← sub_eq_iff_eq_add.mpr df.symm, sub_sub, add_commₓ, ← sub_sub, sub_self, zero_sub]
                  refine' M.mul_mem_left (-z) (neg_mem_iff.mpr hi))
                (him hz)⟩

theorem exists_mul_sub_mem_of_sub_one_mem_jacobson {I : Ideal R} (r : R) (h : r - 1 ∈ jacobson I) :
    ∃ s, r * s - 1 ∈ I := by
  cases' mem_jacobson_iff.1 h 1 with s hs
  use s
  simpa [sub_mul] using hs

theorem is_unit_of_sub_one_mem_jacobson_bot (r : R) (h : r - 1 ∈ jacobson (⊥ : Ideal R)) : IsUnit r := by
  cases' exists_mul_sub_mem_of_sub_one_mem_jacobson r h with s hs
  rw [mem_bot, sub_eq_zero] at hs
  exact is_unit_of_mul_eq_one _ _ hs

/-- An ideal equals its Jacobson radical iff it is the intersection of a set of maximal ideals.
Allowing the set to include ⊤ is equivalent, and is included only to simplify some proofs. -/
theorem eq_jacobson_iff_Inf_maximal :
    I.jacobson = I ↔ ∃ M : Set (Ideal R), (∀, ∀ J ∈ M, ∀, IsMaximal J ∨ J = ⊤) ∧ I = inf M := by
  use fun hI => ⟨{ J : Ideal R | I ≤ J ∧ J.IsMaximal }, ⟨fun _ hJ => Or.inl hJ.right, hI.symm⟩⟩
  rintro ⟨M, hM, hInf⟩
  refine' le_antisymmₓ (fun x hx => _) le_jacobson
  rw [hInf, mem_Inf]
  intro I hI
  cases' hM I hI with is_max is_top
  · exact (mem_Inf.1 hx) ⟨le_Inf_iff.1 (le_of_eqₓ hInf) I hI, IsMax⟩
    
  · exact is_top.symm ▸ Submodule.mem_top
    

theorem eq_jacobson_iff_Inf_maximal' :
    I.jacobson = I ↔ ∃ M : Set (Ideal R), (∀, ∀ J ∈ M, ∀ K : Ideal R, J < K → K = ⊤) ∧ I = inf M :=
  eq_jacobson_iff_Inf_maximal.trans
    ⟨fun h =>
      let ⟨M, hM⟩ := h
      ⟨M,
        ⟨fun J hJ K hK => Or.rec_on (hM.1 J hJ) (fun h => h.1.2 K hK) fun h => eq_top_iff.2 (le_of_ltₓ (h ▸ hK)),
          hM.2⟩⟩,
      fun h =>
      let ⟨M, hM⟩ := h
      ⟨M, ⟨fun J hJ => Or.rec_on (Classical.em (J = ⊤)) (fun h => Or.inr h) fun h => Or.inl ⟨⟨h, hM.1 J hJ⟩⟩, hM.2⟩⟩⟩

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (x «expr ∉ » I)
/-- An ideal `I` equals its Jacobson radical if and only if every element outside `I`
also lies outside of a maximal ideal containing `I`. -/
theorem eq_jacobson_iff_not_mem : I.jacobson = I ↔ ∀ x _ : x ∉ I, ∃ M : Ideal R, (I ≤ M ∧ M.IsMaximal) ∧ x ∉ M := by
  constructor
  · intro h x hx
    erw [← h, mem_Inf] at hx
    push_neg  at hx
    exact hx
    
  · refine' fun h => le_antisymmₓ (fun x hx => _) le_jacobson
    contrapose hx
    erw [mem_Inf]
    push_neg
    exact h x hx
    

theorem map_jacobson_of_surjective {f : R →+* S} (hf : Function.Surjective f) :
    RingHom.ker f ≤ I → map f I.jacobson = (map f I).jacobson := by
  intro h
  unfold Ideal.jacobson
  have : ∀, ∀ J ∈ { J : Ideal R | I ≤ J ∧ J.IsMaximal }, ∀, f.ker ≤ J := fun J hJ => le_transₓ h hJ.left
  refine' trans (map_Inf hf this) (le_antisymmₓ _ _)
  · refine' Inf_le_Inf fun J hJ => ⟨comap f J, ⟨⟨le_comap_of_map_le hJ.1, _⟩, map_comap_of_surjective f hf J⟩⟩
    have : J.is_maximal := hJ.right
    exact comap_is_maximal_of_surjective f hf
    
  · refine' Inf_le_Inf_of_subset_insert_top fun j hj => hj.recOn fun J hJ => _
    rw [← hJ.2]
    cases' map_eq_top_or_is_maximal_of_surjective f hf hJ.left.right with htop hmax
    · exact htop.symm ▸ Set.mem_insert ⊤ _
      
    · exact Set.mem_insert_of_mem ⊤ ⟨map_mono hJ.1.1, hmax⟩
      
    

theorem map_jacobson_of_bijective {f : R →+* S} (hf : Function.Bijective f) : map f I.jacobson = (map f I).jacobson :=
  map_jacobson_of_surjective hf.right (le_transₓ (le_of_eqₓ (f.injective_iff_ker_eq_bot.1 hf.left)) bot_le)

theorem comap_jacobson {f : R →+* S} {K : Ideal S} :
    comap f K.jacobson = inf (comap f '' { J : Ideal S | K ≤ J ∧ J.IsMaximal }) :=
  trans (comap_Inf' f _) Inf_eq_infi.symm

theorem comap_jacobson_of_surjective {f : R →+* S} (hf : Function.Surjective f) {K : Ideal S} :
    comap f K.jacobson = (comap f K).jacobson := by
  unfold Ideal.jacobson
  refine' le_antisymmₓ _ _
  · refine' le_transₓ (comap_mono (le_of_eqₓ (trans top_inf_eq.symm Inf_insert.symm))) _
    rw [comap_Inf', Inf_eq_infi]
    refine' infi_le_infi_of_subset fun J hJ => _
    have : comap f (map f J) = J :=
      trans (comap_map_of_surjective f hf J)
        (le_antisymmₓ (sup_le_iff.2 ⟨le_of_eqₓ rfl, le_transₓ (comap_mono bot_le) hJ.left⟩) le_sup_left)
    cases' map_eq_top_or_is_maximal_of_surjective _ hf hJ.right with htop hmax
    · refine' ⟨⊤, ⟨Set.mem_insert ⊤ _, htop ▸ this⟩⟩
      
    · refine' ⟨map f J, ⟨Set.mem_insert_of_mem _ ⟨le_map_of_comap_le_of_surjective f hf hJ.1, hmax⟩, this⟩⟩
      
    
  · rw [comap_Inf]
    refine' le_infi_iff.2 fun J => le_infi_iff.2 fun hJ => _
    have : J.is_maximal := hJ.right
    refine' Inf_le ⟨comap_mono hJ.left, comap_is_maximal_of_surjective _ hf⟩
    

theorem mem_jacobson_bot {x : R} : x ∈ jacobson (⊥ : Ideal R) ↔ ∀ y, IsUnit (x * y + 1) :=
  ⟨fun hx y =>
    let ⟨z, hz⟩ := (mem_jacobson_iff.1 hx) y
    is_unit_iff_exists_inv.2
      ⟨z, by
        rwa [add_mulₓ, one_mulₓ, ← sub_eq_zero]⟩,
    fun h =>
    mem_jacobson_iff.mpr fun y =>
      let ⟨b, hb⟩ := is_unit_iff_exists_inv.1 (h y)
      ⟨b,
        (Submodule.mem_bot R).2
          (hb ▸ by
            ring)⟩⟩

/-- An ideal `I` of `R` is equal to its Jacobson radical if and only if
the Jacobson radical of the quotient ring `R/I` is the zero ideal -/
theorem jacobson_eq_iff_jacobson_quotient_eq_bot : I.jacobson = I ↔ jacobson (⊥ : Ideal (R ⧸ I)) = ⊥ := by
  have hf : Function.Surjective (Quotientₓ.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    replace h := congr_argₓ (map (Quotientₓ.mk I)) h
    rw [map_jacobson_of_surjective hf (le_of_eqₓ mk_ker)] at h
    simpa using h
    
  · intro h
    replace h := congr_argₓ (comap (Quotientₓ.mk I)) h
    rw [comap_jacobson_of_surjective hf, ← (Quotientₓ.mk I).ker_eq_comap_bot] at h
    simpa using h
    

/-- The standard radical and Jacobson radical of an ideal `I` of `R` are equal if and only if
the nilradical and Jacobson radical of the quotient ring `R/I` coincide -/
theorem radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot :
    I.radical = I.jacobson ↔ radical (⊥ : Ideal (R ⧸ I)) = jacobson ⊥ := by
  have hf : Function.Surjective (Quotientₓ.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    have := congr_argₓ (map (Quotientₓ.mk I)) h
    rw [map_radical_of_surjective hf (le_of_eqₓ mk_ker), map_jacobson_of_surjective hf (le_of_eqₓ mk_ker)] at this
    simpa using this
    
  · intro h
    have := congr_argₓ (comap (Quotientₓ.mk I)) h
    rw [comap_radical, comap_jacobson_of_surjective hf, ← (Quotientₓ.mk I).ker_eq_comap_bot] at this
    simpa using this
    

@[mono]
theorem jacobson_mono {I J : Ideal R} : I ≤ J → I.jacobson ≤ J.jacobson := by
  intro h x hx
  erw [mem_Inf] at hx⊢
  exact fun K ⟨hK, hK_max⟩ => hx ⟨trans h hK, hK_max⟩

theorem jacobson_radical_eq_jacobson : I.radical.jacobson = I.jacobson :=
  le_antisymmₓ
    (le_transₓ (le_of_eqₓ (congr_argₓ jacobson (radical_eq_Inf I)))
      (Inf_le_Inf fun J hJ => ⟨Inf_le ⟨hJ.1, hJ.2.IsPrime⟩, hJ.2⟩))
    (jacobson_mono le_radical)

end Jacobson

section Polynomial

open Polynomial

theorem jacobson_bot_polynomial_le_Inf_map_maximal :
    jacobson (⊥ : Ideal R[X]) ≤ inf (map c '' { J : Ideal R | J.IsMaximal }) := by
  refine' le_Inf fun J => exists_imp_distrib.2 fun j hj => _
  have : j.is_maximal := hj.1
  refine' trans (jacobson_mono bot_le) (le_of_eqₓ _ : J.jacobson ≤ J)
  suffices (⊥ : Ideal (Polynomial (R ⧸ j))).jacobson = ⊥ by
    rw [← hj.2, jacobson_eq_iff_jacobson_quotient_eq_bot]
    replace this := congr_argₓ (map (polynomial_quotient_equiv_quotient_polynomial j).toRingHom) this
    rwa [map_jacobson_of_bijective _, map_bot] at this
    exact RingEquiv.bijective (polynomial_quotient_equiv_quotient_polynomial j)
  refine' eq_bot_iff.2 fun f hf => _
  simpa [(fun hX => by
      simpa using congr_argₓ (fun f => coeff f 1) hX : (X : (R ⧸ j)[X]) ≠ 0)] using
    eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit ((mem_jacobson_bot.1 hf) X))

theorem jacobson_bot_polynomial_of_jacobson_bot (h : jacobson (⊥ : Ideal R) = ⊥) : jacobson (⊥ : Ideal R[X]) = ⊥ := by
  refine' eq_bot_iff.2 (le_transₓ jacobson_bot_polynomial_le_Inf_map_maximal _)
  refine' fun f hf => (Submodule.mem_bot _).2 (Polynomial.ext fun n => trans _ (coeff_zero n).symm)
  suffices f.coeff n ∈ Ideal.jacobson ⊥ by
    rwa [h, Submodule.mem_bot] at this
  exact mem_Inf.2 fun j hj => (mem_map_C_iff.1 ((mem_Inf.1 hf) ⟨j, ⟨hj.2, rfl⟩⟩)) n

end Polynomial

section IsLocal

/-- An ideal `I` is local iff its Jacobson radical is maximal. -/
class IsLocal (I : Ideal R) : Prop where
  out : IsMaximal (jacobson I)

theorem is_local_iff {I : Ideal R} : IsLocal I ↔ IsMaximal (jacobson I) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem is_local_of_is_maximal_radical {I : Ideal R} (hi : IsMaximal (radical I)) : IsLocal I :=
  ⟨have : radical I = jacobson I :=
      le_antisymmₓ (le_Inf fun M ⟨him, hm⟩ => hm.IsPrime.radical_le_iff.2 him) (Inf_le ⟨le_radical, hi⟩)
    show IsMaximal (jacobson I) from this ▸ hi⟩

theorem IsLocal.le_jacobson {I J : Ideal R} (hi : IsLocal I) (hij : I ≤ J) (hj : J ≠ ⊤) : J ≤ jacobson I :=
  let ⟨M, hm, hjm⟩ := exists_le_maximal J hj
  le_transₓ hjm <| le_of_eqₓ <| Eq.symm <| hi.1.eq_of_le hm.1.1 <| Inf_le ⟨le_transₓ hij hjm, hm⟩

theorem IsLocal.mem_jacobson_or_exists_inv {I : Ideal R} (hi : IsLocal I) (x : R) :
    x ∈ jacobson I ∨ ∃ y, y * x - 1 ∈ I :=
  Classical.by_cases
    (fun h : I⊔span {x} = ⊤ =>
      let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
      let ⟨r, hr⟩ := mem_span_singleton.1 hq
      Or.inr
        ⟨r, by
          rw [← hpq, mul_comm, ← hr, ← neg_sub, add_sub_cancel] <;> exact I.neg_mem hpi⟩)
    fun h : I⊔span {x} ≠ ⊤ =>
    Or.inl <| le_transₓ le_sup_right (hi.le_jacobson le_sup_left h) <| mem_span_singleton.2 <| dvd_refl x

end IsLocal

theorem is_primary_of_is_maximal_radical {I : Ideal R} (hi : IsMaximal (radical I)) : IsPrimary I :=
  have : radical I = jacobson I :=
    le_antisymmₓ (le_Inf fun M ⟨him, hm⟩ => hm.IsPrime.radical_le_iff.2 him) (Inf_le ⟨le_radical, hi⟩)
  ⟨ne_top_of_lt <| lt_of_le_of_ltₓ le_radical (lt_top_iff_ne_top.2 hi.1.1), fun x y hxy =>
    ((is_local_of_is_maximal_radical hi).mem_jacobson_or_exists_inv y).symm.imp
      (fun ⟨z, hz⟩ => by
        rw [← mul_oneₓ x, ← sub_sub_cancel (z * y) 1, mul_sub, mul_left_commₓ] <;>
          exact I.sub_mem (I.mul_mem_left _ hxy) (I.mul_mem_left _ hz))
      (this ▸ id)⟩

end Ideal

