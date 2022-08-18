/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathbin.Algebra.Module.Pid
import Mathbin.Data.Zmod.Quotient

/-!
# Structure of finite(ly generated) abelian groups

* `add_comm_group.equiv_free_prod_direct_sum_zmod` : Any finitely generated abelian group is the
  product of a power of `ℤ` and a direct sum of some `zmod (p i ^ e i)` for some prime powers
  `p i ^ e i`.
* `add_comm_group.equiv_direct_sum_zmod_of_fintype` : Any finite abelian group is a direct sum of
  some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`.

-/


open DirectSum

universe u

namespace Module

variable (M : Type u)

theorem finite_of_fg_torsion [AddCommGroupₓ M] [Module ℤ M] [Module.Finite ℤ M] (hM : Module.IsTorsion ℤ M) :
    Finite M := by
  rcases Module.equiv_direct_sum_of_is_torsion hM with ⟨ι, _, p, h, e, ⟨l⟩⟩
  haveI : ∀ i : ι, Fact <| 0 < (p i ^ e i).natAbs := fun i =>
    Fact.mk <| Int.nat_abs_pos_of_ne_zero <| pow_ne_zero (e i) (h i).ne_zero
  haveI : ∀ i : ι, _root_.finite <| ℤ ⧸ Submodule.span ℤ {p i ^ e i} := fun i =>
    Finite.of_equiv _ (p i ^ e i).quotientSpanEquivZmod.symm.toEquiv
  haveI : _root_.finite (⨁ i, ℤ ⧸ (Submodule.span ℤ {p i ^ e i} : Submodule ℤ ℤ)) :=
    Finite.of_equiv _ dfinsupp.equiv_fun_on_fintype.symm
  exact Finite.of_equiv _ l.symm.to_equiv

end Module

variable (G : Type u)

namespace AddCommGroupₓ

variable [AddCommGroupₓ G]

/-- **Structure theorem of finitely generated abelian groups** : Any finitely generated abelian
group is the product of a power of `ℤ` and a direct sum of some `zmod (p i ^ e i)` for some
prime powers `p i ^ e i`. -/
theorem equiv_free_prod_direct_sum_zmod [hG : AddGroupₓ.Fg G] :
    ∃ (n : ℕ)(ι : Type)(_ : Fintype ι)(p : ι → ℕ)(_ : ∀ i, Nat.Prime <| p i)(e : ι → ℕ),
      Nonempty <| G ≃+ (Finₓ n →₀ ℤ) × ⨁ i : ι, Zmod (p i ^ e i) :=
  by
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ :=
    @Module.equiv_free_prod_direct_sum _ _ _ _ _ _ _ (module.finite.iff_add_group_fg.mpr hG)
  refine' ⟨n, ι, fι, fun i => (p i).natAbs, fun i => _, e, ⟨_⟩⟩
  · rw [← Int.prime_iff_nat_abs_prime, ← GcdMonoid.irreducible_iff_prime]
    exact hp i
    
  exact
    f.to_add_equiv.trans
      ((AddEquiv.refl _).prodCongr <|
        Dfinsupp.mapRange.addEquiv fun i =>
          ((Int.quotientSpanEquivZmod _).trans <| Zmod.ringEquivCongr <| (p i).nat_abs_pow _).toAddEquiv)

/-- **Structure theorem of finite abelian groups** : Any finite abelian group is a direct sum of
some `zmod (p i ^ e i)` for some prime powers `p i ^ e i`. -/
theorem equiv_direct_sum_zmod_of_fintype [Finite G] :
    ∃ (ι : Type)(_ : Fintype ι)(p : ι → ℕ)(_ : ∀ i, Nat.Prime <| p i)(e : ι → ℕ),
      Nonempty <| G ≃+ ⨁ i : ι, Zmod (p i ^ e i) :=
  by
  cases nonempty_fintype G
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := equiv_free_prod_direct_sum_zmod G
  cases n
  · exact ⟨ι, fι, p, hp, e, ⟨f.trans AddEquiv.uniqueProd⟩⟩
    
  · haveI := @Fintype.prodLeft _ _ _ (Fintype.ofEquiv G f.to_equiv) _
    exact
      ((Fintype.ofSurjective fun f : Finₓ n.succ →₀ ℤ => f 0) fun a =>
            ⟨Finsupp.single 0 a, Finsupp.single_eq_same⟩).False.elim
    

theorem finite_of_fg_torsion [hG' : AddGroupₓ.Fg G] (hG : AddMonoidₓ.IsTorsion G) : Finite G :=
  @Module.finite_of_fg_torsion _ _ _ (Module.Finite.iff_add_group_fg.mpr hG') <|
    AddMonoidₓ.is_torsion_iff_is_torsion_int.mp hG

end AddCommGroupₓ

namespace CommGroupₓ

theorem finite_of_fg_torsion [CommGroupₓ G] [Groupₓ.Fg G] (hG : Monoidₓ.IsTorsion G) : Finite G :=
  @Finite.of_equiv _ _ (AddCommGroupₓ.finite_of_fg_torsion (Additive G) hG) Multiplicative.ofAdd

end CommGroupₓ

