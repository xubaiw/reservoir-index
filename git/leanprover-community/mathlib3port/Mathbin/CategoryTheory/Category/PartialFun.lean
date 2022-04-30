/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.CategoryTheory.Category.Pointed
import Mathbin.Data.Pfun

/-!
# The category of types with partial functions

This defines `PartialFun`, the category of types equipped with partial functions.

This category is classically equivalent to the category of pointed types. The reason it doesn't hold
constructively stems from the difference between `part` and `option`. Both can model partial
functions, but the latter forces a decidable domain.

Precisely, `PartialFun_to_Pointed` turns a partial function `α →. β` into a function
`option α → option β` by sending to `none` the undefined values (and `none` to `none`). But being
defined is (generally) undecidable while being sent to `none` is decidable. So it can't be
constructive.

## References

* [nLab, *The category of sets and partial functions*]
  (https://ncatlab.org/nlab/show/partial+function)
-/


open CategoryTheory Option

universe u

variable {α β : Type _}

/-- The category of types equipped with partial functions. -/
def PartialFun : Type _ :=
  Type _

namespace PartialFun

instance : CoeSort PartialFun (Type _) :=
  ⟨id⟩

/-- Turns a type into a `PartialFun`. -/
@[nolint has_inhabited_instance]
def of : Type _ → PartialFun :=
  id

@[simp]
theorem coe_of (X : Type _) : ↥(of X) = X :=
  rfl

instance : Inhabited PartialFun :=
  ⟨Type _⟩

instance largeCategory : LargeCategory.{u} PartialFun where
  Hom := Pfun
  id := Pfun.id
  comp := fun X Y Z f g => g.comp f
  id_comp' := @Pfun.comp_id
  comp_id' := @Pfun.id_comp
  assoc' := fun W X Y Z _ _ _ => (Pfun.comp_assoc _ _ _).symm

/-- Constructs a partial function isomorphism between types from an equivalence between them. -/
@[simps]
def Iso.mk {α β : PartialFun.{u}} (e : α ≃ β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := (Pfun.coe_comp _ _).symm.trans <| congr_argₓ coe e.symm_comp_self
  inv_hom_id' := (Pfun.coe_comp _ _).symm.trans <| congr_argₓ coe e.self_comp_symm

end PartialFun

/-- The forgetful functor from `Type` to `PartialFun` which forgets that the maps are total. -/
def typeToPartialFun : Type u ⥤ PartialFun where
  obj := id
  map := @Pfun.lift
  map_comp' := fun _ _ _ _ _ => Pfun.coe_comp _ _

instance : Faithful typeToPartialFun :=
  ⟨fun X Y => Pfun.coe_injective⟩

/-- The functor which deletes the point of a pointed type. In return, this makes the maps partial.
This the computable part of the equivalence `PartialFun_equiv_Pointed`. -/
def pointedToPartialFun : Pointed.{u} ⥤ PartialFun where
  obj := fun X => { x : X // x ≠ X.point }
  map := fun X Y f => Pfun.toSubtype _ f.toFun ∘ Subtype.val
  map_id' := fun X => Pfun.ext fun a b => Pfun.mem_to_subtype_iff.trans (Subtype.coe_inj.trans Part.mem_some_iff.symm)
  map_comp' := fun X Y Z f g =>
    Pfun.ext fun a c => by
      refine' (pfun.mem_to_subtype_iff.trans _).trans part.mem_bind_iff.symm
      simp_rw [Pfun.mem_to_subtype_iff, Subtype.exists]
      refine'
        ⟨fun h =>
          ⟨f.to_fun a, fun ha => c.2 <| h.trans ((congr_argₓ g.to_fun ha : g.to_fun _ = _).trans g.map_point), rfl, h⟩,
          _⟩
      rintro ⟨b, _, rfl : b = _, h⟩
      exact h

/-- The functor which maps undefined values to a new point. This makes the maps total and creates
pointed types. This the noncomputable part of the equivalence `PartialFun_equiv_Pointed`. It can't
be computable because `= option.none` is decidable while the domain of a general `part` isn't. -/
noncomputable def partialFunToPointed : PartialFun ⥤ Pointed := by
  classical <;>
    exact
      { obj := fun X => ⟨Option X, none⟩, map := fun X Y f => ⟨fun o => o.elim none fun a => (f a).toOption, rfl⟩,
        map_id' := fun X => Pointed.Hom.ext _ _ <| funext fun o => (Option.recOn o rfl) fun a => Part.some_to_option _,
        map_comp' := fun X Y Z f g =>
          Pointed.Hom.ext _ _ <| funext fun o => (Option.recOn o rfl) fun a => Part.bind_to_option _ _ }

/-- The equivalence induced by `PartialFun_to_Pointed` and `Pointed_to_PartialFun`.
`part.equiv_option` made functorial. -/
@[simps]
noncomputable def partialFunEquivPointed : PartialFun.{u} ≌ Pointed := by
  classical <;>
    exact
      equivalence.mk partialFunToPointed pointedToPartialFun
        ((nat_iso.of_components fun X =>
            PartialFun.Iso.mk
              { toFun := fun a => ⟨some a, some_ne_none a⟩, invFun := fun a => get <| ne_none_iff_is_some.1 a.2,
                left_inv := fun a => get_some _ _,
                right_inv := fun a => by
                  simp only [Subtype.val_eq_coe, some_get, Subtype.coe_eta] })
          fun X Y f =>
          Pfun.ext fun a b => by
            unfold_projs
            dsimp
            rw [Part.bind_some]
            refine' (part.mem_bind_iff.trans _).trans pfun.mem_to_subtype_iff.symm
            obtain ⟨b | b, hb⟩ := b
            · exact (hb rfl).elim
              
            dsimp
            simp_rw [Part.mem_some_iff, Subtype.mk_eq_mk, exists_prop, some_inj, exists_eq_right']
            refine' part.mem_to_option.symm.trans _
            convert eq_comm
            convert rfl)
        ((nat_iso.of_components fun X =>
            Pointed.Iso.mk
              { toFun := fun a => a.elim X.point Subtype.val,
                invFun := fun a => if h : a = X.point then none else some ⟨_, h⟩,
                left_inv := fun a =>
                  (Option.recOn a (dif_pos rfl)) fun a =>
                    (dif_neg a.2).trans <| by
                      simp only [Option.elim, Subtype.val_eq_coe, Subtype.coe_eta],
                right_inv := fun a => by
                  change Option.elim (dite _ _ _) _ _ = _
                  split_ifs
                  · rw [h]
                    rfl
                    
                  · rfl
                     }
              rfl)
          fun X Y f =>
          Pointed.Hom.ext _ _ <|
            funext fun a =>
              (Option.recOn a f.map_point.symm) fun a => by
                change Option.elim (Option.elim _ _ _) _ _ = _
                rw [Option.elim, Part.elim_to_option]
                split_ifs
                · rfl
                  
                · exact Eq.symm (of_not_not h)
                  )

/-- Forgetting that maps are total and making them total again by adding a point is the same as just
adding a point. -/
@[simps]
noncomputable def typeToPartialFunIsoPartialFunToPointed : typeToPartialFun ⋙ partialFunToPointed ≅ typeToPointed :=
  (NatIso.ofComponents fun X => { Hom := ⟨id, rfl⟩, inv := ⟨id, rfl⟩, hom_inv_id' := rfl, inv_hom_id' := rfl })
    fun X Y f =>
    Pointed.Hom.ext _ _ <|
      funext fun a =>
        (Option.recOn a rfl) fun a => by
          convert Part.some_to_option _

