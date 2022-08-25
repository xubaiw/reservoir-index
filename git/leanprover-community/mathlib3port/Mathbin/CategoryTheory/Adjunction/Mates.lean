/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Adjunction.Basic
import Mathbin.CategoryTheory.Conj

/-!
# Mate of natural transformations

This file establishes the bijection between the 2-cells

         L₁                  R₁
      C --→ D             C ←-- D
    G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
      E --→ F             E ←-- F
         L₂                  R₂

where `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, and shows that in the special case where `G,H` are identity then the
bijection preserves and reflects isomorphisms (i.e. we have bijections `(L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)`, and
if either side is an iso then the other side is as well).

On its own, this bijection is not particularly useful but it includes a number of interesting cases
as specializations.

For instance, this generalises the fact that adjunctions are unique (since if `L₁ ≅ L₂` then we
deduce `R₁ ≅ R₂`).
Another example arises from considering the square representing that a functor `H` preserves
products, in particular the morphism `HA ⨯ H- ⟶ H(A ⨯ -)`. Then provided `(A ⨯ -)` and `HA ⨯ -` have
left adjoints (for instance if the relevant categories are cartesian closed), the transferred
natural transformation is the exponential comparison morphism: `H(A ^ -) ⟶ HA ^ H-`.
Furthermore if `H` has a left adjoint `L`, this morphism is an isomorphism iff its mate
`L(HA ⨯ -) ⟶ A ⨯ L-` is an isomorphism, see
https://ncatlab.org/nlab/show/Frobenius+reciprocity#InCategoryTheory.
This also relates to Grothendieck's yoga of six operations, though this is not spelled out in
mathlib: https://ncatlab.org/nlab/show/six+operations.
-/


universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

section Square

variable {E : Type u₃} {F : Type u₄} [Category.{v₃} E] [Category.{v₄} F]

variable {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

include adj₁ adj₂

/-- Suppose we have a square of functors (where the top and bottom are adjunctions `L₁ ⊣ R₁` and
`L₂ ⊣ R₂` respectively).

      C ↔ D
    G ↓   ↓ H
      E ↔ F

Then we have a bijection between natural transformations `G ⋙ L₂ ⟶ L₁ ⋙ H` and
`R₁ ⋙ G ⟶ H ⋙ R₂`.
This can be seen as a bijection of the 2-cells:

         L₁                  R₁
      C --→ D             C ←-- D
    G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
      E --→ F             E ←-- F
         L₂                  R₂

Note that if one of the transformations is an iso, it does not imply the other is an iso.
-/
def transferNatTrans : (G ⋙ L₂ ⟶ L₁ ⋙ H) ≃ (R₁ ⋙ G ⟶ H ⋙ R₂) where
  toFun := fun h =>
    { app := fun X => adj₂.Unit.app _ ≫ R₂.map (h.app _ ≫ H.map (adj₁.counit.app _)),
      naturality' := fun X Y f => by
        dsimp'
        rw [assoc, ← R₂.map_comp, assoc, ← H.map_comp, ← adj₁.counit_naturality, H.map_comp, ← functor.comp_map L₁, ←
          h.naturality_assoc]
        simp }
  invFun := fun h =>
    { app := fun X => L₂.map (G.map (adj₁.Unit.app _) ≫ h.app _) ≫ adj₂.counit.app _,
      naturality' := fun X Y f => by
        dsimp'
        rw [← L₂.map_comp_assoc, ← G.map_comp_assoc, ← adj₁.unit_naturality, G.map_comp_assoc, ← functor.comp_map,
          h.naturality]
        simp }
  left_inv := fun h => by
    ext X
    dsimp'
    simp only [L₂.map_comp, assoc, adj₂.counit_naturality, adj₂.left_triangle_components_assoc, ← functor.comp_map G L₂,
      h.naturality_assoc, functor.comp_map L₁, ← H.map_comp, adj₁.left_triangle_components]
    dsimp'
    simp
  -- See library note [dsimp, simp].
  right_inv := fun h => by
    ext X
    dsimp'
    simp [-functor.comp_map, ← functor.comp_map H, functor.comp_map R₁, -nat_trans.naturality, ← h.naturality,
      -functor.map_comp, ← functor.map_comp_assoc G, R₂.map_comp]

theorem transfer_nat_trans_counit (f : G ⋙ L₂ ⟶ L₁ ⋙ H) (Y : D) :
    L₂.map ((transferNatTrans adj₁ adj₂ f).app _) ≫ adj₂.counit.app _ = f.app _ ≫ H.map (adj₁.counit.app Y) := by
  erw [functor.map_comp]
  simp

theorem unit_transfer_nat_trans (f : G ⋙ L₂ ⟶ L₁ ⋙ H) (X : C) :
    G.map (adj₁.Unit.app X) ≫ (transferNatTrans adj₁ adj₂ f).app _ = adj₂.Unit.app _ ≫ R₂.map (f.app _) := by
  dsimp' [transfer_nat_trans]
  rw [← adj₂.unit_naturality_assoc, ← R₂.map_comp, ← functor.comp_map G L₂, f.naturality_assoc, functor.comp_map, ←
    H.map_comp]
  dsimp'
  simp

-- See library note [dsimp, simp]
end Square

section Self

variable {L₁ L₂ L₃ : C ⥤ D} {R₁ R₂ R₃ : D ⥤ C}

variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

/-- Given two adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` both between categories `C`, `D`, there is a
bijection between natural transformations `L₂ ⟶ L₁` and natural transformations `R₁ ⟶ R₂`.
This is defined as a special case of `transfer_nat_trans`, where the two "vertical" functors are
identity.
TODO: Generalise to when the two vertical functors are equivalences rather than being exactly `𝟭`.

Furthermore, this bijection preserves (and reflects) isomorphisms, i.e. a transformation is an iso
iff its image under the bijection is an iso, see eg `category_theory.transfer_nat_trans_self_iso`.
This is in contrast to the general case `transfer_nat_trans` which does not in general have this
property.
-/
def transferNatTransSelf : (L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂) :=
  calc
    (L₂ ⟶ L₁) ≃ _ := (Iso.homCongr L₂.leftUnitor L₁.rightUnitor).symm
    _ ≃ _ := transferNatTrans adj₁ adj₂
    _ ≃ (R₁ ⟶ R₂) := R₁.rightUnitor.homCongr R₂.leftUnitor
    

theorem transfer_nat_trans_self_counit (f : L₂ ⟶ L₁) (X) :
    L₂.map ((transferNatTransSelf adj₁ adj₂ f).app _) ≫ adj₂.counit.app X = f.app _ ≫ adj₁.counit.app X := by
  dsimp' [transfer_nat_trans_self]
  rw [id_comp, comp_id]
  have := transfer_nat_trans_counit adj₁ adj₂ (L₂.left_unitor.hom ≫ f ≫ L₁.right_unitor.inv) X
  dsimp'  at this
  rw [this]
  simp

theorem unit_transfer_nat_trans_self (f : L₂ ⟶ L₁) (X) :
    adj₁.Unit.app _ ≫ (transferNatTransSelf adj₁ adj₂ f).app _ = adj₂.Unit.app X ≫ Functor.map _ (f.app _) := by
  dsimp' [transfer_nat_trans_self]
  rw [id_comp, comp_id]
  have := unit_transfer_nat_trans adj₁ adj₂ (L₂.left_unitor.hom ≫ f ≫ L₁.right_unitor.inv) X
  dsimp'  at this
  rw [this]
  simp

@[simp]
theorem transfer_nat_trans_self_id : transferNatTransSelf adj₁ adj₁ (𝟙 _) = 𝟙 _ := by
  ext
  dsimp' [transfer_nat_trans_self, transfer_nat_trans]
  simp

-- See library note [dsimp, simp]
@[simp]
theorem transfer_nat_trans_self_symm_id : (transferNatTransSelf adj₁ adj₁).symm (𝟙 _) = 𝟙 _ := by
  rw [Equivₓ.symm_apply_eq]
  simp

theorem transfer_nat_trans_self_comp (f g) :
    transferNatTransSelf adj₁ adj₂ f ≫ transferNatTransSelf adj₂ adj₃ g = transferNatTransSelf adj₁ adj₃ (g ≫ f) := by
  ext
  dsimp' [transfer_nat_trans_self, transfer_nat_trans]
  simp only [id_comp, comp_id]
  rw [← adj₃.unit_naturality_assoc, ← R₃.map_comp, g.naturality_assoc, L₂.map_comp, assoc, adj₂.counit_naturality,
    adj₂.left_triangle_components_assoc, assoc]

theorem transfer_nat_trans_self_adjunction_id {L R : C ⥤ C} (adj : L ⊣ R) (f : 𝟭 C ⟶ L) (X : C) :
    (transferNatTransSelf adj Adjunction.id f).app X = f.app (R.obj X) ≫ adj.counit.app X := by
  dsimp' [transfer_nat_trans_self, transfer_nat_trans, adjunction.id]
  simp only [comp_id, id_comp]

theorem transfer_nat_trans_self_adjunction_id_symm {L R : C ⥤ C} (adj : L ⊣ R) (g : R ⟶ 𝟭 C) (X : C) :
    ((transferNatTransSelf adj Adjunction.id).symm g).app X = adj.Unit.app X ≫ g.app (L.obj X) := by
  dsimp' [transfer_nat_trans_self, transfer_nat_trans, adjunction.id]
  simp only [comp_id, id_comp]

theorem transfer_nat_trans_self_symm_comp (f g) :
    (transferNatTransSelf adj₂ adj₁).symm f ≫ (transferNatTransSelf adj₃ adj₂).symm g =
      (transferNatTransSelf adj₃ adj₁).symm (g ≫ f) :=
  by
  rw [Equivₓ.eq_symm_apply, ← transfer_nat_trans_self_comp _ adj₂]
  simp

theorem transfer_nat_trans_self_comm {f g} (gf : g ≫ f = 𝟙 _) :
    transferNatTransSelf adj₁ adj₂ f ≫ transferNatTransSelf adj₂ adj₁ g = 𝟙 _ := by
  rw [transfer_nat_trans_self_comp, gf, transfer_nat_trans_self_id]

theorem transfer_nat_trans_self_symm_comm {f g} (gf : g ≫ f = 𝟙 _) :
    (transferNatTransSelf adj₁ adj₂).symm f ≫ (transferNatTransSelf adj₂ adj₁).symm g = 𝟙 _ := by
  rw [transfer_nat_trans_self_symm_comp, gf, transfer_nat_trans_self_symm_id]

/-- If `f` is an isomorphism, then the transferred natural transformation is an isomorphism.
The converse is given in `transfer_nat_trans_self_of_iso`.
-/
instance transfer_nat_trans_self_iso (f : L₂ ⟶ L₁) [IsIso f] : IsIso (transferNatTransSelf adj₁ adj₂ f) :=
  ⟨⟨transferNatTransSelf adj₂ adj₁ (inv f),
      ⟨transfer_nat_trans_self_comm _ _
          (by
            simp ),
        transfer_nat_trans_self_comm _ _
          (by
            simp )⟩⟩⟩

/-- If `f` is an isomorphism, then the un-transferred natural transformation is an isomorphism.
The converse is given in `transfer_nat_trans_self_symm_of_iso`.
-/
instance transfer_nat_trans_self_symm_iso (f : R₁ ⟶ R₂) [IsIso f] : IsIso ((transferNatTransSelf adj₁ adj₂).symm f) :=
  ⟨⟨(transferNatTransSelf adj₂ adj₁).symm (inv f),
      ⟨transfer_nat_trans_self_symm_comm _ _
          (by
            simp ),
        transfer_nat_trans_self_symm_comm _ _
          (by
            simp )⟩⟩⟩

/-- If `f` is a natural transformation whose transferred natural transformation is an isomorphism,
then `f` is an isomorphism.
The converse is given in `transfer_nat_trans_self_iso`.
-/
theorem transfer_nat_trans_self_of_iso (f : L₂ ⟶ L₁) [IsIso (transferNatTransSelf adj₁ adj₂ f)] : IsIso f := by
  suffices is_iso ((transfer_nat_trans_self adj₁ adj₂).symm (transfer_nat_trans_self adj₁ adj₂ f)) by
    simpa using this
  infer_instance

/-- If `f` is a natural transformation whose un-transferred natural transformation is an isomorphism,
then `f` is an isomorphism.
The converse is given in `transfer_nat_trans_self_symm_iso`.
-/
theorem transfer_nat_trans_self_symm_of_iso (f : R₁ ⟶ R₂) [IsIso ((transferNatTransSelf adj₁ adj₂).symm f)] : IsIso f :=
  by
  suffices is_iso ((transfer_nat_trans_self adj₁ adj₂) ((transfer_nat_trans_self adj₁ adj₂).symm f)) by
    simpa using this
  infer_instance

end Self

end CategoryTheory

