/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathbin.CategoryTheory.Sites.Sheafification
import Mathbin.CategoryTheory.Sites.Whiskering

/-!

In this file, we prove that the plus functor is compatible with functors which
preserve the correct limits and colimits.

See `category_theory/sites/compatible_sheafification` for the compatibility
of sheafification, which follows easily from the content in this file.

-/


namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w₁ w₂ v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {D : Type w₁} [Category.{max v u} D]

variable {E : Type w₂} [Category.{max v u} E]

variable (F : D ⥤ E)

noncomputable section

variable [∀ (α β : Type max v u) (fst snd : β → α), HasLimitsOfShape (WalkingMulticospan fst snd) D]

variable [∀ (α β : Type max v u) (fst snd : β → α), HasLimitsOfShape (WalkingMulticospan fst snd) E]

variable [∀ (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]

variable (P : Cᵒᵖ ⥤ D)

/-- The diagram used to define `P⁺`, composed with `F`, is isomorphic
to the diagram used to define `P ⋙ F`. -/
def diagramCompIso (X : C) : J.diagram P X ⋙ F ≅ J.diagram (P ⋙ F) X :=
  NatIso.ofComponents
    (fun W => by
      refine' _ ≪≫ has_limit.iso_of_nat_iso (W.unop.multicospan_comp _ _).symm
      refine' (is_limit_of_preserves F (limit.is_limit _)).conePointUniqueUpToIso (limit.is_limit _))
    (by
      intro A B f
      ext
      dsimp'
      simp only [functor.map_cone_π_app, multiequalizer.multifork_π_app_left, iso.symm_hom, multiequalizer.lift_ι,
        eq_to_hom_refl, category.comp_id, limit.cone_point_unique_up_to_iso_hom_comp,
        grothendieck_topology.cover.multicospan_comp_hom_inv_left, has_limit.iso_of_nat_iso_hom_π, category.assoc]
      simp only [← F.map_comp, multiequalizer.lift_ι])

@[simp, reassoc]
theorem diagram_comp_iso_hom_ι (X : C) (W : (J.cover X)ᵒᵖ) (i : W.unop.arrow) :
    (J.diagramCompIso F P X).Hom.app W ≫ multiequalizer.ι _ i = F.map (multiequalizer.ι _ _) := by
  delta' diagram_comp_iso
  dsimp'
  simp

variable [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ D]

variable [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ E]

variable [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ F]

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`. -/
def plusCompIso : J.plusObj P ⋙ F ≅ J.plusObj (P ⋙ F) :=
  NatIso.ofComponents
    (fun X => by
      refine' _ ≪≫ has_colimit.iso_of_nat_iso (J.diagram_comp_iso F P X.unop)
      refine'
        (is_colimit_of_preserves F (colimit.is_colimit (J.diagram P (unop X)))).coconePointUniqueUpToIso
          (colimit.is_colimit _))
    (by
      intro X Y f
      apply (is_colimit_of_preserves F (colimit.is_colimit (J.diagram P X.unop))).hom_ext
      intro W
      dsimp' [plus_obj, plus_map]
      simp only [functor.map_comp, category.assoc]
      slice_rhs 1 2 => erw [(is_colimit_of_preserves F (colimit.is_colimit (J.diagram P X.unop))).fac]
      slice_lhs 1 3 =>
        simp only [←
          F.map_comp]dsimp [colim_map, is_colimit.map,
          colimit.pre]simp only [colimit.ι_desc_assoc,
          colimit.ι_desc]dsimp [cocones.precompose]rw [category.assoc,
          colimit.ι_desc]dsimp [cocone.whisker]rw [F.map_comp]
      simp only [category.assoc]
      slice_lhs 2 3 => erw [(is_colimit_of_preserves F (colimit.is_colimit (J.diagram P Y.unop))).fac]
      dsimp'
      simp only [has_colimit.iso_of_nat_iso_ι_hom_assoc, grothendieck_topology.diagram_pullback_app, colimit.ι_pre,
        has_colimit.iso_of_nat_iso_ι_hom, ι_colim_map_assoc]
      simp only [← category.assoc]
      congr 1
      ext
      dsimp'
      simp only [category.assoc]
      erw [multiequalizer.lift_ι, diagram_comp_iso_hom_ι, diagram_comp_iso_hom_ι, ← F.map_comp, multiequalizer.lift_ι])

@[simp, reassoc]
theorem ι_plus_comp_iso_hom (X) (W) :
    F.map (colimit.ι _ W) ≫ (J.plusCompIso F P).Hom.app X = (J.diagramCompIso F P X.unop).Hom.app W ≫ colimit.ι _ W :=
  by
  delta' diagram_comp_iso plus_comp_iso
  dsimp' [is_colimit.cocone_point_unique_up_to_iso]
  simp only [← category.assoc]
  erw [(is_colimit_of_preserves F (colimit.is_colimit (J.diagram P (unop X)))).fac]
  dsimp'
  simp

@[simp, reassoc]
theorem plus_comp_iso_whisker_left {F G : D ⥤ E} (η : F ⟶ G) (P : Cᵒᵖ ⥤ D)
    [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ F]
    [∀ (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
    [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ G]
    [∀ (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan G] :
    whiskerLeft _ η ≫ (J.plusCompIso G P).Hom = (J.plusCompIso F P).Hom ≫ J.plusMap (whiskerLeft _ η) := by
  ext X
  apply (is_colimit_of_preserves F (colimit.is_colimit (J.diagram P X.unop))).hom_ext
  intro W
  dsimp' [plus_obj, plus_map]
  simp only [ι_plus_comp_iso_hom, ι_colim_map, whisker_left_app, ι_plus_comp_iso_hom_assoc, nat_trans.naturality_assoc,
    grothendieck_topology.diagram_nat_trans_app]
  simp only [← category.assoc]
  congr 1
  ext
  dsimp'
  simpa

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `F`. -/
@[simps hom_app inv_app]
def plusFunctorWhiskerLeftIso (P : Cᵒᵖ ⥤ D) [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.plusObj P) ≅ (whiskeringLeft _ _ _).obj P ⋙ J.plusFunctor E :=
  (NatIso.ofComponents fun X => plusCompIso _ _ _) fun F G η => plus_comp_iso_whisker_left _ _ _

@[simp, reassoc]
theorem plus_comp_iso_whisker_right {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    whiskerRight (J.plusMap η) F ≫ (J.plusCompIso F Q).Hom = (J.plusCompIso F P).Hom ≫ J.plusMap (whiskerRight η F) :=
  by
  ext X
  apply (is_colimit_of_preserves F (colimit.is_colimit (J.diagram P X.unop))).hom_ext
  intro W
  dsimp' [plus_obj, plus_map]
  simp only [ι_colim_map, whisker_right_app, ι_plus_comp_iso_hom_assoc, grothendieck_topology.diagram_nat_trans_app]
  simp only [← category.assoc, ← F.map_comp]
  dsimp' [colim_map, is_colimit.map]
  simp only [colimit.ι_desc]
  dsimp' [cocones.precompose]
  simp only [functor.map_comp, category.assoc, ι_plus_comp_iso_hom]
  simp only [← category.assoc]
  congr 1
  ext
  dsimp'
  simp only [diagram_comp_iso_hom_ι_assoc, multiequalizer.lift_ι, diagram_comp_iso_hom_ι, category.assoc]
  simp only [← F.map_comp, multiequalizer.lift_ι]

/-- The isomorphism between `P⁺ ⋙ F` and `(P ⋙ F)⁺`, functorially in `P`. -/
@[simps hom_app inv_app]
def plusFunctorWhiskerRightIso :
    J.plusFunctor D ⋙ (whiskeringRight _ _ _).obj F ≅ (whiskeringRight _ _ _).obj F ⋙ J.plusFunctor E :=
  (NatIso.ofComponents fun P => J.plusCompIso _ _) fun P Q η => plus_comp_iso_whisker_right _ _ _

@[simp, reassoc]
theorem whisker_right_to_plus_comp_plus_comp_iso_hom :
    whiskerRight (J.toPlus _) _ ≫ (J.plusCompIso F P).Hom = J.toPlus _ := by
  ext
  dsimp' [to_plus]
  simp only [ι_plus_comp_iso_hom, functor.map_comp, category.assoc]
  simp only [← category.assoc]
  congr 1
  ext
  delta' cover.to_multiequalizer
  simp only [diagram_comp_iso_hom_ι, category.assoc, ← F.map_comp]
  erw [multiequalizer.lift_ι, multiequalizer.lift_ι]
  rfl

@[simp]
theorem to_plus_comp_plus_comp_iso_inv : J.toPlus _ ≫ (J.plusCompIso F P).inv = whiskerRight (J.toPlus _) _ := by
  simp [iso.comp_inv_eq]

theorem plus_comp_iso_inv_eq_plus_lift (hP : Presheaf.IsSheaf J (J.plusObj P ⋙ F)) :
    (J.plusCompIso F P).inv = J.plusLift (whiskerRight (J.toPlus _) _) hP := by
  apply J.plus_lift_unique
  simp [iso.comp_inv_eq]

end CategoryTheory.GrothendieckTopology

