/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving binary products

Constructions to relate the notions of preserving binary products and reflecting binary products
to concrete binary fans.

In particular, we show that `prod_comparison G X Y` is an isomorphism iff `G` preserves
the product of `X` and `Y`.
-/


noncomputable section

universe v u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v} C]

variable {D : Type u₂} [Category.{v} D]

variable (G : C ⥤ D)

namespace CategoryTheory.Limits

section

variable {P X Y Z : C} (f : P ⟶ X) (g : P ⟶ Y)

/-- The map of a binary fan is a limit iff the fork consisting of the mapped morphisms is a limit. This
essentially lets us commute `binary_fan.mk` with `functor.map_cone`.
-/
def isLimitMapConeBinaryFanEquiv :
    IsLimit (G.mapCone (BinaryFan.mk f g)) ≃ IsLimit (BinaryFan.mk (G.map f) (G.map g)) :=
  (IsLimit.postcomposeHomEquiv (diagramIsoPair.{v} _) _).symm.trans
    (IsLimit.equivIsoLimit
      (Cones.ext (Iso.refl _)
        (by
          rintro (_ | _)
          tidy)))

/-- The property of preserving products expressed in terms of binary fans. -/
def mapIsLimitOfPreservesOfIsLimit [PreservesLimit (pair X Y) G] (l : IsLimit (BinaryFan.mk f g)) :
    IsLimit (BinaryFan.mk (G.map f) (G.map g)) :=
  isLimitMapConeBinaryFanEquiv G f g (PreservesLimit.preserves l)

/-- The property of reflecting products expressed in terms of binary fans. -/
def isLimitOfReflectsOfMapIsLimit [ReflectsLimit (pair X Y) G] (l : IsLimit (BinaryFan.mk (G.map f) (G.map g))) :
    IsLimit (BinaryFan.mk f g) :=
  ReflectsLimit.reflects ((isLimitMapConeBinaryFanEquiv G f g).symm l)

variable (X Y) [HasBinaryProduct X Y]

/-- If `G` preserves binary products and `C` has them, then the binary fan constructed of the mapped
morphisms of the binary product cone is a limit.
-/
def isLimitOfHasBinaryProductOfPreservesLimit [PreservesLimit (pair X Y) G] :
    IsLimit (BinaryFan.mk (G.map (Limits.prod.fst : X ⨯ Y ⟶ X)) (G.map Limits.prod.snd)) :=
  mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd X Y)

variable [HasBinaryProduct (G.obj X) (G.obj Y)]

/-- If the product comparison map for `G` at `(X,Y)` is an isomorphism, then `G` preserves the
pair of `(X,Y)`.
-/
def PreservesLimitPair.ofIsoProdComparison [i : IsIso (prodComparison G X Y)] : PreservesLimit (pair X Y) G := by
  apply preserves_limit_of_preserves_limit_cone (prod_is_prod X Y)
  apply (is_limit_map_cone_binary_fan_equiv _ _ _).symm _
  apply is_limit.of_point_iso (limit.is_limit (pair (G.obj X) (G.obj Y)))
  apply i

variable [PreservesLimit (pair X Y) G]

/-- If `G` preserves the product of `(X,Y)`, then the product comparison map for `G` at `(X,Y)` is
an isomorphism.
-/
def PreservesLimitPair.iso : G.obj (X ⨯ Y) ≅ G.obj X ⨯ G.obj Y :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasBinaryProductOfPreservesLimit G X Y) (limit.isLimit _)

@[simp]
theorem PreservesLimitPair.iso_hom : (PreservesLimitPair.iso G X Y).Hom = prodComparison G X Y :=
  rfl

instance : IsIso (prodComparison G X Y) := by
  rw [← preserves_limit_pair.iso_hom]
  infer_instance

end

section

variable {P X Y Z : C} (f : X ⟶ P) (g : Y ⟶ P)

/-- The map of a binary cofan is a colimit iff
the cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `binary_cofan.mk` with `functor.map_cocone`.
-/
def isColimitMapCoconeBinaryCofanEquiv :
    IsColimit (G.mapCocone (BinaryCofan.mk f g)) ≃ IsColimit (BinaryCofan.mk (G.map f) (G.map g)) :=
  (IsColimit.precomposeHomEquiv (diagramIsoPair.{v} _).symm _).symm.trans
    (IsColimit.equivIsoColimit
      (Cocones.ext (Iso.refl _)
        (by
          rintro (_ | _)
          tidy)))

/-- The property of preserving coproducts expressed in terms of binary cofans. -/
def mapIsColimitOfPreservesOfIsColimit [PreservesColimit (pair X Y) G] (l : IsColimit (BinaryCofan.mk f g)) :
    IsColimit (BinaryCofan.mk (G.map f) (G.map g)) :=
  isColimitMapCoconeBinaryCofanEquiv G f g (PreservesColimit.preserves l)

/-- The property of reflecting coproducts expressed in terms of binary cofans. -/
def isColimitOfReflectsOfMapIsColimit [ReflectsColimit (pair X Y) G]
    (l : IsColimit (BinaryCofan.mk (G.map f) (G.map g))) : IsColimit (BinaryCofan.mk f g) :=
  ReflectsColimit.reflects ((isColimitMapCoconeBinaryCofanEquiv G f g).symm l)

variable (X Y) [HasBinaryCoproduct X Y]

/-- If `G` preserves binary coproducts and `C` has them, then the binary cofan constructed of the mapped
morphisms of the binary product cocone is a colimit.
-/
def isColimitOfHasBinaryCoproductOfPreservesColimit [PreservesColimit (pair X Y) G] :
    IsColimit (BinaryCofan.mk (G.map (Limits.coprod.inl : X ⟶ X ⨿ Y)) (G.map Limits.coprod.inr)) :=
  mapIsColimitOfPreservesOfIsColimit G _ _ (coprodIsCoprod X Y)

variable [HasBinaryCoproduct (G.obj X) (G.obj Y)]

/-- If the coproduct comparison map for `G` at `(X,Y)` is an isomorphism, then `G` preserves the
pair of `(X,Y)`.
-/
def PreservesColimitPair.ofIsoCoprodComparison [i : IsIso (coprodComparison G X Y)] : PreservesColimit (pair X Y) G :=
  by
  apply preserves_colimit_of_preserves_colimit_cocone (coprod_is_coprod X Y)
  apply (is_colimit_map_cocone_binary_cofan_equiv _ _ _).symm _
  apply is_colimit.of_point_iso (colimit.is_colimit (pair (G.obj X) (G.obj Y)))
  apply i

variable [PreservesColimit (pair X Y) G]

/-- If `G` preserves the coproduct of `(X,Y)`, then the coproduct comparison map for `G` at `(X,Y)` is
an isomorphism.
-/
def PreservesColimitPair.iso : G.obj X ⨿ G.obj Y ≅ G.obj (X ⨿ Y) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (isColimitOfHasBinaryCoproductOfPreservesColimit G X Y)

@[simp]
theorem PreservesColimitPair.iso_hom : (PreservesColimitPair.iso G X Y).Hom = coprodComparison G X Y :=
  rfl

instance : IsIso (coprodComparison G X Y) := by
  rw [← preserves_colimit_pair.iso_hom]
  infer_instance

end

end CategoryTheory.Limits

