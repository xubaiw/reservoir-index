/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.KernelPair
import Mathbin.CategoryTheory.Limits.Shapes.CommSq

/-!
# The diagonal object of a morphism.

We provide various API and isomorphisms considering the diagonal object `Δ_{Y/X} := pullback f f`
of a morphism `f : X ⟶ Y`.

-/


open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

variable {C : Type _} [Category C] {X Y Z : C}

namespace Pullback

section Diagonal

variable (f : X ⟶ Y) [HasPullback f f]

/-- The diagonal object of a morphism `f : X ⟶ Y` is `Δ_{X/Y} := pullback f f`. -/
abbrev diagonalObj : C :=
  pullback f f

/-- The diagonal morphism `X ⟶ Δ_{X/Y}` for a morphism `f : X ⟶ Y`. -/
def diagonal : X ⟶ diagonalObj f :=
  pullback.lift (𝟙 _) (𝟙 _) rfl

@[simp, reassoc]
theorem diagonal_fst : diagonal f ≫ pullback.fst = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
theorem diagonal_snd : diagonal f ≫ pullback.snd = 𝟙 _ :=
  pullback.lift_snd _ _ _

instance : IsSplitMono (diagonal f) :=
  ⟨⟨⟨pullback.fst, diagonal_fst f⟩⟩⟩

instance : IsSplitEpi (pullback.fst : pullback f f ⟶ X) :=
  ⟨⟨⟨diagonal f, diagonal_fst f⟩⟩⟩

instance : IsSplitEpi (pullback.snd : pullback f f ⟶ X) :=
  ⟨⟨⟨diagonal f, diagonal_snd f⟩⟩⟩

instance [Mono f] : IsIso (diagonal f) := by
  rw [(is_iso.inv_eq_of_inv_hom_id (diagonal_fst f)).symm]
  infer_instance

/-- The two projections `Δ_{X/Y} ⟶ X` form a kernel pair for `f : X ⟶ Y`. -/
def diagonalIsKernelPair : IsKernelPair f (pullback.fst : diagonalObj f ⟶ _) pullback.snd :=
  ⟨pullback.condition, pullbackIsPullback _ _⟩

end Diagonal

end Pullback

variable [HasPullbacks C]

open Pullback

section

variable {U V₁ V₂ : C} (f : X ⟶ Y) (i : U ⟶ Y)

variable (i₁ : V₁ ⟶ pullback f i) (i₂ : V₂ ⟶ pullback f i)

@[simp, reassoc]
theorem pullback_diagonal_map_snd_fst_fst :
    (pullback.snd :
          pullback (diagonal f)
              (map (i₁ ≫ snd) (i₂ ≫ snd) f f (i₁ ≫ fst) (i₂ ≫ fst) i
                (by
                  simp [condition])
                (by
                  simp [condition])) ⟶
            _) ≫
        fst ≫ i₁ ≫ fst =
      pullback.fst :=
  by
  conv_rhs => rw [← category.comp_id pullback.fst]
  rw [← diagonal_fst f, pullback.condition_assoc, pullback.lift_fst]

@[simp, reassoc]
theorem pullback_diagonal_map_snd_snd_fst :
    (pullback.snd :
          pullback (diagonal f)
              (map (i₁ ≫ snd) (i₂ ≫ snd) f f (i₁ ≫ fst) (i₂ ≫ fst) i
                (by
                  simp [condition])
                (by
                  simp [condition])) ⟶
            _) ≫
        snd ≫ i₂ ≫ fst =
      pullback.fst :=
  by
  conv_rhs => rw [← category.comp_id pullback.fst]
  rw [← diagonal_snd f, pullback.condition_assoc, pullback.lift_snd]

variable [HasPullback i₁ i₂]

/-- This iso witnesses the fact that
given `f : X ⟶ Y`, `i : U ⟶ Y`, and `i₁ : V₁ ⟶ X ×[Y] U`, `i₂ : V₂ ⟶ X ×[Y] U`, the diagram

V₁ ×[X ×[Y] U] V₂ ⟶ V₁ ×[U] V₂
        |                 |
        |                 |
        ↓                 ↓
        X         ⟶  X ×[Y] X

is a pullback square.
Also see `pullback_fst_map_snd_is_pullback`.
-/
def pullbackDiagonalMapIso :
    pullback (diagonal f)
        (map (i₁ ≫ snd) (i₂ ≫ snd) f f (i₁ ≫ fst) (i₂ ≫ fst) i
          (by
            simp [condition])
          (by
            simp [condition])) ≅
      pullback i₁ i₂ where
  Hom :=
    pullback.lift (pullback.snd ≫ pullback.fst) (pullback.snd ≫ pullback.snd)
      (by
        ext <;>
          simp only [category.assoc, pullback.condition, pullback_diagonal_map_snd_fst_fst,
            pullback_diagonal_map_snd_snd_fst])
  inv :=
    pullback.lift (pullback.fst ≫ i₁ ≫ pullback.fst)
      (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) pullback.snd (Category.id_comp _).symm (Category.id_comp _).symm)
      (by
        ext <;>
          simp only [diagonal_fst, diagonal_snd, category.comp_id, pullback.condition_assoc, category.assoc, lift_fst,
            lift_fst_assoc, lift_snd, lift_snd_assoc])
  hom_inv_id' := by
    ext <;>
      simp only [category.id_comp, category.assoc, lift_fst_assoc, pullback_diagonal_map_snd_fst_fst, lift_fst,
        lift_snd, category.comp_id]
  inv_hom_id' := by
    ext <;> simp

@[simp, reassoc]
theorem pullback_diagonal_map_iso_hom_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).Hom ≫ pullback.fst = pullback.snd ≫ pullback.fst := by
  delta' pullback_diagonal_map_iso
  simp

@[simp, reassoc]
theorem pullback_diagonal_map_iso_hom_snd :
    (pullbackDiagonalMapIso f i i₁ i₂).Hom ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  delta' pullback_diagonal_map_iso
  simp

@[simp, reassoc]
theorem pullback_diagonal_map_iso_inv_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.fst = pullback.fst ≫ i₁ ≫ pullback.fst := by
  delta' pullback_diagonal_map_iso
  simp

@[simp, reassoc]
theorem pullback_diagonal_map_iso_inv_snd_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.snd ≫ pullback.fst = pullback.fst := by
  delta' pullback_diagonal_map_iso
  simp

@[simp, reassoc]
theorem pullback_diagonal_map_iso_inv_snd_snd :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.snd ≫ pullback.snd = pullback.snd := by
  delta' pullback_diagonal_map_iso
  simp

theorem pullback_fst_map_snd_is_pullback :
    IsPullback (fst ≫ i₁ ≫ fst)
      (map i₁ i₂ (i₁ ≫ snd) (i₂ ≫ snd) _ _ _ (Category.id_comp _).symm (Category.id_comp _).symm) (diagonal f)
      (map (i₁ ≫ snd) (i₂ ≫ snd) f f (i₁ ≫ fst) (i₂ ≫ fst) i
        (by
          simp [condition])
        (by
          simp [condition])) :=
  IsPullback.of_iso_pullback
    ⟨by
      ext <;> simp [condition_assoc]⟩
    (pullbackDiagonalMapIso f i i₁ i₂).symm (pullback_diagonal_map_iso_inv_fst f i i₁ i₂)
    (by
      ext1 <;> simp )

end

section

variable {S T : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S)

variable [HasPullback i i] [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)]

variable
  [HasPullback (diagonal i) (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _))]

/-- This iso witnesses the fact that
given `f : X ⟶ T`, `g : Y ⟶ T`, and `i : T ⟶ S`, the diagram

X ×ₜ Y ⟶ X ×ₛ Y
   |         |
   |         |
   ↓         ↓
   T   ⟶ T ×ₛ T

is a pullback square.
Also see `pullback_map_diagonal_is_pullback`.
-/
def pullbackDiagonalMapIdIso :
    pullback (diagonal i) (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) ≅
      pullback f g :=
  by
  refine'
    (as_iso <| pullback.map _ _ _ _ (𝟙 _) (pullback.congr_hom _ _).Hom (𝟙 _) _ _) ≪≫
      pullback_diagonal_map_iso i (𝟙 _) (f ≫ inv pullback.fst) (g ≫ inv pullback.fst) ≪≫
        (as_iso <| pullback.map _ _ _ _ (𝟙 _) (𝟙 _) pullback.fst _ _)
  · rw [← category.comp_id pullback.snd, ← condition, category.assoc, is_iso.inv_hom_id_assoc]
    
  · rw [← category.comp_id pullback.snd, ← condition, category.assoc, is_iso.inv_hom_id_assoc]
    
  · rw [category.comp_id, category.id_comp]
    
  · ext <;> simp
    
  · infer_instance
    
  · rw [category.assoc, category.id_comp, is_iso.inv_hom_id, category.comp_id]
    
  · rw [category.assoc, category.id_comp, is_iso.inv_hom_id, category.comp_id]
    
  · infer_instance
    

@[simp, reassoc]
theorem pullback_diagonal_map_id_iso_hom_fst :
    (pullbackDiagonalMapIdIso f g i).Hom ≫ pullback.fst = pullback.snd ≫ pullback.fst := by
  delta' pullback_diagonal_map_id_iso
  simp

@[simp, reassoc]
theorem pullback_diagonal_map_id_iso_hom_snd :
    (pullbackDiagonalMapIdIso f g i).Hom ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  delta' pullback_diagonal_map_id_iso
  simp

@[simp, reassoc]
theorem pullback_diagonal_map_id_iso_inv_fst : (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.fst = pullback.fst ≫ f :=
  by
  rw [iso.inv_comp_eq, ← category.comp_id pullback.fst, ← diagonal_fst i, pullback.condition_assoc]
  simp

@[simp, reassoc]
theorem pullback_diagonal_map_id_iso_inv_snd_fst :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd ≫ pullback.fst = pullback.fst := by
  rw [iso.inv_comp_eq]
  simp

@[simp, reassoc]
theorem pullback_diagonal_map_id_iso_inv_snd_snd :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd ≫ pullback.snd = pullback.snd := by
  rw [iso.inv_comp_eq]
  simp

theorem pullback.diagonal_comp (f : X ⟶ Y) (g : Y ⟶ Z) [HasPullback f f] [HasPullback g g]
    [HasPullback (f ≫ g) (f ≫ g)] :
    diagonal (f ≫ g) = diagonal f ≫ (pullbackDiagonalMapIdIso f f g).inv ≫ pullback.snd := by
  ext <;> simp

theorem pullback_map_diagonal_is_pullback :
    IsPullback (pullback.fst ≫ f)
      (pullback.map f g (f ≫ i) (g ≫ i) _ _ i (Category.id_comp _).symm (Category.id_comp _).symm) (diagonal i)
      (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) :=
  by
  apply is_pullback.of_iso_pullback _ (pullback_diagonal_map_id_iso f g i).symm
  · simp
    
  · ext <;> simp
    
  · constructor
    ext <;> simp [condition]
    

/-- The diagonal object of `X ×[Z] Y ⟶ X` is isomorphic to `Δ_{Y/Z} ×[Z] X`. -/
def diagonalObjPullbackFstIso {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    diagonalObj (pullback.fst : pullback f g ⟶ X) ≅ pullback (pullback.snd ≫ g : diagonalObj g ⟶ Z) f :=
  pullbackRightPullbackFstIso _ _ _ ≪≫
    pullback.congrHom pullback.condition rfl ≪≫
      pullbackAssoc _ _ _ _ ≪≫ pullbackSymmetry _ _ ≪≫ pullback.congrHom pullback.condition rfl

@[simp, reassoc]
theorem diagonal_obj_pullback_fst_iso_hom_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).Hom ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd := by
  delta' diagonal_obj_pullback_fst_iso
  simp

@[simp, reassoc]
theorem diagonal_obj_pullback_fst_iso_hom_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).Hom ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd := by
  delta' diagonal_obj_pullback_fst_iso
  simp

@[simp, reassoc]
theorem diagonal_obj_pullback_fst_iso_hom_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).Hom ≫ pullback.snd = pullback.fst ≫ pullback.fst := by
  delta' diagonal_obj_pullback_fst_iso
  simp

@[simp, reassoc]
theorem diagonal_obj_pullback_fst_iso_inv_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst ≫ pullback.fst = pullback.snd := by
  delta' diagonal_obj_pullback_fst_iso
  simp

@[simp, reassoc]
theorem diagonal_obj_pullback_fst_iso_inv_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst ≫ pullback.snd = pullback.fst ≫ pullback.fst := by
  delta' diagonal_obj_pullback_fst_iso
  simp

@[simp, reassoc]
theorem diagonal_obj_pullback_fst_iso_inv_snd_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd ≫ pullback.fst = pullback.snd := by
  delta' diagonal_obj_pullback_fst_iso
  simp

@[simp, reassoc]
theorem diagonal_obj_pullback_fst_iso_inv_snd_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.snd := by
  delta' diagonal_obj_pullback_fst_iso
  simp

theorem diagonal_pullback_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    diagonal (pullback.fst : pullback f g ⟶ _) =
      (pullbackSymmetry _ _).Hom ≫
        ((baseChange f).map
              (Over.homMk (diagonal g)
                (by
                  simp ) :
                Over.mk g ⟶ Over.mk (pullback.snd ≫ g))).left ≫
          (diagonalObjPullbackFstIso f g).inv :=
  by
  ext <;> simp

end

/-- Given the following diagram with `S ⟶ S'` a monomorphism,

    X  ⟶ X'
      ↘      ↘
        S  ⟶ S'
      ↗      ↗
    Y  ⟶ Y'

This iso witnesses the fact that

      X ×[S] Y ⟶ (X' ×[S'] Y') ×[Y'] Y
          |                  |
          |                  |
          ↓                  ↓
(X' ×[S'] Y') ×[X'] X ⟶ X' ×[S'] Y'

is a pullback square. The diagonal map of this square is `pullback.map`.
Also see `pullback_lift_map_is_pullback`.
-/
@[simps]
def pullbackFstFstIso {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    pullback (pullback.fst : pullback (pullback.fst : pullback f' g' ⟶ _) i₁ ⟶ _)
        (pullback.fst : pullback (pullback.snd : pullback f' g' ⟶ _) i₂ ⟶ _) ≅
      pullback f g where
  Hom :=
    pullback.lift (pullback.fst ≫ pullback.snd) (pullback.snd ≫ pullback.snd)
      (by
        rw [← cancel_mono i₃, category.assoc, category.assoc, category.assoc, category.assoc, e₁, e₂, ←
          pullback.condition_assoc, pullback.condition_assoc, pullback.condition, pullback.condition_assoc])
  inv :=
    pullback.lift (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) pullback.fst (pullback.lift_fst _ _ _))
      (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) pullback.snd (pullback.lift_snd _ _ _))
      (by
        rw [pullback.lift_fst, pullback.lift_fst])
  hom_inv_id' := by
    ext <;>
      simp only [category.assoc, category.id_comp, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, condition, ←
        condition_assoc]
  inv_hom_id' := by
    ext <;> simp only [category.assoc, category.id_comp, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc]

theorem pullback_map_eq_pullback_fst_fst_iso_inv {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S')
    (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ =
      (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).inv ≫ pullback.snd ≫ pullback.fst :=
  by
  ext <;>
    simp only [category.assoc, category.id_comp, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc,
      pullback_fst_fst_iso_inv, ← pullback.condition, ← pullback.condition_assoc]

theorem pullback_lift_map_is_pullback {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    IsPullback (pullback.lift (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) fst (lift_fst _ _ _))
      (pullback.lift (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) snd (lift_snd _ _ _)) pullback.fst pullback.fst :=
  IsPullback.of_iso_pullback
    ⟨by
      rw [lift_fst, lift_fst]⟩
    (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).symm
    (by
      simp )
    (by
      simp )

end CategoryTheory.Limits

