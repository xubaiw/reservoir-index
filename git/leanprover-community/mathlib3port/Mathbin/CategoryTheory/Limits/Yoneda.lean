/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.FunctorCategory

/-!
# Limit properties relating to the (co)yoneda embedding.

We calculate the colimit of `Y ↦ (X ⟶ Y)`, which is just `punit`.
(This is used in characterising cofinal functors.)

We also show the (co)yoneda embeddings preserve limits and jointly reflect them.
-/


open Opposite

open CategoryTheory

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

namespace Coyoneda

variable {C : Type v} [SmallCategory C]

/-- The colimit cocone over `coyoneda.obj X`, with cocone point `punit`.
-/
@[simps]
def colimitCocone (X : Cᵒᵖ) : Cocone (coyoneda.obj X) where
  x := PUnit
  ι :=
    { app := by
        tidy }

/-- The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
@[simps]
def colimitCoconeIsColimit (X : Cᵒᵖ) : IsColimit (colimitCocone X) where
  desc := fun s x => s.ι.app (unop X) (𝟙 _)
  fac' := fun s Y => by
    ext f
    convert congr_fun (s.w f).symm (𝟙 (unop X))
    simp
  uniq' := fun s m w => by
    ext ⟨⟩
    rw [← w]
    simp

instance (X : Cᵒᵖ) : HasColimit (coyoneda.obj X) :=
  HasColimit.mk { Cocone := _, IsColimit := colimitCoconeIsColimit X }

/-- The colimit of `coyoneda.obj X` is isomorphic to `punit`.
-/
noncomputable def colimitCoyonedaIso (X : Cᵒᵖ) : colimit (coyoneda.obj X) ≅ PUnit :=
  colimit.isoColimitCocone { Cocone := _, IsColimit := colimitCoconeIsColimit X }

end Coyoneda

variable {C : Type u} [Category.{v} C]

open Limits

/-- The yoneda embedding `yoneda.obj X : Cᵒᵖ ⥤ Type v` for `X : C` preserves limits. -/
instance yonedaPreservesLimits (X : C) :
    PreservesLimits
      (yoneda.obj
        X) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun K =>
        { preserves := fun c t =>
            { lift := fun s x => Quiver.Hom.unop (t.lift ⟨op X, fun j => (s.π.app j x).op, fun j₁ j₂ α => _⟩),
              fac' := fun s j => funext fun x => Quiver.Hom.op_inj (t.fac _ _),
              uniq' := fun s m w =>
                funext fun x => by
                  refine' Quiver.Hom.op_inj (t.uniq ⟨op X, _, _⟩ _ fun j => _)
                  · dsimp'
                    simp [s.w α]
                    
                  -- See library note [dsimp, simp]
                  · exact Quiver.Hom.unop_inj (congr_fun (w j) x)
                     } } }

/-- The coyoneda embedding `coyoneda.obj X : C ⥤ Type v` for `X : Cᵒᵖ` preserves limits. -/
instance coyonedaPreservesLimits (X : Cᵒᵖ) :
    PreservesLimits
      (coyoneda.obj
        X) where PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun K =>
        { preserves := fun c t =>
            { lift := fun s x =>
                t.lift
                  ⟨unop X, fun j => s.π.app j x, fun j₁ j₂ α => by
                    dsimp'
                    simp [s.w α]⟩,-- See library note [dsimp, simp]
              fac' := fun s j => funext fun x => t.fac _ _,
              uniq' := fun s m w =>
                funext fun x => by
                  refine' t.uniq ⟨unop X, _⟩ _ fun j => _
                  exact congr_fun (w j) x } } }

/-- The yoneda embeddings jointly reflect limits. -/
def yonedaJointlyReflectsLimits (J : Type w) [SmallCategory J] (K : J ⥤ Cᵒᵖ) (c : Cone K)
    (t : ∀ X : C, IsLimit ((yoneda.obj X).mapCone c)) : IsLimit c :=
  let s' : ∀ s : Cone K, Cone (K ⋙ yoneda.obj s.x.unop) := fun s =>
    ⟨PUnit, fun j _ => (s.π.app j).unop, fun j₁ j₂ α => funext fun _ => Quiver.Hom.op_inj (s.w α).symm⟩
  { lift := fun s => ((t s.x.unop).lift (s' s) PUnit.unit).op,
    fac' := fun s j => Quiver.Hom.unop_inj (congr_fun ((t s.x.unop).fac (s' s) j) PUnit.unit),
    uniq' := fun s m w => by
      apply Quiver.Hom.unop_inj
      suffices (fun x : PUnit => m.unop) = (t s.X.unop).lift (s' s) by
        apply congr_fun this PUnit.unit
      apply (t _).uniq (s' s) _ fun j => _
      ext
      exact Quiver.Hom.op_inj (w j) }

/-- The coyoneda embeddings jointly reflect limits. -/
def coyonedaJointlyReflectsLimits (J : Type w) [SmallCategory J] (K : J ⥤ C) (c : Cone K)
    (t : ∀ X : Cᵒᵖ, IsLimit ((coyoneda.obj X).mapCone c)) : IsLimit c :=
  let s' : ∀ s : Cone K, Cone (K ⋙ coyoneda.obj (op s.x)) := fun s =>
    ⟨PUnit, fun j _ => s.π.app j, fun j₁ j₂ α => funext fun _ => (s.w α).symm⟩
  { lift := fun s => (t (op s.x)).lift (s' s) PUnit.unit, fac' := fun s j => congr_fun ((t _).fac (s' s) j) PUnit.unit,
    uniq' := fun s m w => by
      suffices (fun x : PUnit => m) = (t _).lift (s' s) by
        apply congr_fun this PUnit.unit
      apply (t _).uniq (s' s) _ fun j => _
      ext
      exact w j }

variable {D : Type u} [SmallCategory D]

instance yonedaFunctorPreservesLimits : PreservesLimits (@yoneda D _) := by
  apply preserves_limits_of_evaluation
  intro K
  change preserves_limits (coyoneda.obj K)
  infer_instance

instance coyonedaFunctorPreservesLimits : PreservesLimits (@coyoneda D _) := by
  apply preserves_limits_of_evaluation
  intro K
  change preserves_limits (yoneda.obj K)
  infer_instance

instance yonedaFunctorReflectsLimits : ReflectsLimits (@yoneda D _) :=
  Limits.fullyFaithfulReflectsLimits _

instance coyonedaFunctorReflectsLimits : ReflectsLimits (@coyoneda D _) :=
  Limits.fullyFaithfulReflectsLimits _

end CategoryTheory

