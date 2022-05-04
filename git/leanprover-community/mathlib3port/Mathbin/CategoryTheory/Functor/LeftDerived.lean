/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Preadditive.ProjectiveResolution

/-!
# Left-derived functors

We define the left-derived functors `F.left_derived n : C ⥤ D` for any additive functor `F`
out of a category with projective resolutions.

The definition is
```
projective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n
```
that is, we pick a projective resolution (thought of as an object of the homotopy category),
we apply `F` objectwise, and compute `n`-th homology.

We show that these left-derived functors can be calculated
on objects using any choice of projective resolution,
and on morphisms by any choice of lift to a chain map between chosen projective resolutions.

Similarly we define natural transformations between left-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Implementation

We don't assume the categories involved are abelian
(just preadditive, and have equalizers, cokernels, and image maps),
or that the functors are right exact.
None of these assumptions are needed yet.

It is often convenient, of course, to work with `[abelian C] [enough_projectives C] [abelian D]`
which (assuming the results from `category_theory.abelian.projective`) are enough to
provide all the typeclass hypotheses assumed here.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type _} [Category D]

-- Importing `category_theory.abelian.projective` and assuming
-- `[abelian C] [enough_projectives C] [abelian D]` suffices to acquire all the following:
variable [Preadditive C] [HasZeroObject C] [HasEqualizers C] [HasImages C] [HasProjectiveResolutions C]

variable [Preadditive D] [HasZeroObject D] [HasEqualizers D] [HasCokernels D] [HasImages D] [HasImageMaps D]

/-- The left derived functors of an additive functor. -/
def Functor.leftDerived (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D :=
  projectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙ HomotopyCategory.homologyFunctor D _ n

/-- We can compute a left derived functor using a chosen projective resolution. -/
-- TODO the left derived functors are additive (and linear when `F` is linear)
@[simps]
def Functor.leftDerivedObjIso (F : C ⥤ D) [F.Additive] (n : ℕ) {X : C} (P : ProjectiveResolution X) :
    (F.leftDerived n).obj X ≅ (homologyFunctor D _ n).obj ((F.mapHomologicalComplex _).obj P.complex) :=
  (HomotopyCategory.homologyFunctor D _ n).mapIso
      (HomotopyCategory.isoOfHomotopyEquiv (F.mapHomotopyEquiv (ProjectiveResolution.homotopyEquiv _ P))) ≪≫
    (HomotopyCategory.homologyFactors D _ n).app _

/-- The 0-th derived functor of `F` on a projective object `X` is just `F.obj X`. -/
@[simps]
def Functor.leftDerivedObjProjectiveZero (F : C ⥤ D) [F.Additive] (X : C) [Projective X] :
    (F.leftDerived 0).obj X ≅ F.obj X :=
  F.leftDerivedObjIso 0 (ProjectiveResolution.self X) ≪≫
    (homologyFunctor _ _ _).mapIso ((ChainComplex.single₀MapHomologicalComplex F).app X) ≪≫
      (ChainComplex.homologyFunctor0Single₀ D).app (F.obj X)

open ZeroObject

/-- The higher derived functors vanish on projective objects. -/
@[simps]
def Functor.leftDerivedObjProjectiveSucc (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) [Projective X] :
    (F.leftDerived (n + 1)).obj X ≅ 0 :=
  F.leftDerivedObjIso (n + 1) (ProjectiveResolution.self X) ≪≫
    (homologyFunctor _ _ _).mapIso ((ChainComplex.single₀MapHomologicalComplex F).app X) ≪≫
      (ChainComplex.homologyFunctorSuccSingle₀ D n).app (F.obj X) ≪≫ (Functor.zero_obj _).isoZero

/-- We can compute a left derived functor on a morphism using a lift of that morphism
to a chain map between chosen projective resolutions.
-/
theorem Functor.left_derived_map_eq (F : C ⥤ D) [F.Additive] (n : ℕ) {X Y : C} (f : X ⟶ Y) {P : ProjectiveResolution X}
    {Q : ProjectiveResolution Y} (g : P.complex ⟶ Q.complex) (w : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) :
    (F.leftDerived n).map f =
      (F.leftDerivedObjIso n P).Hom ≫
        (homologyFunctor D _ n).map ((F.mapHomologicalComplex _).map g) ≫ (F.leftDerivedObjIso n Q).inv :=
  by
  dsimp' only [functor.left_derived, functor.left_derived_obj_iso]
  dsimp'
  simp only [category.comp_id, category.id_comp]
  rw [← homology_functor_map, HomotopyCategory.homology_functor_map_factors]
  simp only [← functor.map_comp]
  congr 1
  apply HomotopyCategory.eq_of_homotopy
  apply functor.map_homotopy
  apply Homotopy.trans
  exact HomotopyCategory.homotopyOutMap _
  apply ProjectiveResolution.lift_homotopy f
  · simp
    
  · simp [w]
    

/-- The natural transformation between left-derived functors induced by a natural transformation. -/
@[simps]
def NatTrans.leftDerived {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) :
    F.leftDerived n ⟶ G.leftDerived n :=
  whiskerLeft (projectiveResolutions C)
    (whiskerRight (NatTrans.mapHomotopyCategory α _) (HomotopyCategory.homologyFunctor D _ n))

@[simp]
theorem NatTrans.left_derived_id (F : C ⥤ D) [F.Additive] (n : ℕ) :
    NatTrans.leftDerived (𝟙 F) n = 𝟙 (F.leftDerived n) := by
  simp [nat_trans.left_derived]
  rfl

-- The `simp_nf` linter times out here, so we disable it.
@[simp, nolint simp_nf]
theorem NatTrans.left_derived_comp {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive] (α : F ⟶ G) (β : G ⟶ H)
    (n : ℕ) : NatTrans.leftDerived (α ≫ β) n = NatTrans.leftDerived α n ≫ NatTrans.leftDerived β n := by
  simp [nat_trans.left_derived]

/-- A component of the natural transformation between left-derived functors can be computed
using a chosen projective resolution.
-/
theorem NatTrans.left_derived_eq {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) {X : C}
    (P : ProjectiveResolution X) :
    (NatTrans.leftDerived α n).app X =
      (F.leftDerivedObjIso n P).Hom ≫
        (homologyFunctor D _ n).map ((NatTrans.mapHomologicalComplex α _).app P.complex) ≫
          (G.leftDerivedObjIso n P).inv :=
  by
  symm
  dsimp' [nat_trans.left_derived, functor.left_derived_obj_iso]
  simp only [category.comp_id, category.id_comp]
  rw [← homology_functor_map, HomotopyCategory.homology_functor_map_factors]
  simp only [← functor.map_comp]
  congr 1
  apply HomotopyCategory.eq_of_homotopy
  simp only [nat_trans.map_homological_complex_naturality_assoc, ← functor.map_comp]
  apply Homotopy.compLeftId
  rw [← Functor.map_id]
  apply functor.map_homotopy
  apply HomotopyEquiv.homotopyHomInvId

-- TODO:
-- lemma nat_trans.left_derived_projective_zero {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G)
--   (X : C) [projective X] :
--   (nat_trans.left_derived α 0).app X =
--     (F.left_derived_obj_projective_zero X).hom ≫
--       α.app X ≫
--         (G.left_derived_obj_projective_zero X).inv := sorry
-- TODO:
-- lemma nat_trans.left_derived_projective_succ {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G)
--   (n : ℕ) (X : C) [projective X] :
--   (nat_trans.left_derived α (n+1)).app X = 0 := sorry
-- TODO left-derived functors of the identity functor are the identity
-- (requires we assume `abelian`?)
-- PROJECT left-derived functors of a composition (Grothendieck sequence)
end CategoryTheory

