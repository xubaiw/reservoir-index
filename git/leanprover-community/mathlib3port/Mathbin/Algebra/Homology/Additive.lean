/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Homology.Homology
import Mathbin.Algebra.Homology.Single
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Homology is an additive functor

When `V` is preadditive, `homological_complex V c` is also preadditive,
and `homology_functor` is additive.

TODO: similarly for `R`-linear.
-/


universe v u

open Classical

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

variable {ι : Type _}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

namespace HomologicalComplex

instance : Zero (C ⟶ D) :=
  ⟨{ f := fun i => 0 }⟩

instance : Add (C ⟶ D) :=
  ⟨fun f g => { f := fun i => f.f i + g.f i }⟩

instance : Neg (C ⟶ D) :=
  ⟨fun f => { f := fun i => -f.f i }⟩

instance : Sub (C ⟶ D) :=
  ⟨fun f g => { f := fun i => f.f i - g.f i }⟩

instance hasNatScalar : HasScalar ℕ (C ⟶ D) :=
  ⟨fun n f =>
    { f := fun i => n • f.f i,
      comm' := fun i j h => by
        simp [preadditive.nsmul_comp, preadditive.comp_nsmul] }⟩

instance hasIntScalar : HasScalar ℤ (C ⟶ D) :=
  ⟨fun n f =>
    { f := fun i => n • f.f i,
      comm' := fun i j h => by
        simp [preadditive.zsmul_comp, preadditive.comp_zsmul] }⟩

@[simp]
theorem zero_f_apply (i : ι) : (0 : C ⟶ D).f i = 0 :=
  rfl

@[simp]
theorem add_f_apply (f g : C ⟶ D) (i : ι) : (f + g).f i = f.f i + g.f i :=
  rfl

@[simp]
theorem neg_f_apply (f : C ⟶ D) (i : ι) : (-f).f i = -f.f i :=
  rfl

@[simp]
theorem sub_f_apply (f g : C ⟶ D) (i : ι) : (f - g).f i = f.f i - g.f i :=
  rfl

@[simp]
theorem nsmul_f_apply (n : ℕ) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i :=
  rfl

@[simp]
theorem zsmul_f_apply (n : ℤ) (f : C ⟶ D) (i : ι) : (n • f).f i = n • f.f i :=
  rfl

instance : AddCommGroupₓ (C ⟶ D) :=
  Function.Injective.addCommGroup Hom.f HomologicalComplex.hom_f_injective
    (by
      tidy)
    (by
      tidy)
    (by
      tidy)
    (by
      tidy)
    (by
      tidy)
    (by
      tidy)

instance : Preadditive (HomologicalComplex V c) :=
  {  }

/-- The `i`-th component of a chain map, as an additive map from chain maps to morphisms. -/
@[simps]
def Hom.fAddMonoidHom {C₁ C₂ : HomologicalComplex V c} (i : ι) : (C₁ ⟶ C₂) →+ (C₁.x i ⟶ C₂.x i) :=
  AddMonoidHom.mk' (fun f => Hom.f f i) fun _ _ => rfl

end HomologicalComplex

namespace HomologicalComplex

instance eval_additive (i : ι) : (eval V c i).Additive :=
  {  }

variable [HasZeroObject V]

instance cycles_additive [HasEqualizers V] : (cyclesFunctor V c i).Additive :=
  {  }

variable [HasImages V] [HasImageMaps V]

instance boundaries_additive : (boundariesFunctor V c i).Additive :=
  {  }

variable [HasEqualizers V] [HasCokernels V]

instance homology_additive : (homologyFunctor V c i).Additive where
  map_add' := fun C D f g => by
    dsimp [homologyFunctor]
    ext
    simp only [homology.π_map, preadditive.comp_add, ← preadditive.add_comp]
    congr
    ext
    simp

end HomologicalComplex

namespace CategoryTheory

variable {W : Type _} [Category W] [Preadditive W]

/-- An additive functor induces a functor between homological complexes.
This is sometimes called the "prolongation".
-/
@[simps]
def Functor.mapHomologicalComplex (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    HomologicalComplex V c ⥤ HomologicalComplex W c where
  obj := fun C =>
    { x := fun i => F.obj (C.x i), d := fun i j => F.map (C.d i j),
      shape' := fun i j w => by
        rw [C.shape _ _ w, F.map_zero],
      d_comp_d' := fun i j k _ _ => by
        rw [← F.map_comp, C.d_comp_d, F.map_zero] }
  map := fun C D f =>
    { f := fun i => F.map (f.f i),
      comm' := fun i j h => by
        dsimp
        rw [← F.map_comp, ← F.map_comp, f.comm] }

instance Functor.map_homogical_complex_additive (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) :
    (F.mapHomologicalComplex c).Additive :=
  {  }

/-- A natural transformation between functors induces a natural transformation
between those functors applied to homological complexes.
-/
@[simps]
def NatTrans.mapHomologicalComplex {F G : V ⥤ W} [F.Additive] [G.Additive] (α : F ⟶ G) (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⟶ G.mapHomologicalComplex c where
  app := fun C => { f := fun i => α.app _ }

@[simp]
theorem NatTrans.map_homological_complex_id (c : ComplexShape ι) (F : V ⥤ W) [F.Additive] :
    NatTrans.mapHomologicalComplex (𝟙 F) c = 𝟙 (F.mapHomologicalComplex c) := by
  tidy

@[simp]
theorem NatTrans.map_homological_complex_comp (c : ComplexShape ι) {F G H : V ⥤ W} [F.Additive] [G.Additive]
    [H.Additive] (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.mapHomologicalComplex (α ≫ β) c =
      NatTrans.mapHomologicalComplex α c ≫ NatTrans.mapHomologicalComplex β c :=
  by
  tidy

@[simp, reassoc]
theorem NatTrans.map_homological_complex_naturality {c : ComplexShape ι} {F G : V ⥤ W} [F.Additive] [G.Additive]
    (α : F ⟶ G) {C D : HomologicalComplex V c} (f : C ⟶ D) :
    (F.mapHomologicalComplex c).map f ≫ (NatTrans.mapHomologicalComplex α c).app D =
      (NatTrans.mapHomologicalComplex α c).app C ≫ (G.mapHomologicalComplex c).map f :=
  by
  tidy

end CategoryTheory

namespace ChainComplex

variable {W : Type _} [Category W] [Preadditive W]

variable {α : Type _} [AddRightCancelSemigroup α] [One α] [DecidableEq α]

theorem map_chain_complex_of (F : V ⥤ W) [F.Additive] (X : α → V) (d : ∀ n, X (n + 1) ⟶ X n)
    (sq : ∀ n, d (n + 1) ≫ d n = 0) :
    (F.mapHomologicalComplex _).obj (ChainComplex.of X d sq) =
      ChainComplex.of (fun n => F.obj (X n)) (fun n => F.map (d n)) fun n => by
        rw [← F.map_comp, sq n, functor.map_zero] :=
  by
  refine' HomologicalComplex.ext rfl _
  rintro i j (rfl : j + 1 = i)
  simp only [CategoryTheory.Functor.map_homological_complex_obj_d, of_d, eq_to_hom_refl, comp_id, id_comp]

end ChainComplex

variable [HasZeroObject V] {W : Type _} [Category W] [Preadditive W] [HasZeroObject W]

namespace HomologicalComplex

/-- Turning an object into a complex supported at `j` then applying a functor is
the same as applying the functor then forming the complex.
-/
def singleMapHomologicalComplex (F : V ⥤ W) [F.Additive] (c : ComplexShape ι) (j : ι) :
    single V c j ⋙ F.mapHomologicalComplex _ ≅ F ⋙ single W c j :=
  NatIso.ofComponents
    (fun X =>
      { Hom :=
          { f := fun i =>
              if h : i = j then
                eqToHom
                  (by
                    simp [h])
              else 0 },
        inv :=
          { f := fun i =>
              if h : i = j then
                eqToHom
                  (by
                    simp [h])
              else 0 },
        hom_inv_id' := by
          ext i
          dsimp
          split_ifs with h
          · simp [h]
            
          · rw [zero_comp, if_neg h]
            exact (zero_of_source_iso_zero _ F.map_zero_object).symm
            ,
        inv_hom_id' := by
          ext i
          dsimp
          split_ifs with h
          · simp [h]
            
          · rw [zero_comp, if_neg h]
            simp
             })
    fun X Y f => by
    ext i
    dsimp
    split_ifs with h <;> simp [h]

variable (F : V ⥤ W) [Functor.Additive F] (c)

@[simp]
theorem single_map_homological_complex_hom_app_self (j : ι) (X : V) :
    ((singleMapHomologicalComplex F c j).Hom.app X).f j =
      eqToHom
        (by
          simp ) :=
  by
  simp [single_map_homological_complex]

@[simp]
theorem single_map_homological_complex_hom_app_ne {i j : ι} (h : i ≠ j) (X : V) :
    ((singleMapHomologicalComplex F c j).Hom.app X).f i = 0 := by
  simp [single_map_homological_complex, h]

@[simp]
theorem single_map_homological_complex_inv_app_self (j : ι) (X : V) :
    ((singleMapHomologicalComplex F c j).inv.app X).f j =
      eqToHom
        (by
          simp ) :=
  by
  simp [single_map_homological_complex]

@[simp]
theorem single_map_homological_complex_inv_app_ne {i j : ι} (h : i ≠ j) (X : V) :
    ((singleMapHomologicalComplex F c j).inv.app X).f i = 0 := by
  simp [single_map_homological_complex, h]

end HomologicalComplex

namespace ChainComplex

/-- Turning an object into a chain complex supported at zero then applying a functor is
the same as applying the functor then forming the complex.
-/
def single₀MapHomologicalComplex (F : V ⥤ W) [F.Additive] : single₀ V ⋙ F.mapHomologicalComplex _ ≅ F ⋙ single₀ W :=
  NatIso.ofComponents
    (fun X =>
      { Hom :=
          { f := fun i =>
              match i with
              | 0 => 𝟙 _
              | i + 1 => F.mapZeroObject.Hom },
        inv :=
          { f := fun i =>
              match i with
              | 0 => 𝟙 _
              | i + 1 => F.mapZeroObject.inv },
        hom_inv_id' := by
          ext (_ | i)
          · unfold_aux
            simp
            
          · unfold_aux
            dsimp
            simp only [comp_f, id_f, zero_comp]
            exact (zero_of_source_iso_zero _ F.map_zero_object).symm
            ,
        inv_hom_id' := by
          ext (_ | i) <;>
            · unfold_aux
              dsimp
              simp
               })
    fun X Y f => by
    ext (_ | i) <;>
      · unfold_aux
        dsimp
        simp
        

@[simp]
theorem single₀_map_homological_complex_hom_app_zero (F : V ⥤ W) [F.Additive] (X : V) :
    ((single₀MapHomologicalComplex F).Hom.app X).f 0 = 𝟙 _ :=
  rfl

@[simp]
theorem single₀_map_homological_complex_hom_app_succ (F : V ⥤ W) [F.Additive] (X : V) (n : ℕ) :
    ((single₀MapHomologicalComplex F).Hom.app X).f (n + 1) = 0 :=
  rfl

@[simp]
theorem single₀_map_homological_complex_inv_app_zero (F : V ⥤ W) [F.Additive] (X : V) :
    ((single₀MapHomologicalComplex F).inv.app X).f 0 = 𝟙 _ :=
  rfl

@[simp]
theorem single₀_map_homological_complex_inv_app_succ (F : V ⥤ W) [F.Additive] (X : V) (n : ℕ) :
    ((single₀MapHomologicalComplex F).inv.app X).f (n + 1) = 0 :=
  rfl

end ChainComplex

namespace CochainComplex

/-- Turning an object into a cochain complex supported at zero then applying a functor is
the same as applying the functor then forming the cochain complex.
-/
def single₀MapHomologicalComplex (F : V ⥤ W) [F.Additive] : single₀ V ⋙ F.mapHomologicalComplex _ ≅ F ⋙ single₀ W :=
  NatIso.ofComponents
    (fun X =>
      { Hom :=
          { f := fun i =>
              match i with
              | 0 => 𝟙 _
              | i + 1 => F.mapZeroObject.Hom },
        inv :=
          { f := fun i =>
              match i with
              | 0 => 𝟙 _
              | i + 1 => F.mapZeroObject.inv },
        hom_inv_id' := by
          ext (_ | i)
          · unfold_aux
            simp
            
          · unfold_aux
            dsimp
            simp only [comp_f, id_f, zero_comp]
            exact (zero_of_source_iso_zero _ F.map_zero_object).symm
            ,
        inv_hom_id' := by
          ext (_ | i) <;>
            · unfold_aux
              dsimp
              simp
               })
    fun X Y f => by
    ext (_ | i) <;>
      · unfold_aux
        dsimp
        simp
        

@[simp]
theorem single₀_map_homological_complex_hom_app_zero (F : V ⥤ W) [F.Additive] (X : V) :
    ((single₀MapHomologicalComplex F).Hom.app X).f 0 = 𝟙 _ :=
  rfl

@[simp]
theorem single₀_map_homological_complex_hom_app_succ (F : V ⥤ W) [F.Additive] (X : V) (n : ℕ) :
    ((single₀MapHomologicalComplex F).Hom.app X).f (n + 1) = 0 :=
  rfl

@[simp]
theorem single₀_map_homological_complex_inv_app_zero (F : V ⥤ W) [F.Additive] (X : V) :
    ((single₀MapHomologicalComplex F).inv.app X).f 0 = 𝟙 _ :=
  rfl

@[simp]
theorem single₀_map_homological_complex_inv_app_succ (F : V ⥤ W) [F.Additive] (X : V) (n : ℕ) :
    ((single₀MapHomologicalComplex F).inv.app X).f (n + 1) = 0 :=
  rfl

end CochainComplex

